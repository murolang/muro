defmodule Muro.Emit.C do
  @moduledoc """
  Emit a closed run book to C. Specs and evidence are omitted.
  Run bodies are the image from `Muro.IR`.

  `Nat` is a tagged struct. User data, indexed data included, is a tag
  plus fields. `match` is a `switch`. Erased arguments are dropped.
  `run internal` is `static`.

  A `run` stream is a struct: the seed, an environment for values the
  step closes over, and a function pointer for the step. `uncons` calls
  that function and builds a new struct for the tail. `Always`, `~`,
  and a raw `ν` in a run are refused (`c:stream`). `U8`, `U32`, `U64`,
  and `I64` are passed by value. Signed wrapping goes through `uint64_t`.
  A shift past the width and a division by zero are not evaluated.
  `F32`, `Tensor`, `addt`, and `packI` are refused (`c:machine`).
  A string is `muro__str`: a pointer and an octet length, passed by value.
  Scalar 0 is an octet in that buffer. A lambda applied on the spot is a
  local. An unapplied lambda, and a call of a local function, are
  `c:lambda`. An unboxed product in a pair, a stream seed, or an
  `Opt` is `c:unboxed`. An `Opt` of ordinary data is a pointer.

  Allocations call `muro__ALLOC`, which is `malloc` unless the caller
  defines it. A constructor with no fields is a static object and does
  not. An `unboxed data` constructor returns the struct by value and
  does not.

  Identifiers come from `Muro.Emit.Name`. A source name is spelled there.
  A helper, a step, a constructor argument, and a temporary are generated
  there. The two spellings share no identifier. A binder is claimed there
  against every name visible in its scope, including type names.
  """

  alias Muro.{Ast, Emit, IR}
  alias Muro.Emit.Name

  # Keywords through C23, including the underscore spellings. `bool`,
  # `true`, and `false` are also the `<stdbool.h>` macros.
  @c_keywords ~w(
    alignas alignof auto bool break case char const constexpr continue
    default do double else enum extern false float for goto if inline int
    long nullptr register restrict return short signed sizeof static
    static_assert struct switch thread_local true typedef typeof
    typeof_unqual union unsigned void volatile while
    _Alignas _Alignof _Atomic _BitInt _Bool _Complex _Decimal128 _Decimal32
    _Decimal64 _Generic _Imaginary _Noreturn _Static_assert _Thread_local
  ) |> MapSet.new()

  # Typedefs from `<stdint.h>`, which the header includes, and functions
  # from stdio, stdlib, string, and unistd. `delete` is a C++ keyword.
  # `error` is the GNU `error` function. `spell/3` matches the encoding,
  # which has no underscore, so a source `uint8_t` is `uint8zut` and does
  # not spell the typedef. A name outside this set is unchanged.
  @host_names ~w(
    int8_t int16_t int32_t int64_t uint8_t uint16_t uint32_t uint64_t
    int_least8_t int_least16_t int_least32_t int_least64_t
    uint_least8_t uint_least16_t uint_least32_t uint_least64_t
    int_fast8_t int_fast16_t int_fast32_t int_fast64_t
    uint_fast8_t uint_fast16_t uint_fast32_t uint_fast64_t
    intptr_t uintptr_t intmax_t uintmax_t size_t ptrdiff_t wchar_t
    NULL EOF assert offsetof stdin stdout stderr
    remove rename tmpfile tmpnam fclose fflush fopen freopen setbuf setvbuf
    fprintf fscanf printf scanf snprintf sprintf sscanf
    vfprintf vfscanf vprintf vscanf vsnprintf vsprintf vsscanf
    fgetc fgets fputc fputs getc getchar gets putc putchar puts ungetc
    fread fwrite fgetpos fseek fsetpos ftell rewind clearerr feof ferror perror
    atof atoi atol atoll strtod strtof strtold strtol strtoll strtoul strtoull
    rand srand calloc malloc realloc free aligned_alloc
    abort atexit at_quick_exit exit quick_exit getenv system bsearch qsort
    abs labs llabs div ldiv lldiv mblen mbtowc wctomb mbstowcs wcstombs
    memcpy memmove strcpy strncpy strcat strncat memcmp strcmp strncmp strcoll
    memchr strchr strrchr strcspn strspn strpbrk strstr strtok memset strerror strlen
    access alarm chdir chown close creat dup dup2
    execl execle execlp execv execve execvp
    fork fsync getcwd getegid geteuid getgid getpid getppid getuid
    isatty link lseek open pause pipe read rmdir
    setgid setuid sleep symlink sync unlink write
    delete error
  ) |> MapSet.new()

  @forbidden MapSet.union(@c_keywords, @host_names)

  @doc false
  def source_id(name) when is_binary(name), do: spell(name)

  @doc false
  def generated_samples do
    tags = ~w(
      nat unit pair stream atom
      zero suc tt nat_new mk_pair stream_new
      ALLOC tt_obj
      field_tag field_suc field_fst field_snd field_step field_seed field_env
      as unused
      envp seedp ep p n s
    )

    Enum.map(tags, &Name.gen/1) ++
      [
        Name.gen("step", 0),
        Name.gen("env", 0),
        Name.gen("ep", 0),
        Name.gen("f", 0),
        Name.gen("s", 0),
        Name.gen("t", 0),
        Name.gen("obj_List_nil")
      ]
  end

  defp spell(name), do: Name.spell(name, @forbidden)
  defp g(tag), do: Name.gen(tag)
  defp g(tag, n) when is_integer(n), do: Name.gen(tag, n)
  defp claim(base, used), do: Name.claim(base, used)

  defp nat_ptr, do: g("nat") <> " *"
  defp unit_ptr, do: g("unit") <> " *"
  defp pair_ptr, do: g("pair") <> " *"
  defp stream_ptr, do: g("stream") <> " *"
  defp atom_ty, do: g("atom") <> " "

  # Struct spellings, then atoms, then constructor functions. A run is
  # claimed after those, so a shared C namespace suffixes inside one
  # space. Generated names are not in this set: they already contain `__`.
  defp name_map(book) do
    {structs, taken} =
      Enum.reduce(data_defs(book), {%{}, MapSet.new()}, fn d, {map, used} ->
        {rn, used} = claim(spell(d.name), used)
        {Map.put(map, d.name, rn), used}
      end)

    {atoms, taken} =
      Enum.reduce(Ast.atoms(book), {%{}, taken}, fn name, {map, used} ->
        {rn, used} = claim(spell(name), used)
        {Map.put(map, name, rn), used}
      end)

    {ctors, taken} =
      Enum.reduce(data_defs(book), {%{}, taken}, fn d, {map, used} ->
        Enum.reduce(d.ctors, {map, used}, fn c, {map, used} ->
          {rn, used} = claim(spell(c.name), used)
          {Map.put(map, {d.name, c.name}, rn), used}
        end)
      end)

    %{structs: structs, atoms: atoms, ctors: ctors, taken: taken}
  end

  @doc """
  Render `book` as `{header, source}` for a file stem such as `half_ok`.

  Run bodies are printed from `Muro.IR`. A refusal is that elaboration's.
  """
  def render(book, stem) when is_list(book) and is_binary(stem) do
    case prepare(book, stem) do
      {:ok, header, source, _sigs} -> {:ok, {header, source}}
      {:error, _} = err -> err
    end
  end

  @doc """
  Names, signatures, layouts, and clause heads of the C file `render/2`
  writes. The signatures are the ones `compile_fun/6` builds for each
  run. No source is written.
  """
  def outline(book, stem) when is_list(book) and is_binary(stem) do
    case IR.elaborate(book) do
      {:ok, funs} ->
        nm = name_map(book)

        with :ok <- Emit.refuse_may_fail(book),
             :ok <- Emit.refuse_unboxed_opt(book, funs),
             {:ok, sigs, _texts, _extras} <- compile_funs(funs, book, nm),
             {:ok, groups, _} <- Emit.partition_funs(funs, Emit.run_defs(book)) do
          {:ok, c_outline(book, sigs, groups)}
        end

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp c_outline(book, sigs, groups) do
    user = Enum.map(groups, fn {fun, _} -> fun end)

    signatures =
      Enum.zip(sigs, user)
      |> Enum.map(fn {sig, fun} ->
        %{
          source: fun.name,
          name: sig.name,
          layout: fun.ret,
          param_layouts: Enum.map(fun.params, fn {_n, lay} -> lay end),
          params: Enum.map(sig.params, fn {_ty, cname} -> cname end),
          ret: sig.ret,
          export: sig.export
        }
      end)

    names =
      signatures
      |> Enum.flat_map(fn sig -> [sig.name | sig.params] end)
      |> Enum.uniq()

    %{
      names: names,
      elixir: Emit.elixir_names(book),
      signatures: signatures,
      layouts:
        Enum.map(signatures, &%{name: &1.source, layout: &1.layout, params: &1.param_layouts}) ++
          data_layouts(book),
      clauses: Enum.map(sigs, &decl/1)
    }
  end

  @doc """
  `render/2` plus the signature of each run, in book order.

  A signature is `%{name, export, params, ret}`. `name` is the C spelling.
  `params` is `{ctype, c_name}` for each live argument. `run internal` has
  `export: false`.
  """
  def prepare(book, stem) when is_list(book) and is_binary(stem) do
    case IR.elaborate(book) do
      {:ok, funs} ->
        nm = name_map(book)

        case compile_funs(funs, book, nm) do
          {:ok, sigs, texts, extras} ->
            runs = Emit.run_defs(book)
            bytes? = bytes_image?(funs) or data_field_bytes?(book)
            strings? = strings_image?(funs) or data_field_string?(book)

            with :ok <- Emit.refuse_may_fail(book),
                 :ok <- Emit.refuse_unboxed_opt(book, funs),
                 {:ok, opts} <- opt_typedefs(funs, book, bytes?) do
              {:ok, header(book, sigs, stem, nm, opts, bytes?, strings?),
               source(book, runs, sigs, texts, extras, stem, nm, opts, bytes?, strings?), sigs}
            end

          {:error, _} = err ->
            err
        end

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp compile_funs(funs, book, nm) do
    runs = Emit.run_defs(book)

    with {:ok, groups, step_map} <- Emit.partition_funs(funs, runs) do
      names = Emit.def_names(book, &spell/1, nm.taken)
      by_name = Map.new(groups, fn {fun, _} -> {fun.name, fun} end)

      Enum.reduce_while(groups, {:ok, [], [], []}, fn {fun, _steps}, {:ok, sigs, texts, extras} ->
        case compile_fun(fun, book, names, by_name, step_map, nm) do
          {:ok, sig, text, extra} ->
            {:cont, {:ok, sigs ++ [sig], texts ++ [text], extras ++ extra}}

          {:error, _} = err ->
            {:halt, err}
        end
      end)
    end
  end

  defp compile_fun(fun, book, names, by_name, step_map, nm) do
    file_scope = file_scope(nm, MapSet.new(Map.values(names)))

    {bound, scope} =
      Enum.map_reduce(fun.params, file_scope, fn {pname, lay}, scope ->
        {c, scope} = Name.bind(spell(pname), scope)
        {{pname, c, lay}, scope}
      end)

    sig = %{
      name: Map.fetch!(names, fun.name),
      source: fun.name,
      export: fun.export,
      params: for({_n, c, lay} <- bound, do: {ctype(lay, book), c}),
      ret: ctype(fun.ret, book)
    }

    env = Enum.reduce(bound, [], fn {n, c, lay}, env -> [{n, c, lay} | env] end)

    st = %{
      t: 0,
      s: 0,
      steps: [],
      envs: [],
      names: names,
      book: book,
      funs: by_name,
      steps_by_name: step_map,
      fold_done: MapSet.new(),
      nm: nm,
      file_scope: file_scope,
      base_scope: scope,
      scope: scope
    }

    with {:ok, {pre, expr, lay, st}} <- emit_ir(fun.body, env, st, sig.ret) do
      expr = as_ret(expr, lay, fun.ret)

      discards =
        bound
        |> Enum.reject(fn {n, _c, _lay} -> uses?(fun.body, n) end)
        |> Enum.map_join("\n", fn {_n, c, _lay} -> "  (void)#{c};" end)

      body =
        cond do
          discards != "" and pre != "" ->
            discards <> "\n" <> indent(pre, 2) <> "\n  return #{expr};"

          discards != "" ->
            discards <> "\n  return #{expr};"

          pre != "" ->
            indent(pre, 2) <> "\n  return #{expr};"

          true ->
            "  return #{expr};"
        end

      {:ok, sig, "#{decl(sig)} {\n#{body}\n}", st.envs ++ st.steps}
    end
  end

  defp decl(sig) do
    args =
      case sig.params do
        [] -> "void"
        ps -> Enum.map_join(ps, ", ", fn {ty, name} -> "#{ty}#{name}" end)
      end

    kw = if sig.export, do: "", else: "__attribute__((unused)) static "
    "#{kw}#{sig.ret}#{sig.name}(#{args})"
  end

  defp telescope(t), do: telescope(t, [])
  defp telescope({:pi, q, a, x, b}, acc), do: telescope(b, [{q, a, x} | acc])
  defp telescope(ret, acc), do: {Enum.reverse(acc), ret}

  defp emit_ir({:var, name}, env, st, _expect) do
    case lookup(env, name) do
      {c, lay} -> {:ok, {"", c, lay, st}}
      nil -> {:error, "c:unsupported"}
    end
  end

  defp emit_ir(:ze, _env, st, _expect), do: {:ok, {"", "#{g("zero")}()", :nat, st}}
  defp emit_ir(:tt, _env, st, _expect), do: {:ok, {"", "#{g("tt")}()", :unit, st}}

  defp emit_ir({:su, u}, env, st, _expect) do
    with {:ok, {pre, ex, _lay, st}} <- emit_ir(u, env, st, nat_ptr()) do
      {:ok, {pre, "#{g("suc")}(#{ex})", :nat, st}}
    end
  end

  defp emit_ir({:call, name, args}, env, st, _expect) do
    with {:ok, {pres, exprs, st}} <- emit_args(args, live_ctypes(st.book, name), env, st) do
      {:ok,
       {squash(pres), "#{ename(st, name)}(#{Enum.join(exprs, ", ")})", call_lay(st, name), st}}
    end
  end

  defp emit_ir({:con, "Atom", name, []}, _env, st, _expect) do
    {:ok, {"", atom_c(name, st.nm), {:data, "Atom"}, st}}
  end

  defp emit_ir({:con, dname, cname, args}, env, st, _expect) do
    with {:ok, {pres, exprs, st}} <- emit_args(args, con_ctypes(st.book, cname), env, st) do
      fun = Map.fetch!(st.nm.ctors, {dname, cname})
      {:ok, {squash(pres), "#{fun}(#{Enum.join(exprs, ", ")})", {:data, dname}, st}}
    end
  end

  # An erased constructor field, marked `:erased`. `0`, and the payload
  # is ignored. A zero passed under a spec alias is bound at the
  # argument's layout, so this clause does not see it.
  defp emit_ir({:let, name, :erased, _val, body}, env, st, expect) do
    {c, scope} = Name.bind(spell(name), st.scope)
    st = %{st | scope: scope}

    with {:ok, {pre, ex, lay, st}} <- emit_ir(body, [{name, c, :opaque} | env], st, expect) do
      void = if uses?(body, name), do: "", else: "(void)#{c};"
      {:ok, {squash(["void *#{c} = 0;", void, pre]), ex, lay, st}}
    end
  end

  # `matchEmpty`. The scrutinee is bound only so the expression is evaluated.
  defp emit_ir({:let, _name, _lay, val, :abort}, env, st, _expect) do
    with {:ok, {pre, ex, _vlay, st}} <- emit_ir(val, env, st, "void *") do
      stmt = squash([pre, "(void)(#{ex});", "/* unreachable */", "abort();"])
      {:ok, {stmt, "0", :opaque, st}}
    end
  end

  defp emit_ir({:let, name, lay, val, body}, env, st, expect) do
    ty = ctype(lay, st.book)

    with {:ok, {pre, ex, _vlay, st}} <- emit_ir(val, env, st, ty) do
      {local, st} = news(st)

      with {:ok, {pre2, ex2, blay, st}} <-
             emit_ir(body, [{name, local, lay} | env], st, expect) do
        void = if uses?(body, name), do: "", else: "(void)#{local};"
        stmt = squash([pre, "#{ty}#{local} = #{ex};", void, pre2])
        {:ok, {stmt, ex2, blay, st}}
      end
    end
  end

  defp emit_ir({:pair, a, b}, env, st, _expect) do
    with {:ok, {pre, ea, la, st}} <- emit_ir(a, env, st, "void *"),
         {:ok, {pre2, eb, lb, st}} <- emit_ir(b, env, st, "void *") do
      if unboxed_lay?(st.book, la) or unboxed_lay?(st.book, lb) do
        {:error, "c:unboxed"}
      else
        {:ok,
         {squash([pre, pre2]), "#{g("mk_pair")}(#{slot_store(ea, la)}, #{slot_store(eb, lb)})",
          {:pair, la, lb}, st}}
      end
    end
  end

  defp emit_ir({:letp, a, b, e, body}, env, st, expect) do
    with {:ok, {pre, ex, elay, st}} <- emit_ir(e, env, st, pair_ptr()) do
      {sname, st} = news(st)
      {ca, scope} = Name.bind(spell(a), st.scope)
      {cb, scope} = Name.bind(spell(b), scope)
      st = %{st | scope: scope}
      {la, lb} = pair_halves(elay)
      env1 = [{b, cb, lb}, {a, ca, la} | env]

      with {:ok, {pre2, ex2, blay, st}} <- emit_ir(body, env1, st, expect) do
        unused =
          [{a, ca}, {b, cb}]
          |> Enum.reject(fn {n, _} -> uses?(body, n) end)
          |> Enum.map_join("\n", fn {_n, c} -> "(void)#{c};" end)

        stmt =
          squash([
            pre,
            "#{pair_ptr()}#{sname} = #{ex};",
            bind_half_c(ca, sname, g("field_fst"), la),
            bind_half_c(cb, sname, g("field_snd"), lb),
            unused,
            pre2
          ])

        {:ok, {stmt, ex2, blay, st}}
      end
    end
  end

  defp emit_ir({:uncons, e}, env, st, _expect) do
    with {:ok, {pre, ex, elay, st}} <- emit_ir(e, env, st, stream_ptr()) do
      {sname, st} = news(st)
      {pname, st} = news(st)
      {hname, st} = news(st)
      {nname, st} = news(st)
      {tname, st} = news(st)

      stmt =
        squash([
          "#{stream_ptr()}#{sname} = #{ex};",
          "#{pair_ptr()}#{pname} = #{sname}->#{g("field_step")}(#{sname}->#{g("field_env")}, #{sname}->#{g("field_seed")});",
          "void *#{hname} = #{pname}->#{g("field_fst")};",
          "void *#{nname} = #{pname}->#{g("field_snd")};",
          "#{stream_ptr()}#{tname} = #{g("stream_new")}(#{nname}, #{sname}->#{g("field_env")}, #{sname}->#{g("field_step")});"
        ])

      {:ok, {squash([pre, stmt]), "#{g("mk_pair")}(#{hname}, #{tname})", uncons_lay(elay), st}}
    end
  end

  defp emit_ir({:stream, seed, caps, step_name}, env, st, _expect) do
    with {:ok, step} <- fetch_step(st, step_name),
         {:ok, {seed_p, cap_ps}} <- ok_split(step.params, caps),
         {:ok, {pre, seed_ex, seed_lay, st}} <-
           emit_ir(seed, env, st, ctype(lay_of(seed, env, st), st.book)) do
      id = step_id(step_name)
      slots = capture_slots(caps, cap_ps, st.file_scope)
      pointer_lays = [seed_lay | Enum.map(slots, fn {_n, _f, _tm, lay} -> lay end)]

      if Enum.any?(pointer_lays, &unboxed_lay?(st.book, &1)) do
        {:error, "c:unboxed"}
      else
        with {:ok, {cpre, outers, st}} <- emit_outers(slots, env, st) do
          {env_ty, env_src, env_ex, st} = alloc_env(slots, outers, id, st)
          saved = st.scope

          with {:ok, {src, st}} <- emit_step_fun(step, slots, seed_p, id, env_ty, st) do
            expr =
              "#{g("stream_new")}(#{slot_store(seed_ex, seed_lay)}, #{env_ex}, #{g("step", id)})"

            st = %{st | steps: st.steps ++ [src], scope: saved}

            {:ok,
             {squash([pre, cpre, env_src]), expr, {:stream, seed_domain(seed_p, seed_lay)}, st}}
          end
        end
      end
    end
  end

  defp emit_ir({:match, scrut, arms} = tm, env, st, expect) do
    kind = match_kind(lay_of(scrut, env, st), arms, st.book)
    rlay = lay_of(tm, env, st)
    # A word operation emits its operand as `void *`. The arms still
    # name a word, so the temporary uses that layout.
    expect = match_expect(expect, rlay, st.book)

    with {:ok, {pre, ex, _lay, st}} <- emit_ir(scrut, env, st, scrut_ty(kind, st.book)),
         {:ok, {stmt, name, st}} <- emit_switch(kind, pre, ex, arms, env, st, expect) do
      {:ok, {stmt, name, rlay, st}}
    end
  end

  defp emit_ir({:wrd, k, op, args}, env, st, expect) do
    with {:ok, {pres, exprs, st}} <- emit_word_args(args, env, st) do
      case word_c(k, op, exprs, st, expect) do
        {:ok, {more, expr, lay, st}} ->
          {:ok, {squash(pres ++ [more]), expr, lay, st}}

        {:error, _} = err ->
          err
      end
    end
  end

  defp emit_ir(:abort, _env, st, _expect) do
    {:ok, {squash(["/* unreachable */", "abort();"]), "0", :opaque, st}}
  end

  defp emit_ir({:byt, bin}, _env, st, _expect) when is_binary(bin) do
    if bin == "" do
      {:ok, {"", "#{g("slice_empty")}()", :slice, st}}
    else
      {name, st} = news(st)
      bytes = bin |> :binary.bin_to_list() |> Enum.map_join(", ", &Integer.to_string/1)
      pre = "static const uint8_t #{name}[] = {#{bytes}};"
      expr = "(#{g("slice")}){#{name}, sizeof #{name}}"
      {:ok, {pre, expr, :slice, st}}
    end
  end

  defp emit_ir({:bcat, a, b}, env, st, _expect) do
    with {:ok, {pa, ea, _, st}} <- emit_ir(a, env, st, slice_ty()),
         {:ok, {pb, eb, _, st}} <- emit_ir(b, env, st, slice_ty()) do
      {:ok, {squash([pa, pb]), "#{g("bytes_cat")}(#{ea}, #{eb})", :slice, st}}
    end
  end

  defp emit_ir({:blen, a}, env, st, _expect) do
    with {:ok, {pre, ex, _, st}} <- emit_ir(a, env, st, slice_ty()) do
      {:ok, {pre, "(uint64_t)((#{ex}).n)", :u64, st}}
    end
  end

  defp emit_ir({:beq, a, b}, env, st, _expect) do
    with {:ok, {pa, ea, _, st}} <- emit_ir(a, env, st, slice_ty()),
         {:ok, {pb, eb, _, st}} <- emit_ir(b, env, st, slice_ty()) do
      {:ok, {squash([pa, pb]), "#{g("slice_eq")}(#{ea}, #{eb})", :wbool, st}}
    end
  end

  defp emit_ir({:bsub, s, off, len}, env, st, _expect) do
    with {:ok, {ps, es, _, st}} <- emit_ir(s, env, st, slice_ty()),
         {:ok, {po, eo, _, st}} <- emit_ir(off, env, st, "uint64_t "),
         {:ok, {pn, en, _, st}} <- emit_ir(len, env, st, "uint64_t ") do
      {:ok, {squash([ps, po, pn]), "#{g("slice_sub")}(#{es}, #{eo}, #{en})", :slice, st}}
    end
  end

  defp emit_ir({:bget, s, i}, env, st, _expect) do
    with {:ok, {ps, es, _, st}} <- emit_ir(s, env, st, slice_ty()),
         {:ok, {pi, ei, _, st}} <- emit_ir(i, env, st, "uint64_t ") do
      {:ok, {squash([ps, pi]), "#{g("slice_get")}(#{es}, #{ei})", {:opt, :u8}, st}}
    end
  end

  defp emit_ir({:btil, s, b}, env, st, _expect) do
    with {:ok, {ps, es, _, st}} <- emit_ir(s, env, st, slice_ty()),
         {:ok, {pb, eb, _, st}} <- emit_ir(b, env, st, "uint8_t ") do
      {:ok, {squash([ps, pb]), "#{g("slice_until")}(#{es}, #{eb})", :slice, st}}
    end
  end

  defp emit_ir({:baft, s, b}, env, st, _expect) do
    with {:ok, {ps, es, _, st}} <- emit_ir(s, env, st, slice_ty()),
         {:ok, {pb, eb, _, st}} <- emit_ir(b, env, st, "uint8_t ") do
      {:ok, {squash([ps, pb]), "#{g("slice_after")}(#{es}, #{eb})", :slice, st}}
    end
  end

  defp emit_ir({:sbytes, s}, env, st, _expect) do
    with {:ok, {pre, ex, lay, st}} <- emit_ir(s, env, st, str_ty()) do
      {:ok, {pre, "#{g("str_bytes")}(#{as_str(ex, lay)})", :slice, st}}
    end
  end

  defp emit_ir({:bunc, s}, env, st, _expect) do
    nothing = Map.get(st.nm.ctors, {"Maybe", "nothing"})
    just = Map.get(st.nm.ctors, {"Maybe", "just"})

    if nothing == nil or just == nil do
      {:error, "c:unsupported"}
    else
      with {:ok, {pre, ex, _, st}} <- emit_ir(s, env, st, slice_ty()) do
        {out, st} = news(st)
        {bp, st} = news(st)
        {sp, st} = news(st)
        alloc = g("ALLOC")
        sl = g("slice")

        stmt = """
        #{struct_ptr("Maybe")}#{out};
        if ((#{ex}).n == 0) {
          #{out} = #{nothing}();
        } else {
          uint8_t *#{bp} = #{alloc}(1);
          if (#{bp} == 0) abort();
          *#{bp} = (#{ex}).p[0];
          #{sl} *#{sp} = #{alloc}(sizeof *#{sp});
          if (#{sp} == 0) abort();
          *#{sp} = (#{sl}){(#{ex}).p + 1, (#{ex}).n - 1};
          #{out} = #{just}(#{g("mk_pair")}(#{bp}, #{sp}));
        }
        """

        {:ok, {squash([pre, stmt]), out, {:data, "Maybe"}, st}}
      end
    end
  end

  defp emit_ir({:bfold, step, caps, z, s}, env, st, _expect) do
    with {:ok, st} <- ensure_fold_step(step, st),
         {:ok, {cpre, cexs, st}} <- emit_cap_list(caps, env, st),
         {:ok, {pz, ez, lay, st}} <- emit_ir(z, env, st, ctype(fold_ret(st, step), st.book)),
         {:ok, {ps, es, _, st}} <- emit_ir(s, env, st, slice_ty()) do
      {acc, st} = news(st)
      {cur, st} = news(st)
      {b, st} = news(st)
      {rest, st} = news(st)
      cty = ctype(lay, st.book)
      sl = g("slice")
      call = Enum.join(cexs ++ [b, rest, acc], ", ")

      loop = """
      #{cty}#{acc} = #{ez};
      #{sl} #{cur} = #{es};
      while (#{cur}.n > 0) {
        uint8_t #{b} = #{cur}.p[0];
        #{sl} #{rest} = (#{sl}){#{cur}.p + 1, #{cur}.n - 1};
        #{acc} = #{fold_cname(step)}(#{call});
        #{cur} = #{rest};
      }
      """

      {:ok, {squash([cpre, pz, ps, loop]), acc, lay, st}}
    end
  end

  defp emit_ir({:str, bin}, _env, st, _expect) when is_binary(bin) do
    if bin == "" do
      {:ok, {"", "#{g("str_empty")}()", :string, st}}
    else
      {name, st} = news(st)
      bytes = bin |> :binary.bin_to_list() |> Enum.map_join(", ", &Integer.to_string/1)
      pre = "static const uint8_t #{name}[] = {#{bytes}};"
      expr = "(#{g("str")}){#{name}, sizeof #{name}}"
      {:ok, {pre, expr, :string, st}}
    end
  end

  defp emit_ir({:scat, a, b}, env, st, _expect) do
    with {:ok, {pa, ea, la, st}} <- emit_ir(a, env, st, str_ty()),
         {:ok, {pb, eb, lb, st}} <- emit_ir(b, env, st, str_ty()) do
      {:ok,
       {squash([pa, pb]), "#{g("str_cat")}(#{as_str(ea, la)}, #{as_str(eb, lb)})", :string, st}}
    end
  end

  defp emit_ir({:slen, a}, env, st, _expect) do
    with {:ok, {pre, ex, lay, st}} <- emit_ir(a, env, st, str_ty()) do
      {:ok, {pre, "#{g("str_len")}(#{as_str(ex, lay)})", :nat, st}}
    end
  end

  defp emit_ir({:seq, a, b}, env, st, _expect) do
    with {:ok, {pa, ea, la, st}} <- emit_ir(a, env, st, str_ty()),
         {:ok, {pb, eb, lb, st}} <- emit_ir(b, env, st, str_ty()) do
      {:ok,
       {squash([pa, pb]), "#{g("str_eq")}(#{as_str(ea, la)}, #{as_str(eb, lb)})", :wbool, st}}
    end
  end

  defp emit_ir(_other, _env, _st, _expect), do: {:error, "c:unsupported"}

  # A pair slot and a stream seed are `void *`. The struct is copied
  # once; the octets stay where they are. A value that is already a
  # string is passed through.
  defp slot_store(ex, :string), do: "#{g("box_str")}(#{ex})"
  defp slot_store(ex, _lay), do: ex

  defp as_str(ex, :string), do: ex
  defp as_str(ex, _lay), do: "*(#{g("str")} *)(#{ex})"

  defp adapt(ex, lay, ty) do
    cond do
      lay == :string and String.trim(ty) == "void *" -> slot_store(ex, :string)
      String.trim(ty) == g("str") and lay != :string -> as_str(ex, lay)
      true -> ex
    end
  end

  defp bind_half_c(name, sname, field, :string) do
    "#{g("str")} #{name} = *(#{g("str")} *)#{sname}->#{field};"
  end

  defp bind_half_c(name, sname, field, _lay) do
    "void *#{name} = #{sname}->#{field};"
  end

  defp str_ty, do: g("str") <> " "

  defp cap_ref(ep, field, :string), do: "(*((#{g("str")} *)#{ep}->#{field}))"
  defp cap_ref(ep, field, _lay), do: "#{ep}->#{field}"

  defp seed_load(seedp, :string), do: "*(#{g("str")} *)#{seedp}"
  defp seed_load(seedp, _lay), do: seedp

  defp match_expect(expect, lay, book) do
    if String.trim(expect) == "void *" do
      ty = ctype(lay, book)
      if String.trim(ty) == "void *", do: expect, else: ty
    else
      expect
    end
  end

  defp emit_args(args, types, env, st) do
    paired = Enum.zip(args, pad_types(types, length(args)))

    Enum.reduce_while(paired, {:ok, [], [], st}, fn {arg, ty}, {:ok, pres, exprs, st} ->
      case emit_ir(arg, env, st, ty) do
        {:ok, {pre, ex, lay, st}} ->
          {:cont, {:ok, pres ++ [pre], exprs ++ [adapt(ex, lay, ty)], st}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, pres, exprs, st} -> {:ok, {pres, exprs, st}}
      err -> err
    end
  end

  defp pad_types(types, n) do
    types ++ List.duplicate("void *", max(n - length(types), 0))
  end

  defp scrut_ty(:nat, _book), do: nat_ptr()
  defp scrut_ty(:atom, _book), do: atom_ty()
  defp scrut_ty({:data, name}, book), do: ctype({:data, name}, book)
  defp scrut_ty(:wbool, book), do: ctype(:wbool, book)
  defp scrut_ty({:opt, pay}, book), do: ctype({:opt, pay}, book)
  defp scrut_ty(_, _book), do: "void *"

  # A pointer or a scalar accepts 0. A struct does not: `muro__slice t = 0`
  # is a type error. `{0}` is the universal initializer, and a scalar
  # written that way trips -Wbraces-around-scalar under -Wall.
  # A string is a struct whose pointer must not be a bare 0. The empty
  # value is a complete initializer, and the match arms overwrite it.
  defp init_temp(expect, tname) do
    ty = String.trim(expect)

    cond do
      ty == g("str") -> "#{expect}#{tname} = #{g("str_empty")}();"
      String.ends_with?(ty, "*") -> "#{expect}#{tname} = 0;"
      ty in ["uint8_t", "uint32_t", "uint64_t", "int64_t", "size_t"] -> "#{expect}#{tname} = 0;"
      ty == String.trim(atom_ty()) -> "#{expect}#{tname} = 0;"
      true -> "#{expect}#{tname} = {0};"
    end
  end

  defp emit_switch(:nat, pre, ex, [{:arm, "zero", [], z}, {:arm, "suc", [y], s}], env, st, expect) do
    {sname, st} = news(st)
    {tname, st} = newt(st)
    st = %{st | scope: st.base_scope}

    with {:ok, {zpre, zex, _lay, st}} <- emit_ir(z, env, st, expect) do
      st = %{st | scope: st.base_scope}
      {yname, scope} = Name.bind(spell(y), st.scope)
      st = %{st | scope: scope}

      with {:ok, {spre, sex, _lay, st}} <- emit_ir(s, [{y, yname, :nat} | env], st, expect) do
        stmt =
          squash([
            pre,
            init_temp(expect, tname),
            "{",
            "#{nat_ptr()}#{sname} = #{ex};",
            "switch (#{sname}->#{g("field_tag")}) {",
            "case 0: {",
            zpre,
            "#{tname} = #{zex};",
            "break;",
            "}",
            "case 1: {",
            "#{nat_ptr()}#{yname} = #{sname}->#{g("field_suc")};",
            spre,
            "#{tname} = #{sex};",
            "break;",
            "}",
            "default: {",
            "/* unreachable */",
            "abort();",
            "}",
            "}",
            "}"
          ])

        {:ok, {stmt, tname, st}}
      end
    end
  end

  defp emit_switch(:atom, pre, ex, arms, env, st, expect) do
    {sname, st} = news(st)
    {tname, st} = newt(st)

    with {:ok, {cases, st}} <- emit_atom_arms(arms, tname, env, st, expect) do
      stmt =
        squash([
          pre,
          init_temp(expect, tname),
          "{",
          "#{atom_ty()}#{sname} = #{ex};",
          "switch (#{sname}) {",
          cases,
          "default: {",
          "abort();",
          "}",
          "}",
          "}"
        ])

      {:ok, {stmt, tname, st}}
    end
  end

  defp emit_switch({:data, dname}, pre, ex, arms, env, st, expect) do
    case find_data(st.book, dname) do
      nil ->
        {:error, "c:unsupported"}

      data ->
        by_value = unboxed?(data)
        ptr = if by_value, do: struct_name(dname) <> " ", else: struct_ptr(dname)
        arrow = if by_value, do: ".", else: "->"
        {sname, st} = news(st)
        {tname, st} = newt(st)

        with {:ok, {cases, st}} <-
               emit_data_arms(arms, data, sname, tname, arrow, env, st, expect) do
          stmt =
            squash([
              pre,
              init_temp(expect, tname),
              "{",
              "#{ptr}#{sname} = #{ex};",
              "switch (#{sname}#{arrow}#{g("field_tag")}) {",
              cases,
              "default: {",
              "/* unreachable */",
              "abort();",
              "}",
              "}",
              "}"
            ])

          {:ok, {stmt, tname, st}}
        end
    end
  end

  # WBool is the uint8_t word. 1 is wtrue. The test allocates nothing.
  defp emit_switch(
         :wbool,
         pre,
         ex,
         [{:arm, "wtrue", [], t}, {:arm, "wfalse", [], f}],
         env,
         st,
         expect
       ) do
    {sname, st} = news(st)
    {tname, st} = newt(st)
    st = %{st | scope: st.base_scope}

    with {:ok, {tpre, tex, _lay, st}} <- emit_ir(t, env, st, expect) do
      st = %{st | scope: st.base_scope}

      with {:ok, {fpre, fex, _lay, st}} <- emit_ir(f, env, st, expect) do
        stmt =
          squash([
            pre,
            init_temp(expect, tname),
            "{",
            "#{ctype(:wbool, st.book)}#{sname} = #{ex};",
            "if (#{sname}) {",
            tpre,
            "#{tname} = #{tex};",
            "} else {",
            fpre,
            "#{tname} = #{fex};",
            "}",
            "}"
          ])

        {:ok, {stmt, tname, st}}
      end
    end
  end

  # Opt is the by-value struct. tag 0 is wnone. The payload is `val`.
  defp emit_switch(
         {:opt, pay},
         pre,
         ex,
         [{:arm, "wsome", [y], s}, {:arm, "wnone", [], n}],
         env,
         st,
         expect
       ) do
    {sname, st} = news(st)
    {tname, st} = newt(st)
    st = %{st | scope: st.base_scope}

    with {:ok, {npre, nex, _lay, st}} <- emit_ir(n, env, st, expect) do
      st = %{st | scope: st.base_scope}

      {bind, env1, st} =
        if uses?(s, y) do
          {yname, scope} = Name.bind(spell(y), st.scope)
          st = %{st | scope: scope}
          decl = "#{ctype(pay, st.book)}#{yname} = #{sname}.val;"
          {decl, [{y, yname, pay} | env], st}
        else
          {"", env, st}
        end

      with {:ok, {spre, sex, _lay, st}} <- emit_ir(s, env1, st, expect) do
        stmt =
          squash([
            pre,
            init_temp(expect, tname),
            "{",
            "#{ctype({:opt, pay}, st.book)}#{sname} = #{ex};",
            "if (#{sname}.tag) {",
            bind,
            spre,
            "#{tname} = #{sex};",
            "} else {",
            npre,
            "#{tname} = #{nex};",
            "}",
            "}"
          ])

        {:ok, {stmt, tname, st}}
      end
    end
  end

  defp emit_switch(_kind, _pre, _ex, _arms, _env, _st, _expect), do: {:error, "c:unsupported"}

  defp emit_atom_arms(arms, tname, env, st, expect) do
    emit_arm_list(arms, st, fn {:arm, name, _bs, body}, st ->
      st = %{st | scope: st.base_scope}

      with {:ok, {pre, ex, _lay, st}} <- emit_ir(body, env, st, expect) do
        text =
          squash([
            "case #{atom_c(name, st.nm)}: {",
            pre,
            "#{tname} = #{ex};",
            "break;",
            "}"
          ])

        {:ok, {text, st}}
      end
    end)
  end

  defp emit_data_arms(arms, data, sname, tname, arrow, env, st, expect) do
    emit_arm_list(arms, st, fn arm, st ->
      data_arm(arm, data, sname, tname, arrow, env, st, expect)
    end)
  end

  defp emit_arm_list(arms, st, fun) do
    Enum.reduce_while(arms, {:ok, [], st}, fn arm, {:ok, acc, st} ->
      case fun.(arm, st) do
        {:ok, {text, st}} -> {:cont, {:ok, acc ++ [text], st}}
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, cases, st} -> {:ok, {Enum.join(cases, "\n"), st}}
      err -> err
    end
  end

  defp data_arm({:arm, cname, binders, body}, data, sname, tname, arrow, env, st, expect) do
    ctor = Enum.find(data.ctors, &(&1.name == cname))
    tag = Enum.find_index(data.ctors, &(&1.name == cname))
    fields = if ctor, do: live_fields(ctor, st.book), else: []

    if ctor == nil or tag == nil or length(fields) != length(binders) do
      {:error, "c:unsupported"}
    else
      member = spell(cname)

      {decls, env1, scope} =
        Enum.zip(binders, fields)
        |> Enum.reduce({[], env, st.base_scope}, fn {bname, {ty, lay, k}}, {decls, env, scope} ->
          if uses?(body, bname) do
            {c, scope} = Name.bind(spell(bname), scope)
            decl = "#{ty}#{c} = #{sname}#{arrow}#{g("as")}.#{member}.#{g("f", k)};"
            {decls ++ [decl], [{bname, c, lay} | env], scope}
          else
            {decls, env, scope}
          end
        end)

      st = %{st | scope: scope}

      with {:ok, {pre, ex, _lay, st}} <- emit_ir(body, env1, st, expect) do
        text =
          squash([
            "case #{tag}: {",
            Enum.join(decls, "\n"),
            pre,
            "#{tname} = #{ex};",
            "break;",
            "}"
          ])

        {:ok, {text, st}}
      end
    end
  end

  defp live_fields(ctor, book) do
    {pis, _} = telescope(ctor.type)

    pis
    |> Enum.reject(fn {q, _, _} -> q == :erased end)
    |> Enum.with_index()
    |> Enum.map(fn {{_, a, _}, k} -> {ctype(a, book), type_layout(book, a), k} end)
  end

  defp fetch_step(st, name) do
    case Map.fetch(st.steps_by_name, name) do
      {:ok, step} -> {:ok, step}
      :error -> {:error, "c:unsupported"}
    end
  end

  defp ok_split(params, caps) do
    {cap_ps, rest} = Enum.split(params, length(caps))

    case rest do
      [] -> {:ok, {nil, cap_ps}}
      [seed] -> {:ok, {seed, cap_ps}}
      _ -> {:error, "c:unsupported"}
    end
  end

  defp step_id("step" <> n), do: String.to_integer(n)

  defp seed_domain(nil, lay), do: lay
  defp seed_domain({_name, lay}, _lay), do: lay

  # A capture field shares the struct, not the parameter namespace. Claim
  # it against the file, so a field stays `n` when the arm parameter is `n`.
  defp capture_slots(caps, cap_ps, file_scope) do
    lays = Enum.map(cap_ps, fn {_n, lay} -> lay end)

    {slots, _} =
      caps
      |> Enum.zip(lays)
      |> Enum.map_reduce(file_scope, fn {{name, tm}, lay}, scope ->
        {field, scope} = Name.bind(spell(name), scope)
        {{name, field, tm, lay}, scope}
      end)

    slots
  end

  defp emit_outers(slots, env, st) do
    Enum.reduce_while(slots, {:ok, [], [], st}, fn {_n, _f, tm, _lay}, {:ok, pres, exprs, st} ->
      case emit_ir(tm, env, st, "void *") do
        {:ok, {pre, ex, lay, st}} ->
          {:cont, {:ok, pres ++ [pre], exprs ++ [slot_store(ex, lay)], st}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, pres, exprs, st} -> {:ok, {squash(pres), exprs, st}}
      err -> err
    end
  end

  defp alloc_env([], _outers, _id, st), do: {nil, "", "0", st}

  defp alloc_env(slots, outers, id, st) do
    env_ty = g("env", id)
    var = g("ep", id)
    fields = Enum.map_join(slots, "\n", fn {_n, field, _tm, _lay} -> "  void *#{field};" end)
    typedef = "typedef struct {\n#{fields}\n} #{env_ty};"

    assigns =
      Enum.map_join(Enum.zip(slots, outers), "\n", fn {{_n, field, _tm, _lay}, outer} ->
        "#{var}->#{field} = #{outer};"
      end)

    pre =
      "#{env_ty} *#{var} = #{g("ALLOC")}(sizeof *#{var});\nif (#{var} == 0) abort();\n#{assigns}"

    {env_ty, pre, var, %{st | envs: st.envs ++ [typedef]}}
  end

  defp emit_step_fun(step, slots, seed_p, id, env_ty, st) do
    ep = g("ep")
    envp = g("envp")
    seedp = g("seedp")
    saved_base = st.base_scope

    cap_env =
      Enum.reduce(Enum.reverse(slots), [], fn {name, field, _tm, lay}, env ->
        [{name, cap_ref(ep, field, lay), lay} | env]
      end)

    visible =
      [ep, envp, seedp | Enum.map(slots, &elem(&1, 1))]
      |> Enum.reduce(st.file_scope, &Name.see(&2, &1))

    {seed_line, env, step_base} =
      case seed_p do
        nil ->
          {"  (void)#{seedp};", cap_env, visible}

        {sname, slay} ->
          # An unfold binder the body never reads stays out of the step.
          # The parameter is still named; a dead local is -Wunused-variable.
          if uses?(step.body, sname) do
            {local, visible} = Name.bind(spell(sname), visible)
            line = "  #{ctype(slay, st.book)}#{local} = #{seed_load(seedp, slay)};"
            {line, [{sname, local, slay} | cap_env], visible}
          else
            {"  (void)#{seedp};", cap_env, visible}
          end
      end

    env_line =
      if slots == [] do
        "  (void)#{envp};"
      else
        "  #{env_ty} *#{ep} = #{envp};"
      end

    st = %{st | scope: step_base, base_scope: step_base}

    with {:ok, {pre, expr, _lay, st}} <- emit_ir(step.body, env, st, pair_ptr()) do
      st = %{st | base_scope: saved_base, scope: saved_base}
      {:ok, {step_text(id, env_line <> "\n" <> seed_line, pre, expr), st}}
    end
  end

  defp step_text(id, bind, pre, expr) do
    ret =
      if pre == "" do
        "  return #{expr};"
      else
        indent(pre, 2) <> "\n  return #{expr};"
      end

    "static #{pair_ptr()}#{g("step", id)}(void *#{g("envp")}, void *#{g("seedp")}) {\n" <>
      bind <> "\n" <> ret <> "\n}"
  end

  defp lay_of({:var, name}, env, _st) do
    case lookup(env, name) do
      {_c, lay} -> lay
      nil -> :opaque
    end
  end

  # The mark is `:erased`. A use keeps the opaque layout.
  defp lay_of({:let, name, :erased, _val, body}, env, st) do
    lay_of(body, [{name, "", :opaque} | env], st)
  end

  defp lay_of({:let, name, lay, _val, body}, env, st) do
    lay_of(body, [{name, "", lay} | env], st)
  end

  defp lay_of({:call, name, _}, _env, st), do: call_lay(st, name)
  defp lay_of({:con, d, _, _}, _env, _st), do: {:data, d}
  defp lay_of(:ze, _env, _st), do: :nat
  defp lay_of({:su, _}, _env, _st), do: :nat
  defp lay_of(:tt, _env, _st), do: :unit

  defp lay_of({:pair, a, b}, env, st), do: {:pair, lay_of(a, env, st), lay_of(b, env, st)}

  defp lay_of({:letp, a, b, e, body}, env, st) do
    {la, lb} = pair_halves(lay_of(e, env, st))
    lay_of(body, [{b, "", lb}, {a, "", la} | env], st)
  end

  defp lay_of({:uncons, e}, env, st), do: uncons_lay(lay_of(e, env, st))
  defp lay_of(:abort, _env, _st), do: :opaque

  defp lay_of({:stream, seed, caps, step_name}, env, st) do
    case Map.get(st.steps_by_name, step_name) do
      %{params: params} ->
        case ok_split(params, caps) do
          {:ok, {nil, _}} -> {:stream, lay_of(seed, env, st)}
          {:ok, {{_n, lay}, _}} -> {:stream, lay}
          _ -> {:stream, lay_of(seed, env, st)}
        end

      _ ->
        {:stream, lay_of(seed, env, st)}
    end
  end

  # These forms carry their layout on the term. A match on sliceGet is
  # Opt U8, and a match on bytesEq or eqi is WBool. Reconstructing that
  # here is what the switch uses for the scrutinee type.
  defp lay_of({:bget, _, _}, _env, _st), do: {:opt, :u8}
  defp lay_of({:beq, _, _}, _env, _st), do: :wbool
  defp lay_of({:byt, _}, _env, _st), do: :slice
  defp lay_of({:bcat, _, _}, _env, _st), do: :slice
  defp lay_of({:blen, _}, _env, _st), do: :u64
  defp lay_of({:bsub, _, _, _}, _env, _st), do: :slice
  defp lay_of({:btil, _, _}, _env, _st), do: :slice
  defp lay_of({:baft, _, _}, _env, _st), do: :slice
  defp lay_of({:str, _}, _env, _st), do: :string
  defp lay_of({:scat, _, _}, _env, _st), do: :string
  defp lay_of({:slen, _}, _env, _st), do: :nat
  defp lay_of({:seq, _, _}, _env, _st), do: :wbool
  defp lay_of({:sbytes, _}, _env, _st), do: :slice
  defp lay_of({:wrd, k, op, _}, _env, _st), do: wrd_lay(k, op)

  defp lay_of({:match, scrut, arms}, env, st) do
    case match_kind(lay_of(scrut, env, st), arms, st.book) do
      :nat -> arm_result(arms, env, st)
      :atom -> arm_result(arms, env, st)
      :wbool -> arm_result(arms, env, st)
      {:opt, pay} -> opt_result(pay, arms, env, st)
      {:data, dname} -> data_result(dname, arms, env, st)
      :unknown -> :opaque
    end
  end

  defp lay_of(_, _env, _st), do: :opaque

  defp wrd_lay(_k, op) when op in [true, false, :eq, :lt, :le], do: :wbool
  defp wrd_lay(_k, :none), do: {:opt, :opaque}
  defp wrd_lay(k, :some), do: {:opt, k}
  defp wrd_lay(_k, :ton), do: :nat
  defp wrd_lay(k, {:lit, _, _}), do: k
  defp wrd_lay(k, {:of, _}), do: k
  defp wrd_lay(k, {:cast, _}), do: k
  defp wrd_lay(k, op) when op in [:add, :sub, :mul, :and, :or, :xor, :not, :shl, :shr], do: k
  defp wrd_lay(k, op) when op in [:cadd, :csub, :cmul, :div, :rem], do: {:opt, k}
  defp wrd_lay(_, _), do: :opaque

  defp arm_result([{:arm, _, _, body} | _], env, st), do: lay_of(body, env, st)
  defp arm_result(_, _env, _st), do: :opaque

  defp opt_result(pay, [{:arm, "wsome", [y], body} | _], env, st) do
    lay_of(body, [{y, "", pay} | env], st)
  end

  defp opt_result(_pay, arms, env, st), do: arm_result(arms, env, st)

  defp data_result(dname, [{:arm, cname, binders, body} | _], env, st) do
    env1 =
      binders
      |> Enum.zip(field_lays(st.book, dname, cname))
      |> Enum.reduce(env, fn {name, lay}, env -> [{name, "", lay} | env] end)

    lay_of(body, env1, st)
  end

  defp data_result(_dname, _, _env, _st), do: :opaque

  defp field_lays(book, dname, cname) do
    data = find_data(book, dname)
    ctor = data && Enum.find(data.ctors, &(&1.name == cname))

    if ctor == nil do
      []
    else
      {pis, _} = telescope(ctor.type)

      Enum.flat_map(pis, fn
        {:erased, _, _} -> []
        {_, a, _} -> [type_layout(book, a)]
      end)
    end
  end

  defp match_kind(:nat, _arms, _book), do: :nat
  defp match_kind(:wbool, _arms, _book), do: :wbool
  defp match_kind({:opt, pay}, _arms, _book), do: {:opt, pay}
  defp match_kind({:data, "Atom"}, _arms, _book), do: :atom
  defp match_kind({:data, name}, _arms, _book), do: {:data, name}
  defp match_kind(_lay, [{:arm, "zero", [], _}, {:arm, "suc", [_], _}], _book), do: :nat
  defp match_kind(_lay, [{:arm, "wtrue", [], _}, {:arm, "wfalse", [], _}], _book), do: :wbool

  defp match_kind(_lay, [{:arm, "wsome", [_], _}, {:arm, "wnone", [], _}], _book),
    do: {:opt, :opaque}

  defp match_kind(_lay, arms, book) do
    cond do
      atom_arms?(arms, book) -> :atom
      name = ctor_data(arms, book) -> {:data, name}
      true -> :unknown
    end
  end

  defp atom_arms?(arms, book) do
    atoms = Ast.atoms(book)

    atoms != [] and
      Enum.all?(arms, fn
        {:arm, name, [], _} -> name in atoms
        _ -> false
      end)
  end

  defp ctor_data([{:arm, cname, _, _} | _], book) do
    case data_of_ctor(book, cname) do
      %{name: name} -> name
      _ -> nil
    end
  end

  defp ctor_data(_, _), do: nil

  defp type_layout(_book, :bytes), do: :slice
  defp type_layout(_book, :slice), do: :slice
  defp type_layout(_book, :string), do: :string
  defp type_layout(_book, :nat), do: :nat
  defp type_layout(_book, :unit), do: :unit
  defp type_layout(_book, :atom), do: {:data, "Atom"}
  defp type_layout(book, {:stream, a}), do: {:stream, type_layout(book, a)}

  defp type_layout(book, {:var, name}) do
    if data?(book, name), do: {:data, name}, else: :opaque
  end

  defp type_layout(book, {:def, name}), do: type_layout(book, {:var, name})
  defp type_layout(book, {:app, f, _}), do: type_layout(book, f)

  defp type_layout(book, {:prod, a, b}) do
    {:pair, type_layout(book, a), type_layout(book, b)}
  end

  defp type_layout(book, {:ann, e, _}), do: type_layout(book, e)
  defp type_layout(_book, :i64), do: :i64
  defp type_layout(_book, {:word, {:ty, :u8}, []}), do: :u8
  defp type_layout(_book, {:word, {:ty, :u32}, []}), do: :u32
  defp type_layout(_book, {:word, {:ty, :u64}, []}), do: :u64
  defp type_layout(_book, {:word, :bool, []}), do: :wbool
  defp type_layout(_book, {:word, {:optk, :u8}, []}), do: {:opt, :u8}
  defp type_layout(_book, {:word, {:optk, :u32}, []}), do: {:opt, :u32}
  defp type_layout(_book, {:word, {:optk, :u64}, []}), do: {:opt, :u64}
  defp type_layout(_book, {:word, {:optk, :i64}, []}), do: {:opt, :i64}
  defp type_layout(book, {:word, :opt, [a]}), do: {:opt, type_layout(book, a)}
  defp type_layout(_book, _), do: :opaque

  defp pair_halves({:pair, a, b}), do: {a, b}
  defp pair_halves(_), do: {:opaque, :opaque}

  defp uncons_lay({:stream, s}), do: {:pair, :opaque, {:stream, s}}
  defp uncons_lay(_), do: {:pair, :opaque, :opaque}

  defp call_lay(st, name) do
    case Map.get(st.funs, name) do
      %{ret: lay} -> lay
      _ -> :opaque
    end
  end

  defp live_ctypes(book, name) do
    type =
      cond do
        d = find_def(book, name) -> d.type
        c = find_ctor(book, name) -> c.type
        true -> nil
      end

    case type do
      nil -> []
      ty -> live_ctypes_of(ty, book)
    end
  end

  defp con_ctypes(book, cname) do
    case find_ctor(book, cname) do
      nil -> []
      ctor -> live_ctypes_of(ctor.type, book)
    end
  end

  defp live_ctypes_of(ty, book) do
    {pis, _} = telescope(ty)

    Enum.flat_map(pis, fn
      {:erased, _, _} -> []
      {_, a, _} -> [ctype(a, book)]
    end)
  end

  defp find_ctor(book, name) do
    Enum.find_value(book, fn
      %{kind: :data, ctors: cs} -> Enum.find(cs, &(&1.name == name))
      _ -> nil
    end)
  end

  defp find_def(book, name) do
    Enum.find(
      book,
      &(Map.get(&1, :kind, :def) not in [:data, :repr] and Map.get(&1, :name) == name)
    )
  end

  defp find_data(book, name) when is_list(book) do
    Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp find_data(_book, _name), do: nil

  defp data_of_ctor(book, name) do
    Enum.find(book, fn
      %{kind: :data, ctors: cs} -> Enum.any?(cs, &(&1.name == name))
      _ -> false
    end)
  end

  defp lookup(env, name) do
    Enum.find_value(env, fn
      {^name, c, lay} -> {c, lay}
      _ -> nil
    end)
  end

  defp uses?(t, name) when is_tuple(t) do
    t == {:var, name} or t |> Tuple.to_list() |> Enum.any?(&uses?(&1, name))
  end

  defp uses?(t, name) when is_list(t), do: Enum.any?(t, &uses?(&1, name))
  defp uses?(_, _), do: false

  defp news(st), do: {g("s", st.s), %{st | s: st.s + 1}}
  defp newt(st), do: {g("t", st.t), %{st | t: st.t + 1}}

  defp emit_word_args(args, env, st) do
    Enum.reduce_while(args, {:ok, {[], [], st}}, fn arg, {:ok, {pres, exprs, st}} ->
      case emit_ir(arg, env, st, "void *") do
        {:ok, {pre, ex, _lay, st}} -> {:cont, {:ok, {pres ++ [pre], exprs ++ [ex], st}}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp word_c(k, {:lit, k, n}, [], st, _expect) do
    {:ok, {"", c_word_lit(k, n), k, st}}
  end

  defp word_c(_k, true, [], st, _expect), do: {:ok, {"", "1", :wbool, st}}
  defp word_c(_k, false, [], st, _expect), do: {:ok, {"", "0", :wbool, st}}

  defp word_c(_k, :none, [], st, expect) do
    ty =
      if String.starts_with?(String.trim(expect), g("opt")) do
        String.trim(expect)
      else
        opt_name(:u8)
      end

    {tmp, st} = news(st)

    pre =
      if ty == opt_name(:string) do
        "#{ty} #{tmp} = {.tag = 0, .val = #{g("str_empty")}()};"
      else
        "#{ty} #{tmp};\n#{tmp}.tag = 0;\n#{tmp}.val = 0;"
      end

    {:ok, {pre, tmp, {:opt, :opaque}, st}}
  end

  defp word_c(k, {:of, k}, [nat], st, _expect) do
    {acc, st} = news(st)
    {p, st} = news(st)

    pre = """
    uint64_t #{acc} = 0;
    #{g("nat")} *#{p} = #{nat};
    while (#{p}->#{g("field_tag")} != 0) {
      #{acc}++;
      #{p} = #{p}->#{g("field_suc")};
    }
    """

    {:ok, {pre, "(#{cty(k)})#{acc}", k, st}}
  end

  defp word_c(_k, :ton, [x], st, _expect) do
    {n, st} = news(st)
    {r, st} = news(st)

    pre = """
    uint64_t #{n} = (uint64_t)(#{x});
    #{g("nat")} *#{r} = #{g("zero")}();
    while (#{n} != 0) {
      #{r} = #{g("suc")}(#{r});
      #{n}--;
    }
    """

    {:ok, {pre, r, :nat, st}}
  end

  defp word_c(k, op, [x, y], st, _expect) when op in [:add, :sub, :mul] do
    {:ok, {"", wrap_bin(op, k, x, y), k, st}}
  end

  defp word_c(k, op, [x, y], st, _expect) when op in [:and, :or, :xor] do
    {:ok, {"", bit_bin(op, k, x, y), k, st}}
  end

  defp word_c(k, :not, [x], st, _expect), do: {:ok, {"", bit_not(k, x), k, st}}

  defp word_c(k, op, [x, y], st, _expect) when op in [:eq, :lt, :le] do
    {:ok, {"", cmp_c(op, k, x, y), :wbool, st}}
  end

  defp word_c(k, op, [x, y], st, _expect) when op in [:cadd, :csub, :cmul] do
    checked_c(k, op, x, y, st)
  end

  defp word_c(k, op, [x, y], st, _expect) when op in [:div, :rem] do
    divrem_c(k, op, x, y, st)
  end

  defp word_c(k, op, [x, amt], st, _expect) when op in [:shl, :shr] do
    shift_c(k, op, x, amt, st)
  end

  defp word_c(k, {:cast, k}, [x], st, _expect), do: {:ok, {"", cast_c(k, x), k, st}}

  defp word_c(k, :some, [x], st, _expect) do
    {tmp, st} = news(st)
    name = opt_name(k)
    pre = "#{name} #{tmp};\n#{tmp}.tag = 1;\n#{tmp}.val = #{x};"
    {:ok, {pre, tmp, {:opt, k}, st}}
  end

  defp word_c(_k, _op, _args, _st, _expect), do: {:error, "c:unsupported"}

  defp cty(:u8), do: "uint8_t"
  defp cty(:u32), do: "uint32_t"
  defp cty(:u64), do: "uint64_t"
  defp cty(:i64), do: "int64_t"

  defp c_width(:u8), do: 8
  defp c_width(:u32), do: 32
  defp c_width(:u64), do: 64
  defp c_width(:i64), do: 64

  defp c_word_lit(:i64, n) do
    n = rem(n, 18_446_744_073_709_551_616)
    if n >= 9_223_372_036_854_775_808, do: "(int64_t)UINT64_C(#{n})", else: "#{n}LL"
  end

  defp c_word_lit(k, n) do
    mod =
      if k == :u8,
        do: 256,
        else: if(k == :u32, do: 4_294_967_296, else: 18_446_744_073_709_551_616)

    "(#{cty(k)})UINT64_C(#{rem(n, mod)})"
  end

  defp wrap_bin(:add, :i64, x, y), do: "(int64_t)((uint64_t)(#{x}) + (uint64_t)(#{y}))"
  defp wrap_bin(:sub, :i64, x, y), do: "(int64_t)((uint64_t)(#{x}) - (uint64_t)(#{y}))"
  defp wrap_bin(:mul, :i64, x, y), do: "(int64_t)((uint64_t)(#{x}) * (uint64_t)(#{y}))"
  defp wrap_bin(:add, :u64, x, y), do: "(uint64_t)((uint64_t)(#{x}) + (uint64_t)(#{y}))"
  defp wrap_bin(:sub, :u64, x, y), do: "(uint64_t)((uint64_t)(#{x}) - (uint64_t)(#{y}))"
  defp wrap_bin(:mul, :u64, x, y), do: "(uint64_t)((uint64_t)(#{x}) * (uint64_t)(#{y}))"
  defp wrap_bin(:add, :u32, x, y), do: "(uint32_t)((uint64_t)(#{x}) + (uint64_t)(#{y}))"
  defp wrap_bin(:sub, :u32, x, y), do: "(uint32_t)((uint64_t)(#{x}) - (uint64_t)(#{y}))"
  defp wrap_bin(:mul, :u32, x, y), do: "(uint32_t)((uint64_t)(#{x}) * (uint64_t)(#{y}))"
  defp wrap_bin(:add, :u8, x, y), do: "(uint8_t)((uint32_t)(#{x}) + (uint32_t)(#{y}))"
  defp wrap_bin(:sub, :u8, x, y), do: "(uint8_t)((uint32_t)(#{x}) - (uint32_t)(#{y}))"
  defp wrap_bin(:mul, :u8, x, y), do: "(uint8_t)((uint32_t)(#{x}) * (uint32_t)(#{y}))"

  defp bit_bin(op, :i64, x, y) do
    sym = bit_sym(op)
    "(int64_t)((uint64_t)(#{x}) #{sym} (uint64_t)(#{y}))"
  end

  defp bit_bin(op, k, x, y) do
    wide = if k == :u8, do: "uint32_t", else: cty(k)
    "(#{cty(k)})((#{wide})(#{x}) #{bit_sym(op)} (#{wide})(#{y}))"
  end

  defp bit_sym(:and), do: "&"
  defp bit_sym(:or), do: "|"
  defp bit_sym(:xor), do: "^"

  defp bit_not(:i64, x), do: "(int64_t)(~(uint64_t)(#{x}))"

  defp bit_not(k, x) do
    wide = if k == :u8, do: "uint32_t", else: cty(k)
    "(#{cty(k)})(~(#{wide})(#{x}))"
  end

  defp cmp_c(:eq, _k, x, y), do: "(uint8_t)((#{x}) == (#{y}))"
  defp cmp_c(:lt, _k, x, y), do: "(uint8_t)((#{x}) < (#{y}))"
  defp cmp_c(:le, _k, x, y), do: "(uint8_t)((#{x}) <= (#{y}))"

  defp checked_c(k, op, x, y, st) do
    {tmp, st} = news(st)
    {out, st} = news(st)
    name = opt_name(k)
    builtin = checked_builtin(op)

    pre = """
    #{cty(k)} #{tmp};
    #{name} #{out};
    if (#{builtin}(#{x}, #{y}, &#{tmp})) {
      #{out}.tag = 0;
      #{out}.val = 0;
    } else {
      #{out}.tag = 1;
      #{out}.val = #{tmp};
    }
    """

    {:ok, {pre, out, {:opt, k}, st}}
  end

  defp checked_builtin(:cadd), do: "__builtin_add_overflow"
  defp checked_builtin(:csub), do: "__builtin_sub_overflow"
  defp checked_builtin(:cmul), do: "__builtin_mul_overflow"

  defp divrem_c(k, op, x, y, st) do
    {out, st} = news(st)
    name = opt_name(k)
    sym = if op == :div, do: "/", else: "%"

    pre = """
    #{name} #{out};
    if (#{div_guard(k, x, y)}) {
      #{out}.tag = 0;
      #{out}.val = 0;
    } else {
      #{out}.tag = 1;
      #{out}.val = (#{x}) #{sym} (#{y});
    }
    """

    {:ok, {pre, out, {:opt, k}, st}}
  end

  defp div_guard(:i64, x, y) do
    "(#{y}) == 0 || ((uint64_t)(#{x}) == (UINT64_C(1) << 63) && (uint64_t)(#{y}) == UINT64_MAX)"
  end

  defp div_guard(_k, _x, y), do: "(#{y}) == 0"

  defp shift_c(k, op, x, amt, st) do
    {sh, st} = news(st)
    {p, st} = news(st)
    {out, st} = news(st)
    w = c_width(k)
    nat = g("nat")
    tag = g("field_tag")
    suc = g("field_suc")

    pre = """
    unsigned #{sh} = 0;
    const #{nat} *#{p} = #{amt};
    while (#{p}->#{tag} != 0 && #{sh} + 1u < #{w}u) {
      #{sh}++;
      #{p} = #{p}->#{suc};
    }
    #{cty(k)} #{out};
    if (#{p}->#{tag} != 0) {
      #{out} = #{shift_oob(k, op, x)};
    } else {
      #{out} = #{shift_in(k, op, x, sh)};
    }
    """

    {:ok, {pre, out, k, st}}
  end

  defp shift_oob(k, :shl, _x), do: "(#{cty(k)})0"
  defp shift_oob(k, :shr, _x) when k != :i64, do: "(#{cty(k)})0"

  defp shift_oob(:i64, :shr, x) do
    "((uint64_t)(#{x}) >= (UINT64_C(1) << 63)) ? (int64_t)UINT64_MAX : 0"
  end

  defp shift_in(:u8, :shl, x, sh), do: "(uint8_t)((uint32_t)(#{x}) << #{sh})"
  defp shift_in(:u32, :shl, x, sh), do: "(uint32_t)((uint64_t)(#{x}) << #{sh})"
  defp shift_in(:u64, :shl, x, sh), do: "(uint64_t)((uint64_t)(#{x}) << #{sh})"
  defp shift_in(:i64, :shl, x, sh), do: "(int64_t)((uint64_t)(#{x}) << #{sh})"
  defp shift_in(:u8, :shr, x, sh), do: "(uint8_t)((uint32_t)(#{x}) >> #{sh})"
  defp shift_in(:u32, :shr, x, sh), do: "(uint32_t)((uint64_t)(#{x}) >> #{sh})"
  defp shift_in(:u64, :shr, x, sh), do: "(uint64_t)((#{x}) >> #{sh})"

  defp shift_in(:i64, :shr, x, sh) do
    "((#{sh}) == 0) ? (#{x}) : (int64_t)(((uint64_t)(#{x}) >> #{sh}) | (((uint64_t)(#{x}) >= (UINT64_C(1) << 63)) ? (~((UINT64_C(1) << (64u - #{sh})) - 1u)) : 0u))"
  end

  defp cast_c(:u8, x), do: "(uint8_t)(uint64_t)(#{x})"
  defp cast_c(:u32, x), do: "(uint32_t)(uint64_t)(#{x})"
  defp cast_c(:u64, x), do: "(uint64_t)(#{x})"
  defp cast_c(:i64, x), do: "(int64_t)(uint64_t)(#{x})"

  defp opt_typedefs(funs, book, bytes?) do
    extra = if bytes?, do: [{:opt, :u8}], else: []

    payloads =
      (funs ++ extra ++ data_field_opts(book))
      |> Enum.flat_map(fn
        fun when is_map(fun) ->
          [fun.ret | Enum.map(fun.params, fn {_n, lay} -> lay end)] ++ collect_opts(fun.body, [])

        lay ->
          [lay]
      end)
      |> Enum.flat_map(&opt_payloads/1)
      |> Enum.uniq()

    if Enum.any?(payloads, &unboxed_opt_pay?(book, &1)) do
      {:error, "c:unboxed"}
    else
      {:ok, Enum.map_join(payloads, "\n", &opt_typedef(&1, book))}
    end
  end

  defp collect_opts(tm, acc) when is_tuple(tm) do
    acc =
      case carried_opt(tm) do
        nil -> acc
        lay -> [lay | acc]
      end

    Enum.reduce(Tuple.to_list(tm), acc, &collect_opts/2)
  end

  defp collect_opts(tm, acc) when is_list(tm), do: Enum.reduce(tm, acc, &collect_opts/2)
  defp collect_opts(_tm, acc), do: acc

  # A checked word or a division is Opt even when no binder mentions Opt.
  defp carried_opt({:opt, _} = lay), do: lay
  defp carried_opt({:bget, _, _}), do: {:opt, :u8}
  defp carried_opt({:aget, _, _}), do: {:opt, :u8}
  defp carried_opt({:wrd, k, op, _}) when op in [:div, :rem, :cadd, :csub, :cmul], do: {:opt, k}
  defp carried_opt(_), do: nil

  # A field of Opt is that struct even when no run returns Opt.
  defp data_field_opts(book) do
    book
    |> data_defs()
    |> Enum.flat_map(fn d ->
      Enum.flat_map(d.ctors, fn ctor ->
        {pis, _} = telescope(ctor.type)

        Enum.flat_map(pis, fn
          {:erased, _, _} -> []
          {_, a, _} -> [type_layout(book, a)]
        end)
      end)
    end)
  end

  defp opt_payloads({:opt, p} = lay), do: [lay | opt_payloads(p)]
  defp opt_payloads({:pair, a, b}), do: opt_payloads(a) ++ opt_payloads(b)
  defp opt_payloads({:stream, a}), do: opt_payloads(a)
  defp opt_payloads(_), do: []

  # The option struct is printed before the data structs. A boxed
  # payload is a pointer, so the later struct completes it. An unboxed
  # payload would be that struct by value while it is still incomplete.
  defp unboxed_opt_pay?(book, {:opt, {:data, name}}) when is_binary(name) do
    unboxed_name?(book, name)
  end

  defp unboxed_opt_pay?(book, {:opt, {:opt, _} = inner}), do: unboxed_opt_pay?(book, inner)
  defp unboxed_opt_pay?(_book, _lay), do: false

  defp opt_typedef({:opt, pay}, book) do
    name = opt_name(pay)

    """
    typedef struct #{name} #{name};
    struct #{name} { uint8_t tag; #{ctype(pay, book)}val; };
    """
    |> String.trim()
  end

  defp opt_name(pay), do: g("opt_" <> lay_tag(pay))

  defp lay_tag(:u8), do: "u8"
  defp lay_tag(:u32), do: "u32"
  defp lay_tag(:u64), do: "u64"
  defp lay_tag(:i64), do: "i64"
  defp lay_tag(:nat), do: "nat"
  defp lay_tag(:wbool), do: "bool"
  defp lay_tag(:unit), do: "unit"
  defp lay_tag(:slice), do: "slice"
  defp lay_tag(:string), do: "str"
  defp lay_tag(:opaque), do: "opaque"
  defp lay_tag({:opt, p}), do: "opt_" <> lay_tag(p)
  defp lay_tag({:data, name}), do: "d_" <> to_string(name)
  defp lay_tag({:pair, a, b}), do: "pair_#{lay_tag(a)}_#{lay_tag(b)}"
  defp lay_tag({:stream, a}), do: "stream_#{lay_tag(a)}"
  defp lay_tag(other), do: to_string(other)

  defp ctype(:atom, _book), do: atom_ty()
  defp ctype(:nat, _book), do: nat_ptr()
  defp ctype(:unit, _book), do: unit_ptr()
  defp ctype({:stream, _}, _book), do: stream_ptr()

  defp ctype({:var, name}, book) when is_binary(name) do
    cond do
      unboxed_name?(book, name) -> struct_val(name)
      data?(book, name) -> struct_ptr(name)
      true -> "void *"
    end
  end

  defp ctype({:def, name}, book) do
    if unboxed_name?(book, name), do: struct_val(name), else: "void *"
  end

  defp ctype({:app, f, _a}, book), do: ctype(f, book)
  defp ctype({:data, "Atom"}, _book), do: atom_ty()

  defp ctype({:data, name}, book) do
    if unboxed_name?(book, name), do: struct_val(name), else: struct_ptr(name)
  end

  defp ctype(:u8, _book), do: "uint8_t "
  defp ctype(:u32, _book), do: "uint32_t "
  defp ctype(:u64, _book), do: "uint64_t "
  defp ctype(:i64, _book), do: "int64_t "
  defp ctype(:wbool, _book), do: "uint8_t "
  defp ctype(:slice, _book), do: g("slice") <> " "
  defp ctype(:bytes, _book), do: g("slice") <> " "
  defp ctype(:string, _book), do: str_ty()
  defp ctype({:opt, pay}, _book), do: opt_name(pay) <> " "
  defp ctype({:word, {:ty, :u8}, []}, book), do: ctype(:u8, book)
  defp ctype({:word, {:ty, :u32}, []}, book), do: ctype(:u32, book)
  defp ctype({:word, {:ty, :u64}, []}, book), do: ctype(:u64, book)
  defp ctype({:word, :bool, []}, book), do: ctype(:wbool, book)
  defp ctype({:word, {:optk, k}, []}, book), do: ctype({:opt, k}, book)
  defp ctype({:word, :opt, [a]}, book), do: ctype({:opt, type_layout(book, a)}, book)
  defp ctype(_, _book), do: "void *"

  defp data?(book, name) when is_list(book) do
    Enum.any?(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp data?(_book, _name), do: false

  defp struct_ptr(name), do: struct_name(name) <> " *"
  defp struct_val(name), do: struct_name(name) <> " "

  # Claimed first, against an empty set. `spell/1` is injective, so the
  # struct spelling is the source spelling.
  defp struct_name(name), do: spell(name)

  defp ename(st, name), do: Map.get(st.names, name, spell(name))

  defp squash(parts) do
    parts
    |> Enum.flat_map(fn
      nil -> []
      "" -> []
      s when is_binary(s) -> String.split(s, "\n")
    end)
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n")
  end

  defp indent(s, n) do
    pad = String.duplicate(" ", n)
    s |> String.split("\n") |> Enum.map_join("\n", &(pad <> &1))
  end

  defp header(book, sigs, stem, nm, opts, bytes?, strings?) do
    guard = guard(stem)

    parts = [
      "/* generated by muro — do not edit */",
      "#ifndef #{guard}",
      "#define #{guard}",
      "#include <stdint.h>",
      alloc_macro(),
      nat_struct(),
      unit_struct(),
      if(bytes?, do: bytes_header(), else: ""),
      if(strings?, do: string_header(), else: ""),
      data_typedefs(book),
      opts,
      atom_enum(book, nm),
      stream_typedef(sigs, book),
      data_bodies(book),
      prototypes(sigs),
      "#endif"
    ]

    join_parts(parts)
  end

  defp source(book, runs, sigs, funs, extras, stem, nm, _opts, bytes?, strings?) do
    internals =
      sigs
      |> Enum.reject(& &1.export)
      |> Enum.map_join("\n", &"#{decl(&1)};")

    parts = [
      "/* generated by muro — do not edit */",
      "#include \"#{stem}.h\"",
      "#include <stdlib.h>",
      if(bytes?, do: "#include <string.h>\n" <> bytes_helpers(), else: ""),
      nat_helpers(),
      unit_helpers(),
      if(strings?, do: "#include <string.h>\n" <> string_helpers(bytes?), else: ""),
      pair_helpers(runs),
      stream_helpers(runs, stream_declared?(sigs, book)),
      data_ctors(book, nm, sigs),
      internals,
      Enum.join(extras, "\n\n"),
      Enum.join(funs, "\n\n")
    ]

    join_parts(parts)
  end

  defp join_parts(parts) do
    parts
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n")
    |> Kernel.<>("\n")
  end

  defp prototypes(sigs) do
    sigs
    |> Enum.filter(& &1.export)
    |> Enum.map_join("\n", &"#{decl(&1)};")
  end

  # `encode/1` has no underscore, so the tag cannot contain `__`.
  defp guard(stem), do: g("H_" <> Name.encode(stem))

  defp atom_enum(book, nm) do
    case Ast.atoms(book) do
      [] ->
        ""

      names ->
        consts = Enum.map_join(names, ",\n  ", &atom_c(&1, nm))

        """
        typedef enum {
          #{consts}
        } #{g("atom")};
        """
        |> String.trim()
    end
  end

  defp atom_c(name, nm), do: Map.fetch!(nm.atoms, name)

  defp alloc_macro do
    alloc = g("ALLOC")

    """
    #ifndef #{alloc}
    #define #{alloc}(n) malloc(n)
    #endif
    """
    |> String.trim()
  end

  defp nat_struct do
    nat = g("nat")
    tag = g("field_tag")
    suc = g("field_suc")

    """
    typedef struct #{nat} #{nat};
    struct #{nat} { uint8_t #{tag}; #{nat} *#{suc}; }; /* 0 = zero, 1 = suc */
    """
    |> String.trim()
  end

  defp unit_struct do
    unit = g("unit")
    tag = g("field_tag")

    """
    typedef struct #{unit} #{unit};
    struct #{unit} { uint8_t #{tag}; };
    """
    |> String.trim()
  end

  defp nat_helpers do
    nat = g("nat")
    new = g("nat_new")
    p = g("p")
    n = g("n")
    tag = g("field_tag")
    sucf = g("field_suc")
    alloc = g("ALLOC")
    zero = g("zero")
    suc = g("suc")

    """
    static #{nat} *#{new}(uint8_t #{tag}, #{nat} *#{n}) {
      #{nat} *#{p} = #{alloc}(sizeof *#{p});
      if (#{p} == 0) abort();
      #{p}->#{tag} = #{tag};
      #{p}->#{sucf} = #{n};
      return #{p};
    }

    __attribute__((unused)) static #{nat} *#{zero}(void) { return #{new}(0, 0); }

    __attribute__((unused)) static #{nat} *#{suc}(#{nat} *#{n}) { return #{new}(1, #{n}); }
    """
    |> String.trim()
  end

  defp unit_helpers do
    unit = g("unit")
    obj = g("tt_obj")
    tt = g("tt")

    """
    static #{unit} #{obj} = {0};

    __attribute__((unused)) static #{unit} *#{tt}(void) { return &#{obj}; }
    """
    |> String.trim()
  end

  defp slice_ty, do: g("slice") <> " "

  defp as_ret(expr, lay, :string) when lay != :string, do: as_str(expr, lay)
  defp as_ret(expr, _lay, _ret), do: expr

  defp strings_image?(funs) do
    Enum.any?(funs, fn fun ->
      string_lay?(fun.ret) or Enum.any?(fun.params, fn {_n, lay} -> string_lay?(lay) end) or
        ir_has_string?(fun.body)
    end)
  end

  defp string_lay?(:string), do: true
  defp string_lay?({:opt, a}), do: string_lay?(a)
  defp string_lay?({:pair, a, b}), do: string_lay?(a) or string_lay?(b)
  defp string_lay?({:stream, a}), do: string_lay?(a)
  defp string_lay?(_), do: false

  defp ir_has_string?({:str, _}), do: true
  defp ir_has_string?({:scat, _, _}), do: true
  defp ir_has_string?({:slen, _}), do: true
  defp ir_has_string?({:seq, _, _}), do: true
  defp ir_has_string?({:sbytes, _}), do: true
  defp ir_has_string?(tm) when is_tuple(tm), do: Enum.any?(Tuple.to_list(tm), &ir_has_string?/1)
  defp ir_has_string?(tm) when is_list(tm), do: Enum.any?(tm, &ir_has_string?/1)
  defp ir_has_string?(_), do: false

  defp data_field_string?(book) do
    Enum.any?(book, fn
      %{kind: :data, ctors: cs} -> Enum.any?(cs, &mentions_string_ty?(&1.type))
      _ -> false
    end)
  end

  defp mentions_string_ty?(:string), do: true

  defp mentions_string_ty?(t) when is_tuple(t),
    do: Enum.any?(Tuple.to_list(t), &mentions_string_ty?/1)

  defp mentions_string_ty?(t) when is_list(t), do: Enum.any?(t, &mentions_string_ty?/1)
  defp mentions_string_ty?(_), do: false

  defp string_header do
    ty = g("str")
    empty = g("empty_str")
    emp = g("str_empty")

    """
    #include <stddef.h>
    typedef struct { const uint8_t *p; size_t n; } #{ty};
    static const uint8_t #{empty}[1] = {0};
    __attribute__((unused)) static inline #{ty} #{emp}(void) {
      return (#{ty}){#{empty}, 0};
    }
    """
    |> String.trim()
  end

  defp string_helpers(bytes?) do
    ty = g("str")
    eq = g("str_eq")
    cat = g("str_cat")
    len = g("str_len")
    box = g("box_str")
    emp = g("str_empty")
    alloc = g("ALLOC")
    nat = g("nat")
    zero = g("zero")
    suc = g("suc")
    bytes = if bytes?, do: str_bytes_helper(), else: ""

    """
    __attribute__((unused)) static uint8_t #{eq}(#{ty} a, #{ty} b) {
      if (a.n != b.n) return 0;
      if (a.n == 0) return 1;
      return memcmp(a.p, b.p, a.n) == 0;
    }

    __attribute__((unused)) static #{ty} #{cat}(#{ty} a, #{ty} b) {
      size_t n;
      uint8_t *p;
      if (b.n > SIZE_MAX - a.n) abort();
      n = a.n + b.n;
      if (n == 0) return #{emp}();
      p = #{alloc}(n);
      if (p == 0) abort();
      if (a.n != 0) memcpy(p, a.p, a.n);
      if (b.n != 0) memcpy(p + a.n, b.p, b.n);
      return (#{ty}){p, n};
    }

    /* Counts Unicode scalars by walking lead bytes. The buffer must be well-formed
       UTF-8. A string muro emits always is. A malformed host string may be miscounted. */
    __attribute__((unused)) static #{nat} *#{len}(#{ty} s) {
      size_t i = 0;
      size_t k = 0;
      size_t w;
      uint8_t c;
      #{nat} *n;
      while (i < s.n) {
        c = s.p[i];
        w = 1;
        if ((c & 0xE0) == 0xC0) w = 2;
        else if ((c & 0xF0) == 0xE0) w = 3;
        else if ((c & 0xF8) == 0xF0) w = 4;
        if (w > s.n - i) w = s.n - i;
        i += w;
        k++;
      }
      n = #{zero}();
      while (k != 0) {
        n = #{suc}(n);
        k--;
      }
      return n;
    }

    __attribute__((unused)) static #{ty} *#{box}(#{ty} s) {
      #{ty} *p = #{alloc}(sizeof *p);
      if (p == 0) abort();
      *p = s;
      return p;
    }
    #{bytes}
    """
    |> String.trim()
  end

  defp str_bytes_helper do
    ty = g("str")
    sl = g("slice")
    conv = g("str_bytes")

    """
    __attribute__((unused)) static #{sl} #{conv}(#{ty} s) {
      return (#{sl}){s.p, s.n};
    }
    """
    |> String.trim()
  end

  defp bytes_image?(funs) do
    Enum.any?(funs, fn fun ->
      bytes_lay?(fun.ret) or Enum.any?(fun.params, fn {_n, lay} -> bytes_lay?(lay) end) or
        ir_has_bytes?(fun.body)
    end)
  end

  defp bytes_lay?(:slice), do: true
  defp bytes_lay?({:opt, a}), do: bytes_lay?(a)
  defp bytes_lay?({:pair, a, b}), do: bytes_lay?(a) or bytes_lay?(b)
  defp bytes_lay?(_), do: false

  defp ir_has_bytes?({:byt, _}), do: true
  defp ir_has_bytes?({:bcat, _, _}), do: true
  defp ir_has_bytes?({:blen, _}), do: true
  defp ir_has_bytes?({:beq, _, _}), do: true
  defp ir_has_bytes?({:bsub, _, _, _}), do: true
  defp ir_has_bytes?({:bget, _, _}), do: true
  defp ir_has_bytes?({:bunc, _}), do: true
  defp ir_has_bytes?({:btil, _, _}), do: true
  defp ir_has_bytes?({:baft, _, _}), do: true
  defp ir_has_bytes?({:bfold, _, _, _, _}), do: true
  defp ir_has_bytes?({:sbytes, _}), do: true
  defp ir_has_bytes?(tm) when is_tuple(tm), do: Enum.any?(Tuple.to_list(tm), &ir_has_bytes?/1)
  defp ir_has_bytes?(tm) when is_list(tm), do: Enum.any?(tm, &ir_has_bytes?/1)
  defp ir_has_bytes?(_), do: false

  defp data_field_bytes?(book) do
    Enum.any?(book, fn
      %{kind: :data, ctors: cs} -> Enum.any?(cs, &mentions_bytes_ty?(&1.type))
      _ -> false
    end)
  end

  defp mentions_bytes_ty?(t) when t in [:bytes, :slice], do: true

  defp mentions_bytes_ty?(t) when is_tuple(t),
    do: Enum.any?(Tuple.to_list(t), &mentions_bytes_ty?/1)

  defp mentions_bytes_ty?(t) when is_list(t), do: Enum.any?(t, &mentions_bytes_ty?/1)
  defp mentions_bytes_ty?(_), do: false

  defp bytes_header do
    sl = g("slice")
    empty = g("empty_bytes")
    emp = g("slice_empty")
    wrap = g("slice_of")

    """
    #include <stddef.h>
    typedef struct { const uint8_t *p; size_t n; } #{sl};
    static const uint8_t #{empty}[1] = {0};
    __attribute__((unused)) static inline #{sl} #{emp}(void) {
      return (#{sl}){#{empty}, 0};
    }
    __attribute__((unused)) static inline #{sl} #{wrap}(const uint8_t *p, size_t n) {
      if (n == 0 || p == 0) return #{emp}();
      return (#{sl}){p, n};
    }
    """
    |> String.trim()
  end

  defp bytes_helpers do
    sl = g("slice")
    sub = g("slice_sub")
    eq = g("slice_eq")
    cat = g("bytes_cat")
    get = g("slice_get")
    til = g("slice_until")
    aft = g("slice_after")
    emp = g("slice_empty")
    alloc = g("ALLOC")
    opt = g("opt_u8")

    """
    __attribute__((unused)) static #{sl} #{sub}(#{sl} s, uint64_t off, uint64_t len) {
      if (off > s.n || len > s.n - off) return #{emp}();
      return (#{sl}){s.p + (size_t)off, (size_t)len};
    }

    __attribute__((unused)) static uint8_t #{eq}(#{sl} a, #{sl} b) {
      if (a.n != b.n) return 0;
      if (a.n == 0) return 1;
      return memcmp(a.p, b.p, a.n) == 0;
    }

    __attribute__((unused)) static #{sl} #{cat}(#{sl} a, #{sl} b) {
      size_t n;
      uint8_t *p;
      if (b.n > SIZE_MAX - a.n) abort();
      n = a.n + b.n;
      if (n == 0) return #{emp}();
      p = #{alloc}(n);
      if (p == 0) abort();
      if (a.n != 0) memcpy(p, a.p, a.n);
      if (b.n != 0) memcpy(p + a.n, b.p, b.n);
      return (#{sl}){p, n};
    }

    __attribute__((unused)) static #{opt} #{get}(#{sl} s, uint64_t i) {
      #{opt} o;
      if (i >= s.n) { o.tag = 0; o.val = 0; return o; }
      o.tag = 1;
      o.val = s.p[i];
      return o;
    }

    __attribute__((unused)) static #{sl} #{til}(#{sl} s, uint8_t b) {
      size_t i;
      for (i = 0; i < s.n; i++) if (s.p[i] == b) return (#{sl}){s.p, i};
      return s;
    }

    __attribute__((unused)) static #{sl} #{aft}(#{sl} s, uint8_t b) {
      size_t i;
      for (i = 0; i < s.n; i++) if (s.p[i] == b) return (#{sl}){s.p + i + 1, s.n - i - 1};
      return #{emp}();
    }
    """
    |> String.trim()
  end

  defp emit_cap_list(caps, env, st) do
    Enum.reduce_while(caps, {:ok, [], [], st}, fn {_name, tm}, {:ok, pres, exprs, st} ->
      case emit_ir(tm, env, st, "void *") do
        {:ok, {pre, ex, _lay, st}} -> {:cont, {:ok, pres ++ [pre], exprs ++ [ex], st}}
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, pres, exprs, st} -> {:ok, {squash(pres), exprs, st}}
      err -> err
    end
  end

  defp ensure_fold_step(name, st) do
    done = Map.get(st, :fold_done, MapSet.new())

    if MapSet.member?(done, name) do
      {:ok, st}
    else
      case Map.get(st.steps_by_name, name) do
        nil ->
          {:error, "c:unsupported"}

        fun ->
          case emit_fold_fun(fun, st) do
            {:ok, text, st} ->
              {:ok, %{st | steps: st.steps ++ [text], fold_done: MapSet.put(done, name)}}

            {:error, _} = err ->
              err
          end
      end
    end
  end

  defp emit_fold_fun(fun, st) do
    cname = fold_cname(fun.name)
    saved_base = st.base_scope
    saved_scope = st.scope
    visible = Name.see(st.file_scope, cname)

    {bound, scope} =
      Enum.map_reduce(fun.params, visible, fn {pname, lay}, scope ->
        {c, scope} = Name.bind(spell(pname), scope)
        {{pname, c, lay}, scope}
      end)

    params = for {_n, c, lay} <- bound, do: {ctype(lay, st.book), c}
    ret = ctype(fun.ret, st.book)
    env = Enum.reduce(bound, [], fn {n, c, lay}, env -> [{n, c, lay} | env] end)
    st = %{st | scope: scope, base_scope: scope}

    with {:ok, {pre, expr, _lay, st}} <- emit_ir(fun.body, env, st, ret) do
      discards =
        bound
        |> Enum.reject(fn {n, _c, _lay} -> uses?(fun.body, n) end)
        |> Enum.map_join("\n", fn {_n, c, _lay} -> "  (void)#{c};" end)

      body =
        cond do
          discards != "" and pre != "" ->
            discards <> "\n" <> indent(pre, 2) <> "\n  return #{expr};"

          discards != "" ->
            discards <> "\n  return #{expr};"

          pre != "" ->
            indent(pre, 2) <> "\n  return #{expr};"

          true ->
            "  return #{expr};"
        end

      args =
        case params do
          [] -> "void"
          ps -> Enum.map_join(ps, ", ", fn {ty, name} -> "#{ty}#{name}" end)
        end

      text = "static #{ret}#{cname}(#{args}) {\n#{body}\n}"
      {:ok, text, %{st | base_scope: saved_base, scope: saved_scope}}
    end
  end

  defp fold_cname(name), do: g("step", step_id(name))

  defp fold_ret(st, name) do
    case Map.get(st.steps_by_name, name) do
      %{ret: lay} -> lay
      _ -> :opaque
    end
  end

  defp pair_helpers(runs) do
    if mentions?(runs, &pair_form?/1) or mentions?(runs, &stream_form?/1) do
      pair = g("pair")
      fst = g("field_fst")
      snd = g("field_snd")
      p = g("p")
      alloc = g("ALLOC")
      mk = g("mk_pair")

      """
      typedef struct #{pair} #{pair};
      struct #{pair} { void *#{fst}; void *#{snd}; };

      static #{pair} *#{mk}(void *#{fst}, void *#{snd}) {
        #{pair} *#{p} = #{alloc}(sizeof *#{p});
        if (#{p} == 0) abort();
        #{p}->#{fst} = #{fst};
        #{p}->#{snd} = #{snd};
        return #{p};
      }
      """
      |> String.trim()
    else
      ""
    end
  end

  defp pair_form?({:pair, _, _}), do: true
  defp pair_form?({:letp, _, _, _, _}), do: true
  defp pair_form?({:bunc, _}), do: true
  defp pair_form?(_), do: false

  defp stream_form?({:stream, _}), do: true
  defp stream_form?({:unf, _, _}), do: true
  defp stream_form?({:ucons, _}), do: true
  defp stream_form?(_), do: false

  defp exports_stream?(sigs) do
    Enum.any?(sigs, fn sig ->
      sig.export and
        (stream_ty?(sig.ret) or Enum.any?(sig.params, fn {ty, _} -> stream_ty?(ty) end))
    end)
  end

  defp stream_ty?(ty), do: String.starts_with?(ty, g("stream") <> " ")

  # A data field typed as a stream needs the typedef even when no
  # signature exports a stream. The .c completes the struct only when a
  # run uses one, and must not repeat the typedef.
  defp stream_declared?(sigs, book) do
    exports_stream?(sigs) or data_field_stream?(book)
  end

  defp data_field_stream?(book) do
    Enum.any?(data_defs(book), fn d ->
      Enum.any?(d.ctors, fn ctor ->
        {pis, _} = telescope(ctor.type)

        Enum.any?(pis, fn
          {:erased, _, _} -> false
          {_, a, _} -> stream_ty?(ctype(a, book))
        end)
      end)
    end)
  end

  defp stream_typedef(sigs, book) do
    stream = g("stream")
    if stream_declared?(sigs, book), do: "typedef struct #{stream} #{stream};", else: ""
  end

  defp stream_helpers(runs, declared?) do
    if mentions?(runs, &stream_form?/1) do
      stream = g("stream")
      seed = g("field_seed")
      env = g("field_env")
      step = g("field_step")
      pair = g("pair")
      new = g("stream_new")
      p = g("p")
      alloc = g("ALLOC")
      decl = if declared?, do: "", else: "typedef struct #{stream} #{stream};"

      """
      #{decl}
      struct #{stream} {
        void *#{seed};
        void *#{env};
        #{pair} *(*#{step})(void *, void *);
      };

      static #{stream} *#{new}(void *#{seed}, void *#{env}, #{pair} *(*#{step})(void *, void *)) {
        #{stream} *#{p} = #{alloc}(sizeof *#{p});
        if (#{p} == 0) abort();
        #{p}->#{seed} = #{seed};
        #{p}->#{env} = #{env};
        #{p}->#{step} = #{step};
        return #{p};
      }
      """
      |> String.trim()
    else
      ""
    end
  end

  defp mentions?(runs, pred) do
    Enum.any?(runs, fn d -> walk?(d.type, pred) or walk?(d.body, pred) end)
  end

  defp walk?(t, pred) do
    pred.(t) or walk_children?(t, pred)
  end

  defp walk_children?(t, pred) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.any?(&walk?(&1, pred))
  end

  defp walk_children?(t, pred) when is_list(t), do: Enum.any?(t, &walk?(&1, pred))
  defp walk_children?(_, _), do: false

  # Forward declarations come before option typedefs. `Opt` of boxed
  # data holds a pointer, and the pointer needs the typedef. The struct
  # body stays after the options, in dependency order.
  defp data_typedefs(book) do
    datas = data_defs(book)
    if datas == [], do: "", else: typedefs(datas)
  end

  defp data_bodies(book) do
    datas = data_defs(book)

    if datas == [],
      do: "",
      else: Enum.map_join(order_value_deps(datas, book), "\n", &struct_src(&1, book))
  end

  defp typedefs(datas) do
    Enum.map_join(datas, "\n", fn d ->
      n = struct_name(d.name)
      "typedef struct #{n} #{n};"
    end)
  end

  defp struct_src(d, book) do
    name = struct_name(d.name)
    tagf = g("field_tag")
    asf = g("as")
    unused = g("unused")

    members =
      d.ctors
      |> Enum.with_index()
      |> Enum.map(fn {ctor, tag} ->
        {pis, _} = telescope(ctor.type)

        fs =
          pis
          |> Enum.reject(fn {q, _, _} -> q == :erased end)
          |> Enum.with_index()
          |> Enum.map(fn {{_, a, _}, k} -> "    #{ctype(a, book)}#{g("f", k)};" end)

        {tag, ctor.name, fs}
      end)

    comment = Enum.map_join(members, ", ", fn {tag, cname, _} -> "#{cname} = #{tag}" end)

    union_members =
      Enum.flat_map(members, fn {_tag, cname, fs} ->
        if fs == [] do
          []
        else
          ["    struct {\n#{Enum.join(fs, "\n")}\n    } #{spell(cname)};"]
        end
      end)

    union_body = Enum.join(["    char #{unused};" | union_members], "\n")

    """
    struct #{name} {
      uint8_t #{tagf}; /* #{comment} */
      union {
    #{union_body}
      } #{asf};
    };
    """
    |> String.trim()
  end

  defp data_ctors(book, nm, sigs) do
    visible = file_scope(nm, MapSet.new(Enum.map(sigs, & &1.name)))

    book
    |> data_defs()
    |> Enum.flat_map(fn d ->
      d.ctors
      |> Enum.with_index()
      |> Enum.map(fn {ctor, tag} -> ctor_fun(d, ctor, tag, book, nm, visible) end)
    end)
    |> Enum.join("\n\n")
  end

  defp file_scope(nm, extra) do
    Name.open(MapSet.union(nm.taken, extra))
  end

  # A constructor with no runtime fields has one value. Share it, as `tt` does.
  # The object name is generated, so a source spelling cannot be it.
  defp ctor_fun(d, ctor, tag, book, nm, file_scope) do
    if unboxed?(d) do
      unboxed_ctor(d, ctor, tag, book, nm, file_scope)
    else
      boxed_ctor(d, ctor, tag, book, nm, file_scope)
    end
  end

  # By value. A compound literal names every field of the active arm, so
  # the return is initialized under -Wall -Wextra.
  defp unboxed_ctor(d, ctor, tag, book, nm, file_scope) do
    {params, member, fun} = ctor_params(d, ctor, book, nm, file_scope)
    ty = struct_name(d.name)
    tagf = g("field_tag")
    asf = g("as")

    body =
      if params == [] do
        "return (#{ty}){ .#{tagf} = #{tag}, .#{asf} = { .#{g("unused")} = 0 } };"
      else
        inner = Enum.map_join(params, ", ", fn {_ty, cname, k} -> ".#{g("f", k)} = #{cname}" end)
        "return (#{ty}){ .#{tagf} = #{tag}, .#{asf} = { .#{member} = { #{inner} } } };"
      end

    args =
      case params do
        [] -> "void"
        ps -> Enum.map_join(ps, ", ", fn {pty, n, _} -> "#{pty}#{n}" end)
      end

    """
    __attribute__((unused)) static #{ty} #{fun}(#{args}) {
      #{body}
    }
    """
    |> String.trim()
  end

  defp boxed_ctor(d, ctor, tag, book, nm, file_scope) do
    {params, member, fun} = ctor_params(d, ctor, book, nm, file_scope)
    ptr = struct_ptr(d.name)
    p = g("p")
    alloc = g("ALLOC")
    tagf = g("field_tag")
    asf = g("as")

    if params == [] do
      obj = g("obj_" <> spell(d.name) <> "_" <> spell(ctor.name))
      unused = g("unused")

      """
      __attribute__((unused)) static #{struct_name(d.name)} #{obj} = { .#{tagf} = #{tag}, .#{asf} = { .#{unused} = 0 } };

      __attribute__((unused)) static #{ptr}#{fun}(void) { return &#{obj}; }
      """
      |> String.trim()
    else
      assigns =
        Enum.map_join(params, "\n", fn {_ty, cname, k} ->
          "  #{p}->#{asf}.#{member}.#{g("f", k)} = #{cname};"
        end)

      args = Enum.map_join(params, ", ", fn {ty, n, _} -> "#{ty}#{n}" end)

      """
      __attribute__((unused)) static #{ptr}#{fun}(#{args}) {
        #{ptr}#{p} = #{alloc}(sizeof *#{p});
        if (#{p} == 0) abort();
        #{p}->#{tagf} = #{tag};
      #{assigns}
        return #{p};
      }
      """
      |> String.trim()
    end
  end

  defp ctor_params(d, ctor, book, nm, file_scope) do
    {pis, _} = telescope(ctor.type)

    fields =
      pis
      |> Enum.reject(fn {q, _, _} -> q == :erased end)
      |> Enum.with_index()
      |> Enum.map(fn {{_, a, x}, k} -> {ctype(a, book), x, k} end)

    {params, _} =
      Enum.map_reduce(fields, file_scope, fn {ty, x, k}, scope ->
        base = if x == "_", do: g("f", k), else: spell(x)
        {cname, scope} = Name.bind(base, scope)
        {{ty, cname, k}, scope}
      end)

    {params, spell(ctor.name), Map.fetch!(nm.ctors, {d.name, ctor.name})}
  end

  defp unboxed?(%{unboxed: true}), do: true
  defp unboxed?(_), do: false

  defp unboxed_name?(book, name) when is_binary(name) do
    case find_data(book, name) do
      %{unboxed: true} -> true
      _ -> false
    end
  end

  defp unboxed_name?(_book, _name), do: false

  defp unboxed_lay?(book, {:data, name}), do: unboxed_name?(book, name)
  defp unboxed_lay?(_book, _lay), do: false

  # An unboxed struct embedded by value needs a complete type. Bodies
  # of those structs come first. A cycle is left in source order; the
  # checker already refuses a recursive unboxed declaration.
  defp order_value_deps(datas, book), do: order_value_deps(datas, book, [])

  defp order_value_deps([], _book, acc), do: acc

  defp order_value_deps(pending, book, acc) do
    done = MapSet.new(Enum.map(acc, & &1.name))

    {ready, rest} =
      Enum.split_with(pending, fn d ->
        d |> value_deps(book) |> Enum.all?(&MapSet.member?(done, &1))
      end)

    if ready == [] do
      acc ++ pending
    else
      order_value_deps(rest, book, acc ++ ready)
    end
  end

  defp value_deps(d, book) do
    d.ctors
    |> Enum.flat_map(fn ctor ->
      {pis, _} = telescope(ctor.type)

      Enum.flat_map(pis, fn
        {q, _, _} when q == :erased ->
          []

        {_, a, _} ->
          case type_layout(book, a) do
            {:data, name} ->
              if name != d.name and unboxed_name?(book, name), do: [name], else: []

            _ ->
              []
          end
      end)
    end)
    |> Enum.uniq()
  end

  defp data_defs(book) do
    Enum.filter(book, &(Map.get(&1, :kind) == :data))
  end

  defp data_layouts(book) do
    Enum.map(data_defs(book), fn d ->
      ctors =
        d.ctors
        |> Enum.with_index()
        |> Enum.map(fn {ctor, tag} ->
          fields = Enum.map(live_fields(ctor, book), fn {_ctype, lay, _k} -> lay end)
          %{name: ctor.name, tag: tag, fields: fields}
        end)

      %{name: d.name, layout: {:data, d.name}, constructors: ctors}
    end)
  end
end
