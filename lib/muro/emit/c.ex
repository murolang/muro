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
  and a raw `ν` in a run are refused (`c:stream`). `I64`, `F32`, and
  `Tensor` are refused (`c:machine`). A lambda applied on the spot is a
  local. An unapplied lambda, and a call of a local function, are
  `c:lambda`.

  Allocations call `muro__ALLOC`, which is `malloc` unless the caller
  defines it. A constructor with no fields is a static object and does not.

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

            {:ok, header(book, sigs, stem, nm), source(book, runs, sigs, texts, extras, stem, nm),
             sigs}

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
      nm: nm,
      file_scope: file_scope,
      base_scope: scope,
      scope: scope
    }

    with {:ok, {pre, expr, _lay, st}} <- emit_ir(fun.body, env, st, sig.ret) do
      body =
        if pre == "" do
          "  return #{expr};"
        else
          indent(pre, 2) <> "\n  return #{expr};"
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

    kw = if sig.export, do: "", else: "static "
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

  # An erased constructor field. `0`, not a Nat zero. A zero passed
  # under a spec alias is bound at the argument's layout, so this clause
  # does not see it.
  defp emit_ir({:let, name, :opaque, :ze, body}, env, st, expect) do
    {c, scope} = Name.bind(spell(name), st.scope)
    st = %{st | scope: scope}

    with {:ok, {pre, ex, lay, st}} <- emit_ir(body, [{name, c, :opaque} | env], st, expect) do
      {:ok, {squash(["void *#{c} = 0;", pre]), ex, lay, st}}
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
        void = if lay == :unit and not uses?(body, name), do: "(void)#{local};", else: ""
        stmt = squash([pre, "#{ty}#{local} = #{ex};", void, pre2])
        {:ok, {stmt, ex2, blay, st}}
      end
    end
  end

  defp emit_ir({:pair, a, b}, env, st, _expect) do
    with {:ok, {pre, ea, la, st}} <- emit_ir(a, env, st, "void *"),
         {:ok, {pre2, eb, lb, st}} <- emit_ir(b, env, st, "void *") do
      {:ok, {squash([pre, pre2]), "#{g("mk_pair")}(#{ea}, #{eb})", {:pair, la, lb}, st}}
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
        stmt =
          squash([
            pre,
            "#{pair_ptr()}#{sname} = #{ex};",
            "void *#{ca} = #{sname}->#{g("field_fst")};",
            "void *#{cb} = #{sname}->#{g("field_snd")};",
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

      with {:ok, {cpre, outers, st}} <- emit_outers(slots, env, st) do
        {env_ty, env_src, env_ex, st} = alloc_env(slots, outers, id, st)
        saved = st.scope

        with {:ok, {src, st}} <- emit_step_fun(step, slots, seed_p, id, env_ty, st) do
          expr = "#{g("stream_new")}(#{seed_ex}, #{env_ex}, #{g("step", id)})"
          st = %{st | steps: st.steps ++ [src], scope: saved}

          {:ok,
           {squash([pre, cpre, env_src]), expr, {:stream, seed_domain(seed_p, seed_lay)}, st}}
        end
      end
    end
  end

  defp emit_ir({:match, scrut, arms} = tm, env, st, expect) do
    kind = match_kind(lay_of(scrut, env, st), arms, st.book)
    rlay = lay_of(tm, env, st)

    with {:ok, {pre, ex, _lay, st}} <- emit_ir(scrut, env, st, scrut_ty(kind, st.book)),
         {:ok, {stmt, name, st}} <- emit_switch(kind, pre, ex, arms, env, st, expect) do
      {:ok, {stmt, name, rlay, st}}
    end
  end

  defp emit_ir(:abort, _env, st, _expect) do
    {:ok, {squash(["/* unreachable */", "abort();"]), "0", :opaque, st}}
  end

  defp emit_ir(_other, _env, _st, _expect), do: {:error, "c:unsupported"}

  defp emit_args(args, types, env, st) do
    paired = Enum.zip(args, pad_types(types, length(args)))

    Enum.reduce_while(paired, {:ok, [], [], st}, fn {arg, ty}, {:ok, pres, exprs, st} ->
      case emit_ir(arg, env, st, ty) do
        {:ok, {pre, ex, _lay, st}} -> {:cont, {:ok, pres ++ [pre], exprs ++ [ex], st}}
        {:error, _} = err -> {:halt, err}
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
  defp scrut_ty({:data, name}, _book), do: struct_ptr(name)
  defp scrut_ty(_, _book), do: "void *"

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
            "#{expect}#{tname} = 0;",
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
          "#{expect}#{tname} = 0;",
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
        ptr = struct_ptr(dname)
        {sname, st} = news(st)
        {tname, st} = newt(st)

        with {:ok, {cases, st}} <- emit_data_arms(arms, data, sname, tname, env, st, expect) do
          stmt =
            squash([
              pre,
              "#{expect}#{tname} = 0;",
              "{",
              "#{ptr}#{sname} = #{ex};",
              "switch (#{sname}->#{g("field_tag")}) {",
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

  defp emit_data_arms(arms, data, sname, tname, env, st, expect) do
    emit_arm_list(arms, st, fn arm, st ->
      data_arm(arm, data, sname, tname, env, st, expect)
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

  defp data_arm({:arm, cname, binders, body}, data, sname, tname, env, st, expect) do
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
          {c, scope} = Name.bind(spell(bname), scope)
          decl = "#{ty}#{c} = #{sname}->#{g("as")}.#{member}.#{g("f", k)};"
          {decls ++ [decl], [{bname, c, lay} | env], scope}
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
        {:ok, {pre, ex, _lay, st}} -> {:cont, {:ok, pres ++ [pre], exprs ++ [ex], st}}
        {:error, _} = err -> {:halt, err}
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
        [{name, "#{ep}->#{field}", lay} | env]
      end)

    visible =
      [ep, envp, seedp | Enum.map(slots, &elem(&1, 1))]
      |> Enum.reduce(st.file_scope, &Name.see(&2, &1))

    {seed_line, env, step_base} =
      case seed_p do
        nil ->
          {"  (void)#{seedp};", cap_env, visible}

        {sname, slay} ->
          {local, visible} = Name.bind(spell(sname), visible)
          line = "  #{ctype(slay, st.book)}#{local} = #{seedp};"
          {line, [{sname, local, slay} | cap_env], visible}
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

  defp lay_of({:match, scrut, arms}, env, st) do
    case match_kind(lay_of(scrut, env, st), arms, st.book) do
      :nat -> arm_result(arms, env, st)
      :atom -> arm_result(arms, env, st)
      {:data, dname} -> data_result(dname, arms, env, st)
      :unknown -> :opaque
    end
  end

  defp lay_of(_, _env, _st), do: :opaque

  defp arm_result([{:arm, _, _, body} | _], env, st), do: lay_of(body, env, st)
  defp arm_result(_, _env, _st), do: :opaque

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
  defp match_kind({:data, "Atom"}, _arms, _book), do: :atom
  defp match_kind({:data, name}, _arms, _book), do: {:data, name}
  defp match_kind(_lay, [{:arm, "zero", [], _}, {:arm, "suc", [_], _}], _book), do: :nat

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

  defp find_data(book, name) do
    Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

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

  defp ctype(:atom, _book), do: atom_ty()
  defp ctype(:nat, _book), do: nat_ptr()
  defp ctype(:unit, _book), do: unit_ptr()
  defp ctype({:stream, _}, _book), do: stream_ptr()

  defp ctype({:var, name}, book) do
    if data?(book, name), do: struct_ptr(name), else: "void *"
  end

  defp ctype({:app, f, _a}, book), do: ctype(f, book)
  defp ctype({:data, "Atom"}, _book), do: atom_ty()
  defp ctype({:data, name}, _book), do: struct_ptr(name)
  defp ctype(_, _book), do: "void *"

  defp data?(book, name) do
    Enum.any?(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp struct_ptr(name), do: struct_name(name) <> " *"

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

  defp header(book, sigs, stem, nm) do
    guard = guard(stem)

    parts = [
      "/* generated by muro — do not edit */",
      "#ifndef #{guard}",
      "#define #{guard}",
      "#include <stdint.h>",
      alloc_macro(),
      nat_struct(),
      unit_struct(),
      atom_enum(book, nm),
      stream_typedef(sigs, book),
      data_structs(book),
      prototypes(sigs),
      "#endif"
    ]

    join_parts(parts)
  end

  defp source(book, runs, sigs, funs, extras, stem, nm) do
    internals =
      sigs
      |> Enum.reject(& &1.export)
      |> Enum.map_join("\n", &"#{decl(&1)};")

    parts = [
      "/* generated by muro — do not edit */",
      "#include \"#{stem}.h\"",
      "#include <stdlib.h>",
      nat_helpers(),
      unit_helpers(),
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

    static #{nat} *#{zero}(void) { return #{new}(0, 0); }

    static #{nat} *#{suc}(#{nat} *#{n}) { return #{new}(1, #{n}); }
    """
    |> String.trim()
  end

  defp unit_helpers do
    unit = g("unit")
    obj = g("tt_obj")
    tt = g("tt")

    """
    static #{unit} #{obj} = {0};

    static #{unit} *#{tt}(void) { return &#{obj}; }
    """
    |> String.trim()
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

  defp data_structs(book) do
    datas = data_defs(book)

    if datas == [],
      do: "",
      else: typedefs(datas) <> "\n" <> Enum.map_join(datas, "\n", &struct_src(&1, book))
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

    ptr = struct_ptr(d.name)
    fun = Map.fetch!(nm.ctors, {d.name, ctor.name})
    member = spell(ctor.name)
    p = g("p")
    alloc = g("ALLOC")
    tagf = g("field_tag")
    asf = g("as")

    if params == [] do
      obj = g("obj_" <> spell(d.name) <> "_" <> spell(ctor.name))

      """
      static #{struct_name(d.name)} #{obj} = {#{tag}};

      static #{ptr}#{fun}(void) { return &#{obj}; }
      """
      |> String.trim()
    else
      assigns =
        Enum.map_join(params, "\n", fn {_ty, cname, k} ->
          "  #{p}->#{asf}.#{member}.#{g("f", k)} = #{cname};"
        end)

      args = Enum.map_join(params, ", ", fn {ty, n, _} -> "#{ty}#{n}" end)

      """
      static #{ptr}#{fun}(#{args}) {
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

  defp data_defs(book) do
    Enum.filter(book, &(Map.get(&1, :kind) == :data))
  end
end
