defmodule Muro.Emit.C do
  @moduledoc """
  Emit a closed run book to C. Specs and evidence are omitted.
  Run bodies are the image from `Muro.IR`.

  `Nat` is a tagged struct. A data type whose constructors all have no
  live fields is an enum of those tags, passed by value, and `match` is
  a `switch` on the tag. User data with a fieldful constructor is a tag
  plus fields, and `match` is a `switch` on the tag. Erased arguments
  are dropped. `run internal` is `static`. Which of the three a data
  type is, enum, by-value struct, or boxed, is `Muro.IR.Rep`, and so
  are the `c:unboxed` rules.

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
  `Opt` is `c:unboxed`. An all-nullary data value in a pair, a stream
  seed, or an environment is packed in a pointer word. An `Opt` of
  all-nullary data stores the tag in `val` by value. An `Opt` of
  ordinary boxed data stores a pointer in `val`.

  A byte fold is a `while` over the slice (`Muro.IR.Loop`): the fold
  step's body is inline, its captures are locals bound once, and the
  accumulator is a local. When the step returns the accumulator
  unchanged for the rest of the input (`Muro.IR.Share.stop/2`) the loop
  breaks. When the step's value is a run that updates a by-value
  struct accumulator, the loop calls that run's in-place twin
  `muro__io_N` on the accumulator's address instead of copying the
  struct into the call and back. When every octet outside a set of one,
  two, or three constant bytes returns that accumulator unchanged, the
  loop advances to the next such byte with `muro__find2` or
  `muro__find3` and runs the body only there. A fold of `U64` whose
  step is the border automaton of a fixed octet string, state in the
  low three bits and the index above them, scans for that string
  instead. A scalar run with no loop that such a byte loop reaches,
  and whose body is no wider than that name step, is `always_inline`.
  A step the emitter cannot read that way keeps the byte-by-byte loop.
  A match on an enum of two constructors is an `if` on the first tag.

  Allocations call `muro__ALLOC`, which is `malloc` unless the caller
  defines it. A constructor of an all-nullary data type is the
  enumerator and does not. A fieldless constructor of a type that also
  has fields is a static object and does not. An `unboxed data`
  constructor with fields returns the struct by value and does not. An
  all-nullary `unboxed data` type is the same enum as ordinary
  all-nullary data.

  A session in the book is a stepper beside the runs. The host passes
  the state and an event. The function returns the next state and the
  action, or refuses an event the protocol does not allow. The host
  keeps the transport. A protocol the machine cannot represent, a repr
  payload, and an unboxed session payload are refused (`c:session`).

  Identifiers come from `Muro.Emit.Name`. A source name is spelled there.
  A helper, a step, a constructor argument, and a temporary are generated
  there. The two spellings share no identifier. A binder is claimed there
  against every name visible in its scope, including type names.
  """

  alias Muro.{Ast, Emit, IR}
  alias Muro.IR.Rep
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

  # Named constants a host can `_Static_assert`. The struct field stays
  # `uint8_t`. The enumerator is the tag the struct already stores.
  # `prefix` is prepended when the host asked for one, and it already
  # includes the separator. Empty is the unprefixed name.
  @doc false
  def ctor_tag_type(type_name, prefix \\ "") when is_binary(type_name) and is_binary(prefix) do
    prefix <> "muro__tag_#{source_id(type_name)}"
  end

  @doc false
  def ctor_tag(type_name, ctor_name, prefix \\ "")
      when is_binary(type_name) and is_binary(ctor_name) and is_binary(prefix) do
    "#{ctor_tag_type(type_name, prefix)}_#{source_id(ctor_name)}"
  end

  # The data struct spelling. Empty `prefix` is the source spelling, which
  # is the ABI an unprefixed book already emits.
  @doc false
  def data_struct(name, prefix \\ "") when is_binary(name) and is_binary(prefix) do
    prefix <> source_id(name)
  end

  # True when every live constructor of `name` is fieldless, so the C
  # type is the tag enum passed by value.
  @doc false
  def enum_type?(book, name) when is_list(book) and is_binary(name) do
    Rep.enum?(book, name)
  end

  # One number space for every data declaration in the book, in book
  # order, constructors in declaration order. The stem keeps two books
  # from defining the same enum. `prefix` is prepended when the host
  # asked for one, and it already includes the separator.
  @doc false
  def ctor_word_type(stem, prefix \\ "") when is_binary(stem) and is_binary(prefix) do
    prefix <> "muro__word_" <> Name.encode(stem)
  end

  @doc false
  def ctor_word(stem, type_name, ctor_name, prefix \\ "")
      when is_binary(stem) and is_binary(type_name) and is_binary(ctor_name) and
             is_binary(prefix) do
    ctor_word_type(stem, prefix) <> "_#{source_id(type_name)}_#{source_id(ctor_name)}"
  end

  @doc false
  def ctor_words(book, stem, prefix \\ "") when is_list(book) and is_binary(stem) do
    book
    |> data_defs()
    |> Enum.flat_map(fn d ->
      Enum.map(d.ctors, fn c ->
        %{type: d.name, ctor: c.name, word: ctor_word(stem, d.name, c.name, prefix)}
      end)
    end)
  end

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
  defp name_map(book, prefix \\ "") do
    {structs, taken} =
      Enum.reduce(data_defs(book), {%{}, MapSet.new()}, fn d, {map, used} ->
        {rn, used} = claim(prefix <> spell(d.name), used)
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
  `opts` are the ones `prepare/3` takes. `path:` is the file a session
  error names. The `Muro.IR.Share.funs/2` options are `share:`,
  `inline:`, `inline_max:`, `grow_max:`, `cost:`, `spec:`, `dup_max:`,
  and `inline_small:`.
  """
  def render(book, stem, opts \\ []) when is_list(book) and is_binary(stem) and is_list(opts) do
    case prepare(book, stem, opts) do
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
          param_layouts: Enum.map(fun.params, &Muro.IR.param_lay/1),
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
  `export: false`. `opts` may hold `c_prefix:`, `path:`, and the
  `Muro.IR.Share.funs/2` options `share:`, `inline:`, `inline_max:`,
  `grow_max:`, `cost:`, `spec:`, `dup_max:`, and `inline_small:`.
  """
  def prepare(book, stem, opts \\ []) when is_list(book) and is_binary(stem) and is_list(opts) do
    prefix = Keyword.get(opts, :c_prefix, "")
    path = Keyword.get(opts, :path, stem <> ".muro")

    with :ok <- validate_c_prefix(prefix),
         {:ok, funs} <- IR.elaborate(book) do
      nm = name_map(book, prefix)

      looped =
        funs
        |> Muro.IR.Share.funs(Muro.IR.Share.opts(opts))
        |> Muro.IR.Loop.funs(book: book)

      case compile_funs(looped, book, nm, prefix) do
        {:ok, sigs, texts, extras} ->
          runs = Emit.run_defs(book)
          bytes? = bytes_image?(funs) or data_field_bytes?(book)
          strings? = strings_image?(funs) or data_field_string?(book)

          with :ok <- Emit.refuse_may_fail(book),
               :ok <- Emit.refuse_unboxed_opt(book, funs),
               {:ok, opt_src} <- opt_typedefs(funs, book, bytes?, prefix),
               {:ok, sess_h, sess_c} <-
                 Muro.Emit.C.Session.fragments(book, path, nm, sigs,
                   c_prefix: prefix,
                   stem: stem
                 ) do
            header = header(book, sigs, stem, nm, opt_src, bytes?, strings?, prefix)

            source =
              source(book, runs, sigs, texts, extras, stem, nm, opt_src, bytes?, strings?, prefix)

            {:ok, splice_session(header, sess_h), source <> sess_c, sigs}
          end

        {:error, _} = err ->
          err
      end
    else
      {:error, reason} -> {:error, reason}
    end
  end

  # Empty is the 0.21.14 names. Anything else is concatenated, so the
  # caller includes the separator (`admit_`).
  defp validate_c_prefix(""), do: :ok

  defp validate_c_prefix(prefix) when is_binary(prefix) do
    if prefix =~ ~r/\A[A-Za-z_][A-Za-z0-9_]*\z/, do: :ok, else: {:error, "c:prefix"}
  end

  defp validate_c_prefix(_), do: {:error, "c:prefix"}

  # The header's last non-empty line is the file guard. An earlier
  # `#endif` closes `muro__ALLOC`, and a comment may contain the same
  # word. Session declarations go in front of that last line.
  @doc false
  def splice_session(header, ""), do: header

  def splice_session(header, sess) when is_binary(header) and is_binary(sess) do
    lines = String.split(header, "\n")

    case last_content(lines) do
      {i, "#endif"} ->
        {front, back} = Enum.split(lines, i)
        # One blank line before the session block, then the file guard.
        Enum.join(front, "\n") <> "\n\n" <> String.trim(sess) <> "\n" <> Enum.join(back, "\n")

      _ ->
        header <> "\n" <> sess
    end
  end

  defp last_content(lines) do
    lines
    |> Enum.with_index()
    |> Enum.reverse()
    |> Enum.find_value(fn {line, i} ->
      if String.trim(line) != "", do: {i, String.trim(line)}
    end)
  end

  defp compile_funs(funs, book, nm, prefix \\ "") do
    runs = Emit.run_defs(book)

    with {:ok, groups, step_map} <- Emit.partition_funs(funs, runs) do
      names = Emit.def_names(book, &(prefix <> spell(&1)), nm.taken)
      by_name = Map.new(groups, fn {fun, _} -> {fun.name, fun} end)

      io = io_names(funs)

      Enum.reduce_while(groups, {:ok, [], [], []}, fn {fun, _steps}, {:ok, sigs, texts, extras} ->
        case compile_fun(fun, book, names, by_name, step_map, nm, prefix, io) do
          {:ok, sig, text, extra} ->
            {:cont, {:ok, sigs ++ [sig], texts ++ [text], extras ++ extra}}

          {:error, _} = err ->
            {:halt, err}
        end
      end)
      |> with_io(groups, book, names, by_name, step_map, nm, prefix, io)
    end
  end

  # A run `Muro.IR.Loop` marked `inout: p` also gets an in-place twin,
  # `static void muro__io_N(..., T *p)`, that writes its result through
  # `p` instead of returning it. A loop whose body ends in
  # `{:inout, f, args}` calls the twin on the address of its
  # accumulator, so the by-value struct is neither copied into the call
  # nor copied back out of it. N is the run's place in the image.
  defp io_names(funs) do
    funs
    |> Enum.with_index()
    |> Enum.filter(fn {f, _i} -> Map.get(f, :inout) != nil end)
    |> Map.new(fn {f, i} -> {f.name, g("io", i)} end)
  end

  defp with_io({:ok, sigs, texts, extras}, groups, book, names, by_name, step_map, nm, prefix, io)
       when map_size(io) > 0 do
    groups
    |> Enum.filter(fn {fun, _} -> Map.has_key?(io, fun.name) end)
    |> Enum.reduce_while({:ok, [], []}, fn {fun, _}, {:ok, protos, defs} ->
      case compile_io(fun, book, names, by_name, step_map, nm, prefix, io) do
        {:ok, proto, text, []} -> {:cont, {:ok, protos ++ [proto], defs ++ [text]}}
        {:ok, _proto, _text, _more} -> {:halt, {:error, "c:unsupported"}}
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, protos, defs} -> {:ok, sigs, texts, [Enum.join(protos, "\n") | extras] ++ defs}
      err -> err
    end
  end

  defp with_io(result, _groups, _book, _names, _by_name, _step_map, _nm, _prefix, _io),
    do: result

  defp compile_fun(fun, book, names, by_name, step_map, nm, prefix, io) do
    file_scope = file_scope(nm, MapSet.new(Map.values(names) ++ Map.values(io)))

    {bound, scope} =
      Enum.map_reduce(fun.params, file_scope, fn {pname, lay, _g}, scope ->
        {c, scope} = Name.bind(spell(pname), scope)
        {{pname, c, lay}, scope}
      end)

    sig = %{
      name: Map.fetch!(names, fun.name),
      source: fun.name,
      export: fun.export,
      params: for({_n, c, lay} <- bound, do: {ctype(lay, book, prefix), c}),
      ret: ctype(fun.ret, book, prefix)
    }

    env = Enum.reduce(bound, [], fn {n, c, lay}, env -> [{n, c, lay} | env] end)

    # A match in tail position returns from each arm (`:return`), so no
    # temporary holds the result. A string result is converted by
    # `as_ret/3` after the match, so it keeps the temporary.
    st =
      fun_state(names, book, by_name, step_map, nm, prefix, io, file_scope, scope)
      |> Map.put(:dest, if(fun.ret == :string, do: nil, else: :return))

    with {:ok, {pre, expr, lay, st}} <- emit_ir(fun.body, env, st, sig.ret) do
      expr = as_ret(expr, lay, fun.ret)

      discards =
        bound
        |> Enum.reject(fn {n, _c, _lay} -> uses?(fun.body, n) end)
        |> Enum.map_join("\n", fn {_n, c, _lay} -> "  (void)#{c};" end)

      body =
        cond do
          expr == :return ->
            [discards, indent(pre, 2)] |> Enum.reject(&(&1 == "")) |> Enum.join("\n")

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

  defp fun_state(names, book, by_name, step_map, nm, prefix, io, file_scope, scope) do
    %{
      t: 0,
      dest: nil,
      s: 0,
      steps: [],
      envs: [],
      names: names,
      io: io,
      book: book,
      funs: by_name,
      steps_by_name: step_map,
      fold_done: MapSet.new(),
      nm: nm,
      prefix: prefix,
      file_scope: file_scope,
      base_scope: scope,
      scope: scope
    }
  end

  # The in-place twin of `fun` (see `io_names/1`). The updated parameter
  # is `T *p`, read as `(*p)`. The body is the run's own body, so every
  # read of `(*p)` happens before the one store of the result at the end.
  defp compile_io(fun, book, names, by_name, step_map, nm, prefix, io) do
    file_scope = file_scope(nm, MapSet.new(Map.values(names) ++ Map.values(io)))
    target = Map.fetch!(fun, :inout)

    {bound, scope} =
      Enum.map_reduce(fun.params, file_scope, fn {pname, lay, _g}, scope ->
        {c, scope} = Name.bind(spell(pname), scope)
        {{pname, c, lay}, scope}
      end)

    params =
      for {n, c, lay} <- bound do
        ty = ctype(lay, book, prefix)
        if n == target, do: {String.trim_trailing(ty) <> " *", c}, else: {ty, c}
      end

    env =
      Enum.reduce(bound, [], fn {n, c, lay}, env ->
        [{n, if(n == target, do: "(*#{c})", else: c), lay} | env]
      end)

    {_, ptr, _} = Enum.find(bound, fn {n, _c, _lay} -> n == target end)
    ret = ctype(fun.ret, book, prefix)

    # A match in tail position stores its arms' values through `p`
    # directly, and an arm whose value is `(*p)` stores nothing.
    st =
      fun_state(names, book, by_name, step_map, nm, prefix, io, file_scope, scope)
      |> Map.put(:dest, "(*#{ptr})")

    with {:ok, {pre, expr, lay, st}} <- emit_ir(fun.body, env, st, ret) do
      expr = as_ret(expr, lay, fun.ret)

      discards =
        bound
        |> Enum.reject(fn {n, _c, _lay} -> uses?(fun.body, n) end)
        |> Enum.map_join("\n", fn {_n, c, _lay} -> "  (void)#{c};" end)

      store = if expr == "(*#{ptr})", do: "", else: "  *#{ptr} = #{expr};"

      body =
        [discards, if(pre == "", do: "", else: indent(pre, 2)), store]
        |> Enum.reject(&(&1 == ""))
        |> Enum.join("\n")

      args = Enum.map_join(params, ", ", fn {ty, name} -> "#{ty}#{name}" end)
      head = "__attribute__((unused)) static void #{Map.fetch!(io, fun.name)}(#{args})"
      {:ok, head <> ";", "#{head} {\n#{body}\n}", st.envs ++ st.steps}
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

  # A term in tail position of a match arm, or of a `let` body there,
  # writes the arm's value straight into the enclosing match's temporary
  # (`st.dest`) instead of into a fresh temporary that each level copies
  # up. Any other term is emitted with no destination, and the arm
  # assigns its value. The one store on a path is the last statement of
  # its innermost arm.
  defp emit_ir(tm, env, st, expect) do
    case Map.get(st, :dest) do
      nil ->
        emit_ir0(tm, env, st, expect)

      d ->
        if dest_form?(tm) do
          emit_ir0(tm, env, st, expect)
        else
          with {:ok, {pre, ex, lay, st}} <- emit_ir0(tm, env, %{st | dest: nil}, expect) do
            {:ok, {pre, ex, lay, %{st | dest: d}}}
          end
        end
    end
  end

  defp dest_form?({:match, _, _}), do: true
  defp dest_form?({:let, _, lay, _, _, body}) when lay != :erased and body != :abort, do: true
  defp dest_form?(_), do: false

  # A match's temporary: the destination it inherits, or a fresh one.
  # Its arms are emitted with that temporary as their destination.
  defp slot(st) do
    case Map.get(st, :dest) do
      nil ->
        {t, st} = newt(st)
        {t, true, Map.put(st, :dest, t)}

      d ->
        {d, false, st}
    end
  end

  defp slot_init(true, expect, tname, st), do: init_temp(expect, tname, st)
  defp slot_init(false, _expect, _tname, _st), do: ""

  defp assign(tname, ex) when tname == ex, do: ""
  defp assign(:return, ex), do: "return #{ex};"
  defp assign(tname, ex), do: "#{tname} = #{ex};"

  defp emit_ir0({:var, name}, env, st, expect) do
    case lookup(env, name) do
      {c, lay} ->
        {:ok, {"", adapt(c, lay, expect, st), adapted_lay(lay, expect, st), st}}

      nil ->
        {:error, "c:unsupported"}
    end
  end

  defp emit_ir0(:ze, _env, st, _expect), do: {:ok, {"", "#{g("zero")}()", :nat, st}}
  defp emit_ir0(:tt, _env, st, _expect), do: {:ok, {"", "#{g("tt")}()", :unit, st}}

  defp emit_ir0({:nat, n}, env, st, expect) when is_integer(n) and n >= 0 do
    emit_ir(nat_spine(n), env, st, expect)
  end

  defp emit_ir0({:su, u}, env, st, _expect) do
    with {:ok, {pre, ex, _lay, st}} <- emit_ir(u, env, st, nat_ptr()) do
      {:ok, {pre, "#{g("suc")}(#{ex})", :nat, st}}
    end
  end

  defp emit_ir0({:call, name, args}, env, st, _expect) do
    with {:ok, {pres, exprs, st}} <- emit_args(args, live_ctypes(st, name), env, st) do
      {:ok,
       {squash(pres), "#{ename(st, name)}(#{Enum.join(exprs, ", ")})", call_lay(st, name), st}}
    end
  end

  defp emit_ir0({:con, "Atom", name, []}, _env, st, _expect) do
    {:ok, {"", atom_c(name, st.nm), {:data, "Atom"}, st}}
  end

  defp emit_ir0({:con, dname, cname, args}, env, st, _expect) do
    with {:ok, {pres, exprs, st}} <- emit_args(args, con_ctypes(st, cname), env, st) do
      fun = Map.fetch!(st.nm.ctors, {dname, cname})
      expr = enum_ctor_expr(dname, cname, fun, exprs, st)
      {:ok, {squash(pres), expr, {:data, dname}, st}}
    end
  end

  # An erased constructor field, marked `:erased`. `0`, and the payload
  # is ignored. A zero passed under a spec alias is bound at the
  # argument's layout, so this clause does not see it.
  defp emit_ir0({:let, name, :erased, _g, _val, body}, env, st, expect) do
    {c, scope} = Name.bind(spell(name), st.scope)
    st = %{st | scope: scope}

    with {:ok, {pre, ex, lay, st}} <- emit_ir(body, [{name, c, :opaque} | env], st, expect) do
      void = if uses?(body, name), do: "", else: "(void)#{c};"
      {:ok, {squash(["void *#{c} = 0;", void, pre]), ex, lay, st}}
    end
  end

  # `matchEmpty`. The scrutinee is bound only so the expression is evaluated.
  defp emit_ir0({:let, _name, _lay, _g, val, :abort}, env, st, _expect) do
    with {:ok, {pre, ex, _vlay, st}} <- emit_ir(val, env, st, "void *") do
      stmt = squash([pre, "(void)(#{ex});", "/* unreachable */", "abort();"])
      {:ok, {stmt, "0", :opaque, st}}
    end
  end

  defp emit_ir0({:let, name, lay, _g, val, body}, env, st, expect) do
    ty = ctype(lay, st.book, st.prefix)
    d = Map.get(st, :dest)

    with {:ok, {pre, ex, _vlay, st}} <- emit_ir(val, env, Map.put(st, :dest, nil), ty) do
      {local, st} = news(Map.put(st, :dest, d))

      with {:ok, {pre2, ex2, blay, st}} <-
             emit_ir(body, [{name, local, lay} | env], st, expect) do
        void = if uses?(body, name), do: "", else: "(void)#{local};"
        stmt = squash([pre, "#{ty}#{local} = #{ex};", void, pre2])
        {:ok, {stmt, ex2, blay, st}}
      end
    end
  end

  defp emit_ir0({:pair, a, b}, env, st, _expect) do
    with {:ok, {pre, ea, la, st}} <- emit_ir(a, env, st, "void *"),
         {:ok, {pre2, eb, lb, st}} <- emit_ir(b, env, st, "void *") do
      if Rep.value_lay?(st.book, la) or Rep.value_lay?(st.book, lb) do
        {:error, "c:unboxed"}
      else
        {:ok,
         {squash([pre, pre2]),
          "#{g("mk_pair")}(#{slot_store(ea, la, st)}, #{slot_store(eb, lb, st)})",
          {:pair, la, lb}, st}}
      end
    end
  end

  defp emit_ir0({:letp, a, b, e, body}, env, st, expect) do
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
            bind_half_c(ca, sname, g("field_fst"), la, st),
            bind_half_c(cb, sname, g("field_snd"), lb, st),
            unused,
            pre2
          ])

        {:ok, {stmt, ex2, blay, st}}
      end
    end
  end

  defp emit_ir0({:uncons, e}, env, st, _expect) do
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

  defp emit_ir0({:stream, seed, caps, step_name}, env, st, _expect) do
    with {:ok, step} <- fetch_step(st, step_name),
         {:ok, {seed_p, cap_ps}} <- ok_split(step.params, caps),
         {:ok, {pre, seed_ex, seed_lay, st}} <-
           emit_ir(seed, env, st, ctype(lay_of(seed, env, st), st.book, st.prefix)) do
      id = step_id(step_name)
      slots = capture_slots(caps, cap_ps, st.file_scope)
      pointer_lays = [seed_lay | Enum.map(slots, fn {_n, _f, _tm, lay} -> lay end)]

      if Enum.any?(pointer_lays, &Rep.value_lay?(st.book, &1)) do
        {:error, "c:unboxed"}
      else
        with {:ok, {cpre, outers, st}} <- emit_outers(slots, env, st) do
          {env_ty, env_src, env_ex, st} = alloc_env(slots, outers, id, st)
          saved = st.scope

          with {:ok, {src, st}} <- emit_step_fun(step, slots, seed_p, id, env_ty, st) do
            expr =
              "#{g("stream_new")}(#{slot_store(seed_ex, seed_lay, st)}, #{env_ex}, #{g("step", id)})"

            st = %{st | steps: st.steps ++ [src], scope: saved}

            {:ok,
             {squash([pre, cpre, env_src]), expr, {:stream, seed_domain(seed_p, seed_lay)}, st}}
          end
        end
      end
    end
  end

  defp emit_ir0({:match, scrut, arms} = tm, env, st, expect) do
    kind = match_kind(lay_of(scrut, env, st), arms, st.book)
    rlay = lay_of(tm, env, st)
    # A word operation emits its operand as `void *`. The arms still
    # name a word, so the temporary uses that layout.
    expect = match_expect(expect, rlay, st.book, st.prefix)

    d = Map.get(st, :dest)

    with {:ok, {pre, ex, _lay, st}} <-
           emit_ir(scrut, env, Map.put(st, :dest, nil), scrut_ty(kind, st.book, st.prefix)),
         {:ok, {stmt, name, st}} <-
           emit_switch(kind, pre, ex, arms, env, Map.put(st, :dest, d), expect) do
      {:ok, {stmt, name, rlay, Map.put(st, :dest, d)}}
    end
  end

  defp emit_ir0({:wrd, k, op, args}, env, st, expect) do
    with {:ok, {pres, exprs, st}} <- emit_word_args(args, env, st) do
      case word_c(k, op, exprs, st, expect) do
        {:ok, {more, expr, lay, st}} ->
          {:ok, {squash(pres ++ [more]), expr, lay, st}}

        {:error, _} = err ->
          err
      end
    end
  end

  defp emit_ir0(:abort, _env, st, _expect) do
    {:ok, {squash(["/* unreachable */", "abort();"]), "0", :opaque, st}}
  end

  defp emit_ir0({:byt, bin}, _env, st, _expect) when is_binary(bin) do
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

  defp emit_ir0({:bcat, a, b}, env, st, _expect) do
    with {:ok, {pa, ea, _, st}} <- emit_ir(a, env, st, slice_ty()),
         {:ok, {pb, eb, _, st}} <- emit_ir(b, env, st, slice_ty()) do
      {:ok, {squash([pa, pb]), "#{g("bytes_cat")}(#{ea}, #{eb})", :slice, st}}
    end
  end

  defp emit_ir0({:blen, a}, env, st, _expect) do
    with {:ok, {pre, ex, _, st}} <- emit_ir(a, env, st, slice_ty()) do
      {:ok, {pre, "(uint64_t)((#{ex}).n)", :u64, st}}
    end
  end

  defp emit_ir0({:beq, a, b}, env, st, _expect) do
    with {:ok, {pa, ea, _, st}} <- emit_ir(a, env, st, slice_ty()),
         {:ok, {pb, eb, _, st}} <- emit_ir(b, env, st, slice_ty()) do
      {:ok, {squash([pa, pb]), "#{g("slice_eq")}(#{ea}, #{eb})", :wbool, st}}
    end
  end

  defp emit_ir0({:bsub, s, off, len}, env, st, _expect) do
    with {:ok, {ps, es, _, st}} <- emit_ir(s, env, st, slice_ty()),
         {:ok, {po, eo, _, st}} <- emit_ir(off, env, st, "uint64_t "),
         {:ok, {pn, en, _, st}} <- emit_ir(len, env, st, "uint64_t ") do
      {:ok, {squash([ps, po, pn]), "#{g("slice_sub")}(#{es}, #{eo}, #{en})", :slice, st}}
    end
  end

  defp emit_ir0({:bget, s, i}, env, st, _expect) do
    with {:ok, {ps, es, _, st}} <- emit_ir(s, env, st, slice_ty()),
         {:ok, {pi, ei, _, st}} <- emit_ir(i, env, st, "uint64_t ") do
      {:ok, {squash([ps, pi]), "#{g("slice_get")}(#{es}, #{ei})", {:opt, :u8}, st}}
    end
  end

  defp emit_ir0({:btil, s, b}, env, st, _expect) do
    with {:ok, {ps, es, _, st}} <- emit_ir(s, env, st, slice_ty()),
         {:ok, {pb, eb, _, st}} <- emit_ir(b, env, st, "uint8_t ") do
      {:ok, {squash([ps, pb]), "#{g("slice_until")}(#{es}, #{eb})", :slice, st}}
    end
  end

  defp emit_ir0({:baft, s, b}, env, st, _expect) do
    with {:ok, {ps, es, _, st}} <- emit_ir(s, env, st, slice_ty()),
         {:ok, {pb, eb, _, st}} <- emit_ir(b, env, st, "uint8_t ") do
      {:ok, {squash([ps, pb]), "#{g("slice_after")}(#{es}, #{eb})", :slice, st}}
    end
  end

  defp emit_ir0({:sbytes, s}, env, st, _expect) do
    with {:ok, {pre, ex, lay, st}} <- emit_ir(s, env, st, str_ty()) do
      {:ok, {pre, "#{g("str_bytes")}(#{as_str(ex, lay)})", :slice, st}}
    end
  end

  defp emit_ir0({:bunc, s}, env, st, _expect) do
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
        #{struct_ptr("Maybe", st.prefix)}#{out};
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

  # `Muro.IR.Loop`: the fold step is the loop body. The captures are
  # bound once, the accumulator is a local the body assigns, and a body
  # that returns the accumulator unchanged assigns nothing. A body that
  # ends in `{:inout, f, args}` calls `f`'s in-place twin on the
  # accumulator's address. The body sees only the loop's binders.
  # `inert_skip/5` jumps to the next byte that can change the
  # accumulator, when that set is one, two, or three constants.
  # `needle_loop/3` replaces a fold that is the border automaton of a
  # fixed string. Anything else is the byte loop.
  defp emit_ir0({:loop, _, _, _, _, _, _, _, _} = tm, env, st, expect) do
    case needle_loop(tm, env, st) do
      {:ok, emitted} -> {:ok, emitted}
      :no -> emit_byte_loop(tm, env, st, expect)
      {:error, _} = err -> err
    end
  end

  # In expression position (a match arm of a loop body) the in-place
  # call is a comma expression whose value is the updated accumulator.
  defp emit_ir0({:inout, name, args}, env, st, _expect) do
    with {:ok, {pre, call, acc_c, st}} <- io_call(name, args, env, st) do
      {:ok, {pre, "(#{call}, #{acc_c})", call_lay(st, name), st}}
    end
  end

  defp emit_ir0({:bfold, step, caps, z, s}, env, st, _expect) do
    with {:ok, st} <- ensure_fold_step(step, st),
         {:ok, {cpre, cexs, st}} <- emit_cap_list(caps, env, st),
         {:ok, {pz, ez, lay, st}} <-
           emit_ir(z, env, st, ctype(fold_ret(st, step), st.book, st.prefix)),
         {:ok, {ps, es, _, st}} <- emit_ir(s, env, st, slice_ty()) do
      {acc, st} = news(st)
      {cur, st} = news(st)
      {b, st} = news(st)
      {rest, st} = news(st)
      cty = ctype(lay, st.book, st.prefix)
      sl = g("slice")
      call = Enum.join(cexs ++ [b, rest, acc], ", ")

      with {:ok, {stop, st}} <- fold_stop(step, acc, lay, env, st) do
        loop = """
        #{cty}#{acc} = #{ez};
        #{sl} #{cur} = #{es};
        while (#{cur}.n > 0) {
        #{stop}  uint8_t #{b} = #{cur}.p[0];
          #{sl} #{rest} = (#{sl}){#{cur}.p + 1, #{cur}.n - 1};
          #{acc} = #{fold_cname(step)}(#{call});
          #{cur} = #{rest};
        }
        """

        {:ok, {squash([cpre, pz, ps, loop]), acc, lay, st}}
      end
    end
  end

  defp emit_ir0({:str, bin}, _env, st, _expect) when is_binary(bin) do
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

  defp emit_ir0({:scat, a, b}, env, st, _expect) do
    with {:ok, {pa, ea, la, st}} <- emit_ir(a, env, st, str_ty()),
         {:ok, {pb, eb, lb, st}} <- emit_ir(b, env, st, str_ty()) do
      {:ok,
       {squash([pa, pb]), "#{g("str_cat")}(#{as_str(ea, la)}, #{as_str(eb, lb)})", :string, st}}
    end
  end

  defp emit_ir0({:slen, a}, env, st, _expect) do
    with {:ok, {pre, ex, lay, st}} <- emit_ir(a, env, st, str_ty()) do
      {:ok, {pre, "#{g("str_len")}(#{as_str(ex, lay)})", :nat, st}}
    end
  end

  defp emit_ir0({:seq, a, b}, env, st, _expect) do
    with {:ok, {pa, ea, la, st}} <- emit_ir(a, env, st, str_ty()),
         {:ok, {pb, eb, lb, st}} <- emit_ir(b, env, st, str_ty()) do
      {:ok,
       {squash([pa, pb]), "#{g("str_eq")}(#{as_str(ea, la)}, #{as_str(eb, lb)})", :wbool, st}}
    end
  end

  defp emit_ir0(_other, _env, _st, _expect), do: {:error, "c:unsupported"}

  # A nullary constructor of an enum-scalar type is the enumerator.
  # The function is still emitted for a host that calls it.
  defp enum_ctor_expr(dname, cname, fun, [], st) do
    if Rep.enum?(st.book, dname) do
      ctor_tag(dname, cname, st.prefix)
    else
      "#{fun}()"
    end
  end

  defp enum_ctor_expr(_dname, _cname, fun, exprs, _st) do
    "#{fun}(#{Enum.join(exprs, ", ")})"
  end

  defp emit_byte_loop({:loop, caps, octet, rest, acc, z, s, stop, body}, env, st, _expect) do
    {on, _, _} = octet
    {rn, _, _} = rest
    {an, alay, _} = acc
    cty = ctype(alay, st.book, st.prefix)
    cap_tys = Enum.map(caps, fn {_n, lay, _g, _tm} -> ctype(lay, st.book, st.prefix) end)

    with {:ok, {cpres, cexs, st}} <- emit_args(Enum.map(caps, &elem(&1, 3)), cap_tys, env, st),
         {:ok, {pz, ez, _zlay, st}} <- emit_ir(z, env, st, cty),
         {:ok, {ps, es, _, st}} <- emit_ir(s, env, st, slice_ty()) do
      {accv, st} = news(st)
      {cur, st} = news(st)
      sl = g("slice")

      {cap_decls, benv, st} =
        caps
        |> Enum.zip(Enum.zip(cap_tys, cexs))
        |> Enum.reduce({[], [], st}, fn {{n, lay, _g, _tm}, {ty, ex}}, {decls, benv, st} ->
          {local, st} = news(st)
          void = if uses?(body, n) or stop_uses?(stop, n), do: "", else: "(void)#{local};"
          {decls ++ ["#{ty}#{local} = #{ex};", void], [{n, local, lay} | benv], st}
        end)

      {bv, st} = news(st)
      {rv, st} = news(st)
      benv = [{an, accv, alay}, {rn, rv, :slice}, {on, bv, :u8} | benv]

      with {:ok, {stop_src, st}} <- loop_stop(stop, accv, alay, st),
           {:ok, {bpre, step, st}} <- loop_body(body, an, accv, benv, cty, st) do
        {skip, st} = inert_skip(body, on, an, cur, st)
        octet_decl = if uses?(body, on), do: "uint8_t #{bv} = #{cur}.p[0];", else: ""
        rest_decl = "#{sl} #{rv} = (#{sl}){#{cur}.p + 1, #{cur}.n - 1};"
        rest_void = if uses?(body, rn), do: "", else: "(void)#{rv};"

        inner =
          squash([
            stop_src,
            skip,
            octet_decl,
            rest_decl,
            rest_void,
            bpre,
            step,
            "#{cur} = #{rv};"
          ])

        loop =
          squash([
            "#{cty}#{accv} = #{ez};",
            "#{sl} #{cur} = #{es};",
            "while (#{cur}.n > 0) {",
            indent(inner, 2),
            "}"
          ])

        {:ok, {squash(cpres ++ cap_decls ++ [pz, ps, loop]), accv, alay, st}}
      end
    end
  end

  # A pair slot and a stream seed are `void *`. The struct is copied
  # once; the octets stay where they are. A value that is already a
  # string is passed through.
  defp slot_store(ex, :string, _st), do: "#{g("box_str")}(#{ex})"

  defp slot_store(ex, lay, st) do
    if Rep.enum_lay?(st.book, lay) do
      "(void *)(uintptr_t)(#{ex})"
    else
      ex
    end
  end

  # A constructor argument or a function argument whose C type is
  # `void *` packs here. Other expected types only unpack.
  defp store_as(ex, lay, ty, st) do
    if String.trim(ty) == "void *" do
      slot_store(ex, lay, st)
    else
      adapt(ex, lay, ty, st)
    end
  end

  defp as_str(ex, :string), do: ex
  defp as_str(ex, _lay), do: "*(#{g("str")} *)(#{ex})"

  # Unpack only. Packing a string or an enum into a `void *` slot is
  # `slot_store`, at the store site, so a var read does not pack twice.
  defp adapt(ex, lay, ty, st) do
    want = String.trim(ty)

    cond do
      want == g("str") and lay != :string ->
        as_str(ex, lay)

      # A polymorphic field is `void *`. An all-nullary value packed in
      # that word is restored when the expected type is the enum.
      enum_scalar_ctype?(want, st) and not Rep.enum_lay?(st.book, lay) ->
        "(#{want})(uintptr_t)(#{ex})"

      true ->
        ex
    end
  end

  defp adapted_lay(lay, ty, st) do
    want = String.trim(ty)

    cond do
      want == g("str") and lay != :string ->
        :string

      enum_scalar_ctype?(want, st) and not Rep.enum_lay?(st.book, lay) ->
        enum_lay_of_ctype(want, st) || lay

      true ->
        lay
    end
  end

  defp enum_lay_of_ctype(ty, st) do
    Enum.find_value(data_defs(st.book), fn d ->
      if Rep.enum_data?(d) and struct_name(d.name, st.prefix) == ty do
        {:data, d.name}
      end
    end)
  end

  defp bind_half_c(name, sname, field, :string, _st) do
    "#{g("str")} #{name} = *(#{g("str")} *)#{sname}->#{field};"
  end

  defp bind_half_c(name, sname, field, lay, st) do
    if Rep.enum_lay?(st.book, lay) do
      ty = String.trim(ctype(lay, st.book, st.prefix))
      "#{ty} #{name} = (#{ty})(uintptr_t)#{sname}->#{field};"
    else
      "void *#{name} = #{sname}->#{field};"
    end
  end

  defp str_ty, do: g("str") <> " "

  defp cap_ref(ep, field, :string, _st), do: "(*((#{g("str")} *)#{ep}->#{field}))"

  defp cap_ref(ep, field, lay, st) do
    if Rep.enum_lay?(st.book, lay) do
      ty = String.trim(ctype(lay, st.book, st.prefix))
      "((#{ty})(uintptr_t)#{ep}->#{field})"
    else
      "#{ep}->#{field}"
    end
  end

  defp seed_load(seedp, :string, _st), do: "*(#{g("str")} *)#{seedp}"

  defp seed_load(seedp, lay, st) do
    if Rep.enum_lay?(st.book, lay) do
      ty = String.trim(ctype(lay, st.book, st.prefix))
      "(#{ty})(uintptr_t)#{seedp}"
    else
      seedp
    end
  end

  defp match_expect(expect, lay, book, prefix) do
    if String.trim(expect) == "void *" do
      ty = ctype(lay, book, prefix)
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
          {:cont, {:ok, pres ++ [pre], exprs ++ [store_as(ex, lay, ty, st)], st}}

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

  defp scrut_ty(:nat, _book, _prefix), do: nat_ptr()
  defp scrut_ty(:atom, _book, _prefix), do: atom_ty()
  defp scrut_ty({:data, name}, book, prefix), do: ctype({:data, name}, book, prefix)
  defp scrut_ty(:wbool, book, prefix), do: ctype(:wbool, book, prefix)
  defp scrut_ty({:opt, pay}, book, prefix), do: ctype({:opt, pay}, book, prefix)
  defp scrut_ty(_, _book, _prefix), do: "void *"

  # A pointer or a scalar accepts 0. A struct does not: `muro__slice t = 0`
  # is a type error. `{0}` is the universal initializer, and a scalar
  # written that way trips -Wbraces-around-scalar under -Wall.
  # A string is a struct whose pointer must not be a bare 0. The empty
  # value is a complete initializer, and the match arms overwrite it.
  defp init_temp(expect, tname, st) do
    ty = String.trim(expect)

    cond do
      ty == g("str") -> "#{expect}#{tname} = #{g("str_empty")}();"
      String.ends_with?(ty, "*") -> "#{expect}#{tname} = 0;"
      ty in ["uint8_t", "uint32_t", "uint64_t", "int64_t", "size_t"] -> "#{expect}#{tname} = 0;"
      ty == String.trim(atom_ty()) -> "#{expect}#{tname} = 0;"
      enum_scalar_ctype?(ty, st) -> "#{expect}#{tname} = 0;"
      true -> "#{expect}#{tname} = {0};"
    end
  end

  defp emit_switch(:nat, pre, ex, [{:arm, "zero", [], z}, {:arm, "suc", [y], s}], env, st, expect) do
    {sname, st} = news(st)
    {tname, fresh, st} = slot(st)
    st = %{st | scope: st.base_scope}

    with {:ok, {zpre, zex, _lay, st}} <- emit_ir(z, env, st, expect) do
      st = %{st | scope: st.base_scope}
      {yname, scope} = Name.bind(spell(y), st.scope)
      st = %{st | scope: scope}

      with {:ok, {spre, sex, _lay, st}} <- emit_ir(s, [{y, yname, :nat} | env], st, expect) do
        stmt =
          squash([
            pre,
            slot_init(fresh, expect, tname, st),
            "{",
            "#{nat_ptr()}#{sname} = #{ex};",
            "switch (#{sname}->#{g("field_tag")}) {",
            "case 0: {",
            zpre,
            assign(tname, zex),
            "break;",
            "}",
            "case 1: {",
            "#{nat_ptr()}#{yname} = #{sname}->#{g("field_suc")};",
            spre,
            assign(tname, sex),
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
    {tname, fresh, st} = slot(st)

    with {:ok, {cases, st}} <- emit_atom_arms(arms, tname, env, st, expect) do
      stmt =
        squash([
          pre,
          slot_init(fresh, expect, tname, st),
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
        if enum_if?(data, arms) do
          emit_enum_if(data, dname, pre, ex, arms, env, st, expect)
        else
          emit_data_switch(data, dname, pre, ex, arms, env, st, expect)
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
    {tname, fresh, st} = slot(st)
    st = %{st | scope: st.base_scope}

    with {:ok, {tpre, tex, _lay, st}} <- emit_ir(t, env, st, expect) do
      st = %{st | scope: st.base_scope}

      with {:ok, {fpre, fex, _lay, st}} <- emit_ir(f, env, st, expect) do
        stmt =
          squash([
            pre,
            slot_init(fresh, expect, tname, st),
            "{",
            "#{ctype(:wbool, st.book, st.prefix)}#{sname} = #{ex};",
            "if (#{sname}) {",
            tpre,
            assign(tname, tex),
            "} else {",
            fpre,
            assign(tname, fex),
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
    {tname, fresh, st} = slot(st)
    st = %{st | scope: st.base_scope}

    with {:ok, {npre, nex, _lay, st}} <- emit_ir(n, env, st, expect) do
      st = %{st | scope: st.base_scope}

      {bind, env1, st} =
        if uses?(s, y) do
          {yname, scope} = Name.bind(spell(y), st.scope)
          st = %{st | scope: scope}
          decl = "#{ctype(pay, st.book, st.prefix)}#{yname} = #{sname}.val;"
          {decl, [{y, yname, pay} | env], st}
        else
          {"", env, st}
        end

      with {:ok, {spre, sex, _lay, st}} <- emit_ir(s, env1, st, expect) do
        stmt =
          squash([
            pre,
            slot_init(fresh, expect, tname, st),
            "{",
            "#{ctype({:opt, pay}, st.book, st.prefix)}#{sname} = #{ex};",
            "if (#{sname}.tag) {",
            bind,
            spre,
            assign(tname, sex),
            "} else {",
            npre,
            assign(tname, nex),
            "}",
            "}"
          ])

        {:ok, {stmt, tname, st}}
      end
    end
  end

  defp emit_switch(_kind, _pre, _ex, _arms, _env, _st, _expect), do: {:error, "c:unsupported"}

  # All-nullary data is the tag itself. An unboxed struct is matched on
  # `.tag`. A boxed struct is matched on `->tag`.
  defp data_scrut(data, dname, sname, st) do
    tagf = g("field_tag")

    case Rep.kind(Rep.of_data(st.book, data)) do
      :enum -> {struct_name(dname, st.prefix) <> " ", sname, "->"}
      :value -> {struct_name(dname, st.prefix) <> " ", "#{sname}.#{tagf}", "."}
      :boxed -> {struct_ptr(dname, st.prefix), "#{sname}->#{tagf}", "->"}
    end
  end

  # Both tags are the whole type, so an out-of-range value is not a
  # third arm. The `else` is the second constructor. A wider enum keeps
  # the switch and its `abort`.
  defp enum_if?(data, arms) do
    Rep.enum_data?(data) and length(data.ctors) == 2 and enum_arms?(data, arms)
  end

  defp enum_arms?(data, [{:arm, a, [], _}, {:arm, b, [], _}]) do
    Enum.map(data.ctors, & &1.name) == [a, b]
  end

  defp enum_arms?(_data, _arms), do: false

  defp emit_enum_if(data, dname, pre, ex, arms, env, st, expect) do
    {sname, st} = news(st)
    {tname, fresh, st} = slot(st)
    [c0 | _] = data.ctors
    [arm0, arm1] = arms
    tag0 = ctor_tag(dname, c0.name, st.prefix)
    ptr = struct_name(dname, st.prefix) <> " "

    with {:ok, {t0, st}} <- enum_if_arm(arm0, tname, env, st, expect),
         {:ok, {t1, st}} <- enum_if_arm(arm1, tname, env, st, expect) do
      stmt =
        squash([
          pre,
          slot_init(fresh, expect, tname, st),
          "{",
          "#{ptr}#{sname} = #{ex};",
          "if (#{sname} == #{tag0}) {",
          t0,
          "} else {",
          t1,
          "}",
          "}"
        ])

      {:ok, {stmt, tname, st}}
    end
  end

  defp enum_if_arm({:arm, _cname, [], body}, tname, env, st, expect) do
    st = %{st | scope: st.base_scope}

    with {:ok, {pre, ex, _lay, st}} <- emit_ir(body, env, st, expect) do
      {:ok, {squash([pre, assign(tname, ex)]), st}}
    end
  end

  defp emit_data_switch(data, dname, pre, ex, arms, env, st, expect) do
    {sname, st} = news(st)
    {tname, fresh, st} = slot(st)
    {ptr, switch_on, arrow} = data_scrut(data, dname, sname, st)

    with {:ok, {cases, st}} <-
           emit_data_arms(arms, data, sname, tname, arrow, env, st, expect) do
      stmt =
        squash([
          pre,
          slot_init(fresh, expect, tname, st),
          "{",
          "#{ptr}#{sname} = #{ex};",
          "switch (#{switch_on}) {",
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

  defp emit_atom_arms(arms, tname, env, st, expect) do
    emit_arm_list(arms, st, fn {:arm, name, _bs, body}, st ->
      st = %{st | scope: st.base_scope}

      with {:ok, {pre, ex, _lay, st}} <- emit_ir(body, env, st, expect) do
        text =
          squash([
            "case #{atom_c(name, st.nm)}: {",
            pre,
            assign(tname, ex),
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
    fields = if ctor, do: live_fields(ctor, st.book, st.prefix), else: []

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
            assign(tname, ex),
            "break;",
            "}"
          ])

        {:ok, {text, st}}
      end
    end
  end

  defp live_fields(ctor, book, prefix) do
    {pis, _} = telescope(ctor.type)

    pis
    |> Enum.reject(fn {q, _, _} -> q == :erased end)
    |> Enum.with_index()
    |> Enum.map(fn {{_, a, _}, k} -> {ctype(a, book, prefix), Rep.type_layout(book, a), k} end)
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
  defp seed_domain(p, _lay), do: Muro.IR.param_lay(p)

  # A capture field shares the struct, not the parameter namespace. Claim
  # it against the file, so a field stays `n` when the arm parameter is `n`.
  defp capture_slots(caps, cap_ps, file_scope) do
    lays = Enum.map(cap_ps, &Muro.IR.param_lay/1)

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
          {:cont, {:ok, pres ++ [pre], exprs ++ [slot_store(ex, lay, st)], st}}

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
        [{name, cap_ref(ep, field, lay, st), lay} | env]
      end)

    visible =
      [ep, envp, seedp | Enum.map(slots, &elem(&1, 1))]
      |> Enum.reduce(st.file_scope, &Name.see(&2, &1))

    {seed_line, env, step_base} =
      case seed_p do
        nil ->
          {"  (void)#{seedp};", cap_env, visible}

        seed ->
          sname = Muro.IR.param_name(seed)
          slay = Muro.IR.param_lay(seed)
          # An unfold binder the body never reads stays out of the step.
          # The parameter is still named; a dead local is -Wunused-variable.
          if uses?(step.body, sname) do
            {local, visible} = Name.bind(spell(sname), visible)
            line = "  #{ctype(slay, st.book, st.prefix)}#{local} = #{seed_load(seedp, slay, st)};"
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
  defp lay_of({:let, name, :erased, _g, _val, body}, env, st) do
    lay_of(body, [{name, "", :opaque} | env], st)
  end

  defp lay_of({:let, name, lay, _g, _val, body}, env, st) do
    lay_of(body, [{name, "", lay} | env], st)
  end

  defp lay_of({:call, name, _}, _env, st), do: call_lay(st, name)
  defp lay_of({:con, d, _, _}, _env, _st), do: {:data, d}
  defp lay_of(:ze, _env, _st), do: :nat
  defp lay_of({:su, _}, _env, _st), do: :nat
  defp lay_of({:nat, n}, _env, _st) when is_integer(n) and n >= 0, do: :nat
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
          {:ok, {{_n, lay, _g}, _}} -> {:stream, lay}
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
        {_, a, _} -> [Rep.type_layout(book, a)]
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

  defp live_ctypes(st, name) do
    book = st.book

    type =
      cond do
        d = find_def(book, name) -> d.type
        c = find_ctor(book, name) -> c.type
        true -> nil
      end

    case type do
      nil -> []
      ty -> live_ctypes_of(ty, book, st.prefix)
    end
  end

  defp con_ctypes(st, cname) do
    case find_ctor(st.book, cname) do
      nil -> []
      ctor -> live_ctypes_of(ctor.type, st.book, st.prefix)
    end
  end

  defp live_ctypes_of(ty, book, prefix) do
    {pis, _} = telescope(ty)

    Enum.flat_map(pis, fn
      {:erased, _, _} -> []
      {_, a, _} -> [ctype(a, book, prefix)]
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
      &(Map.get(&1, :kind, :def) not in [:data, :repr, :prefix] and Map.get(&1, :name) == name)
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

  # A loop's body and stop see only the loop's binders.
  defp uses?({:loop, caps, _o, _r, _a, z, s, _stop, _body}, name),
    do: uses?([Enum.map(caps, &elem(&1, 3)), z, s], name)

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

  defp opt_typedefs(funs, book, bytes?, prefix) do
    extra = if bytes?, do: [{:opt, :u8}], else: []

    payloads =
      (funs ++ extra ++ data_field_opts(book))
      |> Enum.flat_map(fn
        fun when is_map(fun) ->
          [fun.ret | Enum.map(fun.params, &Muro.IR.param_lay/1)] ++ collect_opts(fun.body, [])

        lay ->
          [lay]
      end)
      |> Enum.flat_map(&opt_payloads/1)
      |> Enum.uniq()

    if Enum.any?(payloads, &Rep.value_opt_payload?(book, &1)) do
      {:error, "c:unboxed"}
    else
      {:ok, Enum.map_join(payloads, "\n", &opt_typedef(&1, book, prefix))}
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
          {_, a, _} -> [Rep.type_layout(book, a)]
        end)
      end)
    end)
  end

  defp opt_payloads({:opt, p} = lay), do: [lay | opt_payloads(p)]
  defp opt_payloads({:pair, a, b}), do: opt_payloads(a) ++ opt_payloads(b)
  defp opt_payloads({:stream, a}), do: opt_payloads(a)
  defp opt_payloads(_), do: []

  # The option struct is printed before the data structs. A boxed
  # payload is a pointer, so the later struct completes it. A by-value
  # payload would be that struct while it is still incomplete
  # (`Muro.IR.Rep.value_opt_payload?/2`).
  # A word, a nat, unit, a string, or a slice is the same struct in every
  # book, so the guard lets two headers share it. An option of data names
  # that book's struct, and a prefix changes the spelling, so it stays
  # unguarded: two such headers are a redefinition, not a silent mismatch.
  defp opt_typedef({:opt, pay}, book, prefix) do
    name = opt_name(pay)

    body = """
    typedef struct #{name} #{name};
    struct #{name} { uint8_t tag; #{ctype(pay, book, prefix)}val; };
    """

    text =
      if opt_shared?(pay, prefix) do
        guard = opt_guard(pay)

        """
        #ifndef #{guard}
        #define #{guard}
        #{String.trim(body)}
        #endif
        """
      else
        body
      end

    text |> String.trim()
  end

  defp opt_shared?(pay, prefix), do: prefix == "" or not opt_names_data?(pay)

  defp opt_names_data?({:data, _}), do: true
  defp opt_names_data?({:var, _}), do: true
  defp opt_names_data?({:def, _}), do: true
  defp opt_names_data?({:app, f, _}), do: opt_names_data?(f)
  defp opt_names_data?({:opt, inner}), do: opt_names_data?(inner)
  defp opt_names_data?({:pair, a, b}), do: opt_names_data?(a) or opt_names_data?(b)
  defp opt_names_data?({:stream, a}), do: opt_names_data?(a)
  defp opt_names_data?(_), do: false

  defp opt_guard(pay), do: "MURO__OPT_" <> String.upcase(lay_tag(pay))

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

  defp ctype(type, book, prefix)

  defp ctype(:atom, _book, _prefix), do: atom_ty()
  defp ctype(:nat, _book, _prefix), do: nat_ptr()
  defp ctype(:unit, _book, _prefix), do: unit_ptr()
  defp ctype({:stream, _}, _book, _prefix), do: stream_ptr()

  defp ctype({:var, name}, book, prefix) when is_binary(name) do
    cond do
      Rep.enum?(book, name) -> struct_val(name, prefix)
      Rep.unboxed?(book, name) -> struct_val(name, prefix)
      data?(book, name) -> struct_ptr(name, prefix)
      true -> "void *"
    end
  end

  defp ctype({:def, name}, book, prefix) do
    cond do
      Rep.enum?(book, name) -> struct_val(name, prefix)
      Rep.unboxed?(book, name) -> struct_val(name, prefix)
      true -> "void *"
    end
  end

  defp ctype({:app, f, _a}, book, prefix), do: ctype(f, book, prefix)
  defp ctype({:data, "Atom"}, _book, _prefix), do: atom_ty()

  defp ctype({:data, name}, book, prefix) do
    cond do
      Rep.enum?(book, name) -> struct_val(name, prefix)
      Rep.unboxed?(book, name) -> struct_val(name, prefix)
      true -> struct_ptr(name, prefix)
    end
  end

  defp ctype(:u8, _book, _prefix), do: "uint8_t "
  defp ctype(:u32, _book, _prefix), do: "uint32_t "
  defp ctype(:u64, _book, _prefix), do: "uint64_t "
  defp ctype(:i64, _book, _prefix), do: "int64_t "
  defp ctype(:wbool, _book, _prefix), do: "uint8_t "
  defp ctype(:slice, _book, _prefix), do: g("slice") <> " "
  defp ctype(:bytes, _book, _prefix), do: g("slice") <> " "
  defp ctype(:string, _book, _prefix), do: str_ty()
  defp ctype({:opt, pay}, _book, _prefix), do: opt_name(pay) <> " "
  defp ctype({:word, {:ty, :u8}, []}, book, prefix), do: ctype(:u8, book, prefix)
  defp ctype({:word, {:ty, :u32}, []}, book, prefix), do: ctype(:u32, book, prefix)
  defp ctype({:word, {:ty, :u64}, []}, book, prefix), do: ctype(:u64, book, prefix)
  defp ctype({:word, :bool, []}, book, prefix), do: ctype(:wbool, book, prefix)
  defp ctype({:word, {:optk, k}, []}, book, prefix), do: ctype({:opt, k}, book, prefix)

  defp ctype({:word, :opt, [a]}, book, prefix),
    do: ctype({:opt, Rep.type_layout(book, a)}, book, prefix)

  defp ctype(_, _book, _prefix), do: "void *"

  defp data?(book, name) when is_list(book) do
    Enum.any?(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp data?(_book, _name), do: false

  defp struct_ptr(name, prefix), do: struct_name(name, prefix) <> " *"
  defp struct_val(name, prefix), do: struct_name(name, prefix) <> " "

  # `spell/1` is injective. A prefix, when the host asked for one, is
  # prepended and already includes the separator. Empty keeps the source
  # spelling an unprefixed book already emits.
  defp struct_name(name, prefix), do: data_struct(name, prefix)

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

  defp header(book, sigs, stem, nm, opts, bytes?, strings?, prefix) do
    guard = guard(stem)

    parts = [
      "/* generated by muro — do not edit */",
      "#ifndef #{guard}",
      "#define #{guard}",
      "#include <stdint.h>",
      alloc_macro(),
      prelude_guard(),
      if(bytes?, do: bytes_header(), else: ""),
      if(strings?, do: string_header(), else: ""),
      data_typedefs(book, prefix),
      opts,
      atom_enum(book, nm),
      stream_typedef(sigs, book),
      data_bodies(book, prefix),
      word_enum(book, stem, prefix),
      prototypes(sigs),
      "#endif"
    ]

    join_parts(parts)
  end

  # `muro__nat` and `muro__unit` are the same two structs in every book.
  # One guard lets two headers share a translation unit.
  defp prelude_guard do
    """
    #ifndef MURO__PRELUDE
    #define MURO__PRELUDE
    #{nat_struct()}
    #{unit_struct()}
    #endif
    """
    |> String.trim()
  end

  defp source(book, runs, sigs, funs, extras, stem, nm, _opts, bytes?, strings?, prefix) do
    {funs, extras} = inline_hot(funs, extras, book, prefix)

    internals =
      sigs
      |> Enum.reject(& &1.export)
      |> Enum.map_join("\n", &"#{decl(&1)};")

    parts = [
      "/* generated by muro — do not edit */",
      "#include \"#{stem}.h\"",
      "#include <stdlib.h>",
      if(bytes?, do: "#include <string.h>\n" <> bytes_helpers(), else: ""),
      find_helpers(Enum.join(funs ++ extras, "\n")),
      nat_helpers(),
      unit_helpers(),
      if(strings?, do: "#include <string.h>\n" <> string_helpers(bytes?), else: ""),
      pair_helpers(runs),
      stream_helpers(runs, stream_declared?(sigs, book)),
      data_ctors(book, nm, sigs, prefix),
      internals,
      Enum.join(extras, "\n\n"),
      Enum.join(funs, "\n\n")
    ]

    join_parts(parts)
  end

  # A scalar run the byte loops reach, with no loop of its own and a
  # body no wider than the name step. Inlining it removes the call
  # around each octet. A run past that width, or one the loops do not
  # reach, stays a call: inlining it bloated the request step.
  @inline_body 700

  defp inline_hot(funs, extras, book, prefix) do
    parsed = Enum.flat_map(funs ++ extras, &parse_cfun/1)
    by = Map.new(parsed, fn p -> {p.name, p} end)
    chosen = inline_names(parsed, by, scalar_rets(book, prefix))
    {Enum.map(funs, &apply_inline(&1, chosen)), Enum.map(extras, &apply_inline(&1, chosen))}
  end

  defp scalar_rets(book, prefix) do
    enums =
      book
      |> data_defs()
      |> Enum.filter(&Rep.enum_data?/1)
      |> Enum.map(&struct_name(&1.name, prefix))

    MapSet.new(["uint8_t", "uint32_t", "uint64_t", "int64_t" | enums])
  end

  defp inline_names(parsed, by, scalar) do
    small =
      parsed
      |> Enum.filter(fn p ->
        MapSet.member?(scalar, p.ret) and not p.loop and not p.field and p.size <= @inline_body
      end)
      |> MapSet.new(& &1.name)

    parsed
    |> hot_steps()
    |> Enum.reduce(MapSet.new(), fn name, seen -> inline_walk(name, by, seen) end)
    |> MapSet.intersection(small)
  end

  defp hot_steps(parsed) do
    Enum.reduce(parsed, MapSet.new(), fn p, acc ->
      if p.loop, do: MapSet.union(acc, assigned_in_loops(p.body, p.name)), else: acc
    end)
  end

  defp inline_walk(name, by, seen) do
    cond do
      MapSet.member?(seen, name) ->
        seen

      match?(%{loop: true}, Map.get(by, name)) ->
        seen

      is_map(Map.get(by, name)) ->
        seen = MapSet.put(seen, name)
        Enum.reduce(Map.fetch!(by, name).calls, seen, &inline_walk(&1, by, &2))

      true ->
        seen
    end
  end

  defp assigned_in_loops(body, self) do
    body
    |> String.split("\n")
    |> Enum.reduce({MapSet.new(), 0, false}, fn line, {set, depth, pending} ->
      pending = pending or Regex.match?(~r/\b(while|for)\s*\(/, line)
      opens = length(:binary.matches(line, "{"))
      closes = length(:binary.matches(line, "}"))

      set =
        if depth > 0 or pending do
          ~r/=\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(/
          |> Regex.scan(line)
          |> Enum.reduce(set, fn [_, n], s ->
            if n == self, do: s, else: MapSet.put(s, n)
          end)
        else
          set
        end

      {depth, pending} =
        cond do
          pending and opens > 0 -> {depth + opens, false}
          depth > 0 -> {max(depth + opens - closes, 0), false}
          true -> {depth, pending}
        end

      {set, depth, pending}
    end)
    |> elem(0)
  end

  defp parse_cfun(text) when is_binary(text) do
    case Regex.run(~r/\A(.*?)\{(.*)\}\s*\z/s, text) do
      [_, head, body] ->
        cleaned =
          head
          |> String.replace(~r/__attribute__\(\([^)]*\)\)/, "")
          |> String.replace(~r/\b(static|inline)\b/, "")
          |> String.trim()

        case Regex.run(~r/\A(.+?)\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(/s, cleaned) do
          [_, ret, name] ->
            [
              %{
                name: name,
                ret: String.trim(ret),
                size: byte_size(text),
                loop: Regex.match?(~r/\b(while|for)\s*\(/, body),
                field: String.contains?(body, "muro__field_tag"),
                calls: c_calls(body, name),
                body: body
              }
            ]

          _ ->
            []
        end

      _ ->
        []
    end
  end

  defp c_calls(body, self) do
    ~r/\b([A-Za-z_][A-Za-z0-9_]*)\s*\(/
    |> Regex.scan(body)
    |> Enum.map(fn [_, n] -> n end)
    |> Enum.reject(&(&1 == self))
    |> MapSet.new()
  end

  defp apply_inline(text, chosen) do
    case parse_cfun(text) do
      [%{name: name}] ->
        if MapSet.member?(chosen, name), do: prefix_inline(text), else: text

      _ ->
        text
    end
  end

  defp prefix_inline("__attribute__((unused)) static " <> rest) do
    "__attribute__((always_inline, unused)) static inline " <> rest
  end

  defp prefix_inline(text), do: "__attribute__((always_inline)) inline " <> text

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
      string_lay?(fun.ret) or Enum.any?(fun.params, fn p -> string_lay?(Muro.IR.param_lay(p)) end) or
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
    #ifndef MURO__STR
    #define MURO__STR
    #include <stddef.h>
    typedef struct { const uint8_t *p; size_t n; } #{ty};
    __attribute__((unused)) static const uint8_t #{empty}[1] = {0};
    __attribute__((unused)) static inline #{ty} #{emp}(void) {
      return (#{ty}){#{empty}, 0};
    }
    #endif
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
      bytes_lay?(fun.ret) or Enum.any?(fun.params, fn p -> bytes_lay?(Muro.IR.param_lay(p)) end) or
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
    #ifndef MURO__SLICE
    #define MURO__SLICE
    #include <stddef.h>
    typedef struct { const uint8_t *p; size_t n; } #{sl};
    __attribute__((unused)) static const uint8_t #{empty}[1] = {0};
    __attribute__((unused)) static inline #{sl} #{emp}(void) {
      return (#{sl}){#{empty}, 0};
    }
    __attribute__((unused)) static inline #{sl} #{wrap}(const uint8_t *p, size_t n) {
      if (n == 0 || p == 0) return #{emp}();
      return (#{sl}){p, n};
    }
    #endif
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
      const uint8_t *q;
      if (s.n == 0) return s;
      q = memchr(s.p, b, s.n);
      if (q == 0) return s;
      return (#{sl}){s.p, (size_t)(q - s.p)};
    }

    __attribute__((unused)) static #{sl} #{aft}(#{sl} s, uint8_t b) {
      const uint8_t *q;
      size_t i;
      if (s.n == 0) return #{emp}();
      q = memchr(s.p, b, s.n);
      if (q == 0) return #{emp}();
      i = (size_t)(q - s.p);
      return (#{sl}){s.p + i + 1, s.n - i - 1};
    }
    """
    |> String.trim()
  end

  # Emitted only when a loop jumps to a short set of bytes. A book
  # with no such loop keeps the bytes it had. SSE2 compares sixteen
  # octets and stops on the first equal one. The scalar tail is that
  # same scan, and it is the whole function where SSE2 is absent.
  # Either way the pointer is the first hit or the end, never a later
  # octet. `memcpy` keeps the wide load off the slice's element type.
  defp find_helpers(text) when is_binary(text) do
    want2 = String.contains?(text, g("find2") <> "(")
    want3 = String.contains?(text, g("find3") <> "(")
    sse = want2 or want3 or String.contains?(text, "_mm_cmpeq_epi8")

    parts =
      []
      |> then(fn acc -> if want2, do: acc ++ [find2_helper()], else: acc end)
      |> then(fn acc -> if want3, do: acc ++ [find3_helper()], else: acc end)

    hdr =
      if sse do
        """
        #include <string.h>
        #if defined(__SSE2__)
        #include <emmintrin.h>
        #endif
        """
      else
        ""
      end

    hdr <> Enum.join(parts, "\n\n")
  end

  defp find2_helper do
    name = g("find2")

    """
    __attribute__((always_inline, unused)) static inline const uint8_t *#{name}(const uint8_t *p, size_t n, uint8_t a, uint8_t b) {
      const uint8_t *end = p + n;
    #if defined(__SSE2__)
      const __m128i va = _mm_set1_epi8((char)a);
      const __m128i vb = _mm_set1_epi8((char)b);
      while (n >= 16) {
        __m128i v;
        __m128i m;
        unsigned bits;
        memcpy(&v, p, 16);
        m = _mm_or_si128(_mm_cmpeq_epi8(v, va), _mm_cmpeq_epi8(v, vb));
        bits = (unsigned)_mm_movemask_epi8(m);
        if (bits) return p + (unsigned)__builtin_ctz(bits);
        p += 16;
        n -= 16;
      }
    #endif
      while (p < end) {
        if (*p == a || *p == b) return p;
        p++;
      }
      return end;
    }
    """
    |> String.trim()
  end

  defp find3_helper do
    name = g("find3")

    """
    __attribute__((always_inline, unused)) static inline const uint8_t *#{name}(const uint8_t *p, size_t n, uint8_t a, uint8_t b, uint8_t c) {
      const uint8_t *end = p + n;
    #if defined(__SSE2__)
      const __m128i va = _mm_set1_epi8((char)a);
      const __m128i vb = _mm_set1_epi8((char)b);
      const __m128i vc = _mm_set1_epi8((char)c);
      while (n >= 16) {
        __m128i v;
        __m128i m;
        unsigned bits;
        memcpy(&v, p, 16);
        m = _mm_or_si128(_mm_cmpeq_epi8(v, va), _mm_or_si128(_mm_cmpeq_epi8(v, vb), _mm_cmpeq_epi8(v, vc)));
        bits = (unsigned)_mm_movemask_epi8(m);
        if (bits) return p + (unsigned)__builtin_ctz(bits);
        p += 16;
        n -= 16;
      }
    #endif
      while (p < end) {
        if (*p == a || *p == b || *p == c) return p;
        p++;
      }
      return end;
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

  # Once the step returns its accumulator unchanged for every octet,
  # the rest of the fold is the identity, so the loop stops there.
  # `Muro.IR.Share.stop/2` finds that test. A step it cannot read
  # gets no test, and the loop walks every octet as before.
  defp fold_stop(step, acc, lay, env, st) do
    with %{} = fun <- Map.get(st.steps_by_name, step),
         {:ok, v, test} <- Muro.IR.Share.stop(fun, st.funs),
         {:ok, {pre, ex, _lay, st}} <- emit_ir(test, [{v, acc, lay} | env], st, "uint64_t ") do
      {:ok, {indent(squash([pre, "if (#{ex}) break;"]), 2) <> "\n", st}}
    else
      _ -> {:ok, {"", st}}
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
      Enum.map_reduce(fun.params, visible, fn {pname, lay, _g}, scope ->
        {c, scope} = Name.bind(spell(pname), scope)
        {{pname, c, lay}, scope}
      end)

    params = for {_n, c, lay} <- bound, do: {ctype(lay, st.book, st.prefix), c}
    ret = ctype(fun.ret, st.book, st.prefix)
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

  # The early exit (`Muro.IR.Share.stop/2`) of a loop, before each octet.
  defp loop_stop(:none, _acc, _lay, st), do: {:ok, {"", st}}

  defp loop_stop({v, test}, acc, lay, st) do
    with {:ok, {pre, ex, _lay, st}} <- emit_ir(test, [{v, acc, lay}], st, "uint64_t ") do
      {:ok, {squash([pre, "if (#{ex}) break;"]), st}}
    end
  end

  defp stop_uses?(:none, _n), do: false
  defp stop_uses?({v, test}, n), do: v != n and uses?(test, n)

  # The statements that set the accumulator `acc` to the body's value.
  # A tail `let` is a local, as in `emit_ir/4`. A body that is the
  # accumulator itself sets nothing.
  defp loop_body({:var, an}, an, _acc, _env, _cty, st), do: {:ok, {"", "", st}}

  defp loop_body({:inout, name, args}, _an, _acc, env, _cty, st) do
    with {:ok, {pre, call, _acc_c, st}} <- io_call(name, args, env, st) do
      {:ok, {pre, call <> ";", st}}
    end
  end

  defp loop_body({:let, x, lay, _g, val, body}, an, acc, env, cty, st)
       when lay != :erased and body != :abort and x != an do
    ty = ctype(lay, st.book, st.prefix)

    with {:ok, {pre, ex, _vlay, st}} <- emit_ir(val, env, st, ty) do
      {local, st} = news(st)

      with {:ok, {pre2, step, st}} <- loop_body(body, an, acc, [{x, local, lay} | env], cty, st) do
        void = if uses?(body, x), do: "", else: "(void)#{local};"
        {:ok, {squash([pre, "#{ty}#{local} = #{ex};", void, pre2]), step, st}}
      end
    end
  end

  defp loop_body(body, _an, acc, env, cty, st) do
    d = Map.get(st, :dest)

    with {:ok, {pre, ex, _lay, st}} <- emit_ir(body, env, Map.put(st, :dest, acc), cty) do
      {:ok, {pre, assign(acc, ex), Map.put(st, :dest, d)}}
    end
  end

  # A fold of a `U64` whose step is the border automaton of one octet
  # string: the low three bits are the matched length, the bits above
  # them are how far the fold has read, and the matched length sticks
  # once it is the whole string. The loop is a scan for that string.
  # The unmatched suffix is the automaton, so the packed miss state is
  # the one the byte loop would have returned. A step this cannot read
  # stays the byte loop. Recognition is the transition table, not the
  # step's name.
  defp needle_loop({:loop, [], octet, rest, {an, :u64, _}, z, s, _stop, body}, env, st) do
    {on, _, _} = octet
    {rn, _, _} = rest

    with false <- uses?(body, rn),
         {:ok, bytes, delta, accept} <- needle_table(z, body, on, an, st) do
      cty = ctype(:u64, st.book, st.prefix)
      sl = g("slice")

      with {:ok, {pz, ez, _, st}} <- emit_ir(z, env, st, cty),
           {:ok, {ps, es, _, st}} <- emit_ir(s, env, st, slice_ty()) do
        {accv, st} = news(st)
        {cur, st} = news(st)
        {lab, st} = news(st)

        stmt =
          squash([
            pz,
            ps,
            "#{cty}#{accv} = #{ez};",
            "#{sl} #{cur} = #{es};",
            needle_c(bytes, delta, accept, accv, cur, lab)
          ])

        {:ok, {stmt, accv, :u64, st}}
      end
    else
      _ -> :no
    end
  end

  defp needle_loop(_, _, _), do: :no

  defp needle_table(z, body, on, an, st) do
    funs = Map.values(st.funs)

    with {:ok, {:word, :u64, 0}} <- Muro.IR.Eval.eval(funs, z, %{}, fuel: 8_000),
         {:ok, delta, accept} <- probe_states(funs, body, on, an),
         {:ok, bytes} <- chain_needle(delta, accept),
         true <- border_matches?(bytes, delta, accept) do
      {:ok, bytes, delta, accept}
    else
      _ -> :no
    end
  end

  defp probe_states(funs, body, on, an) do
    walk_states([0], MapSet.new(), %{}, nil, funs, body, on, an)
  end

  defp walk_states([], _seen, _delta, nil, _funs, _body, _on, _an), do: :no

  defp walk_states([], _seen, delta, accept, _funs, _body, _on, _an),
    do: {:ok, delta, accept}

  defp walk_states([s | rest], seen, delta, accept, funs, body, on, an) do
    cond do
      s > 7 or MapSet.member?(seen, s) ->
        walk_states(rest, seen, delta, accept, funs, body, on, an)

      true ->
        seen = MapSet.put(seen, s)

        case classify_state(s, funs, body, on, an) do
          :no ->
            :no

          :absorb ->
            if accept == nil do
              walk_states(rest, seen, delta, s, funs, body, on, an)
            else
              :no
            end

          {:move, map} ->
            delta = Enum.reduce(map, delta, fn {b, n}, d -> Map.put(d, {s, b}, n) end)
            more = map |> Map.values() |> Enum.uniq()
            walk_states(rest ++ more, seen, delta, accept, funs, body, on, an)
        end
    end
  end

  defp classify_state(s, funs, body, on, an) do
    acc = Bitwise.bor(Bitwise.band(s, 7), 40)

    0..255
    |> Enum.reduce_while({:same, %{}}, fn b, {mode, map} ->
      case probe_step(funs, body, on, an, b, acc) do
        {:ok, ^acc} ->
          if mode == :move, do: {:halt, :no}, else: {:cont, {:same, map}}

        {:ok, r} ->
          next = Bitwise.band(r, 7)
          moved = Bitwise.bsr(r, 3) == 6 and next <= 7 and mode != :same_bad

          cond do
            moved and mode in [:same, :move] -> {:cont, {:move, Map.put(map, b, next)}}
            true -> {:halt, :no}
          end

        :no ->
          {:halt, :no}
      end
    end)
    |> case do
      {:same, _} -> :absorb
      {:move, map} when map_size(map) == 256 -> {:move, map}
      _ -> :no
    end
  end

  defp probe_step(funs, body, on, an, byte, acc) do
    env = %{on => {:word, :u8, byte}, an => {:word, :u64, acc}}

    case Muro.IR.Eval.eval(funs, body, env, fuel: 8_000) do
      {:ok, {:word, :u64, n}} when is_integer(n) and n >= 0 -> {:ok, n}
      _ -> :no
    end
  end

  defp chain_needle(delta, accept) when is_integer(accept) and accept >= 2 and accept <= 7 do
    0..(accept - 1)
    |> Enum.reduce_while([], fn s, acc ->
      bytes = for b <- 0..255, Map.get(delta, {s, b}) == s + 1, do: b

      case bytes do
        [b] -> {:cont, acc ++ [b]}
        _ -> {:halt, :no}
      end
    end)
    |> case do
      bytes when is_list(bytes) and length(bytes) == accept -> {:ok, bytes}
      _ -> :no
    end
  end

  defp chain_needle(_delta, _accept), do: :no

  # `pi` is the border table of the needle. Every reached state has to
  # be that automaton, including a byte that is not the next octet of
  # the needle.
  defp border_matches?(bytes, delta, accept) do
    pi = prefix_borders(bytes)

    covered =
      Enum.all?(0..(accept - 1), fn s -> Enum.all?(0..255, &Map.has_key?(delta, {s, &1})) end)

    covered and
      Enum.all?(delta, fn {{s, b}, n} ->
        s <= accept and border_step(bytes, pi, s, b) == n
      end)
  end

  defp prefix_borders(bytes) do
    m = length(bytes)

    {pi, _} =
      Enum.reduce(1..max(m - 1, 0)//1, {%{0 => 0}, 0}, fn q, {pi, k} ->
        k = drop_border(bytes, pi, k, q)
        k = if Enum.at(bytes, k) == Enum.at(bytes, q), do: k + 1, else: k
        {Map.put(pi, q, k), k}
      end)

    pi
  end

  defp drop_border(bytes, pi, k, q) when k > 0 do
    if Enum.at(bytes, k) == Enum.at(bytes, q),
      do: k,
      else: drop_border(bytes, pi, Map.fetch!(pi, k - 1), q)
  end

  defp drop_border(_bytes, _pi, 0, _q), do: 0

  # The step walks borders against the octet just read. `drop_border/4`
  # walks them against a later needle index, which is how `pi` is built.
  defp fall_border(bytes, pi, k, b) when k > 0 do
    if Enum.at(bytes, k) == b,
      do: k,
      else: fall_border(bytes, pi, Map.fetch!(pi, k - 1), b)
  end

  defp fall_border(_bytes, _pi, 0, _b), do: 0

  defp border_step(bytes, pi, s, b) do
    if s == length(bytes) do
      s
    else
      s = fall_border(bytes, pi, s, b)
      if s < length(bytes) and Enum.at(bytes, s) == b, do: s + 1, else: s
    end
  end

  defp needle_c(bytes, delta, accept, accv, cur, lab) do
    len = length(bytes)
    b0 = hd(bytes)
    stride = 16 - (len - 1)
    hit = lab <> "_hit"
    done = lab <> "_done"
    tail = len - 1

    """
    {
      const uint8_t *p = #{cur}.p;
      size_t n = #{cur}.n;
      const uint8_t *hit = 0;
      if (n >= #{len}) {
    #if defined(__SSE2__)
        const __m128i v0 = _mm_set1_epi8((char)#{b0});
        const uint8_t *q = p;
        const uint8_t *end = p + n;
        while ((size_t)(end - q) >= 16) {
          __m128i v;
          unsigned bits;
          memcpy(&v, q, 16);
          bits = (unsigned)_mm_movemask_epi8(_mm_cmpeq_epi8(v, v0));
          while (bits) {
            unsigned i = (unsigned)__builtin_ctz(bits);
            if ((size_t)(q - p) + i + #{len} <= n && #{sse_verify(bytes)}) {
              hit = q + i;
              goto #{hit};
            }
            bits &= bits - 1;
          }
          q += #{stride};
        }
        while (q + #{len} <= end) {
          if (#{scalar_verify(bytes)}) { hit = q; goto #{hit}; }
          q++;
        }
    #else
        const uint8_t *q = p;
        const uint8_t *end = p + n;
        while (q + #{len} <= end) {
          if (#{scalar_verify(bytes)}) { hit = q; goto #{hit}; }
          q++;
        }
    #endif
      }
      {
        size_t i;
        size_t start;
        unsigned st;
        uint8_t b;
        start = n > #{tail} ? n - #{tail} : 0;
        st = 0;
        for (i = start; i < n; i++) {
          b = p[i];
          #{miss_switch(delta, accept)}
          if (st == #{accept}) {
            #{accv} = ((uint64_t)#{accept}) | ((uint64_t)(i + 1) << 3);
            goto #{done};
          }
        }
        #{accv} = ((uint64_t)st) | ((uint64_t)n << 3);
        goto #{done};
      }
    #{hit}:
      #{accv} = ((uint64_t)#{accept}) | ((uint64_t)((size_t)(hit - p) + #{len}) << 3);
    #{done}:
      ;
    }
    """
  end

  defp sse_verify([_b]), do: "1"

  defp sse_verify(bytes) do
    bytes
    |> Enum.drop(1)
    |> Enum.with_index(1)
    |> Enum.map_join(" && ", fn {b, i} -> "q[i + #{i}] == #{b}" end)
  end

  defp scalar_verify(bytes) do
    bytes
    |> Enum.with_index()
    |> Enum.map_join(" && ", fn {b, i} -> "q[#{i}] == #{b}" end)
  end

  defp miss_switch(delta, accept) do
    arms =
      Enum.map(0..(accept - 1), fn s ->
        "case #{s}: { #{miss_arm(delta, s)} break; }"
      end)

    """
    switch (st) {
    #{Enum.join(arms, "\n")}
    case #{accept}: break;
    default: st = 0; break;
    }
    """
    |> String.trim()
  end

  defp miss_arm(delta, s) do
    groups = Enum.group_by(0..255, fn b -> Map.fetch!(delta, {s, b}) end)
    {default, _} = Enum.max_by(groups, fn {_n, bs} -> length(bs) end)

    specials =
      groups
      |> Enum.reject(fn {n, _} -> n == default end)
      |> Enum.sort_by(fn {n, _} -> n end)

    cond do
      specials == [] ->
        "st = #{default};"

      true ->
        chain =
          specials
          |> Enum.with_index()
          |> Enum.map_join(" ", fn {{n, bs}, i} ->
            kw = if i == 0, do: "if", else: "else if"
            test = Enum.map_join(bs, " || ", fn b -> "b == #{b}" end)
            "#{kw} (#{test}) st = #{n};"
          end)

        chain <> " else st = #{default};"
    end
  end

  # A byte the step returns the accumulator for is inert. When every
  # inert byte is outside a set of one, two, or three constants, the
  # loop may jump to the next byte in that set and run the body once
  # there. The index is the distance from the slice the fold was given,
  # so moving the cursor keeps it. A false hit is an earlier byte, and
  # the body is the identity on it, so the loop still moves forward.
  # Anything the walk cannot read (an unconstrained change, a test it
  # does not know, an empty set, a set larger than three) keeps today's
  # loop. The predicates are recognised by their bodies, not their names.
  defp inert_skip(body, oct, acc, cur, st) do
    case hot_bytes(body, oct, acc, st.funs) do
      :no ->
        {"", st}

      {:ok, ks} ->
        {hit, st} = news(st)
        {sk, st} = news(st)
        sl = g("slice")

        src =
          [
            "{",
            "const uint8_t *#{hit} = #{find_call(ks, cur)};",
            "size_t #{sk} = (size_t)(#{hit} - #{cur}.p);",
            "#{cur} = (#{sl}){#{hit}, #{cur}.n - #{sk}};",
            "}",
            "if (#{cur}.n == 0) break;"
          ]
          |> Enum.join("\n")

        {src, st}
    end
  end

  defp find_call([k], cur), do: "#{g("find2")}(#{cur}.p, #{cur}.n, #{k}, #{k})"

  defp find_call([a, b], cur), do: "#{g("find2")}(#{cur}.p, #{cur}.n, #{a}, #{b})"

  defp find_call([a, b, c], cur), do: "#{g("find3")}(#{cur}.p, #{cur}.n, #{a}, #{b}, #{c})"

  defp hot_bytes(body, oct, acc, funs) do
    case follow_step(body, oct, acc, funs, 0) do
      {:ok, set} ->
        ks = set |> MapSet.to_list() |> Enum.sort()

        if ks != [] and length(ks) <= 3 and Enum.all?(ks, &(&1 in 0..255)),
          do: {:ok, ks},
          else: :no

      :no ->
        :no
    end
  end

  # Follow a tail call that passes the octet and the accumulator once
  # each, into that callee, and then read the body. A `let` that binds
  # neither is substituted first. Four hops is enough for a fold that
  # names its step; past that the byte loop stays.
  defp follow_step(tm, oct, acc, funs, depth) do
    case peel_lets(tm, oct, acc) do
      :no ->
        :no

      {:ok, {:call, f, args}} ->
        descend_step(f, args, oct, acc, funs, depth)

      {:ok, {:inout, f, args}} ->
        descend_step(f, args, oct, acc, funs, depth)

      {:ok, other} ->
        walk_hot(other, oct, acc, empty_hot(), funs)
    end
  end

  defp descend_step(f, args, oct, acc, funs, depth) do
    with true <- depth < 4,
         %{} = fun <- Map.get(funs, f),
         {:ok, oct2, acc2} <- map_step_params(fun.params, args, oct, acc) do
      follow_step(fun.body, oct2, acc2, funs, depth + 1)
    else
      _ -> walk_hot({:call, f, args}, oct, acc, empty_hot(), funs)
    end
  end

  defp map_step_params(params, args, oct, acc) do
    pairs = Enum.zip(params, args)
    oct_ps = for {p, {:var, ^oct}} <- pairs, do: IR.param_name(p)
    acc_ps = for {p, {:var, ^acc}} <- pairs, do: IR.param_name(p)

    if length(oct_ps) == 1 and length(acc_ps) == 1 and hd(oct_ps) != hd(acc_ps) do
      {:ok, hd(oct_ps), hd(acc_ps)}
    else
      :no
    end
  end

  defp peel_lets({:let, x, _lay, _g, val, body}, oct, acc) do
    if x == oct or x == acc do
      :no
    else
      case peel_lets(body, oct, acc) do
        :no -> :no
        {:ok, inner} -> {:ok, subst_term(inner, x, val)}
      end
    end
  end

  defp peel_lets(tm, _oct, _acc), do: {:ok, tm}

  defp subst_term({:var, x}, x, val), do: val
  defp subst_term({:var, y}, _x, _val), do: {:var, y}

  defp subst_term({:let, z, lay, g, v, b}, x, val) do
    v = subst_term(v, x, val)
    if z == x, do: {:let, z, lay, g, v, b}, else: {:let, z, lay, g, v, subst_term(b, x, val)}
  end

  defp subst_term({:letp, a, b, e, body}, x, val) do
    e = subst_term(e, x, val)

    if x in [a, b],
      do: {:letp, a, b, e, body},
      else: {:letp, a, b, e, subst_term(body, x, val)}
  end

  defp subst_term({:match, scrut, arms}, x, val) when is_list(arms) do
    {:match, subst_term(scrut, x, val), subst_arms(arms, x, val)}
  end

  defp subst_term({:match, scrut, lay, arms}, x, val) when is_list(arms) do
    {:match, subst_term(scrut, x, val), lay, subst_arms(arms, x, val)}
  end

  defp subst_term(t, x, val) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.map(&subst_term(&1, x, val)) |> List.to_tuple()
  end

  defp subst_term(t, x, val) when is_list(t), do: Enum.map(t, &subst_term(&1, x, val))
  defp subst_term(t, _x, _val), do: t

  defp subst_arms(arms, x, val) do
    Enum.map(arms, fn
      {:arm, c, names, tm} = arm ->
        if is_list(names) and x in names, do: arm, else: {:arm, c, names, subst_term(tm, x, val)}

      other ->
        subst_term(other, x, val)
    end)
  end

  defp empty_hot, do: %{eq: nil, neq: MapSet.new(), inset: MapSet.new()}

  # `{:ok, set}` is the bytes a non-identity leaf may see. `:no` means
  # some leaf is reachable with no finite byte, so the fold is not a
  # search for a short set.
  defp walk_hot({:var, name}, _oct, acc, _c, _funs) when name == acc, do: {:ok, MapSet.new()}

  defp walk_hot({:let, x, _lay, _g, val, body}, oct, acc, c, funs) do
    if x == oct or x == acc do
      :no
    else
      walk_hot(subst_term(body, x, val), oct, acc, c, funs)
    end
  end

  defp walk_hot({:match, scrut, arms}, oct, acc, c, funs) when is_list(arms) do
    walk_match_arms(arms, classify(scrut, oct, funs), oct, acc, c, funs)
  end

  defp walk_hot({:match, scrut, _lay, arms}, oct, acc, c, funs) when is_list(arms) do
    walk_hot({:match, scrut, arms}, oct, acc, c, funs)
  end

  defp walk_hot(_tm, _oct, _acc, c, _funs), do: hot_leaf(c)

  defp walk_match_arms(arms, class, oct, acc, c, funs) do
    Enum.reduce_while(arms, {:ok, MapSet.new()}, fn arm, {:ok, accs} ->
      case arm_hot(arm, class, oct, acc, c, funs) do
        :no -> {:halt, :no}
        {:ok, s} -> {:cont, {:ok, MapSet.union(accs, s)}}
      end
    end)
  end

  defp arm_hot({:arm, ctor, binders, body}, class, oct, acc, c, funs) when is_list(binders) do
    if oct in binders or acc in binders do
      :no
    else
      case arm_constraint(class, ctor, c) do
        :dead -> {:ok, MapSet.new()}
        {:ok, c2} -> walk_hot(body, oct, acc, c2, funs)
      end
    end
  end

  defp arm_hot(_, _, _, _, _, _), do: :no

  defp arm_constraint({:bool_eq, k}, "true", c), do: put_eq(c, k)
  defp arm_constraint({:bool_eq, k}, "false", c), do: add_neq(c, k)
  defp arm_constraint({:bool_neq, k}, "true", c), do: add_neq(c, k)
  defp arm_constraint({:bool_neq, k}, "false", c), do: put_eq(c, k)
  defp arm_constraint({:and_byte, k}, "true", c), do: put_eq(c, k)
  defp arm_constraint({:and_byte, _k}, "false", c), do: {:ok, c}
  defp arm_constraint({:byte_in, ks}, "true", c), do: hot_in(c, ks)
  defp arm_constraint({:byte_in, ks}, "false", c), do: add_neq_all(c, ks)
  defp arm_constraint({:wbool_eq, k}, "wtrue", c), do: put_eq(c, k)
  defp arm_constraint({:wbool_eq, k}, "wfalse", c), do: add_neq(c, k)
  defp arm_constraint(_class, _ctor, c), do: {:ok, c}

  defp put_eq(%{eq: eq, neq: neq} = c, k) do
    cond do
      eq == k ->
        {:ok, c}

      eq == nil and not MapSet.member?(neq, k) ->
        {:ok, %{c | eq: k}}

      eq == :in and MapSet.member?(c.inset, k) and not MapSet.member?(neq, k) ->
        {:ok, %{c | eq: k}}

      true ->
        :dead
    end
  end

  defp add_neq(%{eq: k}, k) when is_integer(k), do: :dead

  defp add_neq(%{eq: :in, inset: inset, neq: neq} = c, k) do
    inset = MapSet.delete(inset, k)

    case MapSet.size(inset) do
      0 ->
        :dead

      1 ->
        {:ok, %{c | eq: hd(MapSet.to_list(inset)), inset: MapSet.new(), neq: MapSet.put(neq, k)}}

      _ ->
        {:ok, %{c | inset: inset, neq: MapSet.put(neq, k)}}
    end
  end

  defp add_neq(%{neq: neq} = c, k), do: {:ok, %{c | neq: MapSet.put(neq, k)}}

  defp add_neq_all(c, ks) do
    Enum.reduce_while(ks, {:ok, c}, fn k, {:ok, c} ->
      case add_neq(c, k) do
        :dead -> {:halt, :dead}
        {:ok, c2} -> {:cont, {:ok, c2}}
      end
    end)
  end

  defp hot_in(%{eq: eq, neq: neq, inset: inset} = c, ks) do
    ks = MapSet.difference(ks, neq)

    cond do
      is_integer(eq) and MapSet.member?(ks, eq) ->
        {:ok, c}

      is_integer(eq) ->
        :dead

      eq == :in ->
        both = MapSet.intersection(inset, ks)

        case MapSet.size(both) do
          0 -> :dead
          1 -> {:ok, %{c | eq: hd(MapSet.to_list(both))}}
          _ -> {:ok, %{c | inset: both}}
        end

      MapSet.size(ks) == 0 ->
        :dead

      MapSet.size(ks) == 1 ->
        {:ok, %{c | eq: hd(MapSet.to_list(ks))}}

      true ->
        {:ok, %{c | eq: :in, inset: ks}}
    end
  end

  defp hot_leaf(%{eq: k, neq: neq}) when is_integer(k) do
    if MapSet.member?(neq, k), do: {:ok, MapSet.new()}, else: {:ok, MapSet.new([k])}
  end

  defp hot_leaf(%{eq: :in, inset: inset, neq: neq}) do
    ks = MapSet.difference(inset, neq)
    if MapSet.size(ks) == 0, do: {:ok, MapSet.new()}, else: {:ok, ks}
  end

  defp hot_leaf(_c), do: :no

  # A scrutinee that does not mention the octet constrains the state.
  # Both arms keep the byte constraint they already had. A call the
  # known boolean forms do not match is opened once, when it passes the
  # octet through, so a named test of that octet is still a byte test.
  # Four opens is the limit; a cycle keeps the byte-by-byte loop.
  defp classify(tm, oct, funs), do: classify_at(tm, oct, funs, 0)

  defp classify_at({:let, x, _lay, _g, val, body}, oct, funs, depth) do
    if x == oct, do: :unknown, else: classify_at(subst_term(body, x, val), oct, funs, depth)
  end

  defp classify_at(tm, oct, funs, depth) do
    if uses?(tm, oct), do: classify_byte(tm, oct, funs, depth), else: :state
  end

  defp classify_byte({:call, f, args}, oct, funs, depth) do
    case Map.get(funs, f) do
      %{} = fun ->
        case classify_fun(fun, args, oct, funs, depth) do
          :unknown -> unfold_test(fun, args, oct, funs, depth)
          other -> other
        end

      _ ->
        :unknown
    end
  end

  defp classify_byte({:wrd, :u8, :eq, args}, oct, _funs, _depth) do
    case lit_pair(args, oct) do
      {:ok, k} -> {:wbool_eq, k}
      :no -> :unknown
    end
  end

  defp classify_byte({:match, {:wrd, :u8, :eq, args}, arms}, oct, _funs, _depth) do
    if u8eq_arms?(arms) do
      case lit_pair(args, oct) do
        {:ok, k} -> {:bool_eq, k}
        :no -> :unknown
      end
    else
      :unknown
    end
  end

  defp classify_byte(
         {:match, first,
          [
            {:arm, "true", [], {:con, "Bool", "false", []}},
            {:arm, "false", [], {:con, "Bool", "true", []}}
          ]},
         oct,
         funs,
         depth
       ) do
    classify_not(first, oct, funs, depth)
  end

  defp classify_byte(
         {:match, first,
          [
            {:arm, "true", [], second},
            {:arm, "false", [], {:con, "Bool", "false", []}}
          ]},
         oct,
         funs,
         depth
       ) do
    classify_and(first, second, oct, funs, depth)
  end

  defp classify_byte(
         {:match, first,
          [
            {:arm, "true", [], {:con, "Bool", "true", []}},
            {:arm, "false", [], second}
          ]},
         oct,
         funs,
         depth
       ) do
    classify_or(first, second, oct, funs, depth)
  end

  defp classify_byte(_, _, _, _), do: :unknown

  # Only a callee that takes the octet as exactly one argument, and
  # does not mention it in any other argument, is a test of that octet.
  defp unfold_test(_fun, _args, _oct, _funs, depth) when depth >= 4, do: :unknown

  defp unfold_test(fun, args, oct, funs, depth) do
    case octet_param(fun.params, args, oct) do
      {:ok, pname} -> classify_at(fun.body, pname, funs, depth + 1)
      :no -> :unknown
    end
  end

  defp octet_param(params, args, oct) do
    pairs = Enum.zip(params, args)
    named = for {p, {:var, ^oct}} <- pairs, do: IR.param_name(p)
    others = for {_p, arg} <- pairs, arg != {:var, oct}, do: arg

    if length(named) == 1 and not Enum.any?(others, &uses?(&1, oct)) do
      {:ok, hd(named)}
    else
      :no
    end
  end

  defp classify_fun(fun, args, oct, funs, depth) do
    cond do
      u8eq_fun?(fun) ->
        case lit_pair(args, oct) do
          {:ok, k} -> {:bool_eq, k}
          :no -> :unknown
        end

      and_fun?(fun) and length(args) == 2 ->
        classify_and(Enum.at(args, 0), Enum.at(args, 1), oct, funs, depth)

      or_fun?(fun) and length(args) == 2 ->
        classify_or(Enum.at(args, 0), Enum.at(args, 1), oct, funs, depth)

      not_fun?(fun) and length(args) == 1 ->
        classify_not(hd(args), oct, funs, depth)

      true ->
        :unknown
    end
  end

  defp classify_and(a, b, oct, funs, depth) do
    case {classify_at(a, oct, funs, depth), classify_at(b, oct, funs, depth)} do
      {:state, {:bool_eq, k}} -> {:and_byte, k}
      {{:bool_eq, k}, :state} -> {:and_byte, k}
      {:state, {:wbool_eq, k}} -> {:and_byte, k}
      {{:wbool_eq, k}, :state} -> {:and_byte, k}
      {:state, :state} -> :state
      _ -> :unknown
    end
  end

  defp classify_or(a, b, oct, funs, depth) do
    case {classify_at(a, oct, funs, depth), classify_at(b, oct, funs, depth)} do
      {:state, :state} ->
        :state

      {{:bool_eq, k}, {:bool_eq, m}} ->
        {:byte_in, MapSet.new([k, m])}

      {{:bool_eq, k}, {:byte_in, ks}} ->
        {:byte_in, MapSet.put(ks, k)}

      {{:byte_in, ks}, {:bool_eq, k}} ->
        {:byte_in, MapSet.put(ks, k)}

      {{:byte_in, ks}, {:byte_in, ms}} ->
        {:byte_in, MapSet.union(ks, ms)}

      _ ->
        :unknown
    end
  end

  defp classify_not(a, oct, funs, depth) do
    case classify_at(a, oct, funs, depth) do
      {:bool_eq, k} -> {:bool_neq, k}
      {:wbool_eq, k} -> {:bool_neq, k}
      :state -> :state
      _ -> :unknown
    end
  end

  defp u8eq_fun?(%{
         params: params,
         body: {:match, {:wrd, :u8, :eq, [{:var, a}, {:var, b}]}, arms}
       }) do
    names = Enum.map(params, &IR.param_name/1)
    length(names) == 2 and MapSet.new(names) == MapSet.new([a, b]) and u8eq_arms?(arms)
  end

  defp u8eq_fun?(_), do: false

  defp u8eq_arms?([
         {:arm, "wtrue", [], {:con, "Bool", "true", []}},
         {:arm, "wfalse", [], {:con, "Bool", "false", []}}
       ]),
       do: true

  defp u8eq_arms?(_), do: false

  defp and_fun?(%{
         params: [p, q],
         body:
           {:match, {:var, a},
            [
              {:arm, "true", [], {:var, b}},
              {:arm, "false", [], {:con, "Bool", "false", []}}
            ]}
       }) do
    IR.param_name(p) == a and IR.param_name(q) == b
  end

  defp and_fun?(_), do: false

  defp or_fun?(%{
         params: [p, q],
         body:
           {:match, {:var, a},
            [
              {:arm, "true", [], {:con, "Bool", "true", []}},
              {:arm, "false", [], {:var, b}}
            ]}
       }) do
    IR.param_name(p) == a and IR.param_name(q) == b
  end

  defp or_fun?(_), do: false

  defp not_fun?(%{
         params: [p],
         body:
           {:match, {:var, a},
            [
              {:arm, "true", [], {:con, "Bool", "false", []}},
              {:arm, "false", [], {:con, "Bool", "true", []}}
            ]}
       }) do
    IR.param_name(p) == a
  end

  defp not_fun?(_), do: false

  defp lit_pair([a, b], oct) do
    cond do
      a == {:var, oct} -> u8_lit(b)
      b == {:var, oct} -> u8_lit(a)
      true -> :no
    end
  end

  defp lit_pair(_, _), do: :no

  defp u8_lit({:wrd, :u8, {:lit, :u8, k}, []}) when is_integer(k) and k >= 0 and k <= 255,
    do: {:ok, k}

  defp u8_lit(_), do: :no

  # `f`'s in-place twin on the address of the accumulator, which is the
  # argument in the place of `f`'s `inout` parameter.
  defp io_call(name, args, env, st) do
    with %{inout: target, params: params} <- Map.get(st.funs, name),
         twin when is_binary(twin) <- Map.get(st.io, name),
         i when is_integer(i) <- Enum.find_index(params, &(IR.param_name(&1) == target)),
         {:var, x} <- Enum.at(args, i),
         {c, _lay} <- lookup(env, x),
         {:ok, {pres, exprs, st}} <- emit_args(args, live_ctypes(st, name), env, st) do
      exprs = List.replace_at(exprs, i, "&#{c}")
      {:ok, {squash(pres), "#{twin}(#{Enum.join(exprs, ", ")})", c, st}}
    else
      {:error, _} = err -> err
      _ -> {:error, "c:unsupported"}
    end
  end

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
          {_, a, _} -> stream_ty?(ctype(a, book, ""))
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
  defp data_typedefs(book, prefix) do
    datas = data_defs(book)
    if datas == [], do: "", else: typedefs(datas, book, prefix)
  end

  defp data_bodies(book, prefix) do
    datas =
      book
      |> data_defs()
      |> Enum.reject(&Rep.enum_data?/1)

    if datas == [],
      do: "",
      else: Enum.map_join(order_value_deps(datas, book), "\n", &struct_src(&1, book, prefix))
  end

  # All-nullary types are a complete enum here, before Opt structs, so
  # an `Opt` of that type can store the tag in `val`. Other types stay
  # an incomplete struct typedef; their bodies come later.
  defp typedefs(datas, _book, prefix) do
    Enum.map_join(datas, "\n", fn d ->
      n = struct_name(d.name, prefix)

      if Rep.enum_data?(d) do
        tag_enum_as(d, prefix, n)
      else
        "typedef struct #{n} #{n};"
      end
    end)
  end

  defp word_enum(book, stem, prefix) do
    rows = ctor_words(book, stem, prefix)

    if rows == [] do
      ""
    else
      ty = ctor_word_type(stem, prefix)

      members =
        rows
        |> Enum.with_index()
        |> Enum.map_join(",\n  ", fn {row, i} -> "#{row.word} = #{i}" end)

      """
      typedef enum #{ty} {
        #{members}
      } #{ty};
      """
      |> String.trim()
    end
  end

  defp tag_enum(%{ctors: []}, _prefix), do: ""

  defp tag_enum(d, prefix) do
    tag_enum_as(d, prefix, ctor_tag_type(d.name, prefix))
  end

  defp tag_enum_as(%{ctors: []}, _prefix, _as), do: ""

  defp tag_enum_as(d, prefix, as_name) do
    ty = ctor_tag_type(d.name, prefix)

    members =
      d.ctors
      |> Enum.with_index()
      |> Enum.map_join(",\n  ", fn {ctor, i} ->
        "#{ctor_tag(d.name, ctor.name, prefix)} = #{i}"
      end)

    """
    typedef enum #{ty} {
      #{members}
    } #{as_name};
    """
    |> String.trim()
  end

  defp struct_src(d, book, prefix) do
    name = struct_name(d.name, prefix)
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
          |> Enum.map(fn {{_, a, _}, k} -> "    #{ctype(a, book, prefix)}#{g("f", k)};" end)

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

    body =
      """
      struct #{name} {
        uint8_t #{tagf}; /* #{comment} */
        union {
      #{union_body}
        } #{asf};
      };
      """
      |> String.trim()

    [tag_enum(d, prefix), body]
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n")
  end

  defp data_ctors(book, nm, sigs, prefix) do
    visible = file_scope(nm, MapSet.new(Enum.map(sigs, & &1.name)))

    book
    |> data_defs()
    |> Enum.flat_map(fn d ->
      d.ctors
      |> Enum.with_index()
      |> Enum.map(fn {ctor, tag} -> ctor_fun(d, ctor, tag, book, nm, visible, prefix) end)
    end)
    |> Enum.join("\n\n")
  end

  defp file_scope(nm, extra) do
    Name.open(MapSet.union(nm.taken, extra))
  end

  # A constructor with no runtime fields has one value. Share it, as `tt` does.
  # The object name is generated, so a source spelling cannot be it.
  defp ctor_fun(d, ctor, tag, book, nm, file_scope, prefix) do
    case Rep.kind(Rep.of_data(book, d)) do
      :enum -> enum_ctor(d, ctor, nm, prefix)
      :value -> unboxed_ctor(d, ctor, tag, book, nm, file_scope, prefix)
      :boxed -> boxed_ctor(d, ctor, tag, book, nm, file_scope, prefix)
    end
  end

  defp enum_ctor(d, ctor, nm, prefix) do
    ty = struct_name(d.name, prefix)
    fun = Map.fetch!(nm.ctors, {d.name, ctor.name})
    tag_name = ctor_tag(d.name, ctor.name, prefix)

    """
    __attribute__((unused)) static #{ty} #{fun}(void) { return #{tag_name}; }
    """
    |> String.trim()
  end

  # By value. A compound literal names every field of the active arm, so
  # the return is initialized under -Wall -Wextra.
  defp unboxed_ctor(d, ctor, tag, book, nm, file_scope, prefix) do
    {params, member, fun} = ctor_params(d, ctor, book, nm, file_scope, prefix)
    ty = struct_name(d.name, prefix)
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

  defp boxed_ctor(d, ctor, tag, book, nm, file_scope, prefix) do
    {params, member, fun} = ctor_params(d, ctor, book, nm, file_scope, prefix)
    ptr = struct_ptr(d.name, prefix)
    p = g("p")
    alloc = g("ALLOC")
    tagf = g("field_tag")
    asf = g("as")

    if params == [] do
      obj = g("obj_" <> spell(d.name) <> "_" <> spell(ctor.name))
      unused = g("unused")

      """
      __attribute__((unused)) static #{struct_name(d.name, prefix)} #{obj} = { .#{tagf} = #{tag}, .#{asf} = { .#{unused} = 0 } };

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

  defp ctor_params(d, ctor, book, nm, file_scope, prefix) do
    {pis, _} = telescope(ctor.type)

    fields =
      pis
      |> Enum.reject(fn {q, _, _} -> q == :erased end)
      |> Enum.with_index()
      |> Enum.map(fn {{_, a, x}, k} -> {ctype(a, book, prefix), x, k} end)

    {params, _} =
      Enum.map_reduce(fields, file_scope, fn {ty, x, k}, scope ->
        base = if x == "_", do: g("f", k), else: spell(x)
        {cname, scope} = Name.bind(base, scope)
        {{ty, cname, k}, scope}
      end)

    {params, spell(ctor.name), Map.fetch!(nm.ctors, {d.name, ctor.name})}
  end

  defp enum_scalar_ctype?(ty, st) do
    st.book
    |> data_defs()
    |> Enum.any?(fn d ->
      Rep.enum_data?(d) and struct_name(d.name, st.prefix) == ty
    end)
  end

  # An unboxed struct embedded by value needs a complete type. Bodies
  # of those structs come first. A cycle is left in source order; the
  # checker already refuses a recursive unboxed declaration.
  defp order_value_deps(datas, book), do: order_value_deps(datas, book, [])

  defp order_value_deps([], _book, acc), do: acc

  defp order_value_deps(pending, book, acc) do
    done = MapSet.new(Enum.map(acc, & &1.name))

    {ready, rest} =
      Enum.split_with(pending, fn d ->
        book |> Rep.value_deps(d) |> Enum.all?(&MapSet.member?(done, &1))
      end)

    if ready == [] do
      acc ++ pending
    else
      order_value_deps(rest, book, acc ++ ready)
    end
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
          fields = Rep.live_layouts(book, ctor)
          %{name: ctor.name, tag: tag, fields: fields}
        end)

      %{name: d.name, layout: {:data, d.name}, constructors: ctors}
    end)
  end

  defp nat_spine(0), do: :ze
  defp nat_spine(n) when is_integer(n) and n > 0, do: {:su, nat_spine(n - 1)}
end
