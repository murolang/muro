defmodule Muro.CLI.Synth do
  @moduledoc false

  @oracles ["trace", "successor", "coind-homo"]

  @doc false
  def switches, do: Enum.map(options(), &{&1.name, &1.type})

  @doc false
  def options do
    fuel = Integer.to_string(Muro.Check.default_fuel())
    depth = Integer.to_string(Muro.Synth.Loop.default_depth())

    [
      %{
        name: :on,
        type: :string,
        value: "NAME",
        default: "traces, when the book defines step",
        doc:
          "The procedure. traces searches the version space of predicate programs on the book's step and the observations that step supports. A book that defines step selects traces when this flag is omitted. A book with no step has no observations to synthesize against. The command refuses it, and the message does not name a flag. The only accepted value is traces. An unknown value is refused, and the message lists the accepted values.",
        lines: Muro.Synth.Procedure.accepted()
      },
      %{
        name: :oracle,
        type: :string,
        value: "NAME",
        default: "trace",
        doc:
          "Where the labels come from. trace reads Finder traces. successor reads successor values. coind-homo reads action values. A pair the oracle cannot order is reported, not ranked.",
        lines: @oracles
      },
      %{
        name: :depth,
        type: :integer,
        value: "N",
        default: depth,
        doc:
          "Initial predicate depth. An empty version space is searched one depth further. The fuel and the round cap stop a search that is not shrinking. They are not a cover theorem."
      },
      %{
        name: :out,
        type: :string,
        value: "out.muro",
        default: "omitted. The book is printed on standard output",
        doc:
          "Write the policy book to this path. The path must not already exist, including a path that appears before the write. A write that fails removes the partial file. Without it, the book is printed and nothing is written. That book's environment import is relative to the current directory."
      },
      %{
        name: :fuel,
        type: :integer,
        value: "N",
        default: fuel,
        doc:
          "The checker's fuel for the environment and for the policy book. out of fuel is not acceptance."
      },
      %{
        name: :json,
        type: :boolean,
        default: "false",
        doc:
          "Print the report as one JSON object on standard error. The object is a log of the version space and the counterexamples. A sized search records considered, distinct, truncated, sizes, and size whether it checks or stops. considered is the programs counted. distinct is the signatures. truncated is a subset skipped for the binomial budget. sizes lists each size that added a signature. size is the last size that counted a program, or 0 when none was counted. It is how far enumeration went, not the size of the survivor. A stop at the considered budget or the memory budget also names that stop. It is not a certificate."
      }
    ]
  end

  @doc false
  def help do
    Muro.CLI.Text.page([
      Muro.CLI.Text.prose("""
      muro synth reads one checked environment and searches a version space of predicate programs. The search calls that book's emitted step. A program that misses an observation is dropped. The smallest program that matches every observation is the policy the result book deploys, and eval runs it. A score does not decide who survives. The checker sees that policy and, when the environment defines it, the homomorphism of the ranking that reads the policy. It does not see the search. Exit 0 is that checked homomorphism.
      """),
      Muro.CLI.Text.prose("""
      --on names the procedure. traces is the version-space search. It is the only accepted value. A book that defines step selects traces when --on is omitted. The observations are the ones that step supports. A book with no step has no observations to synthesize against. The command refuses it, and the message does not name a flag. An unknown value is refused, and the message lists the accepted values.
      """),
      Muro.CLI.Text.section(
        "USAGE",
        Muro.CLI.Text.pre([
          "muro synth path.muro [--on NAME] [--oracle NAME] [--depth N]",
          "    [--out out.muro] [--fuel N] [--json]"
        ])
      ),
      Muro.CLI.Text.section(
        "ARGUMENTS",
        Muro.CLI.Text.arguments([
          {"path.muro", "Required. A checked environment. Exactly one path."}
        ])
      ),
      Muro.CLI.Text.section("OPTIONS", Muro.CLI.Text.options(options())),
      Muro.CLI.Text.section(
        "EXAMPLES",
        Muro.CLI.Text.examples([
          {"muro synth book.muro",
           "Exits 2. A book with no step has nothing to synthesize against."}
        ])
      ),
      Muro.CLI.Text.section(
        "EXIT CODES",
        Muro.CLI.Text.exits([
          {"0",
           "The policy book checks and contains the homomorphism for the synthesized ranking, on the step the search called."},
          {"1",
           "The report names an empty space, a counterexample, a homomorphism that is not derivable, a silent oracle, features that cannot separate two carriers, or a policy whose environment does not define the homomorphism."},
          {"2",
           "The book does not check, it is not an environment, it has no step and no observations to synthesize against, --on is not an accepted value, the oracle name is unknown, --out already exists, or a policy book or a temporary book cannot be written."}
        ])
      ),
      Muro.CLI.Text.section(
        "LEARN MORE",
        Muro.CLI.Text.pre(["https://muro-lang.dev/docs/synth"])
      )
    ])
  end

  @doc false
  def run(args, hooks \\ []) when is_list(args) and is_list(hooks) do
    {opts, paths, invalid} = OptionParser.parse(args, strict: switches())

    cond do
      invalid != [] ->
        {:raise, "", "unknown option: #{inspect(invalid)}"}

      length(paths) != 1 ->
        {:raise, "", "expected one path"}

      Keyword.get(opts, :fuel, Muro.Check.default_fuel()) <= 0 ->
        {:raise, "", "--fuel must be a positive integer"}

      depth_negative?(Keyword.get(opts, :depth)) ->
        {:raise, "", "--depth must be a non-negative integer"}

      true ->
        go(hd(paths), opts, hooks)
    end
  end

  defp depth_negative?(value) when is_integer(value), do: value < 0
  defp depth_negative?(_value), do: false

  defp go(path, opts, hooks) do
    out = Keyword.get(opts, :out)
    on = Keyword.get(opts, :on)
    oracle = Keyword.get(opts, :oracle, "trace")
    depth = Keyword.get(opts, :depth, Muro.Synth.Loop.default_depth())
    fuel = Keyword.get(opts, :fuel, Muro.Check.default_fuel())

    cond do
      not accepted_on?(on) ->
        {:exit, 2, "", [Muro.Synth.Procedure.unknown_on(on)]}

      oracle not in @oracles ->
        {:exit, 2, "", ["unknown oracle #{oracle}"]}

      is_binary(out) and File.exists?(out) ->
        {:exit, 2, "", ["#{out} already exists"]}

      true ->
        case Muro.Synth.Procedure.select(path, fuel) do
          {:error, :book, message} ->
            {:exit, 2, "", [message, "refusing to synthesize from a book that does not check"]}

          {:error, :usage, message} ->
            {:exit, 2, "", [message]}

          {:ok, Muro.Synth.Procedure.Traces} ->
            search(path, out, oracle, depth, fuel, opts, hooks)
        end
    end
  end

  defp accepted_on?(nil), do: true
  defp accepted_on?(name) when is_binary(name), do: name in Muro.Synth.Procedure.accepted()

  defp search(path, out, oracle, depth, fuel, opts, hooks) do
    # Printed on standard output, the book is saved in the current
    # directory, so the import is relative to that directory. `--out`
    # is relative to the file that was written.
    anchor =
      if is_binary(out),
        do: Path.dirname(Path.expand(out)),
        else: File.cwd!()

    case Muro.Synth.Procedure.Traces.run(path, loop_opts(oracle, depth, fuel, anchor, hooks)) do
      {:error, :book, message} ->
        {:exit, 2, "", [message, "refusing to synthesize from a book that does not check"]}

      {:error, :usage, message} ->
        {:exit, 2, "", [message]}

      {:error, :storage, message} ->
        {:exit, 2, "", [message]}

      {:ok, result} ->
        present(result, out, Keyword.get(opts, :json, false), hooks)
    end
  end

  # `hooks` may carry `:considered_budget` and `:memory_budget`. The
  # command does not read those bounds from the application environment.
  # Omitted, the search uses its defaults.
  defp loop_opts(oracle, depth, fuel, anchor, hooks) do
    [oracle: oracle, depth: depth, fuel: fuel, anchor: anchor]
    |> put_hook(:considered_budget, hooks)
    |> put_hook(:memory_budget, hooks)
  end

  defp put_hook(opts, key, hooks) do
    case Keyword.fetch(hooks, key) do
      {:ok, value} -> Keyword.put(opts, key, value)
      :error -> opts
    end
  end

  defp present(result, out, json, hooks) do
    report = if json, do: [json(result)], else: result.lines
    book = result.book || ""

    written = result.status in [:policy, :certified]

    cond do
      written and is_binary(out) ->
        case write_new(out, book, hooks) do
          :ok ->
            {:exit, exit_code(result.status), "", report}

          {:error, :eexist} ->
            {:exit, 2, "", ["#{out} already exists"]}

          {:error, reason} ->
            {:exit, 2, "", ["#{out}: #{inspect(reason)}"]}
        end

      written ->
        {:exit, exit_code(result.status), book, report}

      true ->
        {:exit, 1, "", report}
    end
  end

  defp exit_code(:certified), do: 0
  defp exit_code(_status), do: 1

  # The existence check runs before the search. The open is the guarantee:
  # a path created after that check is the same refusal, and it is not
  # truncated. `before_write` lets a test create the path in between.
  defp write_new(path, contents, hooks) do
    File.mkdir_p!(Path.dirname(path))

    case Keyword.get(hooks, :before_write) do
      fun when is_function(fun, 1) -> fun.(path)
      _ -> :ok
    end

    case File.open(path, [:write, :exclusive]) do
      {:ok, io} ->
        # The policy book is UTF-8. `IO.write` would refuse Π and λ.
        # A failed write or close removes the partial file. A retry is
        # not then refused because the path already exists.
        Muro.Synth.Book.write_bytes(path, io, contents, hooks)

      {:error, reason} ->
        {:error, reason}
    end
  end

  # Present on a sized search that checks and on a stop. `size` is the
  # last size that counted a program, or 0 when none was counted. It is
  # enumeration progress, not the survivor's size. `considered` is
  # programs counted. `distinct` is signatures. `truncated` is whether
  # a subset was skipped for the binomial budget. `sizes` is each size
  # that added a signature, with that count.
  defp json(result) do
    payload =
      %{
        status: result.status,
        program: program_json(result.program),
        versions: result.versions,
        cex: Enum.map(result.cex, &cex_json/1),
        note: note(result.status),
        certificate: Map.get(result, :certificate)
      }
      |> put_present(:features, Map.get(result, :features))
      |> put_present(:kinds, Map.get(result, :kinds))
      |> put_present(:path_depth, Map.get(result, :path_depth))
      |> put_present(:path_bound, Map.get(result, :path_bound))
      |> put_present(:sizes, Map.get(result, :sizes))
      |> put_present(:enum_ms, Map.get(result, :enum_ms))
      |> put_present(:considered, Map.get(result, :considered))
      |> put_present(:distinct, Map.get(result, :distinct))
      |> put_present(:truncated, Map.get(result, :truncated))
      |> put_present(:size, Map.get(result, :size))
      |> put_present(:stop, Map.get(result, :stop))

    JSON.encode!(payload) <> "\n"
  end

  defp put_present(map, _key, nil), do: map
  defp put_present(map, key, value), do: Map.put(map, key, value)

  defp program_json(nil), do: nil

  defp program_json(programs) when is_list(programs),
    do: Enum.map(programs, &Muro.Synth.render/1)

  defp program_json(program), do: Muro.Synth.render(program)

  defp cex_json(cex) do
    %{
      carrier: Muro.Synth.Term.spell(Map.get(cex, :carrier)),
      predicted: Map.get(cex, :predicted),
      oracle: Map.get(cex, :oracle),
      fed: Map.get(cex, :fed),
      pair: pair_json(Map.get(cex, :pair)),
      agrees: Muro.Synth.Term.spell(Map.get(cex, :agrees)),
      reason: Map.get(cex, :reason)
    }
  end

  defp pair_json({action, other}), do: [action, other]
  defp pair_json(_pair), do: nil

  defp note(:certified), do: "homomorphism checked"
  defp note(:policy), do: "homomorphism is not derivable"
  defp note(:insufficient), do: "features cannot separate the counterexample"
  defp note(:empty), do: "no predicate matches the observations"
  defp note(_status), do: nil
end
