defmodule Muro.CLI.Fill do
  @moduledoc false

  @doc false
  def switches, do: Enum.map(options(), &{&1.name, &1.type})

  @doc false
  def options do
    [
      %{
        name: :def,
        type: :string,
        value: "NAME",
        default: "required",
        doc:
          "The definition whose body is ?. Exactly one definition of that name, and the body is the hole."
      },
      %{
        name: :bound,
        type: :integer,
        value: "N",
        default: Integer.to_string(Muro.Fill.default_bound()),
        doc:
          "Largest size the search tries. Size counts each variable, constructor, application, lambda, and match. A match motive is fixed by the goal and is not counted. Past this bound the file is left unchanged."
      },
      %{
        name: :fuel,
        type: :integer,
        value: "N",
        default: Integer.to_string(Muro.Check.default_fuel()),
        doc:
          "The checker's fuel for each candidate. out of fuel is not acceptance and it is not a type error."
      }
    ]
  end

  @doc false
  def help do
    Muro.CLI.Text.page([
      Muro.CLI.Text.prose("""
      muro fill writes a body for one definition. The definition starts as ?. The search tries terms in order of size: variables in scope, constructors, applications of other names and of functions in scope, and a match on a binder. It does not call the definition being filled. The checker decides. A run is kept only when the book's closed equations about that name still check. Evidence is kept when the type checks. A spec is kept the same way. The written text is checked again, then a rename in the same directory puts it in place. This is a search. It is not muro synth, and it certifies nothing beyond the checker.
      """),
      Muro.CLI.Text.section(
        "USAGE",
        Muro.CLI.Text.pre([
          "muro fill path.muro --def NAME [--bound N] [--fuel N]"
        ])
      ),
      Muro.CLI.Text.section(
        "ARGUMENTS",
        Muro.CLI.Text.arguments([
          {"path.muro", "Required. One book. The named definition's body is ?."}
        ])
      ),
      Muro.CLI.Text.section("OPTIONS", Muro.CLI.Text.options(options())),
      Muro.CLI.Text.section(
        "EXAMPLES",
        Muro.CLI.Text.examples([
          {"muro fill book.muro --def add1", "Write a body for add1."},
          {"muro fill book.muro --def add1 --bound 8", "Stop at size 8."}
        ])
      ),
      Muro.CLI.Text.section(
        "EXIT CODES",
        Muro.CLI.Text.exits([
          {"0", "A body was written and the book checks."},
          {"1",
           "The bound was reached, the body is not ?, the name is missing or repeated, the file has an import or param, the book has another hole, or a flag is not usable. The file is unchanged when the bound is reached."}
        ])
      ),
      Muro.CLI.Text.section(
        "LEARN MORE",
        Muro.CLI.Text.pre(["https://muro-lang.dev/docs/fill"])
      )
    ])
  end

  @doc false
  def run(args) when is_list(args) do
    {opts, paths, invalid} = OptionParser.parse(args, strict: switches())
    bound = Keyword.get(opts, :bound, Muro.Fill.default_bound())
    fuel = Keyword.get(opts, :fuel, Muro.Check.default_fuel())

    cond do
      invalid != [] ->
        {:raise, "", "unknown option: #{inspect(invalid)}"}

      length(paths) != 1 ->
        {:raise, "", "expected one path"}

      not is_binary(Keyword.get(opts, :def)) ->
        {:raise, "", "missing --def"}

      not (is_integer(bound) and bound >= 1) ->
        {:raise, "", "--bound must be a positive integer"}

      not (is_integer(fuel) and fuel >= 1) ->
        {:raise, "", "--fuel must be a positive integer"}

      true ->
        go(hd(paths), opts, bound, fuel)
    end
  end

  defp go(path, opts, bound, fuel) do
    case Muro.Fill.fill(path, name: opts[:def], bound: bound, fuel: fuel) do
      {:ok, %{name: name}} ->
        {:ok, "filled #{name}\n", ""}

      {:error, {:bound, info}} ->
        {:raise, "", Muro.Fill.bound_message(info)}

      {:error, message} when is_binary(message) ->
        {:raise, "", message}
    end
  end
end
