defmodule Muro.Environments.Lam do
  @moduledoc """
  The λ-substitution problem as an environment.

  The state is a term. `step/2` performs one action and returns the next
  term with reward `-1`. The episode ends when the head has stopped.
  `:spine` and `:arg` are the actions `step/2` accepts. The agent does
  not read those names off the term. `observe/1` is what it reads.
  """

  alias Muro.{Ast, Parser}
  alias Muro.Reducers.Lam

  @episodes ~w(affine discard copy_discard copy_ready copy2 copy4 copy8)

  @doc """
  The actions `step/2` accepts. `:spine` is the default.
  """
  def actions, do: [:spine, :arg]

  def default, do: :spine

  @doc """
  The head has stopped, so the episode ends.
  """
  def stop?(term), do: Lam.stopped?(term)

  @doc """
  Perform `action`. `{:ok, next, -1}` is one substitution. `:error` is
  an action this state does not offer.
  """
  def step(term, action) when action in [:spine, :arg] do
    case Lam.act(term, action) do
      {:ok, next} -> {:ok, next, -1}
      :error -> :error
    end
  end

  @doc """
  Readings of the application on the function spine.

  `mark` is `affine`, `reuse`, `erased`, or `absent`. `uses` is how
  many times the binder occurs in the body. `arg_head` is the
  constructor of the argument. `arg_apps` is how many λ applications
  sit in the argument. `arg_size` is how many nodes it has.
  """
  def observe(term) do
    case Lam.head_app(term) do
      {:ok, _path, {:app, {:lam, qty, _, _, body}, arg}} ->
        %{
          mark: mark(qty),
          uses: uses(0, body),
          arg_head: head_tag(arg),
          arg_apps: apps(arg),
          arg_size: nodes(arg)
        }

      :error ->
        %{mark: :absent, uses: 0, arg_head: :missing, arg_apps: 0, arg_size: 0}
    end
  end

  @doc """
  Starting states from `examples/lam_uses.muro`. Each name used in a
  body is replaced by that definition's body, so a state is a term.
  """
  def episodes do
    src = File.read!("examples/lam_uses.muro")
    {:ok, book} = Parser.parse(src)

    defs =
      Map.new(book, fn defn ->
        {:ok, body} = Ast.to_db(defn.body)
        {defn.name, body}
      end)

    Map.new(@episodes, fn name -> {name, inline(Map.fetch!(defs, name), defs)} end)
  end

  @doc """
  A book whose `policy` is `chain` over the raw readings. `features` is
  the library the search was allowed to apply. Numeric functions are
  `eq0`, `gt0`, `gt1`, and `square` then `gt1`. A tag test is one
  `{:is, field, tag}` from `features`.
  """
  def book(chain, features) when is_list(chain) and is_list(features) do
    tag_defs = features |> Enum.filter(&match?({:is, _, _}, &1)) |> Enum.map(&tag_def/1)

    """
    data Bool : Type where
      true : Bool
      false : Bool

    data Mark : Type where
      affine : Mark
      reuse : Mark
      erased : Mark
      absent : Mark

    data Head : Type where
      missing : Head
      variable : Head
      fun : Head
      call : Head
      zero : Head
      successor : Head
      other : Head

    data Action : Type where
      spine : Action
      arg : Action

    def eq0 : run Π (n : Nat) → Bool :=
      λ (n : Nat) →
        match n motive (λ _ → Bool)
          | 0 => true
          | suc _ => false

    def gt0 : run Π (n : Nat) → Bool :=
      λ (n : Nat) →
        match n motive (λ _ → Bool)
          | 0 => false
          | suc _ => true

    def gt1 : run Π (n : Nat) → Bool :=
      λ (n : Nat) →
        match n motive (λ _ → Bool)
          | 0 => false
          | suc k => gt0 k

    def times : run Π (n : Nat) → Π (+ m : Nat) → Nat :=
      λ (n : Nat) → λ (+ m : Nat) →
        match n motive (λ _ → Nat)
          | 0 => 0
          | suc p => plus m (times p m)

    def square : run Π (+ n : Nat) → Nat :=
      λ (+ n : Nat) → times n n

    def square-gt1 : run Π (+ n : Nat) → Bool :=
      λ (+ n : Nat) → gt1 (square n)

    #{Enum.join(tag_defs, "\n\n")}

    def policy : run Π (+ mark : Mark) → Π (+ uses : Nat) → Π (+ arg-apps : Nat) → Π (+ arg-size : Nat) → Π (+ arg-head : Head) → Action :=
      λ (+ mark : Mark) → λ (+ uses : Nat) → λ (+ arg-apps : Nat) → λ (+ arg-size : Nat) → λ (+ arg-head : Head) →
        #{chain_term(chain)}
    """
  end

  defp mark(:affine), do: :affine
  defp mark(:reuse), do: :reuse
  defp mark(:erased), do: :erased
  defp mark(_), do: :absent

  defp head_tag({:lam, _, _, _, _}), do: :fun
  defp head_tag({:app, _, _}), do: :call
  defp head_tag({:var, _}), do: :variable
  defp head_tag(:ze), do: :zero
  defp head_tag({:su, _}), do: :successor
  defp head_tag(_), do: :other

  defp uses(i, {:var, j}), do: if(i == j, do: 1, else: 0)
  defp uses(i, {:lam, _, a, _, b}), do: uses(i, a) + uses(i + 1, b)
  defp uses(i, {:pi, _, a, _, b}), do: uses(i, a) + uses(i + 1, b)
  defp uses(i, {:app, f, a}), do: uses(i, f) + uses(i, a)
  defp uses(i, {:su, t}), do: uses(i, t)
  defp uses(_, _), do: 0

  defp apps({:app, f, a}) do
    here = if match?({:lam, _, _, _, _}, f), do: 1, else: 0
    here + apps(f) + apps(a)
  end

  defp apps({:lam, _, a, _, b}), do: apps(a) + apps(b)
  defp apps({:pi, _, a, _, b}), do: apps(a) + apps(b)
  defp apps({:su, t}), do: apps(t)
  defp apps(_), do: 0

  defp nodes({:app, f, a}), do: 1 + nodes(f) + nodes(a)
  defp nodes({:lam, _, a, _, b}), do: 1 + nodes(a) + nodes(b)
  defp nodes({:pi, _, a, _, b}), do: 1 + nodes(a) + nodes(b)
  defp nodes({:su, t}), do: 1 + nodes(t)
  defp nodes(_), do: 1

  defp inline({:def, name}, defs), do: inline(Map.fetch!(defs, name), defs)
  defp inline({:app, f, a}, defs), do: {:app, inline(f, defs), inline(a, defs)}
  defp inline({:lam, q, a, x, b}, defs), do: {:lam, q, inline(a, defs), x, inline(b, defs)}
  defp inline({:pi, q, a, x, b}, defs), do: {:pi, q, inline(a, defs), x, inline(b, defs)}
  defp inline({:su, t}, defs), do: {:su, inline(t, defs)}
  defp inline(other, _defs), do: other

  defp tag_def({:is, :mark, tag}) do
    arms =
      [:affine, :reuse, :erased, :absent]
      |> Enum.map_join("\n", fn ctor ->
        "      | #{ctor} => #{if ctor == tag, do: "true", else: "false"}"
      end)

    """
    def mark-#{tag} : run Π (m : Mark) → Bool :=
      λ (m : Mark) →
        match m motive (λ _ → Bool)
    #{arms}
    """
  end

  defp tag_def({:is, :arg_head, tag}) do
    arms =
      [:missing, :variable, :fun, :call, :zero, :successor, :other]
      |> Enum.map_join("\n", fn ctor ->
        "      | #{ctor} => #{if ctor == tag, do: "true", else: "false"}"
      end)

    """
    def head-#{tag} : run Π (h : Head) → Bool :=
      λ (h : Head) →
        match h motive (λ _ → Bool)
    #{arms}
    """
  end

  defp chain_term([]), do: "spine"

  defp chain_term([{pred, action} | rest]) do
    "(match #{bool_term(pred)} motive (λ _ → Action) | true => #{action} | false => #{chain_term(rest)})"
  end

  defp bool_term({:feat, feature}), do: "(#{spell(feature)})"
  defp bool_term({:not, pred}), do: "(match #{bool_term(pred)} motive (λ _ → Bool) | true => false | false => true)"

  defp bool_term({:and, p, q}) do
    "(match #{bool_term(p)} motive (λ _ → Bool) | true => #{bool_term(q)} | false => false)"
  end

  defp bool_term({:or, p, q}) do
    "(match #{bool_term(p)} motive (λ _ → Bool) | true => true | false => #{bool_term(q)})"
  end

  defp spell({:eq0, field}), do: "eq0 #{field_name(field)}"
  defp spell({:gt0, field}), do: "gt0 #{field_name(field)}"
  defp spell({:gt1, field}), do: "gt1 #{field_name(field)}"
  defp spell({:square_gt1, field}), do: "square-gt1 #{field_name(field)}"
  defp spell({:is, :mark, tag}), do: "mark-#{tag} mark"
  defp spell({:is, :arg_head, tag}), do: "head-#{tag} arg-head"

  defp field_name(:uses), do: "uses"
  defp field_name(:arg_apps), do: "arg-apps"
  defp field_name(:arg_size), do: "arg-size"
end
