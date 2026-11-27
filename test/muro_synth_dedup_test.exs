defmodule Muro.SynthDedupTest do
  use ExUnit.Case, async: false

  alias Muro.Synth

  # `Muro.check_file/1` and `cegis_loop/2` are heavier than a unit walk,
  # so these stay in this non-async module.

  test "a duplicate stem column stays in the family and otherp reads it" do
    path = "test/fixtures/synth_quant_dup.muro"
    assert {:ok, host} = Muro.Synth.Host.open(path)
    families = family_list(host)
    family = Enum.find(families, &(&1.stem == "has-pos-reward"))
    assert family
    assert family.actions == ["up", "left", "right"]
    col = family.by_action
    feat = fn feature, state -> host.eval_feature.(feature, state) end
    states = host.all_states

    up_bits = Enum.map(states, &feat.(col["up"], &1))
    left_bits = Enum.map(states, &feat.(col["left"], &1))
    right_bits = Enum.map(states, &feat.(col["right"], &1))
    assert up_bits == left_bits
    assert up_bits != right_bits
    assert "has-pos-reward-up" in host.features
    refute "has-pos-reward-left" in host.features

    self_left = {:self, family.stem, "left", col["left"]}
    self_up = {:self, family.stem, "up", col["up"]}
    other_up = {:other, family.stem, "up", for(x <- family.actions, x != "up", do: col[x])}
    other_left = {:other, family.stem, "left", for(x <- family.actions, x != "left", do: col[x])}

    other_right =
      {:other, family.stem, "right", for(x <- family.actions, x != "right", do: col[x])}

    assert Enum.map(states, &Synth.eval(self_left, feat, &1)) == left_bits
    assert Enum.map(states, &Synth.eval(self_up, feat, &1)) == up_bits

    # `otherp` at `up` includes `left`. The two columns agree, so that
    # reading is true wherever `up` itself is true, and also wherever
    # `right` is true.
    other_up_bits = Enum.map(states, &Synth.eval(other_up, feat, &1))
    other_left_bits = Enum.map(states, &Synth.eval(other_left, feat, &1))
    expected_other_up = Enum.zip(left_bits, right_bits) |> Enum.map(fn {l, r} -> l or r end)
    expected_other_left = Enum.zip(up_bits, right_bits) |> Enum.map(fn {u, r} -> u or r end)
    assert other_up_bits == expected_other_up
    assert other_left_bits == expected_other_left
    assert Enum.any?(states, &Synth.eval(other_up, feat, &1))

    assert Enum.map(states, &Synth.eval(other_right, feat, &1)) ==
             Enum.zip(up_bits, left_bits) |> Enum.map(fn {u, l} -> u or l end)

    {:ok, index, _meta} =
      Synth.enumerate_sized(
        host.features,
        2,
        &Synth.signature(&1, states, feat),
        length(states),
        nil,
        families: [family]
      )

    # `selfp left` has the same signature as the earlier `feat` atom.
    # `otherp up` is the first size-1 program that is the disjunction of
    # `left` and `right`.
    self_sig = Synth.signature(self_left, states, feat)
    assert self_sig == Synth.signature({:feat, col["up"]}, states, feat)
    assert {kept_self, 1, _} = Map.fetch!(index, self_sig)
    assert Synth.signature(kept_self, states, feat) == self_sig

    other_sig = Synth.signature(other_up, states, feat)
    assert {kept_other, 1, _} = Map.fetch!(index, other_sig)
    assert kept_other == other_up

    preds = [self_up, self_left, other_up, other_left, other_right]
    {_dir, text} = book = quant_book(host, [self_left, other_up])
    assert text =~ "| left => eval-feature #{col["left"]} car"
    assert text =~ "| up => eval-feature #{col["up"]} car"
    refute text =~ "| left => false"
    assert_book_agrees(book, host, families, preds, feat)
  end

  test "a duplicate-column environment certifies the deployed PredProg" do
    path = "test/fixtures/synth_dup_cert.muro"
    assert {:ok, host} = Muro.Synth.Host.open(path)
    family = Enum.find(family_list(host), &(&1.stem == "has-pos-reward"))
    assert family
    assert "go" in family.actions
    assert "copy" in family.actions
    feat = fn feature, state -> host.eval_feature.(feature, state) end
    states = host.all_states
    col = family.by_action

    assert Enum.map(states, &feat.(col["go"], &1)) ==
             Enum.map(states, &feat.(col["copy"], &1))

    refute "has-pos-reward-copy" in host.features

    self_copy = {:self, family.stem, "copy", col["copy"]}
    other_go = {:other, family.stem, "go", for(x <- family.actions, x != "go", do: col[x])}
    {_dir, text} = book = quant_book(host, [self_copy, other_go])
    assert text =~ "| copy => eval-feature #{col["copy"]} car"
    refute text =~ "| copy => false"
    assert_book_agrees(book, host, [family], [self_copy, other_go], feat)

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.book =~ "def survivor"
    assert result.book =~ "run PredProg"
    assert result.book =~ "def policy "
    assert result.book =~ "match eval survivor"
    refute result.book =~ "find-policy"
    refute result.book =~ "find-ranking"
    refute result.book =~ "placed-find-policy"
  end

  defp family_list(host), do: Muro.Synth.Feature.families(host.feature_specs, host.actions)

  # The policy book up to `policy`, as `Muro.Synth.Book.render/4` wrote
  # it. The certificate after it ranks these arms and is not the subject.
  defp quant_book(host, preds) do
    arms =
      preds
      |> Enum.with_index()
      |> Enum.map(fn {pred, i} ->
        %{
          name: "survivor-#{i}",
          pred: pred,
          action: hd(host.actions),
          else: hd(host.actions),
          observations: []
        }
      end)

    dir = tmp_quant_dir()
    assert {:ok, src, _meta} = Muro.Synth.Book.render(host, arms, dir, "trace")
    [head, _rest] = String.split(src, "\ndef policy ", parts: 2)
    assert head =~ "def stem-at "
    assert head =~ "def other-at "
    assert head =~ "data Stem : Type where"
    {dir, head}
  end

  defp assert_book_agrees({dir, head}, host, families, preds, feat) do
    stems =
      for family <- families, action <- host.actions, state <- host.all_states do
        expected = action in family.actions and feat.(family.by_action[action], state)
        others = for a <- family.actions, a != action, do: family.by_action[a]
        other_expected = Enum.any?(others, &feat.(&1, state))

        [
          "{stem-at #{family.stem} #{action} #{state} ≡ #{expected} : Bool}",
          "{other-at #{family.stem} #{action} #{state} ≡ #{other_expected} : Bool}"
        ]
      end

    evals =
      for pred <- preds, state <- host.all_states do
        "{eval #{Synth.render(pred)} #{state} ≡ #{Synth.eval(pred, feat, state)} : Bool}"
      end

    claims =
      (List.flatten(stems) ++ evals)
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {claim, i} -> "def agree-#{i} : evidence #{claim} := refl" end)

    path = Path.join(dir, "agree.muro")
    File.write!(path, head <> "\n" <> claims <> "\n")
    assert Muro.check_file(path) == :ok
  end

  defp tmp_quant_dir do
    dir =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_quant_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}"
      )

    File.rm_rf!(dir)
    File.mkdir_p!(dir)
    dir
  end
end
