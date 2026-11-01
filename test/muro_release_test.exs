defmodule Muro.ReleaseTest do
  use ExUnit.Case, async: true

  test "the executable release loads the http applications and wraps a prod build" do
    text = File.read!("mix.exs")
    assert text =~ "extra_applications: [:logger]"

    for app <- ~w(mix asn1 crypto public_key ssl inets) do
      assert text =~ ~r/#{app}:\s*:load/, "the release does not load :#{app}"
    end

    refute text =~ "{:ssl"
    refute text =~ "{:inets"
    refute text =~ "{:public_key"
    refute text =~ "{:crypto"
    refute text =~ "{:asn1"
    assert text =~ ~s(if debug?, do: "0", else: "1")
    assert text =~ "&mark_muro_release/1"
  end

  test "the muro release marker is written into sys.config and leaves other apps" do
    dir = Path.join(System.tmp_dir!(), "muro_release_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, "sys.config")

    File.write!(path, """
    %% coding: utf-8
    %% RUNTIME_CONFIG=false
    [{logger, [{level, info}]}].
    """)

    assert Muro.Application.write_release_marker(path) == :ok
    {:ok, [config]} = :file.consult(String.to_charlist(path))
    assert config[:muro][:release_cli] == true
    assert config[:logger][:level] == :info

    written = File.read!(path)
    assert written =~ "%% coding: utf-8\n"
    assert written =~ "%% RUNTIME_CONFIG=false\n"

    assert Muro.Application.write_release_marker(path) == :ok
    {:ok, [again]} = :file.consult(String.to_charlist(path))
    assert again == config
  end

  test "the release smoke shell reaches the container intact" do
    scripts =
      run_scripts(".github/workflows/release.yml") ++ run_scripts(".github/workflows/ci.yml")

    refute scripts == []

    dir = tmp()

    for {script, i} <- Enum.with_index(scripts) do
      path = Path.join(dir, "run-#{i}.sh")
      File.write!(path, script)
      {out, status} = System.cmd("bash", ["-n", path], stderr_to_stdout: true)
      assert status == 0, out
    end

    smoke = Enum.find(scripts, &String.contains?(&1, "release-std-smoke.sh"))
    assert smoke =~ "bash /release-std-smoke.sh /tmp/muro"
    assert smoke =~ "muro emit /tmp/one.muro --backend rust"
    refute smoke =~ "bash -c"

    stub_dir = Path.join(dir, "bin")
    File.mkdir_p!(stub_dir)
    captured = Path.join(dir, "container.sh")

    File.write!(Path.join(stub_dir, "docker"), """
    #!/bin/bash
    cat > #{captured}
    """)

    File.chmod!(Path.join(stub_dir, "docker"), 0o755)
    dist = Path.join(dir, "dist")
    File.mkdir_p!(dist)
    File.write!(Path.join(dist, "muro-0.20.3-linux-x86_64"), "bin")
    host = Path.join(dir, "smoke.sh")
    File.write!(host, smoke)

    {out, status} =
      System.cmd("bash", [host],
        cd: dir,
        stderr_to_stdout: true,
        env: [{"PATH", stub_dir <> ":" <> System.get_env("PATH")}]
      )

    assert status == 0, out
    body = File.read!(captured)
    assert body =~ "bash /release-std-smoke.sh /tmp/muro"
    assert body =~ "test -f /tmp/one.rs"
    assert body =~ "the smoke container has Elixir or Erlang"
    refute body =~ "import \"std:bool.muro\"'"
  end

  test "the release std smoke accepts the library book and fails when it is broken" do
    script = Path.expand("scripts/release-std-smoke.sh")
    dir = tmp()
    shim = checker_shim(dir)

    {out, 0} = System.cmd("bash", [script, shim], stderr_to_stdout: true)
    assert out =~ "All terms check. Evidence never becomes a run."

    broken = Path.join(dir, "broken.muro")

    File.write!(broken, """
    import "std:bool.muro"
    def n : run Bool := 0
    """)

    {bad_out, bad_status} =
      System.cmd("bash", [script, shim, "--book", broken], stderr_to_stdout: true)

    assert bad_status != 0
    refute bad_out =~ "All terms check. Evidence never becomes a run."

    missing = Path.join(dir, "no-such-use-std.muro")

    {missing_out, missing_status} =
      System.cmd("bash", [script, shim, "--book", missing], stderr_to_stdout: true)

    assert missing_status != 0
    assert missing_out =~ "std smoke book is missing"

    liar = Path.join(dir, "liar")

    File.write!(liar, """
    #!/bin/bash
    echo checked
    exit 0
    """)

    File.chmod!(liar, 0o755)
    {liar_out, liar_status} = System.cmd("bash", [script, liar], stderr_to_stdout: true)
    assert liar_status != 0
    assert liar_out =~ "std smoke did not accept use_std.muro"
  end

  defp checker_shim(dir) do
    path = Path.join(dir, "muro")
    ebin = ebin_args()

    File.write!(path, """
    #!/bin/bash
    set -euo pipefail
    if [ "${1:-}" != "check" ]; then
      echo "shim expected check" >&2
      exit 2
    fi
    shift
    exec elixir #{ebin} -e '
      book = System.argv() |> List.first()
      :application.load(:muro)
      vsn = :muro |> Application.spec(:vsn) |> to_string()
      case Muro.check_file(book) do
        :ok ->
          IO.write("Muro v" <> vsn <> "\\nAll terms check. Evidence never becomes a run.\\n")
        {:error, msg} ->
          IO.write(:stderr, msg)
          System.halt(1)
      end
    ' -- "$@"
    """)

    File.chmod!(path, 0o755)
    path
  end

  defp ebin_args do
    "_build/test/lib/*/ebin"
    |> Path.wildcard()
    |> Enum.map_join(" ", fn ebin -> "-pa #{Path.expand(ebin)}" end)
  end

  defp run_scripts(path) do
    lines = path |> File.read!() |> String.split("\n")
    {scripts, buf, base} = collect_runs(lines, [], nil, nil)

    scripts =
      case {buf, base} do
        {nil, _} -> scripts
        {lines, base} -> [strip_block(Enum.reverse(lines), base) | scripts]
      end

    Enum.reverse(scripts)
  end

  defp collect_runs([], scripts, buf, base), do: {scripts, buf, base}

  defp collect_runs([line | rest], scripts, nil, nil) do
    case Regex.run(~r/^(\s*)run: \|[[:space:]]*$/, line) do
      [_, indent] -> collect_runs(rest, scripts, [], String.length(indent))
      _ -> collect_runs(rest, scripts, nil, nil)
    end
  end

  defp collect_runs(["" | rest], scripts, buf, base) do
    collect_runs(rest, scripts, ["" | buf], base)
  end

  defp collect_runs([line | rest], scripts, buf, base) do
    indent = line |> String.replace(~r/\S.*/, "") |> String.length()

    if indent > base do
      collect_runs(rest, scripts, [line | buf], base)
    else
      collect_runs([line | rest], [strip_block(Enum.reverse(buf), base) | scripts], nil, nil)
    end
  end

  defp strip_block(lines, base) do
    body = Enum.reject(lines, &(&1 == ""))
    cut = body |> Enum.map(&leading_spaces/1) |> Enum.min(fn -> base + 1 end)

    lines
    |> Enum.map(fn
      "" -> ""
      line -> String.slice(line, cut, String.length(line) - cut)
    end)
    |> Enum.join("\n")
    |> Kernel.<>("\n")
  end

  defp leading_spaces(line), do: line |> String.replace(~r/\S.*/, "") |> String.length()

  defp tmp do
    dir = Path.join(System.tmp_dir!(), "muro_release_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end
