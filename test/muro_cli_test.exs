defmodule Muro.CliTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  test "muro --version matches mix muro --version" do
    assert_same(fn -> Mix.Tasks.Muro.run(["--version"]) end, ["--version"])
    assert_same(fn -> Mix.Tasks.Muro.run(["-v"]) end, ["-v"])
  end

  test "muro with no arguments names the binary commands" do
    version = Mix.Tasks.Muro.version()
    {out, err, code} = cli([])
    assert code == 0
    assert err == ""

    assert out ==
             "Muro v#{version}\nmuro check  muro emit  muro gen  muro init  muro skills add  muro deps.get  muro mutate\n"
  end

  test "an unknown command exits 1" do
    {out, err, code} = cli(["nope"])
    assert code == 1
    assert out == ""
    assert err =~ "usage: muro"
  end

  test "check matches mix muro.check" do
    assert_same(fn -> Mix.Tasks.Muro.Check.run([]) end, ["check"])

    path = "examples/half_ok.muro"
    assert_same(fn -> Mix.Tasks.Muro.Check.run([path]) end, ["check", path])

    bad = "examples/bad_dup.muro"
    assert_same(fn -> Mix.Tasks.Muro.Check.run([bad]) end, ["check", bad])

    assert_same(fn -> Mix.Tasks.Muro.Check.run(["--fuel", "0"]) end, ["check", "--fuel", "0"])

    assert_same(fn -> Mix.Tasks.Muro.Check.run(["--nope"]) end, ["check", "--nope"])
  end

  test "emit matches mix muro.emit for each backend" do
    half = "examples/half_ok.muro"
    assert_same(fn -> Mix.Tasks.Muro.Emit.run([half]) end, ["emit", half])

    assert_same(fn -> Mix.Tasks.Muro.Emit.run([half, "--backend", "elixir"]) end, [
      "emit",
      half,
      "--backend",
      "elixir"
    ])

    assert_same(fn -> Mix.Tasks.Muro.Emit.run(["examples/meet.muro", "--backend", "fsm"]) end, [
      "emit",
      "examples/meet.muro",
      "--backend",
      "fsm"
    ])

    assert_same(fn -> Mix.Tasks.Muro.Emit.run([half, "--backend", "exunit"]) end, [
      "emit",
      half,
      "--backend",
      "exunit"
    ])

    assert_same(fn -> Mix.Tasks.Muro.Emit.run([half, "--backend", "nope"]) end, [
      "emit",
      half,
      "--backend",
      "nope"
    ])

    for backend <- ["rust", "asm", "c"] do
      dir = copy_book(backend)
      path = Path.join(dir, "half.muro")
      argv = ["emit", path, "--backend", backend]
      fun = fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", backend]) end

      if backend == "c" do
        # The second build would see a finished NIF and print a different make line.
        mix = capture_task(fun)
        Enum.each(Path.wildcard(Path.join(dir, "*.o")), &File.rm!/1)
        File.rm_rf!(Path.join(dir, "priv"))
        cli = capture_cli(argv)
        assert cli.stdout == mix.stdout
        assert cli.code == mix.code
        assert cli.stderr == mix.stderr
      else
        assert_same(fun, argv)
      end
    end

    otp = copy_example("ping.muro")

    assert_same(
      fn -> Mix.Tasks.Muro.Emit.run([otp, "--backend", "otp"]) end,
      ["emit", otp, "--backend", "otp"]
    )

    place = copy_example("place.muro")

    assert_same(
      fn -> Mix.Tasks.Muro.Emit.run([place, "--node", "a"]) end,
      ["emit", place, "--node", "a"]
    )
  end

  test "emit c outside the loaded Mix project writes only the header and the source" do
    dir = System.tmp_dir!() |> Path.join("muro_cli_c_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, "half.muro")
    File.cp!("examples/half_ok.muro", path)

    File.cd!(dir, fn ->
      {out, err, code} = cli(["emit", path, "--backend", "c"])
      assert code == 0
      assert err == ""
      assert out =~ "half.h"
      assert out =~ "half.c"
      refute out =~ "elixir_make"
      refute err =~ "elixir_make"
    end)

    refute File.exists?(Path.join(dir, "half_nif.c"))
    refute File.exists?(Path.join(dir, "half.ex"))
    assert File.regular?(Path.join(dir, "half.h"))
    assert File.regular?(Path.join(dir, "half.c"))

    inside = Path.join(File.cwd!(), "cli_c_#{System.unique_integer([:positive])}")
    File.mkdir_p!(inside)
    on_exit(fn -> File.rm_rf!(inside) end)
    inside_book = Path.join(inside, "half.muro")
    File.cp!("examples/half_ok.muro", inside_book)

    capture_io(fn ->
      File.cd!(inside, fn -> Mix.Tasks.Muro.Emit.run([inside_book, "--backend", "c"]) end)
    end)

    assert File.read!(Path.join(dir, "half.c")) == File.read!(Path.join(inside, "half.c"))
    assert File.read!(Path.join(dir, "half.h")) == File.read!(Path.join(inside, "half.h"))
  end

  test "gen and gen --check match mix muro.gen" do
    left = elixir_project()
    right = elixir_project()
    File.cp_r!(left, right)

    assert_same(
      fn -> File.cd!(left, fn -> Mix.Tasks.Muro.Gen.run([]) end) end,
      ["gen"],
      right
    )

    assert File.read!(Path.join(left, "lib/one.ex")) == File.read!(Path.join(right, "lib/one.ex"))

    assert_same(
      fn -> File.cd!(left, fn -> Mix.Tasks.Muro.Gen.run(["--check"]) end) end,
      ["gen", "--check"],
      left
    )
  end

  test "init on a Mix project matches mix muro.init" do
    left = mix_project()
    right = mix_project()

    assert_same(
      fn -> File.cd!(left, fn -> Mix.Tasks.Muro.Init.run([]) end) end,
      ["init"],
      right
    )

    assert File.read!(Path.join(left, "muro.exs")) == File.read!(Path.join(right, "muro.exs"))
    assert File.dir?(Path.join(right, "priv/muro"))
  end

  test "the release workflow builds the four assets and smokes the Linux binary" do
    text = File.read!(".github/workflows/release.yml")
    assert text =~ "tags:"
    assert text =~ "- \"v*\""
    assert text =~ "macos-aarch64"
    assert text =~ "macos-x86_64"
    assert text =~ "linux-x86_64"
    assert text =~ "linux-aarch64"
    refute text =~ "musl"
    assert text =~ "zig-${zarch}-linux-0.15.2"
    assert text =~ "0.15.2"
    assert text =~ "muro --version"
    assert text =~ "muro check"
    assert text =~ "muro emit /tmp/one.muro --backend rust"
    assert text =~ "ubuntu:24.04"
    refute text =~ "hex.publish"
  end

  defp assert_same(fun, argv, cd \\ nil) do
    mix = capture_task(fun)
    cli = if cd, do: File.cd!(cd, fn -> capture_cli(argv) end), else: capture_cli(argv)

    assert cli.stdout == mix.stdout
    assert cli.code == mix.code

    if mix.message do
      assert mix.stderr == ""
      assert cli.stderr == Muro.CLI.ensure_nl(mix.message)
    else
      assert cli.stderr == mix.stderr
    end
  end

  defp capture_task(fun) do
    parent = self()

    stdout =
      capture_io(fn ->
        stderr =
          capture_io(:stderr, fn ->
            result =
              try do
                fun.()
                {:ok, 0, nil}
              rescue
                error in Mix.Error -> {:raise, 1, error.message}
              catch
                :exit, {:shutdown, code} -> {:exit, code, nil}
              end

            send(parent, {:result, result})
          end)

        send(parent, {:stderr, stderr})
      end)

    assert_received {:stderr, stderr}
    assert_received {:result, {_kind, code, message}}
    %{stdout: strip(stdout), stderr: stderr, code: code, message: message}
  end

  defp capture_cli(argv) do
    parent = self()

    stdout =
      capture_io(fn ->
        stderr =
          capture_io(:stderr, fn ->
            send(parent, {:code, Muro.CLI.main(argv)})
          end)

        send(parent, {:stderr, stderr})
      end)

    assert_received {:stderr, stderr}
    assert_received {:code, code}
    %{stdout: stdout, stderr: stderr, code: code}
  end

  defp cli(argv) do
    got = capture_cli(argv)
    {got.stdout, got.stderr, got.code}
  end

  defp strip(text), do: String.replace(text, ~r/^==> \S+\n/m, "")

  defp copy_book(backend) do
    dir =
      if backend == "c" do
        path = Path.join(File.cwd!(), "cli_emit_#{System.unique_integer([:positive])}")
        File.mkdir_p!(path)
        path
      else
        path = Path.join(System.tmp_dir!(), "muro_cli_#{System.unique_integer([:positive])}")
        File.mkdir_p!(path)
        path
      end

    on_exit(fn -> File.rm_rf!(dir) end)
    File.cp!("examples/half_ok.muro", Path.join(dir, "half.muro"))
    dir
  end

  defp copy_example(name) do
    dir = Path.join(System.tmp_dir!(), "muro_cli_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, name)
    File.cp!(Path.join("examples", name), path)
    path
  end

  defp elixir_project do
    dir = Path.join(System.tmp_dir!(), "muro_cli_gen_#{System.unique_integer([:positive])}")
    File.mkdir_p!(Path.join(dir, "priv/muro"))
    on_exit(fn -> File.rm_rf!(dir) end)
    File.write!(Path.join(dir, "priv/muro/one.muro"), "def one : run Nat := suc 0\n")
    version = Mix.Tasks.Muro.version()

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro: "#{version}",
      modules: [
        {"priv/muro/one.muro", MyApp.One, "lib/one.ex"}
      ]
    ]
    """)

    dir
  end

  defp mix_project do
    dir = Path.join(System.tmp_dir!(), "muro_cli_init_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)

    File.write!(Path.join(dir, "mix.exs"), """
    defmodule Tmp.MixProject do
      use Mix.Project
      def project, do: [app: :tmp, version: "0.0.1"]
    end
    """)

    dir
  end
end
