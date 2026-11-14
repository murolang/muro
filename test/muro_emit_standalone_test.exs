defmodule Muro.EmitStandaloneTest do
  use ExUnit.Case, async: false

  alias Muro.{Check, Emit, Load, Prelude}

  @books [
    {"test/fixtures/reason_match.muro", :reason, StandaloneReasonFsm, "standalone-reason"},
    {"examples/may-fail-free.muro", :free, StandaloneFreeFsm, "standalone-free"},
    {"examples/may-fail-send.muro", :send, StandaloneSendFsm, "standalone-send"},
    {"examples/may-fail-control.muro", :control, StandaloneControlFsm, "standalone-control"}
  ]

  test "fsm and otp are plain Elixir for a book that may fail" do
    for {path, kind, fsm_mod, stem} <- @books do
      book = load!(path)
      assert {:ok, fsm} = Emit.Fsm.render(book, path, fsm_mod)
      assert {:ok, otp} = Emit.Otp.render(book, stem)

      refute fsm =~ ~r/Muro\.[A-Za-z_]/, path
      refute otp =~ ~r/Muro\.[A-Za-z_]/, path
      refute fsm =~ "Muro.Emit"
      refute otp =~ "Muro.Emit"
      refute fsm =~ "Muro.Session"
      refute otp =~ "Muro.Session"

      fresh!(fsm, otp, kind)
    end
  end

  defp load!(path) do
    assert {:ok, book} = Load.file(path)
    assert :ok = Check.check_sig(book)
    Prelude.for_emit(book)
  end

  defp fresh!(fsm, otp, kind) do
    dir = Path.join(System.tmp_dir!(), "muro-standalone-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    File.write!(Path.join(dir, "fsm.ex"), fsm)
    File.write!(Path.join(dir, "otp.ex"), otp)
    File.write!(Path.join(dir, "probe.exs"), probe())

    {out, status} =
      System.cmd("elixir", ["probe.exs", Atom.to_string(kind)],
        cd: dir,
        stderr_to_stdout: true,
        env: %{
          "ERL_LIBS" => nil,
          "ERL_AFLAGS" => nil,
          "ERL_FLAGS" => nil,
          "ELIXIR_ERL_OPTIONS" => nil
        }
      )

    File.rm_rf(dir)
    assert status == 0, out
    assert out =~ "MURO_STANDALONE_OK #{kind}"
  end

  defp probe do
    ~S"""
    kind = System.argv() |> List.first()

    if Code.ensure_loaded?(Muro.Emit) != false, do: raise("Muro.Emit is loaded")
    if Code.ensure_loaded?(Muro.Session) != false, do: raise("Muro.Session is loaded")

    {_, diags} =
      Code.with_diagnostics(fn ->
        Code.compile_string(File.read!("fsm.ex"))
        Code.compile_string(File.read!("otp.ex"))
      end)

    warns = Enum.filter(diags, &(&1.severity == :warning))

    if warns != [] do
      raise("warnings:\n" <> Enum.map_join(warns, "\n", & &1.message))
    end

    case kind do
      "reason" ->
        server = StandaloneReasonFsm.ServerWait
        st = server.init()

        case server.down(st) do
          {:error, {:unexpected, where, {:down, {:data, "Why", []}}, :down}} ->
            if not String.contains?(where, "server-wait"), do: raise("down/1 #{where}")

          other ->
            raise("down/1 #{inspect(other)}")
        end

        for reason <- [:killed, :shutdown] do
          case server.down(st, reason) do
            {:ok, done} ->
              if not server.done?(done), do: raise("#{reason} is not done")

            other ->
              raise("#{reason} #{inspect(other)}")
          end
        end

        case server.down(st, :b0) do
          {:error, {:unexpected, _, {:down, {:data, "Why", []}}, :b0}} -> :ok
          other -> raise("b0 #{inspect(other)}")
        end

      "free" ->
        server = StandaloneFreeFsm.ServerWait

        case server.down(server.init()) do
          {:ok, failed} ->
            if not server.done?(failed), do: raise("free down/1 is not done")

          other ->
            raise("free down/1 #{inspect(other)}")
        end

        case server.down(server.init(), :killed) do
          {:error, {:unexpected, _, :down, :killed}} -> :ok
          other -> raise("free down/2 #{inspect(other)}")
        end

        task = StandaloneFreeFsm.TaskWork

        case task.down(task.init()) do
          {:error, {:unexpected, _, {:send, _}, :down}} -> :ok
          other -> raise("free task #{inspect(other)}")
        end

      "send" ->
        server = StandaloneSendFsm.ServerWork

        case server.down(server.init()) do
          {:error, {:unexpected, _, {:send, _}, :down}} -> :ok
          other -> raise("send down at put #{inspect(other)}")
        end

        case server.send(server.init(), 0) do
          {:ok, st} ->
            case server.down(st) do
              {:ok, failed} ->
                if not server.done?(failed), do: raise("send down is not done")

              other ->
                raise("send down #{inspect(other)}")
            end

          other ->
            raise("send #{inspect(other)}")
        end

      "control" ->
        server = StandaloneControlFsm.ServerWait
        if function_exported?(server, :down, 1), do: raise("control exports down/1")
        if function_exported?(server, :down, 2), do: raise("control exports down/2")

        case server.recv(server.init(), :ok) do
          {:ok, done} ->
            if not server.done?(done), do: raise("control recv is not done")

          other ->
            raise("control recv #{inspect(other)}")
        end

      other ->
        raise("unknown kind #{inspect(other)}")
    end

    IO.puts("MURO_STANDALONE_OK #{kind}")
    """
  end
end
