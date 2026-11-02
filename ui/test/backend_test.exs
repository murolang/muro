defmodule MuroVisor.BackendTest do
  use MuroVisor.ConnCase, async: false

  @backends [:otp, :fsm, :c, :rust, :zig]

  test "switching among the five backends redraws that outline and does not check", %{conn: conn} do
    path = example("meet.muro")
    assert {:ok, stamp} = MuroVisor.Book.open(path)
    counter = count_checks()

    {:ok, view, html} = live(conn, "/")
    book = book()
    assert_outline(html, book, path, :otp)
    assert checks(counter) == 0
    assert text_of(html, "#book-stamp") =~ to_string(stamp)

    seen = %{otp: text_of(html, "#outline")}

    order = [:c, :fsm, :rust, :zig, :otp, :rust, :c, :zig, :fsm, :otp]

    seen =
      Enum.reduce(order, seen, fn backend, seen ->
        view |> element("#backend-#{backend}") |> render_click()
        html = render(view)
        assert_outline(html, book, path, backend)
        assert text_of(html, "#book-stamp") =~ to_string(stamp)
        assert book() == book
        assert checks(counter) == 0

        text = text_of(html, "#outline")

        case Map.fetch(seen, backend) do
          {:ok, earlier} -> assert text == earlier
          :error -> :ok
        end

        Map.put(seen, backend, text)
      end)

    assert Map.keys(seen) |> Enum.sort() == Enum.sort(@backends)
    assert seen.otp =~ "handle_info"
    refute seen.c =~ "handle_info"
    assert seen.fsm =~ "backend: fsm"
    refute seen.fsm == seen.otp
  end

  test "the FSM backend refuses a book with no session, and switching back restores the outline",
       %{conn: conn} do
    path = example("half_ok.muro")
    assert {:ok, _stamp} = MuroVisor.Book.open(path)
    counter = count_checks()
    {:ok, view, html} = live(conn, "/")
    book = book()

    assert_outline(html, book, path, :otp)
    otp = text_of(html, "#outline")
    assert checks(counter) == 0

    assert {:error, msg} = emitted(book, path, :fsm)
    assert msg =~ "no session"
    assert msg =~ "half_ok.muro"

    for backend <- [:fsm, :c, :fsm, :zig, :rust, :otp, :fsm] do
      view |> element("#backend-#{backend}") |> render_click()
      html = render(view)
      assert checks(counter) == 0

      if backend == :fsm do
        assert String.trim(text_of(html, "#outline")) == msg
        refute text_of(html, "#outline") =~ "backend:"
      else
        assert_outline(html, book, path, backend)
      end
    end

    view |> element("#backend-otp") |> render_click()
    assert text_of(render(view), "#outline") == otp
    assert checks(counter) == 0
  end

  defp assert_outline(html, book, path, backend) do
    assert {:ok, outline} = emitted(book, path, backend)
    text = text_of(html, "#outline")
    assert text =~ "backend: #{backend}\n"
    assert text =~ "names: #{Enum.join(outline.names, ", ")}"

    for sig <- outline.signatures do
      params = sig |> Map.get(:params, []) |> Enum.map_join(", ", &param/1)
      lays = Map.get(sig, :param_layouts, [])
      assert text =~ "#{sig.name}(#{params}) #{inspect(sig.layout)} #{inspect(lays)}"
    end

    assert text =~ "layouts:\n"

    for lay <- outline.layouts do
      assert text =~ "#{Map.get(lay, :name)} #{inspect(Map.get(lay, :layout))}"
    end

    for clause <- outline.clauses do
      assert text =~ clause
    end
  end

  defp emitted(book, path, :fsm) do
    Muro.Emit.outline(:fsm, Muro.Prelude.for_emit(book), path)
  end

  defp emitted(book, path, backend) do
    stem =
      path
      |> Path.basename()
      |> String.trim_trailing(".muro")
      |> String.replace("-", "_")

    Muro.Emit.outline(backend, Muro.Prelude.for_emit(book), stem)
  end

  defp param(name) when is_binary(name), do: name
  defp param(other), do: inspect(other)

  defp count_checks do
    {:ok, agent} = Agent.start_link(fn -> 0 end)
    :ok = Muro.Check.check_hook(fn -> Agent.update(agent, &(&1 + 1)) end)

    on_exit(fn ->
      Muro.Check.check_hook(nil)
      if Process.alive?(agent), do: Agent.stop(agent)
    end)

    agent
  end

  defp checks(agent), do: Agent.get(agent, & &1)
end
