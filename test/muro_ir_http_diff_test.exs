defmodule Muro.IRHttpDiffTest do
  # The HTTP step book of doctorcorral/muro-http (priv/muro/http, commit
  # 1050ea3), pinned under test/http_step with its evidence
  # removed. Every run and data declaration is verbatim. It sits outside
  # test/fixtures so the corpus walks of other tests do not Share it. The book is
  # checked once; its runs are compared on HTTP request bytes:
  #
  #     normalize == Eval(elaborate) == Eval(Share(elaborate))
  #                == Eval(elaborate(closures: true))
  #
  # and each image in A-normal form (`Muro.IR.Anf`).
  #
  # Share takes most of this module's time on a book this size, so the
  # module runs async beside the rest of the suite.
  use ExUnit.Case, async: true

  Code.require_file("ir_diff_helper.exs", __DIR__)

  alias Muro.IRDiff

  @moduletag timeout: 600_000
  @path "test/http_step/step.muro"

  @requests [
    "",
    "GET / HT",
    "GET / HTTP/1.1\r\nHost: h\r\n",
    "GET /index.html HTTP/1.1\r\nHost: example.com\r\nUser-Agent: t\r\n\r\n",
    "GET / HTTP/1.1\r\nHost: h\r\nConnection: close\r\n\r\n",
    "GET / HTTP/1.0\r\n\r\n",
    "HEAD / HTTP/1.1\r\nHost: h\r\n\r\n",
    "TRACE / HTTP/1.1\r\nHost: h\r\n\r\n",
    "POST /x HTTP/1.1\r\nHost: h\r\nContent-Length: 5\r\n\r\nhello",
    "POST /x HTTP/1.1\r\nHost: h\r\nContent-Length: 50\r\n\r\nshort",
    "POST /x HTTP/1.1\r\nHost: h\r\nContent-Length: 4\r\nExpect: 100-continue\r\n\r\n",
    "POST /c HTTP/1.1\r\nHost: h\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n",
    "POST /c HTTP/1.1\r\nHost: h\r\nTransfer-Encoding: chunked\r\n\r\nzz\r\n",
    "GET / HTTP/1.1\r\nHost: h\r\n\r\nGET /2 HTTP/1.1\r\nHost: h\r\n\r\n",
    "BREW / HTTP/1.1\r\n\r\n",
    "\r\n\r\n",
    "GET / HTTP/1.1\nHost: h\n\n"
  ]

  setup_all do
    {:ok, book} = Muro.Load.file(@path)
    # A closed run reads up to 16 KiB of request bytes, one call per octet.
    # Its checker depth bound is raised the way the book's own check is.
    ctx = IRDiff.prepare_whole(@path, book)
    {:ok, ctx: Map.merge(ctx, %{eval_fuel: 10_000_000, ref_fuel: 100_000})}
  end

  defp u(n), do: {:word, :u64, n}

  defp st(phase, code, left, keep),
    do: {:con, "St", "st", Enum.map([phase, code, left, keep, 0, 0, 0, 0], &u/1)}

  defp agree!(cases) do
    bad = for {:mismatch, d} <- cases, do: d
    assert bad == []
    skipped = for {:skip, r} <- cases, do: r
    assert skipped == []
    assert Enum.all?(cases, fn {:agree, ks} -> ks == IRDiff.image_keys() end)
    length(cases)
  end

  defp run_all(ctx, calls) do
    calls
    |> Task.async_stream(fn {name, args} -> IRDiff.compare(ctx, name, args) end,
      timeout: :infinity,
      ordered: false
    )
    |> Enum.map(fn {:ok, r} -> r end)
  end

  defp args(ctx, vals), do: Enum.map(vals, &{IRDiff.term!(ctx, &1), &1})

  test "step0 on every request and fact from a fresh read", %{ctx: ctx} do
    calls =
      for req <- @requests, fact <- [1, 2, 3, 4, 6, 9], max <- [16_384, 10] do
        {"step0", args(ctx, [st(0, 0, 0, 0), u(fact), {:bytes, req}, u(max), u(0), u(0)])}
      end

    assert agree!(run_all(ctx, calls)) == length(@requests) * 12
  end

  test "stepFact from every phase", %{ctx: ctx} do
    states =
      [st(1, 400, 0, 1), st(2, 0, 0, 0), st(3, 0, 7, 0), st(4, 0, 0, 0), st(5, 0, 0, 0)] ++
        [st(6, 0, 0, 0), st(7, 0, 0, 0), st(8, 0, 0, 0)]

    calls =
      for s <- states,
          fact <- [1, 2, 3, 4, 5, 6],
          req <- Enum.take_every(@requests, 3),
          {n, owed} <- [{0, 0}, {3, 7}] do
        {"stepFact",
         args(ctx, [s, u(fact), {:bytes, req}, u(16_384), u(n), u(owed), u(1000), u(0), u(60_000)])}
      end

    assert agree!(run_all(ctx, calls)) == length(calls)
  end

  # Closed runs that read a buffer of 16 KiB or more. The checker takes
  # well over ten seconds on each, so they compare the three images
  # with one another and not with normalize.
  @big ~w(sawCapLine sawCapHdr capLineShort sawHdrDone)

  test "every closed run of the book", %{ctx: ctx} do
    closed = for f <- ctx.plain, not Map.get(f, :generated, false), f.params == [], do: f.name
    assert length(closed) > 50
    assert Enum.all?(@big, &(&1 in closed))
    small = closed -- @big
    assert agree!(run_all(ctx, Enum.map(small, &{&1, []}))) == length(small)

    for name <- @big do
      [p | rest] =
        for k <- IRDiff.image_keys(),
            do: IRDiff.observe(Map.fetch!(ctx, k), name, [], ctx.eval_fuel)

      assert {:ok, {:con, "Out", "out", _}} = p
      assert Enum.all?(rest, &(&1 == p))
    end
  end
end
