defmodule Muro.AsyncTest do
  use ExUnit.Case, async: true

  alias Muro.{Async, Check, Meet, Parser}

  @h2o """
  orphan message after client put headers, server arm headers, client put trailers, server put rst, client get (c : Ctl), server arm trailers, server put goaway: client: done; server: done; l2r: []; r2l: [goaway]
  """

  test "the worked book checks" do
    assert Muro.check_file("examples/async-meetings.muro") == :ok
    assert Muro.check_file("examples/meet.muro") == :ok

    assert {:ok, book} = Parser.parse(File.read!("examples/async-meetings.muro"))

    buffers = for %{kind: :meet} = m <- book, do: {m.name, m.buffer}
    assert {"inflight", 1} in buffers
    assert {"inflight-two", 2} in buffers
    assert {"crossed", 1} in buffers
    assert {"owed-wire", 1} in buffers
    assert {"vec-wire", 1} in buffers
    assert {"stream-sync", nil} in buffers
    assert {"stream-async", 1} in buffers
    assert {"echo-wire", 1} in buffers
    assert {"spin-wire", 1} in buffers
    assert {"line-wire", 1} in buffers
  end

  test "a synchronous meeting of duals is unchanged" do
    assert check("""
           session ping := recv Nat (send Nat end)
           session back := dual ping
           conform pong : ping := get (k : Nat) (put 1 done)
           conform peer : back := put 1 (get (m : Nat) done)
           meet wire : pong with peer
           """) == :ok
  end

  test "a server that answers an in-flight frame is refused with the trace" do
    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             data Ctl : Type where
               rst : Ctl

             data Goaway : Type where
               goaway : Goaway

             session out-frames := send Frame (send Frame (recv Ctl end))

             conform client : out-frames :=
               put headers (put trailers (get (c : Ctl) done))

             session h2o :=
               recv (f : Frame) (case f
                 | bytes => send Ctl (recv (g : Frame) (case g
                     | bytes => end
                     | trailers => send Goaway end
                     | headers => end))
                 | trailers => send Ctl end
                 | headers => send Ctl (recv (g : Frame) (case g
                     | bytes => end
                     | trailers => send Goaway end
                     | headers => end)))

             conform server : h2o :=
               get (f : Frame) (match f
                 (put rst (get (g : Frame) (match g done (put goaway done) done)))
                 (put rst done)
                 (put rst (get (g : Frame) (match g done (put goaway done) done))))

             meet bad-flight : client with server buffer 1
             """)

    assert msg =~ String.trim(@h2o)
  end

  test "a head of the wrong type is a reception error" do
    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             data Goaway : Type where
               goaway : Goaway

             session shout := send Goaway end

             session take :=
               recv (f : Frame) (case f
                 | bytes => end
                 | trailers => end
                 | headers => end)

             conform shouter : shout := put goaway done

             conform taker : take := get (f : Frame) (match f done done done)

             meet crossed-type : shouter with taker buffer 1
             """)

    assert msg =~
             "reception error after shouter put goaway: shouter: done; taker: get (f : Frame); l2r: [goaway]; r2l: []; head taker is goaway"
  end

  test "both sides sending first meet asynchronously and diverge synchronously" do
    cross = {:put, :nat, {:nat, 1}, {:get, :nat, :n, :done}}
    assert Meet.meets(cross, cross) == {:error, "diverged: left: put 1; right: put 1"}
    assert Async.meets(cross, cross, [], 1) == :ok

    assert Async.meets(cross, cross, [], 0) ==
             {:error, "deadlock: left: put 1; right: put 1; l2r: []; r2l: []"}

    assert {:error, msg} =
             check("""
             session ping := send Nat (recv Nat end)
             conform a : ping := put 1 (get (n : Nat) done)
             conform b : ping := put 1 (get (n : Nat) done)
             meet wire : a with b
             """)

    assert msg =~ "protocol:"
    assert msg =~ "send Nat"
    refute msg =~ "put 1"
  end

  test "two sends in each direction deadlock at buffer 1" do
    dbl = {:put, :nat, {:nat, 0}, {:put, :nat, {:nat, 1}, {:get, :nat, :n, :done}}}

    assert Async.meets(dbl, dbl, [], 1, "a", "b") ==
             {:error, "deadlock after a put 0, b put 0: a: put 1; b: put 1; l2r: [0]; r2l: [0]"}
  end

  test "a server that still wants a frame deadlocks" do
    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             session once := send Frame (send Frame end)

             session forever :=
               rec Y. recv (f : Frame) (case f
                 | bytes => Y
                 | trailers => Y
                 | headers => Y)

             conform client : once := put bytes (put trailers done)

             conform server : forever := rec Y. get (f : Frame) (match f Y Y Y)

             meet stuck : client with server buffer 1
             """)

    assert msg =~
             "deadlock after client put bytes, server arm bytes, client put trailers, server arm trailers: client: done; server: get (f : Frame); l2r: []; r2l: []"
  end

  test "a successor of a received nat in a loop is unbounded" do
    grow =
      {:rec, :X, {:get, :nat, :n, {:put, :nat, {:con, "suc", [{:var, :n}]}, {:call, :X}}}}

    const = {:rec, :Y, {:put, :nat, {:nat, 0}, {:call, :Y}}}
    assert Async.meets(grow, const, [], 1) == {:error, "unbounded recursive payload"}

    assert {:error, msg} =
             check("""
             data Box : Type where
               box : Π (n : Nat) →
                 Box

             session grow := rec X. recv Nat (send Box X)
             session feed := rec Y. send Nat (recv Box Y)
             conform up : grow := rec X. get (n : Nat) (put (box n) X)
             conform down : feed := rec Y. put 0 (get (b : Box) Y)
             meet wire : up with down buffer 1
             """)

    assert msg =~ "unbounded recursive payload"
  end

  test "a one-shot successor is not that refusal" do
    one = {:get, :nat, :n, {:put, :unknown, {:con, "suc", [{:var, :n}]}, :done}}
    send = {:put, :nat, {:nat, 0}, :done}
    assert {:error, msg} = Async.meets(one, send, [], 1)
    refute msg == "unbounded recursive payload"
    assert msg =~ "orphan message"
  end

  test "a constant loop and an echo meet" do
    loop = {:rec, :X, {:put, :nat, {:nat, 0}, {:call, :X}}}
    hear = {:rec, :Y, {:get, :nat, :d, {:call, :Y}}}
    assert Async.meets(loop, hear, [], 1) == :ok

    echo_l = {:rec, :X, {:put, :nat, {:nat, 0}, {:get, :nat, :m, {:call, :X}}}}
    echo_r = {:rec, :Y, {:get, :nat, :n, {:put, :unknown, {:var, :n}, {:call, :Y}}}}
    assert Async.meets(echo_l, echo_r, [], 1) == :ok
  end

  test "unguarded recursion is refused by that name" do
    assert Async.meets({:rec, :X, {:call, :X}}, :done, [], 1) ==
             {:error, "unguarded recursion"}

    assert Async.meets({:call, :Z}, :done, [], 1) ==
             {:error, "free session variable Z"}
  end

  test "evidence that misses the bound does not conform" do
    assert {:error, msg} =
             check("""
             session owed := send (d : Nat) {d ≤ 1} end
             conform over : owed := put 2 done
             conform hear : owed := put 0 done
             meet wire : over with hear buffer 1
             """)

    assert msg =~ "misses bound"
    assert msg =~ "skipped because over does not conform"
  end

  test "done meets stop across a buffer" do
    assert Async.meets(:done, :stop, [], 1) == :ok
    assert {:error, msg} = Meet.meets(:done, :stop)
    assert msg =~ "diverged"
  end

  test "a payload against a choice is a reception error" do
    assert Async.meets({:put, :nat, {:nat, 0}, :done}, {:cover, :done, :done}, [], 1) ==
             {:error,
              "reception error after left put 0: left: done; right: cover; l2r: [0]; r2l: []; head right is 0"}

    assert Async.meets({:pick0, :done}, {:cover, :done, :stop}, [], 1) == :ok
    assert Async.meets({:put, :bit, :b0, :done}, {:iget, :b, :done, :stop}, [], 1) == :ok
  end

  test "a buffer that is not a numeral is refused" do
    assert {:error, msg} = Parser.parse("meet wire : a with b buffer\n")
    assert msg =~ "buffer bound is a nat"

    assert {:error, msg} = Parser.parse("meet wire : a with b buffer x\n")
    assert msg =~ "buffer bound is a nat"

    assert {:ok, [meet]} = Parser.parse("meet wire : a with b buffer 2\n")
    assert meet.buffer == 2

    assert {:ok, [meet]} = Parser.parse("meet wire : a with b\n")
    assert meet.buffer == nil
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end
