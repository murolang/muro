defmodule Muro.EmitAsmTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  @linker """
  ENTRY(Reset_Handler)

  MEMORY
  {
    FLASH (rx) : ORIGIN = 0x00000000, LENGTH = 256K
    RAM (rwx)  : ORIGIN = 0x20000000, LENGTH = 16K
  }

  SECTIONS
  {
    .text : {
      KEEP(*(.vectors))
      *(.text*)
      *(.rodata*)
      . = ALIGN(4);
    } > FLASH

    .bss : {
      . = ALIGN(4);
      __bss_start = .;
      *(.bss*)
      *(COMMON)
      . = ALIGN(4);
      __bss_end = .;
    } > RAM

    _stack_top = ORIGIN(RAM) + LENGTH(RAM);
  }
  """

  test "half and plus match the Nat NIF" do
    dir = tmp_dir()
    File.cp!("examples/half_ok.muro", Path.join(dir, "half_asm.muro"))
    source = File.read!(emit_asm!(dir, "half_asm"))
    assert source =~ ".global half"
    assert source =~ ".global plus"
    refute source =~ "IsEven"
    refute source =~ "half_ok"

    capture_io(fn ->
      Mix.Tasks.Muro.Emit.run([Path.join(dir, "half_asm.muro"), "--backend", "c"])
    end)

    on_exit(fn ->
      :code.delete(:"Elixir.HalfAsm")
      :code.purge(:"Elixir.HalfAsm")
    end)

    Code.compile_file(Path.join(dir, "half_asm.ex"))
    half = fn n -> apply(:"Elixir.HalfAsm", :half, [n]) end
    plus = fn n, m -> apply(:"Elixir.HalfAsm", :plus, [n, m]) end

    out =
      run_asm!(dir, "half_asm", """
        push {r4, r5, r6, lr}
        movs r0, #4
        bl muro_from_u64
        bl half
        bl muro_to_u64
        movs r4, r0
        movs r0, #2
        bl muro_from_u64
        movs r5, r0
        movs r0, #3
        bl muro_from_u64
        movs r1, r0
        movs r0, r5
        bl plus
        bl muro_to_u64
        movs r1, r0
        movs r0, r4
        bl print_pair
        pop {r4, r5, r6, pc}
      """)

    assert half.(4) == 2
    assert plus.(2, 3) == 5
    assert out == "#{half.(4)} #{plus.(2, 3)}\n"
  end

  test "run internal is a label and inc(4) is 5" do
    dir = tmp_dir()
    File.cp!("examples/internal_ok.muro", Path.join(dir, "internal_ok.muro"))
    source = File.read!(emit_asm!(dir, "internal_ok"))
    assert source =~ ".global inc"
    refute source =~ ".global step"

    out =
      run_asm!(dir, "internal_ok", """
        push {r4, lr}
        movs r0, #4
        bl muro_from_u64
        bl inc
        bl muro_to_u64
        bl print_one
        pop {r4, pc}
      """)

    assert out == "5\n"
  end

  test "an applied lambda runs" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "apply_lam.muro"), """
    def id : run Π (n : Nat) → Nat :=
      λ (n : Nat) → (λ (m : Nat) → suc m) n

    def keep : run Π (n : Nat) → Nat :=
      λ (n : Nat) → (λ (- k : Nat) → n) 0
    """)

    emit_asm!(dir, "apply_lam")

    out =
      run_asm!(dir, "apply_lam", """
        push {r4, lr}
        movs r0, #3
        bl muro_from_u64
        bl id
        bl muro_to_u64
        movs r4, r0
        movs r0, #5
        bl muro_from_u64
        bl keep
        bl muro_to_u64
        movs r1, r0
        movs r0, r4
        bl print_pair
        pop {r4, pc}
      """)

    assert out == "4 5\n"
  end

  test "a stream, a list, and a five-argument Nat are refused before a file is written" do
    dir = tmp_dir()

    for name <- ~w(nats list) do
      File.cp!("examples/#{name}.muro", Path.join(dir, "#{name}.muro"))
      refute_scope(dir, name)
    end

    File.cp!("examples/list.muro", Path.join(dir, "list.muro"))
    File.cp!("examples/sort.muro", Path.join(dir, "sort.muro"))
    refute_scope(dir, "sort")

    wide = Path.join(dir, "wide.muro")

    File.write!(wide, """
    def wide : run Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → Π (d : Nat) → Π (e : Nat) → Nat :=
      λ (a : Nat) → λ (b : Nat) → λ (c : Nat) → λ (d : Nat) → λ (e : Nat) → a
    """)

    refute_scope(dir, "wide")
  end

  test "a tensor and a bare lambda are refused before a file is written" do
    dir = tmp_dir()
    nx = Path.join(dir, "nx_add.muro")
    File.cp!("examples/nx_add.muro", nx)

    assert_raise Mix.Error, ~r/c:machine/, fn ->
      Mix.Tasks.Muro.Emit.run([nx, "--backend", "asm"])
    end

    refute File.exists?(Path.join(dir, "nx_add.s"))

    lam = Path.join(dir, "lam.muro")

    File.write!(lam, """
    def bad : run Π (f : Π (x : Nat) → Nat) → Nat :=
      λ (f : Π (x : Nat) → Nat) → f 0
    """)

    assert_raise Mix.Error, ~r/c:lambda/, fn ->
      Mix.Tasks.Muro.Emit.run([lam, "--backend", "asm"])
    end

    refute File.exists?(Path.join(dir, "lam.s"))
  end

  defp refute_scope(dir, name) do
    path = Path.join(dir, "#{name}.muro")

    assert_raise Mix.Error, ~r/asm:scope/, fn ->
      Mix.Tasks.Muro.Emit.run([path, "--backend", "asm"])
    end

    refute File.exists?(Path.join(dir, "#{name}.s"))
  end

  defp emit_asm!(dir, name) do
    path = Path.join(dir, "#{name}.muro")
    out = capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", "asm"]) end)
    s = Path.join(dir, "#{name}.s")
    assert out =~ s
    assert File.regular?(s)
    s
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_asm_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  defp run_asm!(dir, stem, main) do
    File.write!(Path.join(dir, "link.ld"), @linker)
    File.write!(Path.join(dir, "harness.s"), harness(main))
    assemble!(dir, "harness.s")
    assemble!(dir, "#{stem}.s")
    link!(dir, stem)
    {out, status} = qemu!(dir)
    assert status == 0, out
    out
  end

  defp assemble!(dir, src) do
    obj = Path.basename(src, ".s") <> ".o"

    {out, status} =
      System.cmd(tool!("arm-none-eabi-as"), ["-mcpu=cortex-m0", "-mthumb", "-o", obj, src],
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, out
    obj
  end

  defp link!(dir, stem) do
    {out, status} =
      System.cmd(
        tool!("arm-none-eabi-ld"),
        ["-T", "link.ld", "--nmagic", "-o", "prog.elf", "harness.o", "#{stem}.o"],
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, out
  end

  defp qemu!(dir) do
    port =
      Port.open({:spawn_executable, tool!("qemu-system-arm")}, [
        :binary,
        :exit_status,
        :stderr_to_stdout,
        {:cd, dir},
        {:args,
         [
           "-M",
           "microbit",
           "-nographic",
           "-monitor",
           "none",
           "-semihosting-config",
           "enable=on,target=native",
           "-kernel",
           "prog.elf"
         ]}
      ])

    collect(port, "")
  end

  defp collect(port, acc) do
    receive do
      {^port, {:data, data}} ->
        collect(port, acc <> data)

      {^port, {:exit_status, status}} ->
        {acc, status}
    after
      20_000 ->
        case Port.info(port, :os_pid) do
          {:os_pid, pid} -> System.cmd("kill", ["-9", Integer.to_string(pid)])
          _ -> :ok
        end

        Port.close(port)
        flunk("qemu hung\n#{acc}")
    end
  end

  defp tool!(name) do
    path =
      System.find_executable(name) ||
        Enum.find_value(["/opt/homebrew/bin", "/usr/local/bin"], fn dir ->
          candidate = Path.join(dir, name)
          if File.regular?(candidate), do: candidate
        end)

    assert is_binary(path) and File.regular?(path), "#{name} not found"
    path
  end

  defp harness(main) do
    """
    .syntax unified
    .arch armv6-m
    .cpu cortex-m0
    .thumb

    .section .vectors, "a"
    .align 2
    .word _stack_top
    .word Reset_Handler

    .text
    .align 2
    .global Reset_Handler
    .type Reset_Handler, %function
    .thumb_func
    Reset_Handler:
      ldr r0, =_stack_top
      mov sp, r0
      ldr r0, =__bss_start
      ldr r1, =__bss_end
      movs r2, #0
    .Lzero:
      cmp r0, r1
      bhs .Lzero_done
      str r2, [r0]
      adds r0, #4
      b .Lzero
    .Lzero_done:
      bl muro_reset
      bl main
      movs r0, #0x18
      ldr r1, =0x20026
      bkpt #0xAB
      b .

    .align 2
    .global main
    .type main, %function
    .thumb_func
    main:
    #{main}
      .ltorg

    .align 2
    .type print_pair, %function
    .thumb_func
    print_pair:
      ldr r2, =msg
      adds r0, #48
      strb r0, [r2, #0]
      movs r3, #32
      strb r3, [r2, #1]
      adds r1, #48
      strb r1, [r2, #2]
      movs r3, #10
      strb r3, [r2, #3]
      movs r3, #0
      strb r3, [r2, #4]
      ldr r1, =msg
      movs r0, #4
      bkpt #0xAB
      bx lr
      .ltorg

    .align 2
    .type print_one, %function
    .thumb_func
    print_one:
      ldr r2, =msg
      adds r0, #48
      strb r0, [r2, #0]
      movs r3, #10
      strb r3, [r2, #1]
      movs r3, #0
      strb r3, [r2, #2]
      ldr r1, =msg
      movs r0, #4
      bkpt #0xAB
      bx lr
      .ltorg

    .section .bss
    .align 2
    msg:
      .space 8
    """
  end
end
