defmodule Muro.Emit.Asm do
  @moduledoc """
  Emit a closed Nat run as Cortex-M0 Thumb. Specs and evidence are omitted.
  Run bodies are the image from `Muro.IR`.

  The text is what the assembler translates. A refusal is the elaboration's,
  or `asm:scope` when the image is outside this Nat fragment. `asm:scope`
  leaves the image well formed.
  """

  alias Muro.{Emit, IR}

  @runtime ~w(
    muro_zero_obj muro_suc muro_reset muro_from_u64 muro_to_u64 muro_trap
    arena arena_at arena_end main Reset_Handler
  )

  @reserved MapSet.new(
              @runtime ++
                ~w(
                  r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
                  sp lr pc ip sl fp sb
                  text data bss global type word align syntax cpu thumb
                  section ltorg thumb_func
                )
            )

  # `sub sp, #imm` encodes an imm7, in units of 4, so at most 508.
  # `ldr`/`str [sp, #imm]` reach further. The frame check uses the sub.
  @max_sub 508

  @doc """
  Render `book` as one Cortex-M0 assembly file.
  """
  def render(book, stem) when is_list(book) and is_binary(stem) do
    case IR.elaborate(book) do
      {:ok, funs} ->
        if scope_ok?(funs), do: compile(book, funs, stem), else: {:error, "asm:scope"}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp compile(book, funs, stem) do
    names = names_of(book, funs)

    with {:ok, texts} <- emit_funs(funs, names) do
      parts = [header(stem), runtime() | texts]
      {:ok, Enum.join(parts, "\n\n") <> "\n"}
    end
  end

  defp emit_funs(funs, names) do
    case Enum.reduce_while(funs, {:ok, [], 0}, fn fun, {:ok, acc, l} ->
           case emit_fun(fun, names, l) do
             {:ok, text, l} -> {:cont, {:ok, acc ++ [text], l}}
             {:error, _} = err -> {:halt, err}
           end
         end) do
      {:ok, texts, _l} -> {:ok, texts}
      {:error, _} = err -> err
    end
  end

  defp emit_fun(fun, names, l) do
    env = Enum.with_index(fun.params, fn {pname, _lay}, i -> {pname, i} end)
    st = %{env: env, n: length(env), l: l, names: names}

    with {:ok, body, st} <- emit_tm(fun.body, st) do
      sub = stack_sub(st.n)

      if sub > @max_sub do
        {:error, "asm:scope"}
      else
        name = Map.fetch!(names, fun.name)

        stores =
          Enum.map(env, fn {_pname, i} -> "  str r#{i}, [sp, ##{i * 4}]" end)

        {:ok, fun_text(fun.export, name, sub, stores, body), st.l}
      end
    end
  end

  defp emit_tm({:var, name}, st) do
    case lookup(st.env, name) do
      nil -> {:error, "asm:scope"}
      slot -> {:ok, ["  ldr r0, [sp, ##{slot * 4}]"], st}
    end
  end

  defp emit_tm(:ze, st), do: {:ok, ["  ldr r0, =muro_zero_obj"], st}

  defp emit_tm({:su, u}, st) do
    with {:ok, lines, st} <- emit_tm(u, st) do
      {:ok, lines ++ ["  bl muro_suc"], st}
    end
  end

  defp emit_tm({:call, name, args}, st) do
    with {:ok, saved, slots, st} <- save_args(args, st) do
      case Map.fetch(st.names, name) do
        :error ->
          {:error, "asm:scope"}

        {:ok, fname} ->
          loads =
            slots
            |> Enum.with_index()
            |> Enum.map(fn {slot, i} -> "  ldr r#{i}, [sp, ##{slot * 4}]" end)

          {:ok, saved ++ loads ++ ["  bl #{fname}"], st}
      end
    end
  end

  defp emit_tm({:let, name, :nat, val, body}, st) do
    outer = st.env

    with {:ok, vlines, st} <- emit_tm(val, st) do
      slot = st.n
      st = %{st | n: slot + 1, env: [{name, slot} | outer]}

      with {:ok, blines, st} <- emit_tm(body, st) do
        lines = vlines ++ ["  str r0, [sp, ##{slot * 4}]"] ++ blines
        {:ok, lines, %{st | env: outer}}
      end
    end
  end

  defp emit_tm({:match, scrut, [{:arm, "zero", [], z}, {:arm, "suc", [y], s}]}, st) do
    outer = st.env
    {lzero, st} = fresh(st)
    {ljoin, st} = fresh(st)

    with {:ok, slines, st} <- emit_tm(scrut, st) do
      bslot = st.n
      st = %{st | n: bslot + 1}

      with {:ok, zlines, st} <- emit_tm(z, st),
           {:ok, sbody, st} <- emit_tm(s, %{st | env: [{y, bslot} | outer]}) do
        lines =
          slines ++
            [
              "  ldr r1, [r0]",
              "  cmp r1, #0",
              "  beq #{lzero}",
              "  ldr r0, [r0, #4]",
              "  str r0, [sp, ##{bslot * 4}]"
            ] ++
            sbody ++
            [
              "  b #{ljoin}",
              "#{lzero}:"
            ] ++
            zlines ++
            ["#{ljoin}:"]

        {:ok, lines, %{st | env: outer}}
      end
    end
  end

  defp emit_tm(_other, _st), do: {:error, "asm:scope"}

  defp save_args(args, st) do
    Enum.reduce_while(args, {:ok, [], [], st}, fn arg, {:ok, lines, slots, st} ->
      case emit_tm(arg, st) do
        {:ok, alines, st} ->
          slot = st.n
          st = %{st | n: slot + 1}
          store = "  str r0, [sp, ##{slot * 4}]"
          {:cont, {:ok, lines ++ alines ++ [store], slots ++ [slot], st}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  defp fun_text(export, name, sub, stores, body) do
    glob = if export, do: [".global #{name}"], else: []

    head = [
      ".text",
      ".align 2"
    ]

    sig = [
      ".type #{name}, %function",
      ".thumb_func",
      "#{name}:",
      "  push {r4, r5, r6, r7, lr}",
      "  sub sp, ##{sub}"
    ]

    tail = [
      "  add sp, ##{sub}",
      "  pop {r4, r5, r6, r7, pc}",
      "  .ltorg"
    ]

    (head ++ glob ++ sig ++ stores ++ body ++ tail)
    |> Enum.join("\n")
  end

  # push of five registers leaves sp 4 bytes off an 8-byte boundary.
  # The adjustment covers the slots and is 4 (mod 8), so a `bl` sees
  # an 8-byte-aligned sp. The result is at most 508.
  defp stack_sub(slots) do
    bytes = slots * 4
    if rem(bytes, 8) == 4, do: bytes, else: bytes + 4
  end

  defp fresh(st) do
    {".L#{st.l}", %{st | l: st.l + 1}}
  end

  defp lookup(env, name) do
    Enum.find_value(env, fn
      {^name, slot} -> slot
      _ -> nil
    end)
  end

  defp scope_ok?(funs) do
    Enum.all?(funs, fn fun ->
      fun.ret == :nat and length(fun.params) <= 4 and
        Enum.all?(fun.params, fn {_name, lay} -> lay == :nat end) and
        nat_tm?(fun.body)
    end)
  end

  defp nat_tm?({:var, name}) when is_binary(name), do: true
  defp nat_tm?(:ze), do: true
  defp nat_tm?({:su, u}), do: nat_tm?(u)

  defp nat_tm?({:call, name, args}) when is_binary(name) and length(args) <= 4 do
    Enum.all?(args, &nat_tm?/1)
  end

  defp nat_tm?({:let, name, :nat, val, body}) when is_binary(name) do
    nat_tm?(val) and nat_tm?(body)
  end

  defp nat_tm?({:match, scrut, [{:arm, "zero", [], z}, {:arm, "suc", [y], s}]})
       when is_binary(y) do
    nat_tm?(scrut) and nat_tm?(z) and nat_tm?(s)
  end

  defp nat_tm?(_other), do: false

  defp names_of(book, funs) do
    names = Emit.def_names(book, &asm_base/1, MapSet.new(@runtime))

    {names, _used} =
      Enum.reduce(funs, {names, MapSet.new(@runtime ++ Map.values(names))}, fn fun,
                                                                               {names, used} ->
        if Map.has_key?(names, fun.name) do
          {names, used}
        else
          {rn, used} = claim(asm_base(fun.name), used)
          {Map.put(names, fun.name, rn), used}
        end
      end)

    names
  end

  defp asm_base(name) do
    n =
      name
      |> String.replace("-", "_")
      |> String.replace("'", "_")

    cond do
      n == "" or n == "_" -> "x"
      String.match?(n, ~r/^[0-9]/) -> "muro_" <> n
      String.starts_with?(n, "_") -> "muro_" <> n
      MapSet.member?(@reserved, n) -> "muro_" <> n
      true -> n
    end
  end

  defp claim(base, used) do
    name = if MapSet.member?(used, base), do: bump(base, 2, used), else: base
    {name, MapSet.put(used, name)}
  end

  defp bump(base, i, used) do
    n = "#{base}_#{i}"
    if MapSet.member?(used, n), do: bump(base, i + 1, used), else: n
  end

  defp header(stem) do
    """
    @ generated by muro — do not edit
    @ #{stem}.s
    .syntax unified
    .arch armv6-m
    .cpu cortex-m0
    .thumb
    """
    |> String.trim()
  end

  defp runtime do
    """
    .text
    .align 2
    .global muro_suc
    .type muro_suc, %function
    .thumb_func
    muro_suc:
      ldr r1, =arena_at
      ldr r2, [r1]
      cmp r2, #0
      bne .Lsuc_ready
      ldr r2, =arena
      str r2, [r1]
    .Lsuc_ready:
      ldr r3, =arena_end
      subs r3, r3, r2
      cmp r3, #8
      blo muro_trap
      movs r3, #1
      str r3, [r2]
      str r0, [r2, #4]
      movs r0, r2
      adds r2, #8
      str r2, [r1]
      bx lr
      .ltorg

    .align 2
    .global muro_from_u64
    .type muro_from_u64, %function
    .thumb_func
    muro_from_u64:
      push {r4, lr}
      movs r4, r0
      ldr r0, =muro_zero_obj
    .Lfrom:
      cmp r4, #0
      beq .Lfrom_done
      bl muro_suc
      subs r4, #1
      b .Lfrom
    .Lfrom_done:
      pop {r4, pc}
      .ltorg

    .align 2
    .global muro_to_u64
    .type muro_to_u64, %function
    .thumb_func
    muro_to_u64:
      movs r1, #0
    .Lto:
      ldr r2, [r0]
      cmp r2, #0
      beq .Lto_done
      ldr r0, [r0, #4]
      adds r1, #1
      b .Lto
    .Lto_done:
      movs r0, r1
      bx lr

    .align 2
    .global muro_reset
    .type muro_reset, %function
    .thumb_func
    muro_reset:
      ldr r0, =arena
      ldr r1, =arena_at
      str r0, [r1]
      bx lr
      .ltorg

    .align 2
    .type muro_trap, %function
    .thumb_func
    muro_trap:
      bkpt #0
      b muro_trap

    .section .rodata
    .align 2
    muro_zero_obj:
      .word 0
      .word 0

    .section .bss
    .align 2
    arena_at:
      .space 4
    arena:
      .space 8192
    arena_end:
    """
    |> String.trim()
  end
end
