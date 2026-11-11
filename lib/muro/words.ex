defmodule Muro.Words do
  @moduledoc """
  Words and operators the parser accepts.

  `Muro.Parser` decides where a word is a keyword. `Muro.Lexer` classifies
  the same words in every position. Both read these lists, so a highlighter
  cannot drift from the grammar.
  """

  @decl ~w(def data session conform meet place scheme move endpoint read talk choreography seat link relay import param where)
  # A book entry on its own. `place` and `relay` are declaration words too;
  # the parser tells those from a type by what follows the word.
  @book ~w(def data param import session conform where)
  @pay_stop ~w(end send recv choose branch rec case on done stop put get pick0 pick1 cover where)
  @reserved ~w(end send recv choose branch rec case done stop put get pick0 pick1 cover match on Nat Bit Unit Vec dual seen)
  @proc ~w(done stop put get pick0 pick1 cover rec match end send recv choose branch on)
  @proc_start ~w(done stop put get pick0 pick1 cover rec match)
  @proto_head ~w(end send recv choose branch rec)

  # `with` is a name in `seen role with role`. It does not end a payload.
  @talk_stop ~w(over say offer)
  @talk @talk_stop ++ ~w(with)
  @choreo ~w(roles chooses)
  @place ~w(ambient node any fixed stay cross at buffer)
  @temporal ~w(forall always eventually leads_to implies or and not true false inbox is empty full stopped has first second third st nd rd th)
  @repr ~w(else boolean integer nil interned string list optional nullable tuple map_of map open)

  @types ~w(Atom String Type Nat I64 U8 U32 U64 WBool Opt F32 Tensor Unit Empty Stream Always Bit Vec run spec evidence internal)
  @nu ["ν", "nu"]
  @extra_decl ["temporal", "repr"]

  @term ~w(matchEmpty rewrite unfold motive let in uncons packI toI64 toU8 toU32 toU64 toNat asU8 asU32 asU64 asI64 bisim addi subi muli addc subc mulc divi remi eqi lti lei andi ori xori noti shli shri addt head tail refl fst snd suc tt b0 b1 wsome wtrue wfalse wnone rep dual seen strCat strLen strEq)

  # `omega` is the ASCII spelling of the grade ω. It is an operator word,
  # the same way `lam` is the ASCII spelling of λ.
  @word_ops ["lam1", "lam", "Pi", "omega"]
  @pi ["Π", "Pi"]
  @lam ["λ", "lam"]
  @elam ["λ¹", "lam1", "λ", "lam"]

  @symbolic [
    ":=",
    "=>",
    "==",
    "::",
    "->",
    "-o",
    "<=",
    "λ¹",
    "⊸",
    "→",
    "×",
    "⊎",
    "≡",
    "≤",
    "⊢",
    "λ",
    "Π",
    "ω",
    "~",
    "*",
    "+",
    "-",
    "=",
    "<"
  ]

  @naming ~w(def data session conform meet place scheme talk choreography param endpoint seat link temporal repr) ++
            @nu

  @keywords @pay_stop ++
              @proc ++
              @talk ++
              @choreo ++
              @place ++
              @temporal ++
              @repr ++
              @term

  @lexicon (
             typed =
               Enum.map(@types, &{&1, :type}) ++
                 Enum.map(@decl ++ @nu ++ @extra_decl, &{&1, :declaration}) ++
                 Enum.map(@word_ops, &{&1, :operator}) ++
                 Enum.map(@keywords, &{&1, :keyword})

             {rows, _} =
               Enum.reduce(typed, {[], %{}}, fn {word, kind}, {rows, seen} ->
                 if Map.has_key?(seen, word) do
                   {rows, seen}
                 else
                   {[{word, kind} | rows], Map.put(seen, word, kind)}
                 end
               end)

             Enum.reverse(rows)
           )

  @kind_by Map.new(@lexicon)

  @doc "Declaration words. Membership is exact, as in the parser."
  def decl_words, do: @decl

  def decl_word?(name) when is_binary(name), do: name in @decl

  @doc "Declaration words that end a surrounding form on their own."
  def book_words, do: @book

  @doc "Words that end a payload type."
  def pay_stop_words, do: @pay_stop

  def pay_stop?(name) when is_binary(name), do: name in @pay_stop

  @doc "Names a session argument must not take."
  def reserved_session_words, do: @reserved

  def reserved_session?(name) when is_binary(name), do: name in @reserved

  @doc "Process words. A value cannot be one of these names."
  def proc_words, do: @proc

  def proc_word?(name) when is_binary(name), do: name in @proc

  @doc "Words that open a process form, besides a bare name or a parenthesis."
  def proc_start_words, do: @proc_start

  @doc "Words that open a protocol inside a session argument."
  def proto_head_words, do: @proto_head

  def talk_words, do: @talk

  @doc "Talk words that end a payload. `with` is not one of them."
  def talk_stop_words, do: @talk_stop
  def choreo_words, do: @choreo
  def place_words, do: @place
  def temporal_words, do: @temporal
  def repr_words, do: @repr

  def nu_words, do: @nu
  def pi_words, do: @pi
  def lam_words, do: @lam
  def elam_words, do: @elam

  def arrow_words, do: ["→", "->"]
  def times_words, do: ["×", "*"]
  def sum_words, do: ["⊎"]
  def cons_words, do: ["::"]
  def le_words, do: ["<=", "≤"]
  def equiv_words, do: ["≡", "=="]

  @doc "Linear and affine arrows, longest forms first."
  def earrow_forms, do: [{"⊸", :lin}, {"-o", :lin}, {"→", :aff}, {"->", :aff}]

  @doc "Operators, longest first. `⊢` is printed in evidence and is not a parse error."
  def operators do
    Enum.sort_by(@symbolic ++ @word_ops, &byte_size/1, :desc)
  end

  @doc "Symbolic operators. A following identifier character does not extend them."
  def symbolic_operators do
    Enum.sort_by(@symbolic, &byte_size/1, :desc)
  end

  @doc "`[]`, the nil value, as one token."
  def nil_token, do: "[]"

  @doc "`%0` and `%1`. `%10` is not one of these."
  def mult_tokens, do: ["%0", "%1"]

  @doc "Declaration words whose next name is the name being defined."
  def naming_words, do: @naming

  def naming?(word) when is_binary(word), do: word in @naming

  @doc "Every classified word and its lexer kind. The first kind wins."
  def lexicon, do: @lexicon

  def kind(word) when is_binary(word), do: Map.get(@kind_by, word)
end
