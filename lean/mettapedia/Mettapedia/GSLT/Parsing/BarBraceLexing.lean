import Mathlib.Data.List.Basic

/-!
# Lexing bar braces

Spellings for collection literals in which braces `{ … }` delimit one kind,
bar braces `{| … |}` another, and a standalone bar `|` marks a rest. MeTTa
words may contain `|`, so bar braces and the rest bar interact with words.
This module models a character lexer for the fragment under three rules for a
bar inside a word (`Rule`):

* `plain`: words end only at layout and braces;
* `attachedClose`: a bar immediately before a closing brace also ends a word;
* `barPunctuation`: every bar ends a word.

Under every rule a bar brace is taken first: `{|` opens bar braces and `|}`
closes them. A bar followed by layout, a brace or the end of the input stands
alone and marks a rest.

* **The spaced printer is exact under every rule** (`lex_print`), for words
  that are not empty and not the bar itself, contain no layout or brace and,
  under `barPunctuation`, no bar.
* **Compact spellings.** Under `barPunctuation`, `{|a b|}`, `{a b |$r}` and
  `{|a | $r|}` lex as intended, and a symbol spelled with a bar, `{a|b}`,
  becomes a rest pattern (`Controls.bar_punctuation_reads_compact`,
  `Controls.bar_punctuation_splits_symbols`). Under `plain`, `{|a b|}` lexes
  the word `b|` and closes with a plain brace (`Controls.plain_attaches_bar`).
  Under `attachedClose`, `{|a b|}` reads as intended, but in `{a b |$r}` the
  rest is the word `|$r`, silently an element
  (`Controls.attached_bar_is_a_word`).
* **Empty and near-empty forms.** `{||}` and `{| |}` are the empty bar braces
  under every rule (`Controls.empty_bar_braces`). `{|$r}` and `{|}` open bar
  braces and close with a plain brace, which a reader that checks closings
  refuses (`Controls.bar_brace_opens_first`).

The Prime draft reads lists with the same rest bar and the `plain` word rule:
an attached bar is part of a word, so `[a b |$r]` is a list of three elements.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.BarBraceLexing

/-- The lexemes of the collection-literal fragment. -/
inductive Lexeme where
  | openBrace
  | closeBrace
  | openBar
  | closeBar
  | bar
  | word (chars : List Char)
  deriving DecidableEq, Repr

/-- How a bar inside a word is read. -/
inductive Rule where
  /-- Words end only at layout and braces. -/
  | plain
  /-- A bar immediately before a closing brace also ends a word. -/
  | attachedClose
  /-- Every bar ends a word. -/
  | barPunctuation
  deriving DecidableEq, Repr

/-- Whether a character ends a word, given the character after it. -/
def endsWord (rule : Rule) (c : Char) (next : Option Char) : Bool :=
  c == ' ' || c == '{' || c == '}' ||
    (c == '|' &&
      match rule with
      | .plain => false
      | .attachedClose => next == some '}'
      | .barPunctuation => true)

/-- The longest word at the front of the input, and what follows it. -/
def span (rule : Rule) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
      if endsWord rule c rest.head? then ([], c :: rest)
      else
        let read := span rule rest
        (c :: read.1, read.2)

/-- A bar followed by layout, a brace or the end of the input stands alone. -/
def standsAlone : List Char → Bool
  | [] => true
  | c :: _ => c == ' ' || c == '{' || c == '}'

/-- Lex with fuel; the input length suffices. -/
def lexFuel (rule : Rule) : ℕ → List Char → Option (List Lexeme)
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, c :: rest =>
      if c == ' ' then lexFuel rule n rest
      else if c == '{' then
        match rest with
        | '|' :: after => (lexFuel rule n after).map (.openBar :: ·)
        | _ => (lexFuel rule n rest).map (.openBrace :: ·)
      else if c == '}' then (lexFuel rule n rest).map (.closeBrace :: ·)
      else if c == '|' && rest.head? == some '}' then
        (lexFuel rule n rest.tail).map (.closeBar :: ·)
      else if c == '|' && (rule == .barPunctuation || standsAlone rest) then
        (lexFuel rule n rest).map (.bar :: ·)
      else
        let read := span rule (c :: rest)
        if read.1.isEmpty then none
        else (lexFuel rule n read.2).map (.word read.1 :: ·)

/-- Lex a whole input. -/
def lex (rule : Rule) (input : List Char) : Option (List Lexeme) :=
  lexFuel rule input.length input

/-! ## The spaced printer -/

/-- The characters of a lexeme. -/
def printLexeme : Lexeme → List Char
  | .openBrace => ['{']
  | .closeBrace => ['}']
  | .openBar => ['{', '|']
  | .closeBar => ['|', '}']
  | .bar => ['|']
  | .word chars => chars

/-- Lexemes separated by single spaces. -/
def print : List Lexeme → List Char
  | [] => []
  | [lexeme] => printLexeme lexeme
  | lexeme :: rest => printLexeme lexeme ++ ' ' :: print rest

/-- A word the spaced printer can show under a rule: not empty, not the bar,
with no layout or brace, and, when every bar is punctuation, with no bar. -/
def CleanWord (rule : Rule) (chars : List Char) : Prop :=
  chars ≠ [] ∧ chars ≠ ['|'] ∧ (∀ c ∈ chars, c ≠ ' ' ∧ c ≠ '{' ∧ c ≠ '}') ∧
    (rule = .barPunctuation → '|' ∉ chars)

/-- A lexeme the spaced printer can show under a rule. -/
def Clean (rule : Rule) : Lexeme → Prop
  | .word chars => CleanWord rule chars
  | _ => True

/-- What may follow a printed lexeme: nothing, or a space. -/
def Separated (rest : List Char) : Prop := rest = [] ∨ rest.head? = some ' '

theorem span_word (rule : Rule) {chars : List Char}
    (plainChars : ∀ c ∈ chars, c ≠ ' ' ∧ c ≠ '{' ∧ c ≠ '}')
    (noBar : rule = .barPunctuation → '|' ∉ chars) {rest : List Char}
    (separated : Separated rest) : span rule (chars ++ rest) = (chars, rest) := by
  induction chars with
  | nil =>
      rcases separated with rfl | head
      · rfl
      · obtain ⟨c, more, rfl⟩ : ∃ c more, rest = c :: more := by
          cases rest with
          | nil => simp at head
          | cons c more => exact ⟨c, more, rfl⟩
        simp only [List.head?_cons, Option.some.injEq] at head
        subst head
        simp [span, endsWord]
  | cons c chars ih =>
      have cPlain := plainChars c (by simp)
      have restPlain : ∀ d ∈ chars, d ≠ ' ' ∧ d ≠ '{' ∧ d ≠ '}' :=
        fun d member => plainChars d (by simp [member])
      have restNoBar : rule = .barPunctuation → '|' ∉ chars :=
        fun punct member => noBar punct (by simp [member])
      have keeps : endsWord rule c (chars ++ rest).head? = false := by
        cases rule with
        | plain => simp [endsWord, cPlain.1, cPlain.2.1, cPlain.2.2]
        | attachedClose =>
            have nextNotClose : ((chars ++ rest).head? == some '}') = false := by
              rw [beq_eq_false_iff_ne]
              cases chars with
              | nil =>
                  rcases separated with rfl | head
                  · simp
                  · simp [head]
              | cons d more => simpa using (restPlain d (by simp)).2.2
            simp only [endsWord, nextNotClose, Bool.and_false, Bool.or_false]
            simp [cPlain.1, cPlain.2.1, cPlain.2.2]
        | barPunctuation =>
            have notBar : c ≠ '|' := fun same => noBar rfl (by simp [same])
            simp [endsWord, cPlain.1, cPlain.2.1, cPlain.2.2, notBar]
      simp only [List.cons_append, span, keeps, Bool.false_eq_true, if_false,
        ih restPlain restNoBar]

/-- One printed lexeme is lexed in one step. -/
theorem lexFuel_printLexeme (rule : Rule) {lexeme : Lexeme} (clean : Clean rule lexeme)
    (n : ℕ) {rest : List Char} (separated : Separated rest) :
    lexFuel rule (n + 1) (printLexeme lexeme ++ rest) =
      (lexFuel rule n rest).map (lexeme :: ·) := by
  have notBar : ∀ more, rest = '|' :: more → False := by
    intro more same
    rcases separated with empty | head
    · simp [empty] at same
    · simp [same] at head
  cases lexeme with
  | openBrace =>
      cases rest with
      | nil => rfl
      | cons d more =>
          have : d ≠ '|' := fun same => notBar more (by rw [same])
          simp [printLexeme, lexFuel]
  | closeBrace => simp [printLexeme, lexFuel]
  | openBar => simp [printLexeme, lexFuel]
  | closeBar => simp [printLexeme, lexFuel]
  | bar =>
      have alone : standsAlone rest = true := by
        rcases separated with rfl | head
        · rfl
        · cases rest with
          | nil => rfl
          | cons d more =>
              simp only [List.head?_cons, Option.some.injEq] at head
              simp [standsAlone, head]
      have notClose : rest.head? ≠ some '}' := by
        rcases separated with rfl | head
        · simp
        · simp [head]
      simp [printLexeme, lexFuel, alone, notClose]
  | word chars =>
      obtain ⟨nonempty, notBarWord, plainChars, noBar⟩ := clean
      obtain ⟨c, more, rfl⟩ : ∃ c more, chars = c :: more := by
        cases chars with
        | nil => exact absurd rfl nonempty
        | cons c more => exact ⟨c, more, rfl⟩
      have cPlain := plainChars c (by simp)
      have spanned := span_word rule plainChars noBar separated
      have notCloseBar : ¬ (c = '|' ∧ (more ++ rest).head? = some '}') := by
        rintro ⟨rfl, next⟩
        cases more with
        | cons d tail =>
            simp only [List.cons_append, List.head?_cons, Option.some.injEq] at next
            exact (plainChars d (by simp)).2.2 next
        | nil =>
            rcases separated with rfl | head
            · simp at next
            · simp [head] at next
      have notStandalone :
          ¬ (c = '|' ∧ (rule = .barPunctuation ∨ standsAlone (more ++ rest) = true)) := by
        rintro ⟨rfl, punct | alone⟩
        · exact noBar punct (by simp)
        · cases more with
          | cons d tail =>
              have dPlain := plainChars d (by simp)
              simp [standsAlone, dPlain.1, dPlain.2.1, dPlain.2.2] at alone
          | nil => exact notBarWord rfl
      simp only [printLexeme, List.cons_append, lexFuel, cPlain.1, cPlain.2.1, cPlain.2.2,
        beq_iff_eq, if_false, Bool.and_eq_true, Bool.or_eq_true]
      rw [if_neg notCloseBar, if_neg (by simpa using notStandalone)]
      rw [← List.cons_append, spanned]
      simp

/-- **The spaced printer is exact under every rule**, for lexemes it can
show. -/
theorem lex_print (rule : Rule) (lexemes : List Lexeme)
    (clean : ∀ lexeme ∈ lexemes, Clean rule lexeme) : lex rule (print lexemes) = some lexemes := by
  suffices fuelled :
      ∀ n, (print lexemes).length ≤ n → lexFuel rule n (print lexemes) = some lexemes from
    fuelled _ (Nat.le_refl _)
  induction lexemes with
  | nil => intro n _; cases n <;> rfl
  | cons lexeme rest ih =>
      intro n enough
      have headClean := clean lexeme (by simp)
      have restClean : ∀ l ∈ rest, Clean rule l := fun l member => clean l (by simp [member])
      have printedLength : 1 ≤ (printLexeme lexeme).length := by
        cases lexeme with
        | word chars => exact List.length_pos_of_ne_nil (show CleanWord rule chars from headClean).1
        | _ => simp [printLexeme]
      cases rest with
      | nil =>
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [print] at enough; omega⟩
          have := lexFuel_printLexeme rule headClean m (rest := []) (Or.inl rfl)
          rw [List.append_nil] at this
          simp only [print]
          rw [this]
          cases m <;> rfl
      | cons next more =>
          simp only [print, List.length_append, List.length_cons] at enough ⊢
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
          rw [show m + 2 = (m + 1) + 1 from rfl,
            lexFuel_printLexeme rule headClean (m + 1) (Or.inr rfl)]
          have spaceStep : lexFuel rule (m + 1) (' ' :: print (next :: more)) =
              lexFuel rule m (print (next :: more)) := rfl
          rw [spaceStep, ih restClean m (by omega)]
          rfl

namespace Controls

/-- `{|a b|}`: the compact spelling of a two-element bar-brace literal. -/
def compactSet : List Char := ['{', '|', 'a', ' ', 'b', '|', '}']

/-- `{a b |$r}`: a rest bar attached to its variable. -/
def attachedRest : List Char := ['{', 'a', ' ', 'b', ' ', '|', '$', 'r', '}']

/-- `{|a | $r|}`: a bar-brace literal with a named element and a rest. -/
def compactSetRest : List Char := ['{', '|', 'a', ' ', '|', ' ', '$', 'r', '|', '}']

/-- `{a|b}`: braces around a symbol spelled with a bar. -/
def barSymbol : List Char := ['{', 'a', '|', 'b', '}']

/-- **Bar punctuation reads every compact spelling as intended.** -/
theorem bar_punctuation_reads_compact :
    lex .barPunctuation compactSet =
        some [.openBar, .word ['a'], .word ['b'], .closeBar] ∧
      lex .barPunctuation attachedRest =
        some [.openBrace, .word ['a'], .word ['b'], .bar, .word ['$', 'r'], .closeBrace] := by
  decide

/-- With bars as punctuation, a set with a rest reads as intended, and a
symbol spelled with a bar is split into a rest pattern. -/
theorem bar_punctuation_splits_symbols :
    lex .barPunctuation compactSetRest =
        some [.openBar, .word ['a'], .bar, .word ['$', 'r'], .closeBar] ∧
      lex .barPunctuation barSymbol =
        some [.openBrace, .word ['a'], .bar, .word ['b'], .closeBrace] ∧
      lex .plain barSymbol = some [.openBrace, .word ['a', '|', 'b'], .closeBrace] := by
  decide

/-- **Plain words keep a closing bar**: the compact spelling `{|a b|}` lexes the
word `b|` and closes with a plain brace. -/
theorem plain_attaches_bar :
    lex .plain compactSet = some [.openBar, .word ['a'], .word ['b', '|'], .closeBrace] := by
  decide

/-- **A bar attached to a closing brace is enough for the closing, not for
the rest**: `{|a b|}` reads as intended, while in `{a b |$r}` the rest is the
word `|$r`, silently an element. -/
theorem attached_bar_is_a_word :
    lex .attachedClose compactSet = some [.openBar, .word ['a'], .word ['b'], .closeBar] ∧
      lex .attachedClose attachedRest =
        some [.openBrace, .word ['a'], .word ['b'], .word ['|', '$', 'r'], .closeBrace] := by
  decide

/-- The empty bar braces, written compactly or spaced, under every rule. -/
theorem empty_bar_braces (rule : Rule) :
    lex rule ['{', '|', '|', '}'] = some [.openBar, .closeBar] ∧
      lex rule ['{', '|', ' ', '|', '}'] = some [.openBar, .closeBar] := by
  cases rule <;> decide

/-- **The opening bar brace is taken first**, under every rule: `{|$r}` opens
bar braces and closes with a plain brace, and `{|}` is an opening bar brace
and a plain closing brace. A reader that checks closings refuses both, and a
rest with no named element must be spaced, `{ | $r}`. -/
theorem bar_brace_opens_first (rule : Rule) :
    lex rule ['{', '|', '$', 'r', '}'] = some [.openBar, .word ['$', 'r'], .closeBrace] ∧
      lex rule ['{', '|', '}'] = some [.openBar, .closeBrace] ∧
      lex rule ['{', ' ', '|', ' ', '$', 'r', '}'] =
        some [.openBrace, .bar, .word ['$', 'r'], .closeBrace] := by
  cases rule <;> decide

end Controls

end Mettapedia.GSLT.Parsing.BarBraceLexing
