import Mettapedia.Data.String.UnicodeDecimal
import Mettapedia.GSLT.LanguageDef.RegexDecimalValues
import Mettapedia.Computability.RegularLanguages.RegexTraceRendering

/-!
# Replacement templates as syntax and original-observation rendering

The source forms are `$$`, `$` followed by a maximal nonempty decimal run,
and `${...}`. Braces contain either a complete decimal reference or a name.
The supplied decimal-value provider permits mixed scripts; arithmetic is
ordinary positional base ten. Unknown references are separate from malformed
syntax, and declared unmatched groups expand to empty text.

The lexical judgments do not invoke the decoder. The decoder's finite work
parameter exposes unfinished work; its ordinary entry point derives enough
work from the source length rather than imposing a default cutoff.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexReplacementTemplate

open Mettapedia.Data.String
open Mettapedia.Computability.RegularLanguages
open Mettapedia.Computability.RegularLanguages.RegexMatchObservations (Observation)

abbrev Digit := UnicodeDecimal.Digit
abbrev DecimalProvider := Char → Option Digit

structure DecimalLaws (decimal : DecimalProvider) : Prop where
  dollar : decimal '$' = none
  brace : decimal '{' = none

inductive Reference where
  | index (value : Nat)
  | name (value : String)
  deriving DecidableEq, Repr

inductive Piece where
  | literal (value : Char)
  | reference (value : Reference)
  deriving DecidableEq, Repr

inductive SyntaxError where
  | emptyInput
  | danglingDollar
  | invalidDollar (following : Char)
  | unclosedReference
  | emptyReference
  deriving DecidableEq, Repr

def digitRun (decimal : DecimalProvider) : List Char → List Digit × List Char
  | [] => ([], [])
  | character :: rest =>
      match decimal character with
      | none => ([], character :: rest)
      | some digit =>
          let after := digitRun decimal rest
          (digit :: after.1, after.2)

/-- Maximality is part of the grammar: stopping at another decimal is not a
valid numeric-reference token. -/
inductive Digits (decimal : DecimalProvider) : List Char → List Digit → List Char → Prop
  | nil : Digits decimal [] [] []
  | stop (character : Char) (rest : List Char) (notDigit : decimal character = none) :
      Digits decimal (character :: rest) [] (character :: rest)
  | cons (character : Char) (rest tail : List Char) (digit : Digit) (digits : List Digit)
      (recognized : decimal character = some digit) (after : Digits decimal rest digits tail) :
      Digits decimal (character :: rest) (digit :: digits) tail

theorem digitRun_iff (decimal : DecimalProvider) (source : List Char)
    (digits : List Digit) (tail : List Char) :
    digitRun decimal source = (digits, tail) ↔ Digits decimal source digits tail := by
  induction source generalizing digits tail with
  | nil =>
      constructor
      · intro same; cases same; exact .nil
      · intro parsed; cases parsed; rfl
  | cons character rest ih =>
      cases recognized : decimal character with
      | none =>
          constructor
          · intro same
            simp only [digitRun, recognized, Prod.mk.injEq] at same
            rcases same with ⟨rfl, rfl⟩
            exact .stop character rest recognized
          · intro parsed
            cases parsed with
            | stop => simp [digitRun, recognized]
            | cons _ _ _ _ _ accepted _ => simp [recognized] at accepted
      | some digit =>
          constructor
          · intro same
            simp only [digitRun, recognized, Prod.mk.injEq] at same
            rcases same with ⟨rfl, rfl⟩
            exact .cons character rest _ digit _ recognized ((ih _ _).1 rfl)
          · intro parsed
            cases parsed with
            | stop _ _ rejected => simp [recognized] at rejected
            | cons _ _ _ value values accepted after =>
                have identical : value = digit := by simpa [recognized] using accepted.symm
                subst value
                simp only [digitRun, recognized]
                rw [(ih values _).2 after]

theorem Digits.tail_length {decimal : DecimalProvider} {source tail : List Char}
    {digits : List Digit} (read : Digits decimal source digits tail) :
    tail.length ≤ source.length := by
  induction read with
  | nil => simp
  | stop => exact Nat.le_refl _
  | cons _ _ _ _ _ _ _ ih => simp only [List.length_cons]; omega

theorem Digits.value {decimal : DecimalProvider} {source tail : List Char}
    {digits : List Digit} (read : Digits decimal source digits tail) :
    ∃ portion, source = portion ++ tail ∧ UnicodeDecimal.recognize decimal portion = some digits := by
  induction read with
  | nil => exact ⟨[], rfl, rfl⟩
  | stop => exact ⟨[], rfl, rfl⟩
  | cons character rest tail digit digits accepted after ih =>
      obtain ⟨portion, source, recognized⟩ := ih
      refine ⟨character :: portion, by simp [source], ?_⟩
      simp only [UnicodeDecimal.recognize] at recognized ⊢
      simp [accepted, recognized]

def bracket : List Char → Option (List Char × List Char)
  | [] => none
  | character :: rest =>
      if character = '}' then some ([], rest)
      else (bracket rest).map (fun result => (character :: result.1, result.2))

/-- The first closing brace delimits a reference. -/
def Bracket (source body tail : List Char) : Prop :=
  source = body ++ '}' :: tail ∧ '}' ∉ body

theorem bracket_iff (source body tail : List Char) :
    bracket source = some (body, tail) ↔ Bracket source body tail := by
  induction source generalizing body tail with
  | nil => simp [bracket, Bracket]
  | cons character rest ih =>
      by_cases closes : character = '}'
      · subst character
        constructor
        · intro same
          simp only [bracket, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at same
          rcases same with ⟨rfl, rfl⟩
          exact ⟨rfl, by simp⟩
        · rintro ⟨source, noBrace⟩
          cases body with
          | nil => simp_all [bracket]
          | cons head body =>
              have headSame : head = '}' := by simpa using (List.cons.inj source).1.symm
              simp [headSame] at noBrace
      · constructor
        · intro same
          simp only [bracket, closes, ↓reduceIte, Option.map_eq_some_iff] at same
          obtain ⟨⟨inside, after⟩, decoded, result⟩ := same
          cases result
          obtain ⟨source, noBrace⟩ := (ih inside after).1 decoded
          exact ⟨by simp [source], by simp [Ne.symm closes, noBrace]⟩
        · rintro ⟨source, noBrace⟩
          cases body with
          | nil => simp_all
          | cons head body =>
              have same := (List.cons.inj source).1
              have tails := (List.cons.inj source).2
              subst head
              have decoded := (ih body tail).2 ⟨tails, fun member => noBrace (by simp [member])⟩
              simp [bracket, closes, decoded]

inductive BracedReference (decimal : DecimalProvider) : List Char → Reference → Prop
  | numeric (source : List Char) (digits : List Digit) (nonempty : source ≠ [])
      (recognized : UnicodeDecimal.recognize decimal source = some digits) :
      BracedReference decimal source (.index (UnicodeDecimal.positionalValue digits))
  | named (source : List Char) (nonempty : source ≠ [])
      (notNumeric : UnicodeDecimal.recognize decimal source = none) :
      BracedReference decimal source (.name (String.ofList source))

def bracedReference (decimal : DecimalProvider) (source : List Char) : Except SyntaxError Reference :=
  if source = [] then .error .emptyReference
  else match UnicodeDecimal.recognize decimal source with
    | none => .ok (.name (String.ofList source))
    | some digits => .ok (.index (UnicodeDecimal.accumulate digits 0))

theorem bracedReference_iff (decimal : DecimalProvider) (source : List Char) (reference : Reference) :
    bracedReference decimal source = .ok reference ↔ BracedReference decimal source reference := by
  by_cases empty : source = []
  · subst source
    constructor
    · simp [bracedReference]
    · intro read; cases read <;> contradiction
  · cases recognized : UnicodeDecimal.recognize decimal source with
    | none =>
        constructor
        · intro same
          simp only [bracedReference, empty, ↓reduceIte, recognized, Except.ok.injEq] at same
          subst reference; exact .named source empty recognized
        · intro read
          cases read with
          | numeric _ _ accepted => simp [recognized] at accepted
          | named => simp [bracedReference, empty, recognized]
    | some digits =>
        have positional : UnicodeDecimal.accumulate digits 0 = UnicodeDecimal.positionalValue digits := by
          simpa using UnicodeDecimal.accumulate_positional digits 0
        constructor
        · intro same
          simp only [bracedReference, empty, ↓reduceIte, recognized, positional, Except.ok.injEq] at same
          subst reference; exact .numeric source digits empty recognized
        · intro read
          cases read with
          | numeric values _ accepted =>
              have equal : values = digits := by simpa [recognized] using accepted.symm
              subst values
              simp [bracedReference, empty, recognized, positional]
          | named _ rejected => simp [recognized] at rejected

inductive Token (decimal : DecimalProvider) : List Char → Piece → List Char → Prop
  | literal (character : Char) (rest : List Char) (ordinary : character ≠ '$') :
      Token decimal (character :: rest) (.literal character) rest
  | dollar (rest : List Char) : Token decimal ('$' :: '$' :: rest) (.literal '$') rest
  | numeric (source tail : List Char) (digit : Digit) (digits : List Digit)
      (read : Digits decimal source (digit :: digits) tail) :
      Token decimal ('$' :: source) (.reference (.index (UnicodeDecimal.positionalValue (digit :: digits)))) tail
  | braced (source body tail : List Char) (reference : Reference)
      (read : Bracket source body tail) (referenceRead : BracedReference decimal body reference) :
      Token decimal ('$' :: '{' :: source) (.reference reference) tail

def token (decimal : DecimalProvider) : List Char → Except SyntaxError (Piece × List Char)
  | [] => .error .emptyInput
  | character :: rest =>
      if character ≠ '$' then .ok (.literal character, rest)
      else match rest with
        | [] => .error .danglingDollar
        | following :: source =>
            if following = '$' then .ok (.literal '$', source)
            else if following = '{' then
              match bracket source with
              | none => .error .unclosedReference
              | some (body, tail) =>
                  match bracedReference decimal body with
                  | .error reason => .error reason
                  | .ok reference => .ok (.reference reference, tail)
            else match decimal following with
              | none => .error (.invalidDollar following)
              | some digit =>
                  let after := digitRun decimal source
                  .ok (.reference (.index (UnicodeDecimal.accumulate (digit :: after.1) 0)), after.2)

theorem token_sound (decimal : DecimalProvider) (source : List Char) (piece : Piece)
    (tail : List Char) (read : token decimal source = .ok (piece, tail)) :
    Token decimal source piece tail := by
  cases source with
  | nil => simp [token] at read
  | cons character rest =>
      by_cases ordinary : character ≠ '$'
      · simp [token, ordinary] at read
        rcases read with ⟨rfl, rfl⟩
        exact .literal character rest ordinary
      · have equal : character = '$' := by simpa using ordinary
        subst character
        cases rest with
        | nil => simp [token] at read
        | cons following source =>
            by_cases escaped : following = '$'
            · subst following
              simp only [token, ne_eq, not_true_eq_false, ↓reduceIte,
                Except.ok.injEq, Prod.mk.injEq] at read
              rcases read with ⟨rfl, rfl⟩
              exact .dollar source
            · by_cases opens : following = '{'
              · subst following
                cases split : bracket source with
                | none => simp [token, split] at read
                | some pair =>
                    rcases pair with ⟨body, after⟩
                    cases referenceRead : bracedReference decimal body with
                    | error reason => simp [token, split, referenceRead] at read
                    | ok reference =>
                        simp only [token, ne_eq, not_true_eq_false, ↓reduceIte, split,
                          referenceRead] at read
                        rcases read with ⟨rfl, rfl⟩
                        exact .braced source body tail reference
                          ((bracket_iff source body tail).1 split)
                          ((bracedReference_iff decimal body reference).1 referenceRead)
              · cases recognized : decimal following with
                | none => simp [token, escaped, opens, recognized] at read
                | some digit =>
                    have positional := UnicodeDecimal.accumulate_positional
                      (digit :: (digitRun decimal source).1) 0
                    simp only [zero_mul, zero_add] at positional
                    simp only [token, ne_eq, not_true_eq_false, ↓reduceIte, escaped, opens,
                      recognized, positional, Except.ok.injEq, Prod.mk.injEq] at read
                    rcases read with ⟨rfl, rfl⟩
                    exact .numeric (following :: source) _ digit _
                      (.cons following source _ digit _ recognized ((digitRun_iff decimal source _ _).1 rfl))

theorem Token.decoded {decimal : DecimalProvider} (laws : DecimalLaws decimal)
    {source tail : List Char} {piece : Piece} (read : Token decimal source piece tail) :
    token decimal source = .ok (piece, tail) := by
  cases read with
  | literal character rest ordinary => simp [token, ordinary]
  | dollar rest => simp [token]
  | numeric source tail digit digits recognized =>
      cases recognized with
      | cons character rest _ _ _ accepted after =>
          have notDollar : character ≠ '$' := by
            intro equal; subst character; simp [laws.dollar] at accepted
          have notBrace : character ≠ '{' := by
            intro equal; subst character; simp [laws.brace] at accepted
          have afterRead := (digitRun_iff decimal rest digits tail).2 after
          simp [token, notDollar, notBrace, accepted, afterRead,
            UnicodeDecimal.accumulate_positional]
  | braced source body tail reference read referenceRead =>
      have split := (bracket_iff source body tail).2 read
      have value := (bracedReference_iff decimal body reference).2 referenceRead
      simp [token, split, value]

theorem token_iff (decimal : DecimalProvider) (laws : DecimalLaws decimal)
    (source : List Char) (piece : Piece) (tail : List Char) :
    token decimal source = .ok (piece, tail) ↔ Token decimal source piece tail :=
  ⟨token_sound decimal source piece tail, Token.decoded laws⟩

theorem Token.tail_lt {decimal : DecimalProvider} {source tail : List Char} {piece : Piece}
    (read : Token decimal source piece tail) : tail.length < source.length := by
  cases read with
  | literal => simp
  | dollar => simp
  | numeric source tail digit digits read =>
      have bound := read.tail_length
      simp only [List.length_cons]
      omega
  | braced source body tail reference read _ =>
      rcases read with ⟨rfl, _⟩
      simp only [List.length_cons, List.length_append]
      omega

inductive Parsed (decimal : DecimalProvider) : List Char → List Piece → Prop
  | nil : Parsed decimal [] []
  | cons (source tail : List Char) (piece : Piece) (pieces : List Piece)
      (first : Token decimal source piece tail) (rest : Parsed decimal tail pieces) :
      Parsed decimal source (piece :: pieces)

inductive DecodeResult where
  | complete (pieces : List Piece)
  | malformed (reason : SyntaxError)
  | incomplete
  deriving DecidableEq, Repr

def decodeAux (decimal : DecimalProvider) : Nat → List Char → DecodeResult
  | _, [] => .complete []
  | 0, _ :: _ => .incomplete
  | fuel + 1, source@(_ :: _) =>
      match token decimal source with
      | .error reason => .malformed reason
      | .ok (piece, tail) =>
          match decodeAux decimal fuel tail with
          | .complete pieces => .complete (piece :: pieces)
          | .malformed reason => .malformed reason
          | .incomplete => .incomplete

theorem decodeAux_sound (decimal : DecimalProvider) (fuel : Nat) (source : List Char)
    (pieces : List Piece) (read : decodeAux decimal fuel source = .complete pieces) :
    Parsed decimal source pieces := by
  induction fuel generalizing source pieces with
  | zero =>
      cases source with
      | nil => cases read; exact .nil
      | cons => simp [decodeAux] at read
  | succ fuel ih =>
      cases source with
      | nil => cases read; exact .nil
      | cons character rest =>
          cases first : token decimal (character :: rest) with
          | error reason => simp [decodeAux, first] at read
          | ok pair =>
              rcases pair with ⟨piece, tail⟩
              cases after : decodeAux decimal fuel tail with
              | malformed reason => simp [decodeAux, first, after] at read
              | incomplete => simp [decodeAux, first, after] at read
              | complete remaining =>
                  simp only [decodeAux, first, after, DecodeResult.complete.injEq] at read
                  subst pieces
                  exact .cons _ tail piece remaining (token_sound decimal _ piece tail first)
                    (ih tail remaining after)

theorem Parsed.decoded {decimal : DecimalProvider} (laws : DecimalLaws decimal)
    {source : List Char} {pieces : List Piece} (parsed : Parsed decimal source pieces)
    (fuel : Nat) (enough : source.length ≤ fuel) :
    decodeAux decimal fuel source = .complete pieces := by
  induction parsed generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons source tail piece pieces first rest ih =>
      have bound := first.tail_lt
      cases source with
      | nil => simp at bound
      | cons character source =>
          cases fuel with
          | zero => simp at enough
          | succ fuel =>
              have sufficient : tail.length ≤ fuel := by simp only [List.length_cons] at *; omega
              simp only [decodeAux, first.decoded laws, ih fuel sufficient]

def decode (decimal : DecimalProvider) (source : List Char) : DecodeResult :=
  decodeAux decimal source.length source

theorem decode_iff (decimal : DecimalProvider) (laws : DecimalLaws decimal)
    (source : List Char) (pieces : List Piece) :
    decode decimal source = .complete pieces ↔ Parsed decimal source pieces :=
  ⟨decodeAux_sound decimal source.length source pieces,
    fun read => read.decoded laws source.length (Nat.le_refl _)⟩

theorem decodeAux_not_incomplete (decimal : DecimalProvider) (fuel : Nat) (source : List Char)
    (enough : source.length ≤ fuel) : decodeAux decimal fuel source ≠ .incomplete := by
  induction fuel generalizing source with
  | zero => cases source <;> simp_all [decodeAux]
  | succ fuel ih =>
      cases source with
      | nil => simp [decodeAux]
      | cons character rest =>
          cases first : token decimal (character :: rest) with
          | error reason => simp [decodeAux, first]
          | ok pair =>
              rcases pair with ⟨piece, tail⟩
              have bound := (token_sound decimal _ piece tail first).tail_lt
              have remaining : tail.length ≤ fuel := by simp only [List.length_cons] at *; omega
              have complete := ih tail remaining
              cases after : decodeAux decimal fuel tail <;> simp_all [decodeAux]

theorem decode_not_incomplete (decimal : DecimalProvider) (source : List Char) :
    decode decimal source ≠ .incomplete := decodeAux_not_incomplete decimal source.length source (Nat.le_refl _)

structure Layout where
  groups : Nat
  names : List (String × Nat) := []
  deriving DecidableEq, Repr

def findName (name : String) : List (String × Nat) → Option Nat
  | [] => none
  | (head, index) :: rest => if head = name then some index else findName name rest

inductive Named (name : String) : List (String × Nat) → Nat → Prop
  | here (index : Nat) (rest : List (String × Nat)) : Named name ((name, index) :: rest) index
  | there (head : String) (value index : Nat) (rest : List (String × Nat))
      (different : head ≠ name) (later : Named name rest index) :
      Named name ((head, value) :: rest) index

theorem findName_iff (name : String) (names : List (String × Nat)) (index : Nat) :
    findName name names = some index ↔ Named name names index := by
  induction names with
  | nil => constructor <;> intro read <;> cases read
  | cons head rest ih =>
      rcases head with ⟨head, value⟩
      by_cases equal : head = name
      · subst head
        constructor
        · intro read
          simp only [findName, ↓reduceIte, Option.some.injEq] at read
          subst index
          exact .here value rest
        · intro read
          cases read with
          | here => simp [findName]
          | there _ _ _ _ different _ => exact False.elim (different rfl)
      · constructor
        · intro read
          simp only [findName, equal, ↓reduceIte] at read
          exact .there head value index rest equal (ih.1 read)
        · intro read
          cases read with
          | here => contradiction
          | there _ _ _ _ _ later => simp only [findName, equal, ↓reduceIte]; exact ih.2 later

inductive Resolves (layout : Layout) : Reference → Nat → Prop
  | index (index : Nat) (declared : index < layout.groups) : Resolves layout (.index index) index
  | named (name : String) (index : Nat) (found : Named name layout.names index)
      (declared : index < layout.groups) : Resolves layout (.name name) index

def resolve (layout : Layout) : Reference → Option Nat
  | .index index => if index < layout.groups then some index else none
  | .name name => (findName name layout.names).filter (fun index => decide (index < layout.groups))

theorem resolve_iff (layout : Layout) (reference : Reference) (index : Nat) :
    resolve layout reference = some index ↔ Resolves layout reference index := by
  cases reference with
  | index value =>
      by_cases declared : value < layout.groups
      · constructor
        · intro read
          simp only [resolve, declared, ↓reduceIte, Option.some.injEq] at read
          subst index; exact .index value declared
        · intro read; cases read; simp [resolve, declared]
      · constructor
        · simp [resolve, declared]
        · intro read; cases read; contradiction
  | name name =>
      constructor
      · intro read
        obtain ⟨found, declared⟩ := Option.filter_eq_some_iff.mp read
        exact .named name index ((findName_iff name layout.names index).1 found) (by simpa using declared)
      · intro read
        cases read with
        | named _ _ found declared =>
            simp only [resolve, (findName_iff name layout.names index).2 found,
              Option.filter_some, decide_eq_true_eq, declared, ↓reduceIte]

theorem Resolves.bound {layout : Layout} {reference : Reference} {index : Nat}
    (resolved : Resolves layout reference index) : index < layout.groups := by
  cases resolved with
  | index _ bound | named _ _ _ bound => exact bound

inductive Operation where
  | literal (character : Char)
  | capture (index : Nat)
  deriving DecidableEq, Repr

inductive ReferenceError where
  | unknown (reference : Reference)
  deriving DecidableEq, Repr

def prepare (layout : Layout) : List Piece → Except ReferenceError (List Operation)
  | [] => .ok []
  | .literal character :: pieces =>
      match prepare layout pieces with
      | .error reason => .error reason
      | .ok operations => .ok (.literal character :: operations)
  | .reference reference :: pieces =>
      match resolve layout reference with
      | none => .error (.unknown reference)
      | some index =>
          match prepare layout pieces with
          | .error reason => .error reason
          | .ok operations => .ok (.capture index :: operations)

inductive Prepared (layout : Layout) : List Piece → List Operation → Prop
  | nil : Prepared layout [] []
  | literal (character : Char) (pieces : List Piece) (operations : List Operation)
      (after : Prepared layout pieces operations) :
      Prepared layout (.literal character :: pieces) (.literal character :: operations)
  | capture (reference : Reference) (index : Nat) (pieces : List Piece) (operations : List Operation)
      (resolved : Resolves layout reference index) (after : Prepared layout pieces operations) :
      Prepared layout (.reference reference :: pieces) (.capture index :: operations)

theorem prepare_iff (layout : Layout) (pieces : List Piece) (operations : List Operation) :
    prepare layout pieces = .ok operations ↔ Prepared layout pieces operations := by
  induction pieces generalizing operations with
  | nil =>
      constructor
      · intro read; cases read; exact .nil
      · intro read; cases read; rfl
  | cons piece pieces ih =>
      cases piece with
      | literal character =>
          constructor
          · intro read
            cases after : prepare layout pieces with
            | error reason => simp [prepare, after] at read
            | ok ops =>
                simp only [prepare, after, Except.ok.injEq] at read
                subst operations
                exact .literal character pieces ops ((ih ops).1 after)
          · intro read
            cases read with
            | literal _ _ _ after => simp only [prepare, (ih _).2 after]
      | reference reference =>
          constructor
          · intro read
            cases resolved : resolve layout reference with
            | none => simp [prepare, resolved] at read
            | some index =>
                cases after : prepare layout pieces with
                | error reason => simp [prepare, resolved, after] at read
                | ok ops =>
                    simp only [prepare, resolved, after, Except.ok.injEq] at read
                    subst operations
                    exact .capture reference index pieces ops
                      ((resolve_iff layout reference index).1 resolved) ((ih ops).1 after)
          · intro read
            cases read with
            | capture _ index _ _ resolved after =>
                simp only [prepare, (resolve_iff layout reference index).2 resolved, (ih _).2 after]

def Bounded (groups : Nat) (operations : List Operation) : Prop :=
  ∀ index, .capture index ∈ operations → index < groups

theorem Prepared.bounded {layout : Layout} {pieces : List Piece} {operations : List Operation}
    (prepared : Prepared layout pieces operations) : Bounded layout.groups operations := by
  intro index member
  induction prepared with
  | nil => simp at member
  | literal character pieces operations after ih =>
      simp only [List.mem_cons] at member
      rcases member with impossible | member
      · cases impossible
      exact ih member
  | capture reference value pieces operations resolved after ih =>
      rcases List.mem_cons.mp member with same | later
      · have equal : index = value := Operation.capture.inj same
        subst index; exact resolved.bound
      · exact ih later

def insert (input : List Char) (observation : Observation) : Operation → List Char
  | .literal character => [character]
  | .capture index => (RegexTraceRendering.captureText input observation index).getD []

def render (input : List Char) (observation : Observation) (operations : List Operation) : List Char :=
  operations.flatMap (insert input observation)

/-- Declarative expansion refers to the original capture slots. It has no
rule for an undeclared slot. Nonparticipation has its own rule. -/
inductive Expansion (input : List Char) (observation : Observation) :
    List Operation → List Char → Prop
  | nil : Expansion input observation [] []
  | literal (character : Char) (operations : List Operation) (output : List Char)
      (after : Expansion input observation operations output) :
      Expansion input observation (.literal character :: operations) (character :: output)
  | unmatched (index : Nat) (operations : List Operation) (output : List Char)
      (absent : observation.captures[index]? = some none)
      (after : Expansion input observation operations output) :
      Expansion input observation (.capture index :: operations) output
  | captured (index : Nat) (span : RegexMatchObservations.Span)
      (operations : List Operation) (output : List Char)
      (present : observation.captures[index]? = some (some span))
      (after : Expansion input observation operations output) :
      Expansion input observation (.capture index :: operations)
        (RegexTraceRendering.slice input span.start span.stop ++ output)

theorem Expansion.exact {input : List Char} {observation : Observation}
    {operations : List Operation} {output : List Char}
    (expands : Expansion input observation operations output) :
    render input observation operations = output := by
  induction expands with
  | nil => rfl
  | literal character operations output after ih =>
      simp only [render, List.flatMap_cons, insert, List.singleton_append]
      exact congrArg (character :: ·) ih
  | unmatched index operations output absent after ih =>
      simp only [render, List.flatMap_cons, insert, RegexTraceRendering.captureText_absent _ _ _ absent,
        Option.getD_none, List.nil_append]
      exact ih
  | captured index span operations output present after ih =>
      simp only [render, List.flatMap_cons, insert, RegexTraceRendering.captureText, present,
        Option.join_some, Option.map_some, Option.getD_some]
      exact congrArg (RegexTraceRendering.slice input span.start span.stop ++ ·) ih

theorem render_authorized (input : List Char) (observation : Observation) (operations : List Operation)
    (bounded : Bounded observation.captures.length operations) :
    Expansion input observation operations (render input observation operations) := by
  induction operations with
  | nil => exact .nil
  | cons operation operations ih =>
      have after := ih (fun index member => bounded index (List.mem_cons_of_mem _ member))
      cases operation with
      | literal character =>
          simpa only [render, List.flatMap_cons, insert, List.singleton_append] using
            Expansion.literal character operations _ after
      | capture index =>
          have bound := bounded index (by simp)
          have existsSlot := List.getElem?_eq_getElem (l := observation.captures) bound
          cases capture : observation.captures[index] with
          | none =>
              have absent : observation.captures[index]? = some none := by simpa [capture] using existsSlot
              simpa only [render, List.flatMap_cons, insert,
                RegexTraceRendering.captureText_absent _ _ _ absent, Option.getD_none, List.nil_append] using
                Expansion.unmatched index operations _ absent after
          | some span =>
              have present : observation.captures[index]? = some (some span) := by simpa [capture] using existsSlot
              simpa only [render, List.flatMap_cons, insert, RegexTraceRendering.captureText, present,
                Option.join_some, Option.map_some, Option.getD_some] using
                Expansion.captured index span operations _ present after

theorem render_iff (input : List Char) (observation : Observation) (operations : List Operation)
    (bounded : Bounded observation.captures.length operations) (output : List Char) :
    render input observation operations = output ↔ Expansion input observation operations output := by
  constructor
  · intro same; rw [← same]; exact render_authorized input observation operations bounded
  · exact Expansion.exact

/-- Template expansion consumes the same original observations as literal
replacement. It does not restart search on the inserted text. -/
theorem replacement_exact (input : List Char) (operations : List Operation)
    {observations : List Observation}
    (trace : RegexIteration.Trace input.length none observations) (output : List Char) :
    RegexTraceRendering.Rendering (fun observation => render input observation operations)
      input observations output ↔
    RegexTraceRendering.renderTrace (fun observation => render input observation operations)
      input observations = output :=
  RegexTraceRendering.replace_eq_renderTrace _ input trace output

inductive CompileResult where
  | ready (operations : List Operation)
  | malformed (reason : SyntaxError)
  | unknown (reason : ReferenceError)
  | incomplete
  deriving DecidableEq, Repr

def compile (decimal : DecimalProvider) (layout : Layout) (source : List Char) : CompileResult :=
  match decode decimal source with
  | .incomplete => .incomplete
  | .malformed reason => .malformed reason
  | .complete pieces =>
      match prepare layout pieces with
      | .error reason => .unknown reason
      | .ok operations => .ready operations

theorem compile_iff (decimal : DecimalProvider) (laws : DecimalLaws decimal)
    (layout : Layout) (source : List Char) (operations : List Operation) :
    compile decimal layout source = .ready operations ↔
      ∃ pieces, Parsed decimal source pieces ∧ Prepared layout pieces operations := by
  constructor
  · intro compiled
    cases decoded : decode decimal source with
    | incomplete => simp [compile, decoded] at compiled
    | malformed reason => simp [compile, decoded] at compiled
    | complete pieces =>
        cases prepared : prepare layout pieces with
        | error reason => simp [compile, decoded, prepared] at compiled
        | ok actual =>
            simp only [compile, decoded, prepared, CompileResult.ready.injEq] at compiled
            subst operations
            exact ⟨pieces, (decode_iff decimal laws source pieces).1 decoded,
              (prepare_iff layout pieces actual).1 prepared⟩
  · rintro ⟨pieces, parsed, prepared⟩
    simp only [compile, (decode_iff decimal laws source pieces).2 parsed,
      (prepare_iff layout pieces operations).2 prepared]

theorem compile_not_incomplete (decimal : DecimalProvider) (layout : Layout) (source : List Char) :
    compile decimal layout source ≠ .incomplete := by
  have terminates := decode_not_incomplete decimal source
  cases decoded : decode decimal source with
  | incomplete => exact False.elim (terminates decoded)
  | malformed reason => simp [compile, decoded]
  | complete pieces => cases prepared : prepare layout pieces <;> simp [compile, decoded, prepared]

theorem compiled_render_iff (decimal : DecimalProvider) (laws : DecimalLaws decimal)
    (layout : Layout) (source input : List Char) (operations : List Operation)
    (compiled : compile decimal layout source = .ready operations)
    (observation : Observation) (layoutMatches : observation.captures.length = layout.groups)
    (output : List Char) :
    render input observation operations = output ↔ Expansion input observation operations output := by
  obtain ⟨pieces, _, prepared⟩ := (compile_iff decimal laws layout source operations).1 compiled
  apply render_iff
  simpa only [layoutMatches] using prepared.bounded

theorem unicode_decimal_laws : DecimalLaws RegexDecimalValues.characterValue? := by
  constructor <;> decide

theorem unicode_compile_iff (layout : Layout) (source : List Char) (operations : List Operation) :
    compile RegexDecimalValues.characterValue? layout source = .ready operations ↔
      ∃ pieces, Parsed RegexDecimalValues.characterValue? source pieces ∧
        Prepared layout pieces operations := compile_iff _ unicode_decimal_laws _ _ _

namespace Controls

private def decimal : DecimalProvider
  | '0' | '０' => some ⟨0, by decide⟩
  | '1' | '١' | '１' => some ⟨1, by decide⟩
  | '2' | '٢' | '２' => some ⟨2, by decide⟩
  | '3' | '٣' | '３' => some ⟨3, by decide⟩
  | _ => none

theorem mixed_decimal_and_dollar :
    decode decimal "$١３$$".toList =
      .complete [.reference (.index 13), .literal '$'] := by decide

theorem braced_numeric_and_unicode_name :
    decode decimal "${１٣}:${λ}".toList =
      .complete [.reference (.index 13), .literal ':', .reference (.name "λ")] := by decide

theorem decimal_is_maximal :
    decode decimal "$12x".toList =
      .complete [.reference (.index 12), .literal 'x'] := by decide

theorem syntax_errors_are_not_unknown_references :
    decode decimal "$".toList = .malformed .danglingDollar ∧
    decode decimal "${}".toList = .malformed .emptyReference ∧
    prepare ⟨2, []⟩ [.reference (.index 13)] = .error (.unknown (.index 13)) := by decide

theorem unfinished_decode_is_not_malformed :
    decodeAux decimal 0 "$1".toList = .incomplete ∧
    decode decimal "$1".toList = .complete [.reference (.index 1)] := by decide

private def observed : Observation :=
  ⟨⟨1, 2⟩, [some ⟨1, 2⟩, none, some ⟨1, 1⟩], []⟩

theorem original_unicode_capture_and_unmatched_expansion :
    render "aλb".toList observed [.capture 0, .literal '$', .capture 1] = "λ$".toList := by decide

theorem absent_and_empty_stay_distinct_before_expansion :
    RegexTraceRendering.captureText "aλb".toList observed 1 = none ∧
    RegexTraceRendering.captureText "aλb".toList observed 2 = some [] ∧
    render "aλb".toList observed [.capture 1] = [] ∧
    render "aλb".toList observed [.capture 2] = [] := by decide

theorem named_resolution_is_declared_and_first :
    resolve ⟨3, [("λ", 2), ("λ", 1)]⟩ (.name "λ") = some 2 ∧
    resolve ⟨3, [("λ", 7)]⟩ (.name "λ") = none := by decide

theorem complete_unicode_template_compilation :
    compile RegexDecimalValues.characterValue? ⟨14, [("λ", 2)]⟩ "$١３:${λ}$$".toList =
      .ready [.capture 13, .literal ':', .capture 2, .literal '$'] := by decide

theorem unknown_and_malformed_compilations_remain_distinct :
    compile RegexDecimalValues.characterValue? ⟨2, []⟩ "$١３".toList =
      .unknown (.unknown (.index 13)) ∧
    compile RegexDecimalValues.characterValue? ⟨2, []⟩ "${".toList =
      .malformed .unclosedReference := by decide

end Controls

#print axioms digitRun_iff
#print axioms token_iff
#print axioms decode_iff
#print axioms decode_not_incomplete
#print axioms prepare_iff
#print axioms render_iff
#print axioms replacement_exact
#print axioms compile_iff
#print axioms compiled_render_iff
#print axioms unicode_compile_iff

end Mettapedia.GSLT.LanguageDef.RegexReplacementTemplate
