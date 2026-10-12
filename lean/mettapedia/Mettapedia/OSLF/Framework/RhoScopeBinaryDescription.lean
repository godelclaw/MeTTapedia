import Mettapedia.OSLF.Framework.RhoScopeExpressionCode
import Mettapedia.Computability.KolmogorovComplexity.SelfDelimitingCode

/-!
# Binary descriptions with checked sorted scope decoding

Each instruction has a three-bit tag. Atom descriptions and arbitrary
variable indices have self-delimiting payloads. The byte-independent parser
reads this stream, then the separately constructed stack machine checks
sorts and reconstructs the entire scope expression, including fixed points.

Two process descriptions compose into a quoted parallel description with
exactly six extra bits. This is a supplied-description construction and
upper bound, without an assertion about minimal semantic descriptions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeBinaryDescription

open RhoScopeExpression RhoScopeExpressionCode Mettapedia.OSLF.Binding.RhoSchema
open KolmogorovComplexity

universe u

structure AtomCode (Atom : Type u) where
  encode : Atom → List Bool
  decode : List Bool → Option Atom
  roundtrip : ∀ atom, decode (encode atom) = some atom

def cell {Atom : Type u} (atoms : AtomCode Atom) : Instruction Atom → List Bool
  | .atom label => [false, false, false] ++ e2encode (atoms.encode label)
  | .var index => [false, false, true] ++ e2encode (binaryBits index)
  | .disj .pr => [false, true, false]
  | .disj .nm => [false, true, true]
  | .quote => [true, false, false]
  | .drop => [true, false, true]
  | .par => [true, true, false]
  | .mu => [true, true, true]

def readCell {Atom : Type u} (atoms : AtomCode Atom) :
    List Bool → Option (Instruction Atom × List Bool)
  | false :: false :: false :: rest =>
      (e2decode rest).bind (fun pair =>
        (atoms.decode pair.1).map (fun label => (.atom label, pair.2)))
  | false :: false :: true :: rest =>
      (e2decode rest).map (fun pair => (.var (ofBinaryBits pair.1), pair.2))
  | false :: true :: false :: rest => some (.disj .pr, rest)
  | false :: true :: true :: rest => some (.disj .nm, rest)
  | true :: false :: false :: rest => some (.quote, rest)
  | true :: false :: true :: rest => some (.drop, rest)
  | true :: true :: false :: rest => some (.par, rest)
  | true :: true :: true :: rest => some (.mu, rest)
  | _ => none

theorem readCell_append {Atom : Type u} (atoms : AtomCode Atom)
    (instruction : Instruction Atom) (suffix : List Bool) :
    readCell atoms (cell atoms instruction ++ suffix) = some (instruction, suffix) := by
  cases instruction with
  | atom label => simp [cell, readCell, e2decode_e2encode_append, atoms.roundtrip]
  | var index => simp [cell, readCell, e2decode_e2encode_append, ofBinaryBits_binaryBits]
  | disj sort => cases sort <;> rfl
  | quote => rfl
  | drop => rfl
  | par => rfl
  | mu => rfl

theorem cell_length {Atom : Type u} (atoms : AtomCode Atom) (instruction : Instruction Atom) :
    3 ≤ (cell atoms instruction).length := by
  cases instruction with
  | atom label => simp [cell]
  | var index => simp [cell]
  | disj sort => cases sort <;> simp [cell]
  | quote => simp [cell]
  | drop => simp [cell]
  | par => simp [cell]
  | mu => simp [cell]

theorem cell_append_not_empty {Atom : Type u} (atoms : AtomCode Atom)
    (instruction : Instruction Atom) (suffix : List Bool) :
    (cell atoms instruction ++ suffix).isEmpty = false := by
  cases instruction with
  | disj sort => cases sort <;> rfl
  | atom label => rfl
  | var index => rfl
  | quote => rfl
  | drop => rfl
  | par => rfl
  | mu => rfl

def stream {Atom : Type u} (atoms : AtomCode Atom) (code : List (Instruction Atom)) : List Bool :=
  code.flatMap (cell atoms)

theorem stream_append {Atom : Type u} (atoms : AtomCode Atom)
    (first second : List (Instruction Atom)) :
    stream atoms (first ++ second) = stream atoms first ++ stream atoms second :=
  List.flatMap_append

def parse {Atom : Type u} (atoms : AtomCode Atom) :
    Nat → List Bool → Option (List (Instruction Atom))
  | 0, bits => if bits.isEmpty then some [] else none
  | fuel + 1, bits =>
      if bits.isEmpty then some [] else
        (readCell atoms bits).bind (fun pair =>
          (parse atoms fuel pair.2).map (fun rest => pair.1 :: rest))

/-- Any fuel covering the instruction count suffices; no parser termination assumption is used. -/
theorem parse_stream {Atom : Type u} (atoms : AtomCode Atom)
    (code : List (Instruction Atom)) (fuel : Nat) (enough : code.length ≤ fuel) :
    parse atoms fuel (stream atoms code) = some code := by
  induction code generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons instruction rest ih =>
    cases fuel with
    | zero => simp only [List.length_cons] at enough; omega
    | succ fuel =>
      have enoughRest : rest.length ≤ fuel := by simp only [List.length_cons] at enough; omega
      simp only [stream, List.flatMap_cons, parse, cell_append_not_empty,
        Bool.false_eq_true, if_false, readCell_append, Option.bind_some]
      change (parse atoms fuel (stream atoms rest)).map (fun parsed => instruction :: parsed) = _
      rw [ih fuel enoughRest]
      rfl

theorem instruction_count_le_bits {Atom : Type u} (atoms : AtomCode Atom)
    (code : List (Instruction Atom)) : code.length ≤ (stream atoms code).length := by
  induction code with
  | nil => rfl
  | cons instruction rest ih =>
    have cellBound := cell_length atoms instruction
    simp only [stream, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

def encodeBinary {Atom : Type u} (atoms : AtomCode Atom) {sort : Srt}
    (expression : Expression Atom sort) : List Bool := stream atoms (encode expression)

def decodeBinary {Atom : Type u} (atoms : AtomCode Atom) (bits : List Bool) : Option (Packed Atom) :=
  (parse atoms bits.length bits).bind decode

theorem decodeBinary_encode {Atom : Type u} (atoms : AtomCode Atom) {sort : Srt}
    (expression : Expression Atom sort) :
    decodeBinary atoms (encodeBinary atoms expression) = some ⟨sort, expression⟩ := by
  rw [decodeBinary, encodeBinary, parse_stream atoms _ _ (instruction_count_le_bits atoms _)]
  exact decode_encode expression

theorem encodeBinary_injective {Atom : Type u} (atoms : AtomCode Atom) {sort : Srt} :
    Function.Injective (encodeBinary atoms (sort := sort)) := by
  intro first second same
  have decoded := congrArg (decodeBinary atoms) same
  rw [decodeBinary_encode, decodeBinary_encode] at decoded
  exact eq_of_heq ((Sigma.mk.inj_iff.mp (Option.some.inj decoded)).2)

/-- Closed admission additionally checks every variable index under its actual binder depth. -/
def decodeClosed {Atom : Type u} (atoms : AtomCode Atom) (bits : List Bool) : Option (Packed Atom) :=
  (decodeBinary atoms bits).filter (fun expression => expression.2.closedAt 0)

theorem decodeClosed_encode {Atom : Type u} (atoms : AtomCode Atom) {sort : Srt}
    (expression : Expression Atom sort) (closed : expression.closedAt 0 = true) :
    decodeClosed atoms (encodeBinary atoms expression) = some ⟨sort, expression⟩ := by
  simp [decodeClosed, decodeBinary_encode, closed]

def sortMinimum : Srt → Nat
  | .pr => 7
  | .nm => 4

/-- Payload-bearing instructions prevent arbitrarily short process descriptions. -/
theorem sorted_description_lower_bound {Atom : Type u} (atoms : AtomCode Atom)
    (atomBound : ∀ label, 7 ≤ (cell atoms (.atom label)).length)
    {sort : Srt} (expression : Expression Atom sort) :
    sortMinimum sort ≤ (encodeBinary atoms expression).length := by
  induction expression with
  | atom label => simpa [encodeBinary, encode, stream, sortMinimum] using atomBound label
  | var index =>
    simp [encodeBinary, encode, stream, cell, sortMinimum, e2encode_length]
  | @or sort first second firstIH secondIH =>
    cases sort <;>
      simp only [sortMinimum, encodeBinary, encode, stream, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
        cell, List.length_cons, List.length_nil] at firstIH secondIH ⊢ <;> omega
  | quote process ih =>
    simp only [sortMinimum, encodeBinary, encode, stream, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      cell, List.length_cons, List.length_nil] at ih ⊢
    omega
  | drop name ih =>
    simp only [sortMinimum, encodeBinary, encode, stream, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      cell, List.length_cons, List.length_nil] at ih ⊢
    omega
  | par first second firstIH secondIH =>
    simp only [sortMinimum, encodeBinary, encode, stream, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      cell, List.length_cons, List.length_nil] at firstIH secondIH ⊢
    omega
  | mu body ih =>
    simp only [sortMinimum, encodeBinary, encode, stream, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      cell, List.length_cons, List.length_nil] at ih ⊢
    omega

/-- The decoded composite retains both complete descriptions, with two fixed-size instructions. -/
theorem quoted_parallel_description_length {Atom : Type u} (atoms : AtomCode Atom)
    (first second : Expression Atom Srt.pr) :
    (encodeBinary atoms (.quote (.par first second))).length =
      (encodeBinary atoms first).length + (encodeBinary atoms second).length + 6 := by
  simp [encodeBinary, encode, stream, cell, Nat.add_assoc]

end Mettapedia.OSLF.Framework.RhoScopeBinaryDescription
