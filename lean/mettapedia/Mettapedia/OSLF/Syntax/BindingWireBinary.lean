import Mettapedia.Computability.WordEqualityMachine
import Mettapedia.Computability.WordHomomorphismMachine
import Mettapedia.Computability.FiniteWordClassifier
import Mettapedia.OSLF.Syntax.BindingWireString
import Mettapedia.OSLF.MeTTaIL.PatternTokens
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Computability.Encoding
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Binary prefix storage for structural wire data

The five-symbol alphabet stores arbitrary natural numbers in terminated binary
form. Pairs carry an explicit constructor marker, and complete decoding rejects
trailing input. Existing wire codecs supply their own field validation and exact
roundtrip laws. String payloads use the shared UTF-8 codec.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.WireCodec.Binary

open Mettapedia.OSLF.MeTTaIL

/-- Five symbols, each representable by three bits. -/
abbrev Alphabet := Fin 5

private def text (symbol : Alphabet) : String :=
  match symbol.val with
  | 0 => "0" | 1 => "1" | 2 => "e" | 3 => "a" | _ => "p"

/-- Binary digits followed by their terminator. No machine-word bound applies. -/
def natural (value : Nat) : List Alphabet :=
  (Nat.digits 2 value).map (fun digit => if digit = 0 then 0 else 1) ++ [2]

/-- Direct finite-alphabet execution of the existing binary parser. -/
def readNatural : List Alphabet → Option (Nat × List Alphabet)
  | [] => none
  | symbol :: rest =>
    match symbol.val with
    | 2 => some (0, rest)
    | 0 => do
        let (value, tail) ← readNatural rest
        pure (2 * value, tail)
    | 1 => do
        let (value, tail) ← readNatural rest
        pure (2 * value + 1, tail)
    | _ => none

private theorem text_injective : Function.Injective text := by
  intro first second same
  fin_cases first <;> fin_cases second <;> simp_all [text]

/-- The finite-alphabet reader realizes `PatternTokens.readNat` directly,
without constructing string copies of the unconsumed input. -/
theorem readNatural_projection (word : List Alphabet) :
    (readNatural word).map (fun value => (value.1, value.2.map text)) =
      PatternTokens.readNat (word.map text) := by
  induction word with
  | nil => rfl
  | cons symbol word ih =>
    fin_cases symbol
    all_goals
      simp only [List.map_cons]
      simp only [readNatural, text, PatternTokens.readNat]
    all_goals try rfl
    all_goals
      rw [← ih]
      cases parsed : readNatural word with
      | none => rfl
      | some value => rcases value with ⟨number, tail⟩; rfl

theorem readNatural_natural (value : Nat) (tail : List Alphabet) :
    readNatural (natural value ++ tail) = some (value, tail) := by
  have mapped : ((Nat.digits 2 value).map
      (fun digit => (if digit = 0 then 0 else 1 : Alphabet))).map text = PatternTokens.bits value := by
    simp only [PatternTokens.bits, List.map_map]
    apply List.map_congr_left
    intro digit _
    by_cases zero : digit = 0 <;> simp [zero, text]
  have projection := readNatural_projection (natural value ++ tail)
  have mappedInput : (natural value ++ tail).map text =
      PatternTokens.bits value ++ "e" :: tail.map text := by
    simp only [natural, List.append_assoc, List.map_append, mapped]
    rfl
  rw [mappedInput] at projection
  rw [PatternTokens.readNat_bits] at projection
  cases parsed : readNatural (natural value ++ tail) with
  | none => simp [parsed] at projection
  | some result =>
    rcases result with ⟨number, rest⟩
    simp only [parsed, Option.map_some, Option.some.injEq, Prod.mk.injEq] at projection
    have same : rest = tail := List.map_injective_iff.mpr text_injective projection.2
    rw [projection.1, same]

/-- Prefix serialization of the existing generic data carrier. -/
def writeData : Data → List Alphabet → List Alphabet
  | .atom value, tail => 3 :: natural value ++ tail
  | .pair first second, tail => 4 :: writeData first (writeData second tail)

theorem writeData_append (value : Data) (tail : List Alphabet) :
    writeData value tail = writeData value [] ++ tail := by
  induction value generalizing tail with
  | atom value => simp [writeData]
  | pair first second firstIH secondIH =>
      rw [writeData, firstIH, secondIH, writeData, firstIH (writeData second [])]
      simp only [List.cons_append, List.append_assoc]

/-- Bounded by the physical input length, rather than a submitted fuel field. -/
def readData : Nat → List Alphabet → Option (Data × List Alphabet)
  | 0, _ => none
  | _fuel + 1, 3 :: word => do
      let (value, rest) ← readNatural word
      pure (.atom value, rest)
  | fuel + 1, 4 :: word => do
      let (first, rest) ← readData fuel word
      let (second, tail) ← readData fuel rest
      pure (.pair first second, tail)
  | _, _ => none

private def dataDepth : Data → Nat
  | .atom _ => 1
  | .pair first second => max (dataDepth first) (dataDepth second) + 1

private theorem readData_writeData (value : Data) (tail : List Alphabet)
    (fuel : Nat) (enough : dataDepth value ≤ fuel) :
    readData fuel (writeData value tail) = some (value, tail) := by
  cases fuel with
  | zero => cases value <;> simp [dataDepth] at enough
  | succ fuel =>
    cases value with
    | atom value => simp [writeData, readData, readNatural_natural]
    | pair first second =>
      have firstEnough : dataDepth first ≤ fuel := by simp [dataDepth] at enough; omega
      have secondEnough : dataDepth second ≤ fuel := by simp [dataDepth] at enough; omega
      simp [writeData, readData, readData_writeData first _ fuel firstEnough,
        readData_writeData second tail fuel secondEnough]
termination_by sizeOf value

/-- Structural storage measure of the generic carrier, before serialization. -/
def dataWeight : Data → Nat
  | .atom value => 2 + (Nat.digits 2 value).length
  | .pair first second => 1 + dataWeight first + dataWeight second

theorem writeData_length (value : Data) (tail : List Alphabet) :
    (writeData value tail).length = dataWeight value + tail.length := by
  induction value generalizing tail with
  | atom value => simp [writeData, natural, dataWeight]; omega
  | pair first second firstIH secondIH => simp [writeData, dataWeight, firstIH, secondIH]; omega

private theorem dataDepth_le_weight (value : Data) : dataDepth value ≤ dataWeight value := by
  induction value with
  | atom value => simp [dataDepth, dataWeight]; omega
  | pair first second firstIH secondIH => simp [dataDepth, dataWeight]; omega

def encodeData (value : Data) : List Alphabet := writeData value []

theorem encodeData_atom (value : Nat) : encodeData (.atom value) = 3 :: natural value := by
  simp [encodeData, writeData]

theorem encodeData_pair (first second : Data) :
    encodeData (.pair first second) = 4 :: (encodeData first ++ encodeData second) := by
  change 4 :: writeData first (writeData second []) = _
  rw [writeData_append first (writeData second [])]
  rfl

def decodeData (word : List Alphabet) : Option Data := do
  let (value, tail) ← readData word.length word
  if tail.isEmpty then some value else none

theorem decodeData_encodeData (value : Data) : decodeData (encodeData value) = some value := by
  have enough : dataDepth value ≤ (writeData value []).length := by
    simpa [writeData_length] using dataDepth_le_weight value
  simp only [decodeData, encodeData, readData_writeData value [] _ enough]
  rfl

/-- Complete data decoding refuses every nonempty appended suffix. -/
theorem decodeData_encodeData_append (value : Data) (tail : List Alphabet) :
    decodeData (encodeData value ++ tail) = if tail.isEmpty then some value else none := by
  have input : encodeData value ++ tail = writeData value tail :=
    (writeData_append value tail).symm
  rw [input]
  have enough : dataDepth value ≤ (writeData value tail).length := by
    rw [writeData_length]
    exact (dataDepth_le_weight value).trans (Nat.le_add_right _ _)
  simp only [decodeData, readData_writeData value tail _ enough]
  rfl

/-- Convert existing exact codecs into finite-alphabet encoders and decoders. -/
def encodeWith {α : Type} (codec : Codec α) (value : α) : List Alphabet :=
  encodeData (codec.put value)

/-- List fields retain independent original words, explicit pair boundaries
and the original nil terminator. -/
theorem encodeWith_list {α : Type} (codec : Codec α) (values : List α) :
    encodeWith (Codec.list codec) values =
      values.flatMap (fun value => 4 :: encodeWith codec value) ++ encodeData (.atom 0) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    change encodeData (.pair (codec.put value) ((Codec.list codec).put values)) = _
    rw [encodeData_pair]
    change 4 :: (encodeWith codec value ++ encodeWith (Codec.list codec) values) = _
    rw [ih]
    simp only [List.flatMap_cons, List.cons_append, List.append_assoc]

/-- Every physical occurrence contributes its full word to the encoded list.
Equal values are counted independently rather than deduplicated. -/
theorem encodeWith_list_member_length {α : Type} (codec : Codec α) (values : List α)
    (value : α) (member : value ∈ values) :
    (encodeWith codec value).length ≤ (encodeWith (Codec.list codec) values).length := by
  induction values with
  | nil => simp at member
  | cons first rest ih =>
    change _ ≤ (encodeData (.pair (codec.put first) ((Codec.list codec).put rest))).length
    rw [encodeData_pair]
    change _ ≤ (4 :: (encodeWith codec first ++ encodeWith (Codec.list codec) rest)).length
    simp only [List.length_cons, List.length_append]
    rcases List.mem_cons.mp member with same | remaining
    · subst first; omega
    · have bounded := ih remaining; omega

def decodeWith {α : Type} (codec : Codec α) (word : List Alphabet) : Option α :=
  (decodeData word).bind codec.get

theorem decodeWith_encodeWith {α : Type} (codec : Codec α) (value : α) :
    decodeWith codec (encodeWith codec value) = some value := by
  simp [decodeWith, encodeWith, decodeData_encodeData, codec.get_put]

theorem decodeWith_trailing_refused {α : Type} (codec : Codec α) (value : α)
    (tail : List Alphabet) (nonempty : tail.isEmpty = false) :
    decodeWith codec (encodeWith codec value ++ tail) = none := by
  simp only [decodeWith, encodeWith, decodeData_encodeData_append, nonempty, Bool.false_eq_true,
    if_false, Option.bind_none]

theorem encodeWith_injective {α : Type} (codec : Codec α) :
    Function.Injective (encodeWith codec) := by
  intro first second same
  have decoded := congrArg (decodeWith codec) same
  simpa [decodeWith_encodeWith] using decoded

theorem dataWeight_prod {α β : Type} (first : Codec α) (second : Codec β)
    (value : α × β) :
    dataWeight ((Codec.prod first second).put value) =
      1 + dataWeight (first.put value.1) + dataWeight (second.put value.2) := rfl

theorem dataWeight_list_nil {α : Type} (codec : Codec α) :
    dataWeight ((Codec.list codec).put []) = 2 := rfl

theorem dataWeight_list_cons {α : Type} (codec : Codec α) (value : α) (values : List α) :
    dataWeight ((Codec.list codec).put (value :: values)) =
      1 + dataWeight (codec.put value) + dataWeight ((Codec.list codec).put values) := rfl

theorem dataWeight_byte (byte : UInt8) : dataWeight (Codec.byte.put byte) ≤ 10 := by
  change 2 + (Nat.digits 2 byte.toNat).length ≤ 10
  have digits : (Nat.digits 2 byte.toNat).length ≤ 8 :=
    (Nat.digits_length_le_iff (by decide) byte.toNat).mpr byte.toNat_lt_size
  omega

theorem dataWeight_bytes (bytes : List UInt8) :
    dataWeight ((Codec.list Codec.byte).put bytes) ≤ 11 * bytes.length + 2 := by
  induction bytes with
  | nil => simp only [dataWeight_list_nil, List.length_nil]; omega
  | cons byte bytes ih =>
    rw [dataWeight_list_cons, List.length_cons]
    have head := dataWeight_byte byte
    omega

/-- UTF-8 payload bytes, including embedded NUL, are charged individually. -/
theorem dataWeight_string (value : String) :
    dataWeight (Codec.string.put value) ≤ 11 * value.utf8ByteSize + 2 := by
  have bound := dataWeight_bytes (Utf8.bytes value)
  have length : (Utf8.bytes value).length = value.utf8ByteSize := by
    rw [Utf8.bytes, Array.length_toList]
    rfl
  change dataWeight ((Codec.list Codec.byte).put (Utf8.bytes value)) ≤ _
  simpa only [length] using bound

theorem dataWeight_bytes_lower (bytes : List UInt8) :
    bytes.length + 1 ≤ dataWeight ((Codec.list Codec.byte).put bytes) := by
  induction bytes with
  | nil => rw [dataWeight_list_nil]; simp
  | cons byte bytes ih =>
    rw [dataWeight_list_cons, List.length_cons]
    have bytePositive : 1 ≤ dataWeight (Codec.byte.put byte) := by
      change 1 ≤ 2 + (Nat.digits 2 byte.toNat).length
      omega
    omega

theorem dataWeight_string_lower (value : String) :
    value.utf8ByteSize + 1 ≤ dataWeight (Codec.string.put value) := by
  have bytes := dataWeight_bytes_lower (Utf8.bytes value)
  have length : (Utf8.bytes value).length = value.utf8ByteSize := by
    rw [Utf8.bytes, Array.length_toList]
    rfl
  change value.utf8ByteSize + 1 ≤ dataWeight ((Codec.list Codec.byte).put (Utf8.bytes value))
  simpa only [length] using bytes

/-- One unit for each name constructor, one for each UTF-8 payload byte,
and one for each binary digit in a numeric component. -/
def namePayloadSize : Lean.Name → Nat
  | .anonymous => 1
  | .str parent label => namePayloadSize parent + label.utf8ByteSize + 1
  | .num parent index => namePayloadSize parent + (Nat.digits 2 index).length + 1

theorem dataWeight_name_lower (value : Lean.Name) :
    namePayloadSize value ≤ dataWeight (Codec.name.put value) := by
  induction value with
  | anonymous => decide
  | str parent label inductionHypothesis =>
      have text := dataWeight_string_lower label
      change namePayloadSize parent + label.utf8ByteSize + 1 ≤
        1 + 3 + (1 + dataWeight (Codec.name.put parent) +
          dataWeight (Codec.string.put label))
      omega
  | num parent index inductionHypothesis =>
      change namePayloadSize parent + (Nat.digits 2 index).length + 1 ≤
        1 + 4 + (1 + dataWeight (Codec.name.put parent) +
          (2 + (Nat.digits 2 index).length))
      omega

/-- Structural name storage grows linearly in its payload measure. This is
a serialized-size theorem, not a bound on decoder or host execution time. -/
theorem dataWeight_name (value : Lean.Name) :
    dataWeight (Codec.name.put value) ≤ 11 * namePayloadSize value := by
  induction value with
  | anonymous => decide
  | str parent label inductionHypothesis =>
      have text := dataWeight_string label
      change 1 + 3 + (1 + dataWeight (Codec.name.put parent) +
        dataWeight (Codec.string.put label)) ≤
          11 * (namePayloadSize parent + label.utf8ByteSize + 1)
      omega
  | num parent index inductionHypothesis =>
      change 1 + 4 + (1 + dataWeight (Codec.name.put parent) +
        (2 + (Nat.digits 2 index).length)) ≤
          11 * (namePayloadSize parent + (Nat.digits 2 index).length + 1)
      omega

/-- The existing codec becomes an executable finite-alphabet encoding. -/
def encoding {α : Type} (codec : Codec α) : Computability.Encoding α Alphabet where
  encode := encodeWith codec
  decode := decodeWith codec
  decode_encode := decodeWith_encodeWith codec

/-- A total structural order on codec values, computed from their exact words. -/
def encodedLe {α : Type} (codec : Codec α) (first second : α) : Prop :=
  encodeWith codec first ≤ encodeWith codec second

instance {α : Type} (codec : Codec α) : DecidableRel (encodedLe codec) :=
  fun _ _ => inferInstanceAs (Decidable (_ ≤ _))
instance {α : Type} (codec : Codec α) : IsTrans α (encodedLe codec) :=
  ⟨fun _ _ _ => le_trans⟩
instance {α : Type} (codec : Codec α) : Std.Total (encodedLe codec) :=
  ⟨fun _ _ => le_total _ _⟩
instance {α : Type} (codec : Codec α) : Std.Antisymm (encodedLe codec) :=
  ⟨fun _ _ first second => encodeWith_injective codec (le_antisymm first second)⟩

/-- Deterministic finite-set storage retains every element. Decoding restores
set membership; checking the element codec validates each stored payload. -/
def finsetCodec {α : Type} [DecidableEq α] (codec : Codec α) : Codec (Finset α) :=
  (Codec.list codec).mapped (fun values => values.sort (encodedLe codec))
    (fun values => some values.toFinset)
    (fun values => congrArg some (Finset.sort_toFinset values (encodedLe codec)))

/-- List delimiters and each encoded element are charged independently. -/
theorem dataWeight_list_le {α : Type} (codec : Codec α) (size : α → Nat) (factor : Nat)
    (large : 2 ≤ factor) (bounded : ∀ value, dataWeight (codec.put value) + 1 ≤ factor * size value)
    (values : List α) :
    dataWeight ((Codec.list codec).put values) ≤ factor * (1 + (values.map size).sum) := by
  induction values with
  | nil => simp only [dataWeight_list_nil, List.map_nil, List.sum_nil, Nat.add_zero, Nat.mul_one]; exact large
  | cons value values ih =>
      rw [dataWeight_list_cons]
      have head := bounded value
      simp only [List.map_cons, List.sum_cons, Nat.mul_add] at *
      omega

theorem sorted_sum {α : Type} [DecidableEq α] (codec : Codec α) (size : α → Nat)
    (values : Finset α) :
    ((values.sort (encodedLe codec)).map size).sum = ∑ value ∈ values, size value := by
  change (Multiset.map size (↑(values.sort (encodedLe codec)) : Multiset α)).sum = _
  rw [Finset.sort_eq]
  rfl

/-- Finite sets retain the complete payload of every element exactly once. -/
theorem dataWeight_finset_le {α : Type} [DecidableEq α] (codec : Codec α) (size : α → Nat)
    (factor : Nat) (large : 2 ≤ factor)
    (bounded : ∀ value, dataWeight (codec.put value) + 1 ≤ factor * size value)
    (values : Finset α) :
    dataWeight ((finsetCodec codec).put values) ≤ factor * (1 + ∑ value ∈ values, size value) := by
  have bound := dataWeight_list_le codec size factor large bounded (values.sort (encodedLe codec))
  rw [sorted_sum] at bound
  exact bound


/-- Equality of complete words reflects equality of the original wire data. -/
theorem encodeData_injective : Function.Injective encodeData := by
  intro first second same
  have decoded := congrArg decodeData same
  simpa only [decodeData_encodeData, Option.some.injEq] using decoded

namespace Equality
set_option backward.isDefEq.respectTransparency false
open _root_.Computability Turing Polynomial
open Mettapedia.Computability

/-- The outer delimiter is distinct from every original codec symbol. -/
def packet {α : Type} (codec : Codec α) (first second : α) : List (Option Alphabet) :=
  WordEqualityMachine.packet (encodeWith codec first) (encodeWith codec second)

theorem packet_length {α : Type} (codec : Codec α) (first second : α) :
    (packet codec first second).length =
      (encodeWith codec first).length + (encodeWith codec second).length + 1 := by
  exact WordEqualityMachine.packet_length _ _

/-- The original AST comparison is earned from every byte of both canonical
images; constructor-only inspection and digest equality are not used. -/
def outputs {α : Type} [DecidableEq α] (codec : Codec α) (first second : α) :
    TM2OutputsInTime (WordEqualityMachine.machine Alphabet) (packet codec first second)
      (some [decide (first = second)])
      (3 * (encodeWith codec first).length + (encodeWith codec second).length + 4) := by
  have checked := WordEqualityMachine.outputs (encodeWith codec first) (encodeWith codec second)
  have exactFields : encodeWith codec first = encodeWith codec second ↔ first = second :=
    (encodeWith_injective codec).eq_iff
  simpa only [packet, exactFields] using checked

noncomputable def computable {α : Type} [DecidableEq α] (codec : Codec α) :
    TM2ComputableInPolyTime (fun values : α × α => packet codec values.1 values.2)
      (fun value : Bool => [value]) (fun values : α × α => decide (values.1 = values.2)) where
  tm := WordEqualityMachine.machine Alphabet
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Bool
  time := C 3 * X + C 1
  outputsFun values := by
    change TM2OutputsInTime (WordEqualityMachine.machine Alphabet) ((packet codec values.1 values.2).map id)
      (some ([decide (values.1 = values.2)].map id)) _
    simp only [List.map_id_fun]
    have checked := outputs codec values.1 values.2
    change StateTransition.EvalsToInTime (WordEqualityMachine.machine Alphabet).step _ _ _ at checked ⊢
    exact WordEqualityMachine.within checked (by
      simp only [eval_add, eval_mul, eval_C, eval_X, packet_length]
      omega)

noncomputable def same {α : Type} [DecidableEq α] (codec : Codec α) (value : α) :
    TM2OutputsInTime (WordEqualityMachine.machine Alphabet) (packet codec value value)
      (some [true]) (3 * (packet codec value value).length + 1) := by
  have checked := (computable codec).outputsFun (value, value)
  change TM2OutputsInTime (WordEqualityMachine.machine Alphabet) ((packet codec value value).map id)
    (some ([decide (value = value)].map id)) ((C 3 * X + C 1).eval (packet codec value value).length) at checked
  simpa only [List.map_id_fun, id_eq, decide_true, eval_add, eval_mul, eval_C, eval_X] using checked

noncomputable def different {α : Type} [DecidableEq α] (codec : Codec α) (first second : α)
    (distinct : first ≠ second) :
    TM2OutputsInTime (WordEqualityMachine.machine Alphabet) (packet codec first second)
      (some [false]) (3 * (packet codec first second).length + 1) := by
  have checked := (computable codec).outputsFun (first, second)
  change TM2OutputsInTime (WordEqualityMachine.machine Alphabet) ((packet codec first second).map id)
    (some ([decide (first = second)].map id)) ((C 3 * X + C 1).eval (packet codec first second).length) at checked
  simpa only [List.map_id_fun, id_eq, distinct, decide_false, eval_add, eval_mul, eval_C, eval_X] using checked

/-- Raw structural data has the same complete-image equality realization. -/
def dataOutputs (first second : Data) :
    TM2OutputsInTime (WordEqualityMachine.machine Alphabet)
      (WordEqualityMachine.packet (encodeData first) (encodeData second))
      (some [decide (first = second)])
      (3 * (encodeData first).length + (encodeData second).length + 4) := by
  have checked := WordEqualityMachine.outputs (encodeData first) (encodeData second)
  have exactFields : encodeData first = encodeData second ↔ first = second :=
    encodeData_injective.eq_iff
  simpa only [exactFields] using checked

end Equality

namespace Dictionary
set_option backward.isDefEq.respectTransparency false
open Mettapedia.Computability
variable {A : Type} {n : Nat}

def words (codec : Codec A) (authored : Fin n → A) : Fin n → List Alphabet :=
  fun index => encodeWith codec (authored index)

/-- Search the original authored values in their authored order. -/
def result (codec : Codec A) (authored : Fin n → A) (value : A) : Option (Fin n) :=
  let _ := Codec.decEq codec
  (List.finRange n).find? fun index => decide (value = authored index)

/-- The executed classifier compares complete original encodings. Its answer
is the first equal original value, using the existing codec's injectivity. -/
theorem classify_original (codec : Codec A) (authored : Fin n → A) (value : A) :
    FiniteWordClassifier.classify (words codec authored) (encodeWith codec value) = result codec authored value := by
  unfold FiniteWordClassifier.classify result
  apply congrArg (fun predicate => (List.finRange n).find? predicate)
  funext index
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, words]
  exact (encodeWith_injective codec).eq_iff

def output (codec : Codec A) (authored : Fin n → A) (value : A) : List (Sum Alphabet (Option (Fin n))) :=
  .inr (result codec authored value) :: (encodeWith codec value).map Sum.inl

noncomputable def outputs (codec : Codec A) (authored : Fin n → A) (value : A) :
    Turing.TM2OutputsInTime (FiniteWordClassifier.machine (words codec authored)) (encodeWith codec value)
      (some (output codec authored value)) (2 * (encodeWith codec value).length + 2) := by
  have executed := FiniteWordClassifier.outputs (words codec authored) (encodeWith codec value)
  rw [classify_original] at executed
  exact executed

noncomputable def computable (codec : Codec A) (authored : Fin n → A) :
    Turing.TM2ComputableInPolyTime (encodeWith codec)
      (fun word : List (Sum Alphabet (Option (Fin n))) => word) (output codec authored) where
  tm := FiniteWordClassifier.machine (words codec authored)
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl (Sum Alphabet (Option (Fin n)))
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
  outputsFun value := by
    change Turing.TM2OutputsInTime (FiniteWordClassifier.machine (words codec authored))
      ((encodeWith codec value).map id) (some ((output codec authored value).map id)) _
    simp only [List.map_id_fun, id_eq]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using
      outputs codec authored value

end Dictionary

namespace Triples
set_option backward.isDefEq.respectTransparency false
open Mettapedia.Computability Turing Polynomial

/-- A lossless fixed-width physical representation of the five-symbol wire alphabet. -/
def symbol (value : Alphabet) : List Bool :=
  match value.val with
  | 0 => [false, false, false]
  | 1 => [true, false, false]
  | 2 => [false, true, false]
  | 3 => [true, true, false]
  | _ => [false, false, true]

def encode (word : List Alphabet) : List Bool := word.flatMap symbol

private def digit : Bool → Bool → Bool → Option Alphabet
  | false, false, false => some 0
  | true, false, false => some 1
  | false, true, false => some 2
  | true, true, false => some 3
  | false, false, true => some 4
  | _, _, _ => none

/-- All unused triples and incomplete final symbols are refused. -/
def decode : List Bool → Option (List Alphabet)
  | [] => some []
  | first :: second :: third :: rest => do
      let value ← digit first second third
      let tail ← decode rest
      pure (value :: tail)
  | _ => none

theorem symbol_length (value : Alphabet) : (symbol value).length = 3 := by
  fin_cases value <;> rfl

theorem encode_length (word : List Alphabet) : (encode word).length = 3 * word.length := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
      simp only [encode, List.flatMap_cons, List.length_append, symbol_length,
        List.length_cons] at *
      omega

theorem decode_encode (word : List Alphabet) : decode (encode word) = some word := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
      simp only [encode] at ih
      fin_cases head <;> simp [encode, symbol, decode, digit, ih]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa only [decode_encode, Option.some.injEq] using decoded

theorem original_injective {A : Type} (codec : Codec A) :
    Function.Injective (fun value => encode (encodeWith codec value)) :=
  encode_injective.comp (encodeWith_injective codec)

/-- The conversion emits all three bits of every symbol and reverses the output physically. -/
def outputs (word : List Alphabet) :
    TM2OutputsInTime (WordHomomorphismMachine.machine symbol) word (some (encode word))
      (8 * word.length + 2) := by
  have executed := WordHomomorphismMachine.outputs symbol word
  change TM2OutputsInTime (WordHomomorphismMachine.machine symbol) word
    (some (encode word)) (2 * word.length + 2 * (encode word).length + 2) at executed
  rw [encode_length] at executed
  convert executed using 1
  ring

noncomputable def realization : TM2ComputableInPolyTime id id encode where
  tm := WordHomomorphismMachine.machine symbol
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 8 * X + C 2
  outputsFun word := by
    change TM2OutputsInTime (WordHomomorphismMachine.machine symbol) ((id word).map id)
      (some ((id (encode word)).map id)) ((C 8 * X + C 2).eval (id word).length)
    simpa only [id, List.map_id_fun, eval_add, eval_mul, eval_C, eval_X] using outputs word


namespace Recovery
open StateTransition
open Turing.TM2.Stmt

inductive Stack where
  | input | reversed | result
  deriving DecidableEq, Fintype

inductive Phase where
  | status | first | second | third | checkEnd | restore | finish | discardInput | discardOutput
  deriving DecidableEq, Fintype

abbrev Control := Option Alphabet × Bool × Bool

def initial : Control := (none, false, false)
def physicalBit (value : Bool) : Alphabet := if value then 1 else 0

def bits (word : List Alphabet) : List Alphabet := (encode word).map physicalBit

def packet (word : List Alphabet) : List Alphabet := 1 :: bits word ++ [2]

def result (word : List Alphabet) : List Alphabet := 1 :: word

def isBit (value : Option Alphabet) : Bool := value == some 0 || value == some 1

def selected (state : Control) : Option Alphabet :=
  digit state.2.1 state.2.2 (state.1 == some 1)

/-- Recovery consumes every physical triple and checks the final delimiter.
Its finite registers hold only the current three bits; original values remain
on stacks. An unsuccessful response or malformed triple is refused. -/
def program (phase : Phase) : TM2.Stmt (fun _ : Stack => Alphabet) Phase Control :=
  match phase with
  | .status => pop .input (fun state value => (value, state.2))
      (branch (fun state => state.1 == some 1)
        (load (fun _ => initial) (goto fun _ => .first))
        (goto fun _ => .discardInput))
  | .first => pop .input (fun state value => (value, state.2))
      (branch (fun state => state.1 == some 2)
        (goto fun _ => .checkEnd)
        (branch (fun state => isBit state.1)
          (load (fun state => (none, state.1 == some 1, false)) (goto fun _ => .second))
          (goto fun _ => .discardInput)))
  | .second => pop .input (fun state value => (value, state.2))
      (branch (fun state => isBit state.1)
        (load (fun state => (none, state.2.1, state.1 == some 1)) (goto fun _ => .third))
        (goto fun _ => .discardInput))
  | .third => pop .input (fun state value => (value, state.2))
      (branch (fun state => isBit state.1 && (selected state).isSome)
        (push .reversed (fun state => (selected state).getD 0)
          (load (fun _ => initial) (goto fun _ => .first)))
        (goto fun _ => .discardInput))
  | .checkEnd => pop .input (fun state value => (value, state.2))
      (branch (fun state => state.1.isNone)
        (load (fun _ => initial) (goto fun _ => .restore))
        (goto fun _ => .discardInput))
  | .restore => pop .reversed (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome)
        (push .result (fun state => state.1.getD 0) (goto fun _ => .restore))
        (goto fun _ => .finish))
  | .finish => push .result (fun _ => 1) (load (fun _ => initial) halt)
  | .discardInput => pop .input (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome) (goto fun _ => .discardInput)
        (goto fun _ => .discardOutput))
  | .discardOutput => pop .reversed (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome) (goto fun _ => .discardOutput)
        (push .result (fun _ => 0) (load (fun _ => initial) halt)))

def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ _ := Alphabet
  Λ := Phase
  main := .status
  σ := Control
  initialState := initial
  m := program

attribute [local implicit_reducible] machine

def config (phase : Option Phase) (state : Control)
    (input reversed output : List Alphabet) : machine.Cfg where
  l := phase
  var := state
  stk key := match key with
    | .input => input | .reversed => reversed | .result => output

private theorem status_step (word : List Alphabet) :
    machine.step (config (some .status) initial (packet word) [] []) =
      some (config (some .first) initial (bits word ++ [2]) [] []) := by
  simp [FinTM2.step, machine, program, packet, config, initial,
    Turing.TM2.step, Turing.TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

private def symbol_steps (value : Alphabet) (tail reversed output : List Alphabet) :
    EvalsToInTime machine.step
      (config (some .first) initial ((symbol value).map physicalBit ++ tail) reversed output)
      (some (config (some .first) initial tail (value :: reversed) output)) 3 := by
  refine ⟨⟨3, ?_⟩, le_refl _⟩
  fin_cases value <;>
    simp [FinTM2.step, machine, program, config, symbol,
      physicalBit, initial, isBit, selected, digit, Turing.TM2.step, Turing.TM2.stepAux,
      Function.update, Function.iterate_succ_apply, flip, Option.bind] <;>
    funext key <;> cases key <;> simp [Function.update]

private theorem bitWords_cons (value : Alphabet) (tail : List Alphabet) :
    bits (value :: tail) = (symbol value).map physicalBit ++ bits tail := by
  simp [bits, encode]

/-- Each original symbol uses exactly three transition phases. -/
def readWords (word tail reversed output : List Alphabet) :
    EvalsToInTime machine.step
      (config (some .first) initial (bits word ++ tail) reversed output)
      (some (config (some .first) initial tail (word.reverse ++ reversed) output))
      (3 * word.length) := by
  induction word generalizing reversed with
  | nil => exact ⟨⟨0, by simp [bits, encode]⟩, by simp⟩
  | cons value word ih =>
      have first := symbol_steps value (bits word ++ tail) reversed output
      have later := ih (value :: reversed)
      have joined := EvalsToInTime.trans _ 3 (3 * word.length) _ _ _ first later
      simpa only [bitWords_cons, List.append_assoc, List.length_cons, List.reverse_cons,
        List.singleton_append, Nat.mul_add, Nat.mul_one, Nat.add_comm] using joined

private theorem end_step (reversed output : List Alphabet) :
    machine.step (config (some .first) initial [2] reversed output) =
      some (config (some .checkEnd) (some 2, false, false) [] reversed output) := by
  simp [FinTM2.step, machine, program, config, initial, Turing.TM2.step, Turing.TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

private theorem checkEnd_step (reversed output : List Alphabet) :
    machine.step (config (some .checkEnd) (some 2, false, false) [] reversed output) =
      some (config (some .restore) initial [] reversed output) := by
  simp [FinTM2.step, machine, program, config, initial, Turing.TM2.step, Turing.TM2.stepAux]

private theorem restore_cons (value : Alphabet) (tail output : List Alphabet) (state : Control) :
    machine.step (config (some .restore) state [] (value :: tail) output) =
      some (config (some .restore) (some value, state.2) [] tail (value :: output)) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

private theorem restore_nil (output : List Alphabet) (state : Control) :
    machine.step (config (some .restore) state [] [] output) =
      some (config (some .finish) (none, state.2) [] [] output) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]

def restoreWords (reversed output : List Alphabet) (state : Control) :
    EvalsToInTime machine.step (config (some .restore) state [] reversed output)
      (some (config (some .finish) (none, state.2) [] [] (reversed.reverse ++ output)))
      (reversed.length + 1) := by
  induction reversed generalizing output state with
  | nil => simpa using StackMachineComposition.oneStep (restore_nil output state)
  | cons value reversed ih =>
      have first := StackMachineComposition.oneStep (restore_cons value reversed output state)
      have later := ih (value :: output) (some value, state.2)
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, Nat.add_assoc] using
          EvalsToInTime.trans _ 1 (reversed.length + 1) _ _ _ first later

private theorem finish_step (word : List Alphabet) :
    machine.step (config (some .finish) initial [] [] word) =
      some (config none initial [] [] (result word)) := by
  simp [FinTM2.step, machine, program, config, initial, result,
    Turing.TM2.step, Turing.TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

private theorem init_eq (word : List Alphabet) :
    initList machine (packet word) = config (some .status) initial (packet word) [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

private theorem halt_eq (word : List Alphabet) :
    haltList machine (result word) = config none initial [] [] (result word) := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- An encoded cache value is physically restored byte for byte. -/
def outputs (word : List Alphabet) : TM2OutputsInTime machine (packet word)
    (some (result word)) (4 * word.length + 5) := by
  have start := StackMachineComposition.oneStep (status_step word)
  have read := readWords word [2] [] []
  have marker := StackMachineComposition.oneStep (end_step word.reverse [])
  have ended := StackMachineComposition.oneStep (checkEnd_step word.reverse [])
  have restored := restoreWords word.reverse [] initial
  have finished := StackMachineComposition.oneStep (finish_step word)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at read restored
  have one := EvalsToInTime.trans _ 1 (3 * word.length) _ _ _ start read
  have two := EvalsToInTime.trans _ (3 * word.length + 1) 1 _ _ _ one marker
  have three := EvalsToInTime.trans _ (1 + (3 * word.length + 1)) 1 _ _ _ two ended
  have four := EvalsToInTime.trans _ (1 + (1 + (3 * word.length + 1)))
    (word.length + 1) _ _ _ three restored
  have joined := EvalsToInTime.trans _ ((word.length + 1) + (1 + (1 + (3 * word.length + 1))))
    1 _ _ _ four finished
  change EvalsToInTime _ (initList machine (packet word)) (some (haltList machine (result word))) _
  rw [init_eq, halt_eq]
  convert joined using 1; omega

private theorem discardInput_cons (head : Alphabet) (tail reversed : List Alphabet) (state : Control) :
    machine.step (config (some .discardInput) state (head :: tail) reversed []) =
      some (config (some .discardInput) (some head, state.2) tail reversed []) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

private theorem discardInput_nil (reversed : List Alphabet) (state : Control) :
    machine.step (config (some .discardInput) state [] reversed []) =
      some (config (some .discardOutput) (none, state.2) [] reversed []) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]

private theorem discardOutput_cons (head : Alphabet) (tail : List Alphabet) (state : Control) :
    machine.step (config (some .discardOutput) state [] (head :: tail) []) =
      some (config (some .discardOutput) (some head, state.2) [] tail []) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

private theorem discardOutput_nil (state : Control) :
    machine.step (config (some .discardOutput) state [] [] []) =
      some (config none initial [] [] [0]) := by
  simp [FinTM2.step, machine, program, config, initial, Turing.TM2.step, Turing.TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

def discardInputWords (word reversed : List Alphabet) (state : Control) :
    EvalsToInTime machine.step (config (some .discardInput) state word reversed [])
      (some (config (some .discardOutput) (none, state.2) [] reversed []))
      (word.length + 1) := by
  induction word generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (discardInput_nil reversed state)
  | cons head word ih =>
      have first := StackMachineComposition.oneStep (discardInput_cons head word reversed state)
      simpa only [List.length_cons, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ first (ih (some head,state.2))

def discardOutputWords (word : List Alphabet) (state : Control) :
    EvalsToInTime machine.step (config (some .discardOutput) state [] word [])
      (some (config none initial [] [] [0])) (word.length + 1) := by
  induction word generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (discardOutput_nil state)
  | cons head word ih =>
      have first := StackMachineComposition.oneStep (discardOutput_cons head word state)
      simpa only [List.length_cons, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ first (ih (some head,state.2))

/-- An unsuccessful resolver response is consumed and cleared. -/
def refusedOutputs : TM2OutputsInTime machine ([0] : List Alphabet) (some ([0] : List Alphabet)) 3 := by
  have first : machine.step (config (some .status) initial [0] [] []) =
      some (config (some .discardInput) (some 0,false,false) [] [] []) := by
    simp [FinTM2.step,machine,program,config,initial,Turing.TM2.step,Turing.TM2.stepAux]
    funext key
    cases key <;> simp [Function.update]
  have discarded := discardInputWords [] [] (some 0,false,false)
  have ended := discardOutputWords [] (none,false,false)
  have one := EvalsToInTime.trans _ 1 1 _ _ _ (StackMachineComposition.oneStep first) discarded
  have joined := EvalsToInTime.trans _ 2 1 _ _ _ one ended
  have start : initList machine ([0] : List Alphabet) = config (some .status) initial [0] [] [] := by
    simp only [initList,machine,config]
    congr 1
    funext key
    cases key <;> simp
  have stop : haltList machine ([0] : List Alphabet) = config none initial [] [] [0] := by
    simp only [haltList,machine,config]
    congr 1
    funext key
    cases key <;> simp
  change EvalsToInTime _ (initList machine ([0] : List Alphabet)) (some (haltList machine ([0] : List Alphabet))) 3
  rw [start,stop]
  exact joined

def response : Option (List Alphabet) → List Alphabet
  | none => [0]
  | some word => packet word

def decodedResponse : Option (List Alphabet) → List Alphabet
  | none => [0]
  | some word => result word

def responseOutputs (word : Option (List Alphabet)) :
    TM2OutputsInTime machine (response word) (some (decodedResponse word))
      (4 * (word.getD []).length + 5) := by
  cases word with
  | none => exact ⟨refusedOutputs.toEvalsTo,refusedOutputs.steps_le_m.trans (show 3 ≤ 5 by decide)⟩
  | some word => exact outputs word

end Recovery


end Triples

/-! ## Canonical whole-word decoding -/

/-- In addition to field decoding, retain only the physical word emitted by
the selected codec. This rejects aliases and noncanonical scalar encodings. -/
def canonicalDecodeWith {α : Type} (codec : Codec α) (word : List Alphabet) : Option α := do
  let value ← decodeWith codec word
  if encodeWith codec value = word then some value else none

theorem canonicalDecodeWith_encodeWith {α : Type} (codec : Codec α) (value : α) :
    canonicalDecodeWith codec (encodeWith codec value) = some value := by
  simp only [canonicalDecodeWith, decodeWith_encodeWith, Bind.bind, Option.bind, ite_true]

theorem canonicalDecodeWith_exact {α : Type} (codec : Codec α)
    (word : List Alphabet) (value : α) :
    canonicalDecodeWith codec word = some value ↔ encodeWith codec value = word := by
  constructor
  · intro accepted
    unfold canonicalDecodeWith at accepted
    cases decoded : decodeWith codec word with
    | none => simp only [decoded, Bind.bind, Option.bind] at accepted; cases accepted
    | some candidate =>
        simp only [decoded, Bind.bind, Option.bind] at accepted
        split at accepted
        · rename_i canonical
          cases Option.some.inj accepted
          exact canonical
        · cases accepted
  · intro encoded
    rw [← encoded]
    exact canonicalDecodeWith_encodeWith codec value

theorem canonicalDecodeWith_trailing_refused {α : Type} (codec : Codec α)
    (value : α) (tail : List Alphabet) (nonempty : tail.isEmpty = false) :
    canonicalDecodeWith codec (encodeWith codec value ++ tail) = none := by
  have refused := decodeWith_trailing_refused codec value tail nonempty
  simp only [canonicalDecodeWith, refused, Bind.bind, Option.bind]

/-! ## Shared exact ASCII transport -/

namespace Text

def renderSymbol (symbol : Alphabet) : Char :=
  match symbol.val with
  | 0 => '0' | 1 => '1' | 2 => 'e' | 3 => 'a' | _ => 'p'

def readSymbol : Char → Option Alphabet
  | '0' => some 0 | '1' => some 1 | 'e' => some 2
  | 'a' => some 3 | 'p' => some 4 | _ => none

theorem read_renderSymbol (symbol : Alphabet) :
    readSymbol (renderSymbol symbol) = some symbol := by
  fin_cases symbol <;> rfl

def render (word : List Alphabet) : String := String.ofList (word.map renderSymbol)

def parse (text : String) : Option (List Alphabet) := text.toList.mapM readSymbol

theorem parse_render (word : List Alphabet) : parse (render word) = some word := by
  simp only [parse, render, String.toList_ofList]
  induction word with
  | nil => rfl
  | cons symbol word inductionHypothesis =>
      simp only [List.map_cons, List.mapM_cons, read_renderSymbol,
        inductionHypothesis, Bind.bind, Option.bind, pure]

end Text

end Mettapedia.OSLF.Binding.WireCodec.Binary
