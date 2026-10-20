import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendTyping
import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendSelectedTyping

/-!
# Retained arrays for the authored indexed vector family

Array append operates on arrays throughout. Its interpretation is compared
with the original polynomial vector append, including every ordered payload
and the dependent sum index. Executable quotation is a separate boundary
operation; it is not used to implement array append.

The comparison also connects array results to the actual checked textual
append function. These are Lean array and guest-calculus results. They do not
qualify CeTTa ownership, a C array layout or a numeric provider.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.VectorArray

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies Declaration.IndexedFamily SchemaElaboration
open IndexedInductiveNatVec Guest.VectorMeaning Guest.AppendMeaning Guest.AppendTyping

/-- The stored array has the length denoted by the authored natural index. -/
abbrev Family (A : Type) (length : Natural.Carrier) :=
  { values : Array A // values.size = Natural.toNat length }

def toList {A : Type} {length : Natural.Carrier} (values : Family A length) :
    Vectors.ListVector A length := ⟨values.val.toList, values.property⟩

def ofList {A : Type} {length : Natural.Carrier} (values : Vectors.ListVector A length) :
    Family A length := ⟨values.val.toArray, values.property⟩

noncomputable def encode {A : Type} {length : Natural.Carrier}
    (value : Vectors.Vector A length) : Family A length := ofList (Vectors.toList value)

noncomputable def decode {A : Type} {length : Natural.Carrier}
    (value : Family A length) : Vectors.Vector A length := Vectors.fromListVector (toList value)

@[simp] theorem encode_decode {A : Type} {length : Natural.Carrier}
    (value : Family A length) : encode (decode value) = value := by
  unfold encode decode
  rw [Vectors.toList_fromListVector]
  rfl

@[simp] theorem decode_encode {A : Type} {length : Natural.Carrier}
    (value : Vectors.Vector A length) : decode (encode value) = value := by
  exact Vectors.fromListVector_toList value

noncomputable def equivalence (A : Type) (length : Natural.Carrier) :
    Vectors.Vector A length ≃ Family A length where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

/-- This implementation uses actual array append, with no semantic decoding
or guest quotation along its execution path. -/
def append {A : Type} {n m : Natural.Carrier}
    (left : Family A n) (right : Family A m) : Family A (Natural.add n m) :=
  ⟨left.val ++ right.val, by
    rw [Array.size_append, left.property, right.property, Natural.toNat_add]⟩

theorem encode_append {A : Type} {n m : Natural.Carrier}
    (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    encode (Vectors.append left right) = append (encode left) (encode right) := by
  apply Subtype.ext
  apply Array.toList_inj.mp
  simpa only [encode, ofList, append, Array.toList_append, List.toList_toArray] using
    Vectors.append_payload left right

@[simp] theorem decode_append {A : Type} {n m : Natural.Carrier}
    (left : Family A n) (right : Family A m) :
    decode (append left right) = Vectors.append (decode left) (decode right) := by
  apply (equivalence A (Natural.add n m)).injective
  change encode (decode (append left right)) = encode (Vectors.append (decode left) (decode right))
  rw [encode_decode, encode_append, encode_decode, encode_decode]

/-- Both directions compare independently defined implementations. Equal
lengths alone are insufficient: decoding retains the entire array. -/
theorem result_iff {A : Type} {n m : Natural.Carrier}
    (left : Family A n) (right : Family A m) (result : Family A (Natural.add n m)) :
    result = append left right ↔
      decode result = Vectors.append (decode left) (decode right) := by
  rw [← decode_append]
  exact ⟨congrArg decode, fun same => (equivalence A (Natural.add n m)).symm.injective same⟩

/-- Concrete arrays determine their source index without a runtime traversal
of the semantic natural carrier. The source index occurs only in the type. -/
def pack {A : Type} (values : Array A) : Family A (Natural.fromNat values.size) :=
  ⟨values, (Natural.toNat_fromNat values.size).symm⟩

/-- A boundary quotation of ordinary values into the declared constructors.
This function is executable independently of the semantic polynomial model. -/
def quoteValues {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0) :
    List A → Tower.Tm 0
  | [] => vnilApp element
  | head :: tail => vconsApp element (numeral tail.length) (payload head)
      (quoteValues element payload tail)

def quoteArray {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (values : Array A) : Tower.Tm 0 := quoteValues element payload values.toList

theorem quoteValues_injective {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (faithful : Function.Injective payload) : Function.Injective (quoteValues element payload) := by
  intro left
  induction left with
  | nil =>
      intro right same
      cases right with
      | nil => rfl
      | cons head tail => simp [quoteValues, vnilApp, vconsApp] at same
  | cons head tail ih =>
      intro right same
      cases right with
      | nil => simp [quoteValues, vnilApp, vconsApp] at same
      | cons other rest =>
          simp only [quoteValues, vconsApp] at same
          have outer := Tm.app.inj same
          have inner := Tm.app.inj outer.1
          exact congrArg₂ List.cons (faithful inner.2) (ih outer.2)

/-- Faithful payload quotation preserves the whole ordered array, including
repeated values. A separate payload contract is required for this conclusion. -/
theorem quoteArray_injective {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (faithful : Function.Injective payload) : Function.Injective (quoteArray element payload) := by
  intro left right same
  exact Array.toList_inj.mp (quoteValues_injective element payload faithful same)

theorem quote_fromList {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (values : List A) :
    quoteValues element payload values = encodeVector element payload (Vectors.fromList values) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change vconsApp element (numeral tail.length) (payload head) (quoteValues element payload tail) =
        encodeVector element payload (Vectors.cons head (Vectors.fromList tail))
      apply (congrArg (vconsApp element (numeral tail.length) (payload head)) ih).trans
      simpa only [quoteIndex, Natural.toNat_fromNat] using
        (Guest.VectorMeaning.encode_cons element payload head (Vectors.fromList tail)).symm

theorem quote_fromListVector {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    {length : Natural.Carrier} (values : Vectors.ListVector A length) :
    quoteValues element payload values.val = encodeVector element payload (Vectors.fromListVector values) := by
  rcases values with ⟨values, equation⟩
  have same : Natural.fromNat values.length = length :=
    (congrArg Natural.fromNat equation).trans (Natural.fromNat_toNat length)
  cases same
  exact quote_fromList element payload values

theorem quote_decode {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    {length : Natural.Carrier} (values : Family A length) :
    quoteArray element payload values.val = encodeVector element payload (decode values) :=
  quote_fromListVector element payload (toList values)

theorem quote_typed {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Typed .nil (payload value) element)
    (values : Array A) :
    Typed .nil (quoteArray element payload values) (vecApp element (numeral values.size)) := by
  have typed := encode_typed element payload elementTyped payloadTyped (decode (pack values))
  simpa only [← quote_decode, pack, quoteIndex, Natural.toNat_fromNat] using typed

/-- The same function returned by the textual module has a typed execution
to the quotation of the independently implemented array append. This proves
that specialization's result comparison, not all-run raw-calculus confluence. -/
theorem compiled_contract (term : Tower.Tm 0)
    (compiled : AppendSource.proposedAppend = some term)
    {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Typed .nil (payload value) element)
    (left right : Array A) :
    FormationSensitive.Judgment Programs.rules .nil
      (applyArgs term [element, numeral left.size, numeral right.size,
        quoteArray element payload left, quoteArray element payload right])
      (vecApp element (Programs.add (numeral left.size) (numeral right.size))) ∧
    ProgramExecutes (applyArgs term [element, numeral left.size, numeral right.size,
      quoteArray element payload left, quoteArray element payload right])
      (quoteArray element payload (left ++ right)) ∧
    FormationSensitive.Judgment Programs.rules .nil
      (quoteArray element payload (left ++ right))
      (vecApp element (Programs.add (numeral left.size) (numeral right.size))) := by
  have contract := Guest.AppendTyping.compiled_contract term compiled element payload
    elementTyped payloadTyped (decode (pack left)) (decode (pack right))
  rw [← decode_append, ← quote_decode, ← quote_decode, ← quote_decode] at contract
  simpa only [pack, append, quoteIndex, Natural.toNat_fromNat] using contract

/-- The emitted function's smaller checking policy also types its actual
array arguments and result. The intervening path uses the original
operational calculus, including vector iota. -/
theorem compiled_selected_contract (term : Tower.Tm 0)
    (compiled : AppendSource.proposedAppend = some term)
    {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : Selected.Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Selected.Typed .nil (payload value) element)
    (left right : Array A) :
    FormationSensitive.Judgment Selected.rules .nil
      (applyArgs term [element, numeral left.size, numeral right.size,
        quoteArray element payload left, quoteArray element payload right])
      (vecApp element (Programs.add (numeral left.size) (numeral right.size))) ∧
    ProgramExecutes (applyArgs term [element, numeral left.size, numeral right.size,
      quoteArray element payload left, quoteArray element payload right])
      (quoteArray element payload (left ++ right)) ∧
    FormationSensitive.Judgment Selected.rules .nil
      (quoteArray element payload (left ++ right))
      (vecApp element (Programs.add (numeral left.size) (numeral right.size))) := by
  have contract := Selected.compiled_contract term compiled element payload
    elementTyped payloadTyped (decode (pack left)) (decode (pack right))
  rw [← decode_append, ← quote_decode, ← quote_decode, ← quote_decode] at contract
  simpa only [pack, append, quoteIndex, Natural.toNat_fromNat] using contract

#print axioms compiled_selected_contract
#print axioms encode_append
#print axioms result_iff
#print axioms quoteArray_injective
#print axioms quote_typed
#print axioms compiled_contract

end Mettapedia.GSLT.LanguageDef.IndexedInductive.VectorArray
