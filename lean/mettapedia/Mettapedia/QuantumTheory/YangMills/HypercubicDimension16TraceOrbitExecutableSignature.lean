import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChart

/-!
# Transparent executable signatures for the eight-field orbit chart

The mathematical separating signature is deliberately packaged behind
irreducible definitions.  This module gives formula-identical transparent
versions on labeled representatives and proves that they compute the same
standard carrier invariants.  Finite certificate modules may therefore use
ordinary kernel reduction without replacing the invariant they certify.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitExecutableSignature

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16TraceOrbitSignature
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitChart

/-- Transparent copy of the fixed-width rooted trace code. -/
@[reducible] def executableFieldTraceCode (sector : FieldEightLabeledSector)
    (field : Fin 8) : Nat :=
  ∑ offset : Fin 8,
    fieldTraceDigit sector field offset * 12 ^ offset.1

theorem executableFieldTraceCode_eq (sector : FieldEightLabeledSector)
    (field : Fin 8) :
    executableFieldTraceCode sector field = fieldTraceCode sector field := by
  rw [fieldTraceCode_def]

/-- Transparent copy of the field-label-invariant sorted trace signature. -/
@[reducible] def executableLabeledTraceSignature
    (sector : FieldEightLabeledSector) : List Nat :=
  (Finset.univ.val.map (executableFieldTraceCode sector)).sort (· ≤ ·)

theorem executableLabeledTraceSignature_eq
    (sector : FieldEightLabeledSector) :
    executableLabeledTraceSignature sector = labeledTraceSignature sector := by
  rw [labeledTraceSignature_def]
  unfold executableLabeledTraceSignature
  apply congrArg (fun values : Multiset Nat => values.sort (· ≤ ·))
  apply congrArg (fun code : Fin 8 → Nat => Finset.univ.val.map code)
  funext field
  exact executableFieldTraceCode_eq sector field

/-- The 384 transparent signature images of one labeled representative. -/
@[reducible] def executableHypercubicSignatureMultiset
    (sector : FieldEightLabeledSector) : Multiset (List Nat) :=
  Finset.univ.val.map fun h : Hypercubic4 =>
    executableLabeledTraceSignature (sector.hypercubicAct h)

theorem executableHypercubicSignatureMultiset_eq
    (sector : FieldEightLabeledSector) :
    executableHypercubicSignatureMultiset sector =
      hypercubicSignatureMultiset (Quotient.mk _ sector) := by
  unfold executableHypercubicSignatureMultiset hypercubicSignatureMultiset
  apply congrArg
    (fun signature : Hypercubic4 → List Nat =>
      Finset.univ.val.map signature)
  funext h
  rw [FieldRelabelOrbitCarrier.hypercubicAct_mk,
    fieldEightOrbitSignature_mk]
  exact executableLabeledTraceSignature_eq (sector.hypercubicAct h)

/-- Transparent copy of the canonical minimum over the literal `H(4)`
action. -/
@[reducible] def executableCanonicalHypercubicSignature
    (sector : FieldEightLabeledSector) : List Nat :=
  (((executableHypercubicSignatureMultiset sector).map
      (fun signature : List Nat =>
        (signature : WithTop (List Nat)))).fold min ⊤).untopD []

theorem executableCanonicalHypercubicSignature_eq
    (sector : FieldEightLabeledSector) :
    executableCanonicalHypercubicSignature sector =
      canonicalHypercubicSignature (Quotient.mk _ sector) := by
  unfold executableCanonicalHypercubicSignature
    canonicalHypercubicSignature
  rw [executableHypercubicSignatureMultiset_eq]

/-- Executable canonical signature of one checked chart representative. -/
@[reducible] def executableRepresentativeCanonicalSignature
    (index : PositiveRepresentativeIndex) : List Nat :=
  executableCanonicalHypercubicSignature
    (decodedPositiveRepresentative index)

theorem executableRepresentativeCanonicalSignature_eq
    (index : PositiveRepresentativeIndex) :
    executableRepresentativeCanonicalSignature index =
      canonicalHypercubicSignature (positiveRepresentativeTarget index) := by
  unfold executableRepresentativeCanonicalSignature
    positiveRepresentativeTarget
  exact executableCanonicalHypercubicSignature_eq
    (decodedPositiveRepresentative index)

/-- Executable field-label signature after one literal hypercubic action. -/
@[reducible] def executableRepresentativeSignatureAt
    (index : PositiveRepresentativeIndex) (h : Hypercubic4) : List Nat :=
  executableLabeledTraceSignature
    ((decodedPositiveRepresentative index).hypercubicAct h)

theorem executableRepresentativeSignatureAt_eq
    (index : PositiveRepresentativeIndex) (h : Hypercubic4) :
    executableRepresentativeSignatureAt index h =
      fieldEightOrbitSignature
        ((positiveRepresentativeTarget index).hypercubicAct h) := by
  unfold executableRepresentativeSignatureAt positiveRepresentativeTarget
  rw [FieldRelabelOrbitCarrier.hypercubicAct_mk,
    fieldEightOrbitSignature_mk]
  exact executableLabeledTraceSignature_eq
    ((decodedPositiveRepresentative index).hypercubicAct h)

/-- Executable field-label signature before the hypercubic action. -/
@[reducible] def executableRepresentativeSignature
    (index : PositiveRepresentativeIndex) : List Nat :=
  executableLabeledTraceSignature (decodedPositiveRepresentative index)

theorem executableRepresentativeSignature_eq
    (index : PositiveRepresentativeIndex) :
    executableRepresentativeSignature index =
      fieldEightOrbitSignature (positiveRepresentativeTarget index) := by
  unfold executableRepresentativeSignature positiveRepresentativeTarget
  rw [fieldEightOrbitSignature_mk]
  exact executableLabeledTraceSignature_eq
    (decodedPositiveRepresentative index)

/-- Executable tensor sign on the labeled chart representative. -/
@[reducible] def executableRepresentativeTensorSign
    (index : PositiveRepresentativeIndex) (h : Hypercubic4) : ℚ :=
  (decodedPositiveRepresentative index).tensorSign h

theorem executableRepresentativeTensorSign_eq
    (index : PositiveRepresentativeIndex) (h : Hypercubic4) :
    executableRepresentativeTensorSign index h =
      (positiveRepresentativeTarget index).tensorSign h := by
  rfl

/-! ## Proof-free evaluation on the fixed-width chart -/

/-- Iteration of the stored forward trace map without packaging it as an
equivalence. -/
@[reducible] def encodedTraceIterate (code : Array Nat) :
    Nat → Fin 8 → Fin 8
  | 0, field => field
  | power + 1, field =>
      encodedTraceForward code (encodedTraceIterate code power field)

/-- Fixed-depth evaluator used by the certificate.  Its inputs are only
`0,...,8`; the final branch is the eighth iterate. -/
@[reducible] def encodedTraceIterate8 (code : Array Nat)
    (power : Nat) (field : Fin 8) : Fin 8 :=
  match power with
  | 0 => field
  | 1 => encodedTraceForward code field
  | 2 => encodedTraceForward code (encodedTraceForward code field)
  | 3 => encodedTraceForward code
      (encodedTraceForward code (encodedTraceForward code field))
  | 4 => encodedTraceForward code
      (encodedTraceForward code
        (encodedTraceForward code (encodedTraceForward code field)))
  | 5 => encodedTraceForward code
      (encodedTraceForward code
        (encodedTraceForward code
          (encodedTraceForward code (encodedTraceForward code field))))
  | 6 => encodedTraceForward code
      (encodedTraceForward code
        (encodedTraceForward code
          (encodedTraceForward code
            (encodedTraceForward code (encodedTraceForward code field)))))
  | 7 => encodedTraceForward code
      (encodedTraceForward code
        (encodedTraceForward code
          (encodedTraceForward code
            (encodedTraceForward code
              (encodedTraceForward code (encodedTraceForward code field))))))
  | _ => encodedTraceForward code
      (encodedTraceForward code
        (encodedTraceForward code
          (encodedTraceForward code
            (encodedTraceForward code
              (encodedTraceForward code
                (encodedTraceForward code
                  (encodedTraceForward code field)))))))

/-- One rooted trace digit after a literal hypercubic action, evaluated
directly on the fixed-width chart. -/
@[reducible] def encodedFieldTraceDigitAt (code : Array Nat)
    (h : Hypercubic4) (field : Fin 8) (offset : Fin 8) : Nat :=
  (planeAction h
      (encodedPlane code
        (encodedTraceIterate8 code offset.1 field))).1 +
    if encodedTraceIterate8 code (offset.1 + 1) field = field
      then 6 else 0

/-- Transparent rooted trace code directly on a fixed-width entry. -/
@[reducible] def encodedFieldTraceCodeAt (code : Array Nat)
    (h : Hypercubic4) (field : Fin 8) : Nat :=
  ∑ offset : Fin 8,
    encodedFieldTraceDigitAt code h field offset * 12 ^ offset.1

/-- Transparent field-label signature directly on a fixed-width entry. -/
@[reducible] def encodedLabeledTraceSignatureAt (code : Array Nat)
    (h : Hypercubic4) : List Nat :=
  (Finset.univ.val.map (encodedFieldTraceCodeAt code h)).sort (· ≤ ·)

/-- The 384 direct signature images of a fixed-width entry. -/
@[reducible] def encodedHypercubicSignatureMultiset
    (code : Array Nat) : Multiset (List Nat) :=
  Finset.univ.val.map fun h : Hypercubic4 =>
    encodedLabeledTraceSignatureAt code h

/-- Direct canonical signature of a fixed-width entry. -/
@[reducible] def encodedCanonicalHypercubicSignature
    (code : Array Nat) : List Nat :=
  (((encodedHypercubicSignatureMultiset code).map
      (fun signature : List Nat =>
        (signature : WithTop (List Nat)))).fold min ⊤).untopD []

/-- Direct canonical signature of one checked representative. -/
@[reducible] def directRepresentativeCanonicalSignature
    (index : PositiveRepresentativeIndex) : List Nat :=
  encodedCanonicalHypercubicSignature (positiveRepresentativeCode index)

/-- The 24 reflection-blind sorted-signature images of a fixed-width entry. -/
@[reducible] def encodedUnsignedSignatureMultiset
    (code : Array Nat) : Multiset (List Nat) :=
  Finset.univ.val.map fun permutation : Equiv.Perm Axis =>
    encodedLabeledTraceSignatureAt code
      (unsignedHypercubic permutation)

/-- Canonical sorted rooted-code signature over the unsigned coordinate
permutations. -/
@[reducible] def encodedCanonicalUnsignedSignature
    (code : Array Nat) : List Nat :=
  (((encodedUnsignedSignatureMultiset code).map
      (fun signature : List Nat =>
        (signature : WithTop (List Nat)))).fold min ⊤).untopD []

/-- Optimized 24-action form of the original sorted canonical signature. -/
@[reducible] def directRepresentativeCanonicalUnsignedSignature
    (index : PositiveRepresentativeIndex) : List Nat :=
  encodedCanonicalUnsignedSignature (positiveRepresentativeCode index)

/-- Direct base signature of one checked representative. -/
@[reducible] def directRepresentativeSignature
    (index : PositiveRepresentativeIndex) : List Nat :=
  encodedLabeledTraceSignatureAt (positiveRepresentativeCode index) 1

/-- Direct signature after one literal hypercubic action. -/
@[reducible] def directRepresentativeSignatureAt
    (index : PositiveRepresentativeIndex) (h : Hypercubic4) : List Nat :=
  encodedLabeledTraceSignatureAt (positiveRepresentativeCode index) h

/-- Direct derivative-free tensor sign of one fixed-width entry. -/
@[reducible] def directRepresentativeTensorSign
    (index : PositiveRepresentativeIndex) (h : Hypercubic4) : ℚ :=
  ∏ field : Fin 8,
    (planeTensorSign h
      (encodedPlane (positiveRepresentativeCode index) field) : ℚ)

/-! ## Multiplicative symmetric fingerprint -/

/-- Direct evaluation at `X = 1` of the rooted-code polynomial. -/
@[reducible] def encodedTraceProductSignatureAt (code : Array Nat)
    (h : Hypercubic4) : Nat :=
  ∏ field : Fin 8, (encodedFieldTraceCodeAt code h field + 1)

/-- One rooted digit using a separately supplied trace-iterate table.  A
certificate checks the table recurrence against the stored forward
permutation before this evaluator is used. -/
@[reducible] def encodedFieldTraceDigitFromIterateAt (code : Array Nat)
    (iterate : Fin 8 → Nat → Fin 8) (h : Hypercubic4)
    (field : Fin 8) (offset : Fin 8) : Nat :=
  (planeAction h (encodedPlane code (iterate field offset.1))).1 +
    if iterate field (offset.1 + 1) = field then 6 else 0

/-- Rooted trace code evaluated from a checked trace-iterate table. -/
@[reducible] def encodedFieldTraceCodeFromIterateAt (code : Array Nat)
    (iterate : Fin 8 → Nat → Fin 8) (h : Hypercubic4)
    (field : Fin 8) : Nat :=
  ∑ offset : Fin 8,
    encodedFieldTraceDigitFromIterateAt code iterate h field offset *
      12 ^ offset.1

/-- Product signature evaluated from a checked trace-iterate table. -/
@[reducible] def encodedTraceProductSignatureFromIterateAt
    (code : Array Nat) (iterate : Fin 8 → Nat → Fin 8)
    (h : Hypercubic4) : Nat :=
  ∏ field : Fin 8,
    (encodedFieldTraceCodeFromIterateAt code iterate h field + 1)

/-- Canonical product signature evaluated from a checked trace-iterate
table. -/
@[reducible] def encodedCanonicalUnsignedProductSignatureFromIterate
    (code : Array Nat) (iterate : Fin 8 → Nat → Fin 8) : Nat :=
  (((Finset.univ.val.map fun permutationIndex : Fin 24 =>
      encodedTraceProductSignatureFromIterateAt code iterate
        (unsignedHypercubic (permutationCode permutationIndex))).map
      (fun signature : Nat => (signature : WithTop Nat))).fold min ⊤).untopD 0

/-- The 24 unsigned product-signature images of one fixed-width entry. -/
@[reducible] def encodedUnsignedProductSignatureMultiset
    (code : Array Nat) : Multiset Nat :=
  Finset.univ.val.map fun permutationIndex : Fin 24 =>
    encodedTraceProductSignatureAt code
      (unsignedHypercubic (permutationCode permutationIndex))

/-- Direct canonical product signature over the 24 coordinate
permutations. -/
@[reducible] def encodedCanonicalUnsignedProductSignature
    (code : Array Nat) : Nat :=
  (((encodedUnsignedProductSignatureMultiset code).map
      (fun signature : Nat => (signature : WithTop Nat))).fold min ⊤).untopD 0

/-- Canonical product signature of one checked chart entry. -/
@[reducible] def directRepresentativeCanonicalProductSignature
    (index : PositiveRepresentativeIndex) : Nat :=
  encodedCanonicalUnsignedProductSignature
    (positiveRepresentativeCode index)

/-! ### Bridge back to the standard carrier -/

theorem encodedTraceIterate8_eq_decoded_trace_pow
    (index : PositiveRepresentativeIndex) (power : Nat) (field : Fin 8)
    (hpower : power ≤ 8) :
    encodedTraceIterate8 (positiveRepresentativeCode index) power field =
      ((decodedPositiveRepresentative index).trace ^ power) field := by
  interval_cases power <;> rfl

theorem encodedFieldTraceDigitAt_eq_decoded
    (index : PositiveRepresentativeIndex) (h : Hypercubic4)
    (field : Fin 8) (offset : Fin 8) :
    encodedFieldTraceDigitAt (positiveRepresentativeCode index) h
        field offset =
      fieldTraceDigit
        ((decodedPositiveRepresentative index).hypercubicAct h)
        field offset := by
  unfold encodedFieldTraceDigitAt fieldTraceDigit
  rw [encodedTraceIterate8_eq_decoded_trace_pow index offset.1 field (by omega),
    encodedTraceIterate8_eq_decoded_trace_pow index (offset.1 + 1) field
      (by omega)]
  rfl

theorem encodedFieldTraceCodeAt_eq_decoded
    (index : PositiveRepresentativeIndex) (h : Hypercubic4)
    (field : Fin 8) :
    encodedFieldTraceCodeAt (positiveRepresentativeCode index) h field =
      fieldTraceCode
        ((decodedPositiveRepresentative index).hypercubicAct h) field := by
  rw [fieldTraceCode_def]
  unfold encodedFieldTraceCodeAt
  apply Finset.sum_congr rfl
  intro offset _
  rw [encodedFieldTraceDigitAt_eq_decoded]

theorem encodedTraceProductSignatureAt_eq_decoded
    (index : PositiveRepresentativeIndex) (h : Hypercubic4) :
    encodedTraceProductSignatureAt (positiveRepresentativeCode index) h =
      fieldEightOrbitProductSignature
        ((positiveRepresentativeTarget index).hypercubicAct h) := by
  unfold encodedTraceProductSignatureAt positiveRepresentativeTarget
  rw [FieldRelabelOrbitCarrier.hypercubicAct_mk,
    fieldEightOrbitProductSignature_mk]
  unfold labeledTraceProductSignature
  apply Finset.prod_congr rfl
  intro field _
  rw [encodedFieldTraceCodeAt_eq_decoded]

/-- The transparent 24-entry table is the standard finite type of all axis
permutations. -/
noncomputable def axisPermutationCodeEquiv :
    Fin 24 ≃ Equiv.Perm Axis :=
  Equiv.ofBijective permutationCode permutationCode_bijective

@[simp] theorem axisPermutationCodeEquiv_apply (index : Fin 24) :
    axisPermutationCodeEquiv index = permutationCode index :=
  rfl

theorem encodedUnsignedProductSignatureMultiset_eq
    (index : PositiveRepresentativeIndex) :
    encodedUnsignedProductSignatureMultiset
        (positiveRepresentativeCode index) =
      unsignedProductSignatureMultiset
        (positiveRepresentativeTarget index) := by
  unfold encodedUnsignedProductSignatureMultiset
    unsignedProductSignatureMultiset
  have hfunctions :
      (fun permutationIndex : Fin 24 =>
        encodedTraceProductSignatureAt
          (positiveRepresentativeCode index)
          (unsignedHypercubic (permutationCode permutationIndex))) =
        (fun permutation : Equiv.Perm Axis =>
          fieldEightOrbitProductSignature
            ((positiveRepresentativeTarget index).hypercubicAct
              (unsignedHypercubic permutation))) ∘
          axisPermutationCodeEquiv := by
    funext permutationIndex
    rw [Function.comp_apply, axisPermutationCodeEquiv_apply,
      encodedTraceProductSignatureAt_eq_decoded]
  rw [hfunctions, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

theorem directRepresentativeCanonicalProductSignature_eq
    (index : PositiveRepresentativeIndex) :
    directRepresentativeCanonicalProductSignature index =
      canonicalUnsignedProductSignature
        (positiveRepresentativeTarget index) := by
  unfold directRepresentativeCanonicalProductSignature
    encodedCanonicalUnsignedProductSignature
    canonicalUnsignedProductSignature
  rw [encodedUnsignedProductSignatureMultiset_eq]

/-! ## Symmetric power-sum signature -/

/-- One positive-degree power sum of the eight rooted trace codes. -/
@[reducible] def encodedTracePowerSumAt (code : Array Nat)
    (h : Hypercubic4) (moment : Fin 8) : Nat :=
  ∑ field : Fin 8,
    (encodedFieldTraceCodeAt code h field) ^ (moment.1 + 1)

/-- The first eight power sums, a field-label-invariant signature requiring
no sorting during finite replay. -/
@[reducible] def encodedTraceMomentSignatureAt (code : Array Nat)
    (h : Hypercubic4) : List Nat :=
  List.ofFn fun moment : Fin 8 => encodedTracePowerSumAt code h moment

/-- The eight successive powers of one rooted code, generated once in
increasing degree. -/
@[reducible] def firstEightPowers (value : Nat) : List Nat :=
  let second := value * value
  let third := second * value
  let fourth := third * value
  let fifth := fourth * value
  let sixth := fifth * value
  let seventh := sixth * value
  let eighth := seventh * value
  [value, second, third, fourth, fifth, sixth, seventh, eighth]

/-- Contribution of one field label to all eight power sums. -/
@[reducible] def encodedFieldMomentContribution (code : Array Nat)
    (h : Hypercubic4) (field : Fin 8) : List Nat :=
  firstEightPowers (encodedFieldTraceCodeAt code h field)

/-- Power sums accumulated field by field.  This is extensionally the same
signature as `encodedTraceMomentSignatureAt`, but avoids recomputing a rooted
trace code independently for every degree during finite replay. -/
@[reducible] def encodedTraceMomentSignatureFastAt (code : Array Nat)
    (h : Hypercubic4) : List Nat :=
  (List.ofFn fun field : Fin 8 =>
    encodedFieldMomentContribution code h field).foldl
      (List.zipWith (· + ·)) [0, 0, 0, 0, 0, 0, 0, 0]

/-- The 384 moment-signature images of a fixed-width entry. -/
@[reducible] def encodedHypercubicMomentSignatureMultiset
    (code : Array Nat) : Multiset (List Nat) :=
  Finset.univ.val.map fun h : Hypercubic4 =>
    encodedTraceMomentSignatureAt code h

/-- Canonical minimum of the moment signature over the literal hypercubic
group. -/
@[reducible] def encodedCanonicalHypercubicMomentSignature
    (code : Array Nat) : List Nat :=
  (((encodedHypercubicMomentSignatureMultiset code).map
      (fun signature : List Nat =>
        (signature : WithTop (List Nat)))).fold min ⊤).untopD []

/-- The 24 reflection-blind moment-signature images of a fixed-width entry. -/
@[reducible] def encodedUnsignedMomentSignatureMultiset
    (code : Array Nat) : Multiset (List Nat) :=
  Finset.univ.val.map fun permutation : Equiv.Perm Axis =>
    encodedTraceMomentSignatureFastAt code
      (unsignedHypercubic permutation)

/-- Direct canonical moment signature over the 24 unsigned coordinate
permutations. -/
@[reducible] def encodedCanonicalUnsignedMomentSignature
    (code : Array Nat) : List Nat :=
  (((encodedUnsignedMomentSignatureMultiset code).map
      (fun signature : List Nat =>
        (signature : WithTop (List Nat)))).fold min ⊤).untopD []

/-- Direct canonical moment signature of one checked representative. -/
@[reducible] def directRepresentativeCanonicalMomentSignature
    (index : PositiveRepresentativeIndex) : List Nat :=
  encodedCanonicalHypercubicMomentSignature
    (positiveRepresentativeCode index)

/-- The optimized 24-action canonical moment signature used by the finite
certificate. -/
@[reducible] def directRepresentativeCanonicalUnsignedMomentSignature
    (index : PositiveRepresentativeIndex) : List Nat :=
  encodedCanonicalUnsignedMomentSignature
    (positiveRepresentativeCode index)

end HypercubicDimension16TraceOrbitExecutableSignature
end YangMills
end QuantumTheory
end Mettapedia
