import Mettapedia.QuantumTheory.YangMills.V14HypercubicFDCensus

/-!
# Padding obstruction to the dimension-sixteen hypercubic `F,D` census

The fixed-width raw carrier makes finiteness easy, but slots beyond the active
field and derivative counts are padding rather than operator syntax.  This
module states the corresponding fidelity requirement explicitly and proves a
terminal obstruction for the current `ExactCensusCertificate`: an invertible
matrix census of the entire padded carrier cannot have every basis column
independent of inactive padding.

The witness has zero active fields and zero active derivatives.  Two encodings
therefore have identical active syntax while differing in one inactive axis
slot.  If every basis column identified those encodings, the right-inverse
matrix identity would identify two distinct rows of the identity matrix.

This theorem does not affect the certified dimension-eight quartic census,
which uses the separate unpadded carrier `Sym OrientedPlane 4`.  It says that
the full dimension-sixteen campaign must first replace the padded raw carrier
by an unpadded/dependent syntax or explicitly quotient padding before a
faithful basis, relation quotient, or conditioning matrix can be certified.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicFDCensusPaddingNoGo

open V14HypercubicFDCensus

/-! ## Active-syntax equivalence -/

/-- Two padded encodings describe the same active raw syntax when their shape
and every field, trace, derivative-order, ownership, and axis entry below the
active counts agree.  No condition is imposed on inactive padding slots. -/
def SameActiveFDSyntax (left right : RawFDMonomial) : Prop :=
  left.shape = right.shape ∧
  (∀ i : Fin 8, i.1 < left.shape.fieldCount.1 →
    left.traceSuccessor i = right.traceSuccessor i ∧
    left.tracePredecessor i = right.tracePredecessor i ∧
    left.fieldFirst i = right.fieldFirst i ∧
    left.fieldSecond i = right.fieldSecond i) ∧
  (∀ j : Fin 16, j.1 < left.shape.derivativeCount.1 →
    left.derivativeOwner j = right.derivativeOwner j ∧
    left.derivativeSuccessor j = right.derivativeSuccessor j ∧
    left.derivativePredecessor j = right.derivativePredecessor j ∧
    left.derivativeAxis j = right.derivativeAxis j)

/-- A coefficient column is faithful to the raw operator syntax only if it
does not inspect inactive padding. -/
def IsPaddingInvariant (coefficients : RawFDMonomial → ℚ) : Prop :=
  ∀ left right, SameActiveFDSyntax left right →
    coefficients left = coefficients right

/-! ## Two distinct encodings of the empty active syntax -/

def emptyShape : FDShape where
  fieldCount := 0
  derivativeCount := 0
  dimension_le := by decide

def identityTraceLayout : PaddedTraceLayout where
  traceSuccessor := id
  tracePredecessor := id

def identityDerivativeLayout : PaddedDerivativeLayout where
  derivativeOwner := fun _ => 0
  derivativeSuccessor := id
  derivativePredecessor := id

def emptyRawWithAxes (axes : PaddedAxisAssignment) : RawFDMonomial :=
  ⟨{ shape := emptyShape
     trace := identityTraceLayout
     derivatives := identityDerivativeLayout
     axes := axes }, by
    simp [PaddedRawFDMonomial.WellFormed, identityTraceLayout,
      identityDerivativeLayout, emptyShape, Function.LeftInverse,
      Function.RightInverse]⟩

def uniformPaddingAxes : PaddedAxisAssignment where
  fieldFirst := fun _ => 0
  fieldSecond := fun _ => 0
  derivativeAxis := fun _ => 0

def splitPaddingAxes : PaddedAxisAssignment where
  fieldFirst := fun i => if i = 0 then 1 else 0
  fieldSecond := fun _ => 0
  derivativeAxis := fun _ => 0

def uniformEmptyRaw : RawFDMonomial :=
  emptyRawWithAxes uniformPaddingAxes

def splitEmptyRaw : RawFDMonomial :=
  emptyRawWithAxes splitPaddingAxes

theorem emptyRaw_sameActiveSyntax :
    SameActiveFDSyntax uniformEmptyRaw splitEmptyRaw := by
  simp [SameActiveFDSyntax, uniformEmptyRaw, splitEmptyRaw,
    emptyRawWithAxes, RawFDMonomial.shape, emptyShape]

theorem emptyRaw_distinct : uniformEmptyRaw ≠ splitEmptyRaw := by
  intro heq
  have haxis := congrArg (fun monomial : RawFDMonomial =>
    monomial.fieldFirst 0) heq
  norm_num [uniformEmptyRaw, splitEmptyRaw, emptyRawWithAxes,
    RawFDMonomial.fieldFirst, uniformPaddingAxes, splitPaddingAxes] at haxis

/-! ## Terminal certificate obstruction -/

/-- No invertible census of the entire padded raw carrier can have all basis
columns faithful to active syntax.  The obstruction is independent of the
chosen coordinate type and occurs before Bianchi, EOM, IBP, trace, or
`SU(2)` Cayley--Hamilton relation rows are considered. -/
theorem no_paddingInvariant_exactCensus
    (Coordinate : Type*) [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : ExactCensusCertificate Coordinate) :
    ¬ ∀ coordinate : Coordinate,
      IsPaddingInvariant (fun monomial =>
        certificate.basisToRaw monomial coordinate) := by
  intro hpadding
  have hrow (coordinate : Coordinate) :
      certificate.basisToRaw uniformEmptyRaw coordinate =
        certificate.basisToRaw splitEmptyRaw coordinate :=
    hpadding coordinate uniformEmptyRaw splitEmptyRaw
      emptyRaw_sameActiveSyntax
  have hproduct :
      (certificate.basisToRaw * certificate.rawToBasis)
          uniformEmptyRaw uniformEmptyRaw =
        (certificate.basisToRaw * certificate.rawToBasis)
          splitEmptyRaw uniformEmptyRaw := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro coordinate _
    rw [hrow coordinate]
  have hidentity :
      (1 : Matrix RawFDMonomial RawFDMonomial ℚ)
          uniformEmptyRaw uniformEmptyRaw =
        (1 : Matrix RawFDMonomial RawFDMonomial ℚ)
          splitEmptyRaw uniformEmptyRaw := by
    rw [← certificate.rightInverse]
    exact hproduct
  simp [Matrix.one_apply] at hidentity
  exact emptyRaw_distinct hidentity.symm

/-- The current dimension-sixteen exact-census target, strengthened only by
the indispensable requirement that every basis vector ignore padding, is
uninhabited. -/
theorem faithful_dimension16_exactCensus_uninhabited :
    ¬ ∃ (Coordinate : Type) (_ : Fintype Coordinate)
        (_ : DecidableEq Coordinate)
        (certificate : ExactCensusCertificate Coordinate),
      ∀ coordinate : Coordinate,
        IsPaddingInvariant (fun monomial =>
          certificate.basisToRaw monomial coordinate) := by
  rintro ⟨Coordinate, coordinateFintype, coordinateDecidableEq,
    certificate, hpadding⟩
  letI : Fintype Coordinate := coordinateFintype
  letI : DecidableEq Coordinate := coordinateDecidableEq
  exact no_paddingInvariant_exactCensus Coordinate certificate hpadding

end V14HypercubicFDCensusPaddingNoGo
end YangMills
end QuantumTheory
end Mettapedia
