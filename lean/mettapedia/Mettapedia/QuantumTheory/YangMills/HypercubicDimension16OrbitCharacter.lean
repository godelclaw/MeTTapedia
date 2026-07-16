import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LocalWordCarrier
import Mettapedia.QuantumTheory.YangMills.WeightedOrbitBurnside

/-!
# The actual signed character on the local-word orbit carrier

The character in this module is defined directly as the signed fixed-point
sum of the literal hypercubic permutation on genuine field-label orbits.  A
specialization of the weighted twisted Burnside identity then expresses it as
an average of labeled fixed-point sums.  No cycle-index formula is used in
the definition or in this first bridge.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16OrbitCharacter

open HypercubicDimension16LocalWordCarrier
open V14HypercubicFDCensus

def labeledHypercubicEquiv (h : Hypercubic4)
    (fieldCount derivativeCount : ℕ) :
    LabeledLocalWordSector fieldCount derivativeCount ≃
      LabeledLocalWordSector fieldCount derivativeCount where
  toFun := LabeledLocalWordSector.hypercubicAct h
  invFun := LabeledLocalWordSector.hypercubicAct h⁻¹
  left_inv sector := by
    rw [← LabeledLocalWordSector.hypercubicAct_mul, inv_mul_cancel h,
      LabeledLocalWordSector.hypercubicAct_one]
  right_inv sector := by
    rw [← LabeledLocalWordSector.hypercubicAct_mul, mul_inv_cancel h,
      LabeledLocalWordSector.hypercubicAct_one]

theorem labeledHypercubicEquiv_fieldRelabel
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    labeledHypercubicEquiv h fieldCount derivativeCount (rename • sector) =
      rename •
        labeledHypercubicEquiv h fieldCount derivativeCount sector := by
  change (sector.relabel rename).hypercubicAct h =
    (sector.hypercubicAct h).relabel rename
  exact hypercubicAct_relabel h rename sector

theorem tensorSign_fieldRelabel
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    (rename • sector).tensorSign h = sector.tensorSign h := by
  exact LabeledLocalWordSector.tensorSign_relabel h rename sector

/-- The literal signed character on genuine field-label orbits. -/
def actualOrbitCharacter (h : Hypercubic4)
    (fieldCount derivativeCount : ℕ) : ℚ :=
  Finset.univ.sum fun orbit :
      FieldRelabelOrbitCarrier fieldCount derivativeCount =>
    if orbit.hypercubicAct h = orbit then orbit.tensorSign h else 0

/-- The corresponding twisted fixed-point sum before quotienting field
labels. -/
def labeledBurnsideNumerator (h : Hypercubic4)
    (fieldCount derivativeCount : ℕ) : ℚ :=
  Finset.univ.sum fun rename : Equiv.Perm (Fin fieldCount) =>
    Finset.univ.sum fun sector :
        LabeledLocalWordSector fieldCount derivativeCount =>
      if rename • sector.hypercubicAct h = sector then
        sector.tensorSign h
      else 0

theorem genericQuotientTwist_eq_hypercubicAct
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (orbit : FieldRelabelOrbitCarrier fieldCount derivativeCount) :
    WeightedOrbitBurnside.quotientTwist
        (G := Equiv.Perm (Fin fieldCount))
        (labeledHypercubicEquiv h fieldCount derivativeCount)
        (labeledHypercubicEquiv_fieldRelabel h) orbit =
      orbit.hypercubicAct h := by
  refine Quotient.inductionOn orbit ?_
  intro sector
  rfl

theorem genericQuotientWeight_eq_tensorSign
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (orbit : FieldRelabelOrbitCarrier fieldCount derivativeCount) :
    WeightedOrbitBurnside.quotientWeight
        (G := Equiv.Perm (Fin fieldCount))
        (fun sector : LabeledLocalWordSector fieldCount derivativeCount =>
          sector.tensorSign h)
        (tensorSign_fieldRelabel h) orbit =
      orbit.tensorSign h := by
  refine Quotient.inductionOn orbit ?_
  intro sector
  rfl

theorem genericQuotientFixedWeightSum_eq_actualOrbitCharacter
    (h : Hypercubic4) (fieldCount derivativeCount : ℕ) :
    WeightedOrbitBurnside.quotientFixedWeightSum
        (G := Equiv.Perm (Fin fieldCount))
        (labeledHypercubicEquiv h fieldCount derivativeCount)
        (labeledHypercubicEquiv_fieldRelabel h)
        (fun sector : LabeledLocalWordSector fieldCount derivativeCount =>
          sector.tensorSign h)
        (tensorSign_fieldRelabel h) =
      actualOrbitCharacter h fieldCount derivativeCount := by
  unfold WeightedOrbitBurnside.quotientFixedWeightSum actualOrbitCharacter
  apply Finset.sum_congr rfl
  intro orbit _
  rw [genericQuotientTwist_eq_hypercubicAct,
    genericQuotientWeight_eq_tensorSign]

theorem genericLabeledTwistedWeightSum_eq_labeledBurnsideNumerator
    (h : Hypercubic4) (fieldCount derivativeCount : ℕ) :
    WeightedOrbitBurnside.labeledTwistedWeightSum
        (G := Equiv.Perm (Fin fieldCount))
        (labeledHypercubicEquiv h fieldCount derivativeCount)
        (fun sector : LabeledLocalWordSector fieldCount derivativeCount =>
          sector.tensorSign h) =
      labeledBurnsideNumerator h fieldCount derivativeCount := by
  rfl

/-- Exact weighted Burnside bridge for the honest carrier. -/
theorem labeledBurnsideNumerator_eq_factorial_mul_actualOrbitCharacter
    (h : Hypercubic4) (fieldCount derivativeCount : ℕ) :
    labeledBurnsideNumerator h fieldCount derivativeCount =
      Nat.factorial fieldCount *
        actualOrbitCharacter h fieldCount derivativeCount := by
  rw [← genericLabeledTwistedWeightSum_eq_labeledBurnsideNumerator]
  rw [WeightedOrbitBurnside.labeledTwistedWeightSum_eq_card_mul_quotientFixedWeightSum
    (G := Equiv.Perm (Fin fieldCount))
    (twist_equivariant := labeledHypercubicEquiv_fieldRelabel h)
    (weight_invariant := tensorSign_fieldRelabel h)]
  rw [Fintype.card_perm, Fintype.card_fin,
    genericQuotientFixedWeightSum_eq_actualOrbitCharacter]

@[simp] theorem actualOrbitCharacter_one
    (fieldCount derivativeCount : ℕ) :
    actualOrbitCharacter 1 fieldCount derivativeCount =
      Fintype.card (FieldRelabelOrbitCarrier fieldCount derivativeCount) := by
  unfold actualOrbitCharacter
  simp only [FieldRelabelOrbitCarrier.hypercubicAct_one,
    FieldRelabelOrbitCarrier.tensorSign_one, if_pos, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  rfl

end HypercubicDimension16OrbitCharacter
end YangMills
end QuantumTheory
end Mettapedia
