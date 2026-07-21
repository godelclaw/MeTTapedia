import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartSignCertificate
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The checked orbit chart is a basis of the standard signed quotient

The Reynolds vectors of the decoded chart representatives have disjoint
literal hypercubic-orbit supports.  Their diagonal coefficients are nonzero
because every actual stabilizer has sign `+1`.  They are therefore linearly
independent.  The chart cardinality equals the independently proved Reynolds
invariant dimension, so these vectors form a basis of the standard invariant
subspace and, by the Reynolds equivalence, of the standard signed coinvariant
quotient.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitBasis

open V14HypercubicFDCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitChart
open HypercubicDimension16TraceOrbitChartData
open HypercubicDimension16TraceOrbitChartCertificate
open HypercubicDimension16TraceOrbitChartSignCertificate

/-- A decoded representative averaged into the standard invariant subspace. -/
def positiveRepresentativeReynoldsVector
    (index : PositiveRepresentativeIndex) :
    sectorFieldOrbitInvariantSubmodule 8 0 :=
  ⟨sectorFieldOrbitReynolds 8 0
      (Finsupp.single (positiveRepresentativeTarget index) 1),
    sectorFieldOrbitReynolds_invariant 8 0 _⟩

/-- Point evaluation of a Reynolds-averaged basis vector. -/
theorem fieldEightReynolds_single_apply
    (target probe : FieldEightOrbitCarrier) :
    sectorFieldOrbitReynolds 8 0 (Finsupp.single target 1) probe =
      (1 / 384 : ℚ) *
        ∑ h : Hypercubic4,
          if target.hypercubicAct h = probe then target.tensorSign h else 0 := by
  classical
  unfold sectorFieldOrbitReynolds
  change (1 / 384 : ℚ) *
      (∑ h : Hypercubic4,
        signedSectorFieldOrbitAction h 8 0
          (Finsupp.single target 1) probe) = _
  simp only [signedSectorFieldOrbitAction_single, one_mul,
    Finsupp.single_apply]

/-- Distinct chart representatives give zero off-diagonal evaluations. -/
theorem positiveRepresentativeReynoldsVector_apply_ne
    (source probe : PositiveRepresentativeIndex) (hdifferent : source ≠ probe) :
    (positiveRepresentativeReynoldsVector source : FieldEightOrbitSpace)
        (positiveRepresentativeTarget probe) = 0 := by
  rw [positiveRepresentativeReynoldsVector,
    fieldEightReynolds_single_apply]
  have hseparated :=
    positiveRepresentativeTargets_hypercubic_separated hdifferent
  simp only [hseparated, if_false, Finset.sum_const_zero, mul_zero]

/-- The diagonal evaluation of every chart Reynolds vector is nonzero. -/
theorem positiveRepresentativeReynoldsVector_apply_self_ne_zero
    (index : PositiveRepresentativeIndex) :
    (positiveRepresentativeReynoldsVector index : FieldEightOrbitSpace)
        (positiveRepresentativeTarget index) ≠ 0 := by
  rw [positiveRepresentativeReynoldsVector,
    fieldEightReynolds_single_apply]
  have hsumPositive :
      0 < ∑ h : Hypercubic4,
        if (positiveRepresentativeTarget index).hypercubicAct h =
            positiveRepresentativeTarget index then
          (positiveRepresentativeTarget index).tensorSign h
        else 0 := by
    apply Finset.sum_pos'
    · intro h _
      by_cases hfixed :
          (positiveRepresentativeTarget index).hypercubicAct h =
            positiveRepresentativeTarget index
      · simp [hfixed,
          positiveRepresentativeTarget_stabilizer_sign index h hfixed]
      · simp [hfixed]
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      rw [FieldRelabelOrbitCarrier.hypercubicAct_one,
        FieldRelabelOrbitCarrier.tensorSign_one]
      norm_num
  exact (mul_pos (by norm_num) hsumPositive).ne'

/-- The checked representatives supply a linearly independent Reynolds
family in the independently defined invariant subspace. -/
theorem positiveRepresentativeReynoldsVector_linearIndependent :
    LinearIndependent ℚ positiveRepresentativeReynoldsVector := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients hsum index
  have hsumSpace :
      (∑ source,
          coefficients source •
            (positiveRepresentativeReynoldsVector source :
              FieldEightOrbitSpace)) = 0 :=
    congrArg Subtype.val hsum
  have hevaluation := congrArg
    (fun value : FieldEightOrbitSpace =>
      value (positiveRepresentativeTarget index)) hsumSpace
  change
    (∑ source,
        coefficients source *
          (positiveRepresentativeReynoldsVector source :
            FieldEightOrbitSpace)
              (positiveRepresentativeTarget index)) = 0 at hevaluation
  have hcollapse :
      (∑ source,
          coefficients source *
            (positiveRepresentativeReynoldsVector source :
              FieldEightOrbitSpace)
                (positiveRepresentativeTarget index)) =
        coefficients index *
          (positiveRepresentativeReynoldsVector index :
            FieldEightOrbitSpace)
              (positiveRepresentativeTarget index) := by
    apply Finset.sum_eq_single index
    · intro source _ hsource
      rw [positiveRepresentativeReynoldsVector_apply_ne source index hsource,
        mul_zero]
    · intro hnotMember
      exact False.elim (hnotMember (Finset.mem_univ index))
  rw [hcollapse] at hevaluation
  exact (mul_eq_zero.mp hevaluation).resolve_right
    (positiveRepresentativeReynoldsVector_apply_self_ne_zero index)

/-- The decoded chart is an honest basis of the standard Reynolds-invariant
space; its cardinality is not obtained from the chart itself. -/
def positiveRepresentativeReynoldsBasis :
    Module.Basis PositiveRepresentativeIndex ℚ
      (sectorFieldOrbitInvariantSubmodule 8 0) :=
  basisOfLinearIndependentOfCardEqFinrank
    positiveRepresentativeReynoldsVector_linearIndependent (by
      rw [fieldEightScalarInvariantDimension]
      simp [PositiveRepresentativeIndex, positiveRepresentativeCount])

@[simp] theorem positiveRepresentativeReynoldsBasis_apply
    (index : PositiveRepresentativeIndex) :
    positiveRepresentativeReynoldsBasis index =
      positiveRepresentativeReynoldsVector index := by
  simp [positiveRepresentativeReynoldsBasis]

/-- Transport of the honest Reynolds basis to the standard signed
coinvariant quotient. -/
def positiveRepresentativeCoinvariantBasis :
    Module.Basis PositiveRepresentativeIndex ℚ
      FieldEightSignedOrbitCoinvariant :=
  positiveRepresentativeReynoldsBasis.map
    fieldEightSignedOrbitCoinvariantEquivInvariant.symm

end HypercubicDimension16TraceOrbitBasis
end YangMills
end QuantumTheory
end Mettapedia
