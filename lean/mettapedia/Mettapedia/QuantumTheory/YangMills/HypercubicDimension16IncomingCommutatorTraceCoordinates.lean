import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateCertificate
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceRank

/-!
# OUR exact trace coordinates of the incoming commutator class

The bounded incoming commutator projection is evaluated in the genuine
Reynolds normalization of the ordinary derivative-free eight-field trace
quotient.  The resulting coordinate identity describes that bounded quotient
only: it is not an identification with the complete coordinate-free physical
quotient.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceCoordinates

open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceEvaluationReynolds
open HypercubicDimension16PhysicalTraceQuotient
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16PhysicalTraceEvaluationExecutable
open HypercubicDimension16PhysicalTracePublicConditioning
open HypercubicDimension16IncomingCommutatorTraceCoordinateCore
open HypercubicDimension16IncomingCommutatorTraceCoordinateCertificate

/-- The public trace evaluation of OUR literal incoming class is the
kernel-checked incoming column divided by the Reynolds factor `24`. -/
theorem quotientTraceEvaluation_literalIncoming
    (assignment : Fin 98) :
    quotientTraceEvaluation assignment literalIncomingCommutatorClass =
      (expectedUnsignedEvaluation assignment ⟨6, by decide⟩ -
        expectedUnsignedEvaluation assignment ⟨4, by decide⟩) / 96 := by
  rw [← incomingQuotientTraceEvaluation_eq_public]
  change rawReynoldsTraceEvaluation assignment literalIncomingCommutatorVector = _
  rw [rawReynoldsTraceEvaluation_literalIncoming_eq_unsigned,
    literalIncomingUnsignedEvaluation_replay]
  ring

/-- OUR exact coordinate function for the incoming class in the certified
98-element standard trace basis. -/
def literalIncomingCoordinate (row : Fin 98) : ℚ :=
  (1 / 4 : ℚ) *
    ((if row = ⟨6, by decide⟩ then 1 else 0) -
      (if row = ⟨4, by decide⟩ then 1 else 0))

/-- Each pre-existing public coefficient dual reads the explicitly certified
incoming coordinate. -/
theorem physicalTraceCoefficientDual_literalIncoming
    (row : Fin 98) :
    physicalTraceCoefficientDual row literalIncomingCommutatorClass =
      literalIncomingCoordinate row := by
  simp only [physicalTraceCoefficientDual, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  simp_rw [quotientTraceEvaluation_literalIncoming]
  unfold literalIncomingCoordinate
  calc
    (∑ assignment : Fin 98,
        publicEvaluationInverse row assignment *
          ((expectedUnsignedEvaluation assignment ⟨6, by decide⟩ -
            expectedUnsignedEvaluation assignment ⟨4, by decide⟩) / 96)) =
        (1 / 4 : ℚ) *
          ((∑ assignment : Fin 98,
            publicEvaluationInverse row assignment *
              (expectedUnsignedEvaluation assignment ⟨6, by decide⟩ / 24)) -
            ∑ assignment : Fin 98,
              publicEvaluationInverse row assignment *
                (expectedUnsignedEvaluation assignment ⟨4, by decide⟩ / 24)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro assignment _
      ring
    _ = (1 / 4 : ℚ) *
          ((if row = ⟨6, by decide⟩ then 1 else 0) -
            (if row = ⟨4, by decide⟩ then 1 else 0)) := by
      rw [publicEvaluationInverse_replay,
        publicEvaluationInverse_replay]

/-- The literal incoming class is exactly the difference of the fourth and
sixth certified free classes, with coefficient magnitude one quarter. -/
theorem literalIncomingCommutatorClass_eq_freeCombination :
    literalIncomingCommutatorClass =
      (-(1 / 4 : ℚ)) • physicalTraceFreeClass ⟨4, by decide⟩ +
        (1 / 4 : ℚ) • physicalTraceFreeClass ⟨6, by decide⟩ := by
  apply (Module.Basis.ext_elem_iff physicalTraceFreeBasis).mpr
  intro row
  change physicalTraceFreeBasis.coord row literalIncomingCommutatorClass =
    physicalTraceFreeBasis.coord row
      ((-(1 / 4 : ℚ)) • physicalTraceFreeClass ⟨4, by decide⟩ +
        (1 / 4 : ℚ) • physicalTraceFreeClass ⟨6, by decide⟩)
  rw [← physicalTraceCoefficientDual_eq_coord row]
  simp only [LinearMap.map_add, LinearMap.map_smul,
    smul_eq_mul]
  rw [physicalTraceCoefficientDual_literalIncoming,
    physicalTraceCoefficientDual_freeClass,
    physicalTraceCoefficientDual_freeClass]
  by_cases hfour : row = ⟨4, by decide⟩
  · subst row
    norm_num [literalIncomingCoordinate]
  by_cases hsix : row = ⟨6, by decide⟩
  · subst row
    norm_num [literalIncomingCoordinate]
  ·
    have hfour' : ¬ row = (4 : Fin 98) := by
      intro h
      apply hfour
      simpa using h
    have hsix' : ¬ row = (6 : Fin 98) := by
      intro h
      apply hsix
      simpa using h
    simp [literalIncomingCoordinate, hfour', hsix']

/-- The standard trace-basis coordinate functional of OUR incoming class is
the explicit two-pivot coordinate function. -/
theorem literalIncomingCommutatorClass_coordinate
    (row : Fin 98) :
    (physicalTraceFreeBasis.repr literalIncomingCommutatorClass) row =
      literalIncomingCoordinate row := by
  change physicalTraceFreeBasis.coord row literalIncomingCommutatorClass = _
  rw [← physicalTraceCoefficientDual_eq_coord row]
  exact physicalTraceCoefficientDual_literalIncoming row

#print axioms quotientTraceEvaluation_literalIncoming
#print axioms physicalTraceCoefficientDual_literalIncoming
#print axioms literalIncomingCommutatorClass_eq_freeCombination
#print axioms literalIncomingCommutatorClass_coordinate

end HypercubicDimension16IncomingCommutatorTraceCoordinates
end YangMills
end QuantumTheory
end Mettapedia
