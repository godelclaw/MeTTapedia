import Mettapedia.QuantumTheory.YangMills.SU2AssociatedGradedExtractionDecision

/-!
# Regressions for the dimension-sixteen extraction-repair decision
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2ExtractionRepairDecisionRegression

open SU2AssociatedGradedExtraction
open SU2IndependentTraceBasis
open SU2AssociatedGradedExtractionDecision

example : manuscriptSupExtractionConstant16 < 2 :=
  manuscriptSupExtractionConstant16_lt_two

example : independentTraceSupExtractionConstant16 < 2 :=
  independentTraceSupExtractionConstant16_lt_two

example : extractionDecisionMatrix.length = 6 :=
  extractionDecisionMatrix_length

example : ¬ Nonempty
    (BlockAssociatedGraded16 ≃ₗ[ℂ] (Fin 1851 → ℂ)) :=
  no_associatedGraded_linearEquiv_atMost1851 (by rfl)

#print axioms blockJetBasisPolynomial_linearIndependent
#print axioms blockDualJet16_biorthogonal
#print axioms blockJetMatrix16_eq_one
#print axioms blockAssociatedGraded16_evaluation_injective
#print axioms radialJetCoefficient_polynomial_eval
#print axioms blockAssociatedGradedExtraction16_polynomial_eq
#print axioms blockAssociatedGradedExtraction16_fixes_polynomial
#print axioms blockAssociatedGradedExtraction16_norm_le
#print axioms centeredTrace_semantic_iff_normalForm
#print axioms centeredTrace_blockSemantic_iff
#print axioms centeredTraceDualJet16_biorthogonal
#print axioms centeredTraceJetMatrix16_eq_one
#print axioms polynomialTruncateThroughFour_eval_eq_radialExtraction
#print axioms norm_independentCenteredTraceExtraction16_eval_le
#print axioms blockAssociatedGraded16_finrank
#print axioms no_associatedGraded_linearEquiv_atMost1851
#print axioms extractionDecisionMatrix_agrees
#print axioms associatedGradedProposedLedgerConstant_eq
#print axioms associatedGradedProposedLedger_twoSourceSlack_two_sixteen
#print axioms associatedGradedExtractionDecision_sealed

end SU2ExtractionRepairDecisionRegression
end YangMills
end QuantumTheory
end Mettapedia
