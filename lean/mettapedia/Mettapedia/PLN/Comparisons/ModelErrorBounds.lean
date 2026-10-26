import Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointDistribution
import Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInformation
import Mettapedia.PLN.Comparisons.DeductionStability
import Mettapedia.PLN.Comparisons.ScreeningErrorBounds

/-!
# Model discrepancy and PLN approximation are separate errors

A reference joint table and a working joint table may disagree even before
PLN applies a screening approximation. Their full world-weight discrepancy
controls the first error. The working table's dependence or credal bounds
control the second. The resulting budget retains both contributions.
-/

open scoped BigOperators
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointDistribution
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointBalancedInformation
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.PLN.Comparisons.ErrorCharacterization
open Mettapedia.PLN.Comparisons.ScreeningErrorBounds
open Mettapedia.PLN.Comparisons.DeductionStability
open Mettapedia.ProbabilityTheory.FiniteConditionalStability

variable {n : ℕ} (source working : JointDistribution n) (a b c : Fin n)

namespace Mettapedia.PLN.Comparisons.ModelErrorBounds

/-- A conditional-query budget derived from the full table discrepancy.
The denominator is justified only for supported conditioning queries. -/
noncomputable def queryModelErrorBound : ℝ :=
  ((1 / 2 : ℝ) * ∑ world, |source.prob world - working.prob world|) /
    max (marginalProb source a) (marginalProb working a)

theorem query_model_error_le
    (sourcePossible : 0 < marginalProb source a) (workingPossible : 0 < marginalProb working a) :
    |condProb source c a - condProb working c a| ≤ queryModelErrorBound source working a := by
  have bound := conditional_error_le_half_l1 (probabilityEquiv source) (probabilityEquiv working)
    (worldToAssignment n · c) (worldToAssignment n · a) sourcePossible workingPossible
  rw [conditional_readout source c a, conditional_readout working c a,
    mass_marginal source a, mass_marginal working a] at bound
  exact bound

/-- Model error plus the actual PLN formula's dependence error. No screening
premise is needed for either term of this guarantee. -/
theorem model_and_screening_error_le
    (sourcePossible : 0 < marginalProb source a) (workingPossible : 0 < marginalProb working a) :
    |completeDeduction source a b c -
      estimate (deductionPremises working a b c)| ≤
      queryModelErrorBound source working a +
        conservativeErrorEstimate (condProb working b a) (condProb working c b)
          (condProbNeg working c b) := by
  exact (abs_sub_le _ (completeDeduction working a b c) _).trans
    (add_le_add (query_model_error_le source working a c sourcePossible workingPossible)
      (pln_query_error_le_conservative_estimate working a b c workingPossible))

/-- The sharper no-independence interval can be used in the same composition
for any chosen point estimate, including one computed by another system. -/
theorem model_and_credal_error_le
    (sourcePossible : 0 < marginalProb source a) (workingPossible : 0 < marginalProb working a)
    (estimate : ℝ) :
    |completeDeduction source a b c - estimate| ≤ queryModelErrorBound source working a +
      credalRadius (marginalProb working a) (deductionPremises working a b c) estimate := by
  exact (abs_sub_le _ (completeDeduction working a b c) _).trans
    (add_le_add (query_model_error_le source working a c sourcePossible workingPossible)
      (query_error_le_credal_radius working a b c workingPossible estimate))

/-- Full-table model discrepancy and conditional dependence make distinct
contributions. The information term is measured in nats on the working model;
it does not assert that this model is close to the reference model. -/
theorem model_and_information_error_le
    (sourcePossible : 0 < marginalProb source a) (workingPossible : 0 < marginalProb working a) :
    |completeDeduction source a b c -
      estimate (deductionPremises working a b c)| ≤
      queryModelErrorBound source working a +
        informationRadius (marginalProb working a) (deductionInformation working a b c) := by
  exact (abs_sub_le _ (completeDeduction working a b c) _).trans
    (add_le_add (query_model_error_le source working a c sourcePossible workingPossible)
      (Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInformation.query_error_le_sqrt_cmi
        working a b c workingPossible))

end Mettapedia.PLN.Comparisons.ModelErrorBounds

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointBalancedInformation

open Mettapedia.PLN.Comparisons.ModelErrorBounds

/-- Source-model error and the working model's balanced dependence error are
separate terms. Small CMI in the working model does not bound model mismatch. -/
theorem model_and_balanced_information_error_le (sourcePossible : 0 < marginalProb source a)
    (workingPossible : 0 < marginalProb working a) :
    |completeDeduction source a b c -
      estimate (deductionPremises working a b c)| ≤
      queryModelErrorBound source working a + deductionRadius working a b c := by
  exact (abs_sub_le _ (completeDeduction working a b c) _).trans
    (add_le_add (query_model_error_le source working a c sourcePossible workingPossible)
      (query_error_le_sqrt_balanced_cmi working a b c workingPossible))

end Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointBalancedInformation

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInputStability

open Mettapedia.PLN.Comparisons.ModelErrorBounds

/-- Dependence in the source law and perturbation of the premise readouts
contribute separate, proved terms to the conclusion-error certificate. -/
theorem query_error_with_perturbed_readouts {n : ℕ} (joint : JointDistribution n)
    (a b c : Fin n) (approximate : PremiseValues) (margin : ℝ)
    (possible : 0 < marginalProb joint a) (positive : 0 < margin)
    (sourceSeparated : margin ≤ 1-marginalProb joint b)
    (approximateSeparated : margin ≤ 1-(approximate.b : ℝ)) :
    |completeDeduction joint a b c - estimate approximate| ≤
      FiniteJointDistribution.deductionRadius joint a b c +
      perturbationBudget margin (deductionPremises joint a b c) approximate := by
  exact (abs_sub_le _ (estimate (deductionPremises joint a b c)) _).trans
    (add_le_add (query_error_le_sqrt_balanced_cmi joint a b c possible)
      (estimate_stable (deductionPremises joint a b c) approximate margin positive
        sourceSeparated approximateSeparated))

end Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInputStability
