import Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointDistribution
import Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInformation
import Mettapedia.PLN.Comparisons.ScreeningErrorBounds

/-!
# Model discrepancy and PLN approximation are separate errors

A reference joint table and a working joint table may disagree even before
PLN applies a screening approximation. Their full world-weight discrepancy
controls the first error. The working table's dependence or credal bounds
control the second. The resulting budget retains both contributions.
-/

namespace Mettapedia.PLN.Comparisons.ModelErrorBounds

open scoped BigOperators
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointDistribution
open Mettapedia.PLN.Comparisons.ErrorCharacterization
open Mettapedia.PLN.Comparisons.ScreeningErrorBounds
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.ProbabilityTheory.FiniteConditionalStability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.IntervalError

variable {n : ℕ}

/-- A conditional-query budget derived from the full table discrepancy.
The denominator is justified only for supported conditioning queries. -/
noncomputable def queryModelErrorBound (source working : JointDistribution n) (a : Fin n) : ℝ :=
  ((1 / 2 : ℝ) * ∑ world, |source.prob world - working.prob world|) /
    max (marginalProb source a) (marginalProb working a)

theorem query_model_error_le (source working : JointDistribution n) (a c : Fin n)
    (sourcePossible : 0 < marginalProb source a) (workingPossible : 0 < marginalProb working a) :
    |condProb source c a - condProb working c a| ≤ queryModelErrorBound source working a := by
  have sourceSupport : 0 <
      Mettapedia.ProbabilityTheory.FiniteEventMass.mass (probabilityEquiv source).1
        (worldToAssignment n · a) := sourcePossible
  have workingSupport : 0 <
      Mettapedia.ProbabilityTheory.FiniteEventMass.mass (probabilityEquiv working).1
        (worldToAssignment n · a) := workingPossible
  have bound := conditional_error_le_half_l1 (probabilityEquiv source) (probabilityEquiv working)
    (worldToAssignment n · c) (worldToAssignment n · a) sourceSupport workingSupport
  rw [conditional_readout source c a, conditional_readout working c a,
    mass_marginal source a, mass_marginal working a] at bound
  exact bound

/-- Model error plus the actual PLN formula's dependence error. No screening
premise is needed for either term of this guarantee. -/
theorem model_and_screening_error_le (source working : JointDistribution n) (a b c : Fin n)
    (sourcePossible : 0 < marginalProb source a) (workingPossible : 0 < marginalProb working a) :
    |completeDeduction source a b c -
      plnDeductionStrength (condProb working b a) (condProb working c b)
        (marginalProb working b) (marginalProb working c)| ≤
      queryModelErrorBound source working a +
        conservativeErrorEstimate (condProb working b a) (condProb working c b)
          (condProbNeg working c b) := by
  exact (abs_sub_le _ (completeDeduction working a b c) _).trans
    (add_le_add (query_model_error_le source working a c sourcePossible workingPossible)
      (pln_query_error_le_conservative_estimate working a b c workingPossible))

/-- The sharper no-independence interval can be used in the same composition
for any chosen point estimate, including one computed by another system. -/
theorem model_and_credal_error_le (source working : JointDistribution n) (a b c : Fin n)
    (sourcePossible : 0 < marginalProb source a) (workingPossible : 0 < marginalProb working a)
    (estimate : ℝ) :
    |completeDeduction source a b c - estimate| ≤ queryModelErrorBound source working a +
      intervalErrorRadius
        (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.deductionCredalStrengthLower
          (marginalProb working a) (marginalProb working b) (marginalProb working c)
          (condProb working b a) (condProb working c b))
        (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.deductionCredalStrengthUpper
          (marginalProb working a) (marginalProb working b) (marginalProb working c)
          (condProb working b a) (condProb working c b)) estimate := by
  exact (abs_sub_le _ (completeDeduction working a b c) _).trans
    (add_le_add (query_model_error_le source working a c sourcePossible workingPossible)
      (query_error_le_credal_radius working a b c workingPossible estimate))

/-- Full-table model discrepancy and conditional dependence make distinct
contributions. The information term is measured in nats on the working model;
it does not assert that this model is close to the reference model. -/
theorem model_and_information_error_le (source working : JointDistribution n) (a b c : Fin n)
    (sourcePossible : 0 < marginalProb source a) (workingPossible : 0 < marginalProb working a) :
    |completeDeduction source a b c -
      plnDeductionStrength (condProb working b a) (condProb working c b)
        (marginalProb working b) (marginalProb working c)| ≤
      queryModelErrorBound source working a +
        Real.sqrt (Mettapedia.InformationTheory.FiniteRV.condMutualInfo working.prob
          (worldToAssignment n · a) (worldToAssignment n · b) (worldToAssignment n · c) /
            (2 * marginalProb working a)) := by
  exact (abs_sub_le _ (completeDeduction working a b c) _).trans
    (add_le_add (query_model_error_le source working a c sourcePossible workingPossible)
      (Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInformation.query_error_le_sqrt_cmi
        working a b c workingPossible))

end Mettapedia.PLN.Comparisons.ModelErrorBounds
