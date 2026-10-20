import Mettapedia.Logic.BDD.WMPLNBDDWMCExact
import Mettapedia.Logic.MarkovLogicClauseSemantics
import Mettapedia.PLN.Bridges.ProbabilityTheory.MassSemantics

/-!
# ProbLog and clause-potential models share query-mass semantics

Independent probabilistic facts have an actual unary-clause potential
presentation. Its world weights equal the ProbLog total-choice weights.
Arbitrary derived queries remain explicitly interpreted on those fact worlds;
this does not compile a Horn program into hard material implications.
-/

namespace Mettapedia.PLN.Bridges.Languages.ProbLog.MassSemantics

open scoped ENNReal BigOperators
open Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.Evidence.PLNJointEvidence
open Mettapedia.PLN.Evidence.PLNJointEvidence.JointEvidence
open Mettapedia.Logic.BDDCore.WMPLNBDDWMCExact
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicCountable

variable {n : ℕ}

/-- The finite normalized fact-world semantics uses the shared interface. -/
noncomputable def finiteMassSemantics (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1) :
    Mettapedia.ProbabilityTheory.MassSemantics (Fin (2 ^ n) → Bool) where
  queryMass := queryMass p
  totalMass := totalMass p
  queryMass_le_total event := by
    unfold queryMass totalMass countWorld total probLogToJointEvidence
    apply Finset.sum_le_sum
    intro world _
    split_ifs <;> simp
  totalMass_ne_top := by rw [totalMass_eq_one p normalized]; exact ENNReal.one_ne_top

theorem finiteMassSemantics_queryProb (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (event : Fin (2 ^ n) → Bool) :
    (finiteMassSemantics p normalized).queryProb event = queryProb p event := by
  simp [Mettapedia.ProbabilityTheory.MassSemantics.queryProb, finiteMassSemantics, queryProb,
    totalMass_eq_one p normalized]

/-- The existing PLN proposition carrier is exactly the shared mass readout.
Its coordinates are satisfying and refuting world mass, not sample counts. -/
theorem propEvidence_eq_binaryMass (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (A : Fin n) :
    propEvidence (n := n) (E := probLogToJointEvidence p) A =
      (finiteMassSemantics p normalized).binaryMass (worldToAssignment n · A) := by
  apply Mettapedia.PLN.Evidence.BinaryEvidence.ext'
  · rfl
  change (propEvidence (E := probLogToJointEvidence p) A).neg =
    totalMass p - (propEvidence (E := probLogToJointEvidence p) A).pos
  apply ENNReal.eq_sub_of_add_eq'
    (by rw [totalMass_eq_one p normalized]; exact ENNReal.one_ne_top)
  rw [add_comm]
  exact propEvidence_total_eq_totalMass p A

/-- A single probabilistic fact becomes a unary clause with both truth-value
potentials retained. Zero and one probabilities are supported. -/
noncomputable def factClause (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (i : Fin n) : WeightedGroundClause (Fin n) where
  clause := {Literal.pos i}
  satisfiedPotential := p i
  unsatisfiedPotential := 1 - p i
  satisfied_ne_top := ne_top_of_le_ne_top ENNReal.one_ne_top (normalized i)
  unsatisfied_ne_top := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self

noncomputable def independentFactsMLN (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1) :
    GroundMLN (Fin n) (Fin n) where
  clauseData := factClause p normalized

theorem factClause_eval (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (i : Fin n) (world : Fin n → Bool) :
    (factClause p normalized i).eval world = if world i then p i else 1 - p i := by
  classical
  simp [factClause, WeightedGroundClause.eval, GroundClause.holds, Literal.holds]

/-- The independently defined clause product and ProbLog fact product agree
on every world under the existing bit/assignment correspondence. -/
theorem independentFactsMLN_worldWeight (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (world : Fin (2 ^ n)) :
    (independentFactsMLN p normalized).worldWeight Finset.univ (worldAssignmentEquiv n world) =
      worldWeight p world := by
  rw [GroundMLN.worldWeight_eq_prod]
  simp only [independentFactsMLN, factClause_eval,
    worldAssignmentEquiv_apply, worldWeight, factWeight]

/-- The same conclusion holds for every explicitly interpreted derived query.
The probability numerator is a sum over worlds, not proof occurrences. -/
theorem independentFactsMLN_queryMass (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (event : Fin (2 ^ n) → Bool) :
    (∑ world : Fin (2 ^ n), if event world then
      (independentFactsMLN p normalized).worldWeight Finset.univ (worldAssignmentEquiv n world)
      else 0) = queryMass p event := by
  unfold queryMass countWorld probLogToJointEvidence
  apply Finset.sum_congr rfl
  intro world _
  rw [independentFactsMLN_worldWeight]

/-- The actual finite clause semantics, including its own sum over Boolean
valuations. Queries are transported along the proved world equivalence. -/
noncomputable def clauseMassSemantics (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1) :
    Mettapedia.ProbabilityTheory.MassSemantics (Fin (2 ^ n) → Bool) := by
  letI : Encodable (Fin n → Bool) := GroundMLN.atomValuationEncodable
  exact ((independentFactsMLN p normalized).toCountableMLNSemantics Finset.univ
    (fun event world => event ((worldAssignmentEquiv n).symm world) = true)).toMassSemantics

/-- Reindexing the independent clause model yields the same unnormalized
query and total masses as ProbLog, not only an equal scalar probability. -/
theorem clauseMassSemantics_eq (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1) :
    clauseMassSemantics p normalized = finiteMassSemantics p normalized := by
  classical
  apply Mettapedia.ProbabilityTheory.MassSemantics.ext
  · funext event
    dsimp only [clauseMassSemantics, CountableMLNSemantics.toMassSemantics,
      CountableMLNSemantics.queryMass, GroundMLN.toCountableMLNSemantics]
    rw [tsum_fintype, ← (worldAssignmentEquiv n).sum_comp]
    change _ = queryMass p event
    rw [← independentFactsMLN_queryMass p normalized event]
    apply Finset.sum_congr rfl
    intro world _
    simp only [Equiv.symm_apply_apply]
  · change (∑' world : Fin n → Bool,
      (independentFactsMLN p normalized).worldWeight Finset.univ world) = totalMass p
    rw [tsum_fintype, ← (worldAssignmentEquiv n).sum_comp]
    simp only [independentFactsMLN_worldWeight, totalMass, total, probLogToJointEvidence]

theorem clauseMassSemantics_queryProb (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (event : Fin (2 ^ n) → Bool) :
    (clauseMassSemantics p normalized).queryProb event = queryProb p event := by
  rw [clauseMassSemantics_eq, finiteMassSemantics_queryProb]

namespace Controls

private theorem sum_boolean_two (f : Fin (2 ^ 2) → ℝ≥0∞) :
    (∑ x, f x) = f 0 + (f 1 + (f 2 + f 3)) := by
  change (∑ x : Fin 4, f x) = _
  simp [Fin.sum_univ_succ]

def certainFacts : ProbAssignment 2 := fun _ => 1

theorem certain_explanations_count_once :
    queryProb certainFacts (fun world => worldToAssignment 2 world 0 || worldToAssignment 2 world 1) =
      (1 : ℝ≥0∞) ∧ (1 : ℝ≥0∞) + 1 ≠ 1 := by
  norm_num [queryProb, queryMass, totalMass, countWorld, total, probLogToJointEvidence,
    DistributionSemantics.worldWeight, factWeight, certainFacts, worldToAssignment,
    sum_boolean_two, Fin.prod_univ_succ]

end Controls

end Mettapedia.PLN.Bridges.Languages.ProbLog.MassSemantics
