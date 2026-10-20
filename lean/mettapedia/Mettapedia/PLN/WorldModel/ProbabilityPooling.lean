import Mettapedia.ProbabilityTheory.FiniteEnsemble
import Mettapedia.PLN.WorldModel.BinaryWorldModel

/-!
# Unit-mass pooling of model probabilities

Each bounded probability contributes a pair `(p, 1-p)` of total mass one.
The strength of a nonempty sum is exactly the arithmetic mean of the component
probabilities. These pairs represent model votes; their total is not a count
of independent observations or a statistical effective sample size.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ProbabilityPooling

open Mettapedia.PLN.Evidence
open Mettapedia.ProbabilityTheory.FiniteEnsemble
open scoped ENNReal

/-- Give each model probability unit total mass before summing its two coordinates. -/
noncomputable def pool (probabilities : Multiset ℝ≥0∞) : BinaryEvidence :=
  (probabilities.map fun probability => (⟨probability, 1 - probability⟩ : BinaryEvidence)).sum

private theorem pool_cons (probability : ℝ≥0∞) (rest : Multiset ℝ≥0∞) :
    pool (probability ::ₘ rest) = (⟨probability, 1-probability⟩ : BinaryEvidence) + pool rest := by
  simp [pool]

/-- The positive coordinate is the sum of the model probabilities. -/
theorem pool_pos (probabilities : Multiset ℝ≥0∞) : (pool probabilities).pos = probabilities.sum := by
  induction probabilities using Multiset.induction_on with
  | empty => simp [pool]
  | @cons value rest ih =>
    rw [pool_cons]
    change (value + (pool rest).pos) = _
    rw [ih, Multiset.sum_cons]

private theorem total_add (first second : BinaryEvidence) : (first + second).total = first.total + second.total := by
  simp only [BinaryEvidence.total, BinaryEvidence.hplus_def]
  ring

/-- Each bounded component contributes exactly one unit of total mass. -/
theorem pool_total (probabilities : Multiset ℝ≥0∞)
    (bounded : ∀ probability ∈ probabilities, probability ≤ 1) :
    (pool probabilities).total = probabilities.card := by
  revert bounded
  induction probabilities using Multiset.induction_on with
  | empty => simp [pool, BinaryEvidence.total]
  | @cons probability rest ih =>
    intro bounded
    have head := bounded probability (Multiset.mem_cons_self _ _)
    have tail := ih (fun value member => bounded value (Multiset.mem_cons_of_mem member))
    rw [pool_cons, total_add, tail]
    have one : (⟨probability, 1-probability⟩ : BinaryEvidence).total = 1 := by
      change probability + (1-probability) = 1
      rw [add_comm, tsub_add_cancel_of_le head]
    rw [one]
    simp [Multiset.card_cons, add_comm]

/-- A nonempty pool reads out the arithmetic mean, retaining model multiplicities. -/
theorem pool_strength_mean (probabilities : Multiset ℝ≥0∞)
    (bounded : ∀ probability ∈ probabilities, probability ≤ 1)
    (nonempty : 0 < probabilities.card) :
    (BinaryEvidence.toStrength (pool probabilities)).toReal =
      (probabilities.map ENNReal.toReal).sum / probabilities.card := by
  have countNonzero : (probabilities.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast nonempty.ne'
  have finite := finite_sum_toReal probabilities
    (fun value member => ne_top_of_le_ne_top ENNReal.one_ne_top (bounded value member))
  unfold BinaryEvidence.toStrength
  rw [pool_total probabilities bounded]
  simp only [countNonzero, if_false]
  rw [pool_pos, ENNReal.toReal_div, finite.2]
  simp

end Mettapedia.PLN.WorldModel.ProbabilityPooling
