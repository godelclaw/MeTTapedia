import Mettapedia.PLN.Core.CompletePLN
import Mettapedia.Logic.BDD.WMPLNBDDWMCExact
import Mettapedia.ProbabilityTheory.FiniteEventMass

/-!
# Exact Boolean observations of a finite weighted world

An arbitrary finite probability table can be pushed forward along a family
of Boolean observations. The resulting joint distribution retains all joint
information about those observations. Its event and conditional queries agree
with the independently defined source sums.
-/

namespace Mettapedia.PLN.Core.FiniteJointPushforward

open scoped BigOperators
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.Logic.BDDCore.WMPLNBDDWMCExact
open Mettapedia.ProbabilityTheory.FiniteEventMass

variable {Ω : Type*} [Fintype Ω] {n : ℕ}

def encode (observations : Ω → Fin n → Bool) (world : Ω) : Fin (2 ^ n) :=
  (worldAssignmentEquiv n).symm (observations world)

omit [Fintype Ω] in
theorem decode_encode (observations : Ω → Fin n → Bool) (world : Ω) (i : Fin n) :
    worldToAssignment n (encode observations world) i = observations world i := by
  rw [← worldAssignmentEquiv_apply]
  exact congrFun ((worldAssignmentEquiv n).apply_symm_apply (observations world)) i

noncomputable def pushforward (weight : Ω → ℝ) (positive : ∀ world, 0 ≤ weight world)
    (normalized : ∑ world, weight world = 1) (observations : Ω → Fin n → Bool) :
    JointDistribution n where
  prob target := ∑ world, if encode observations world = target then weight world else 0
  prob_nonneg target := Finset.sum_nonneg fun world _ => by split_ifs <;> simp_all
  prob_sum_one := by
    rw [Finset.sum_comm]
    simpa using normalized

/-- Pushforward preserves expectations of every real-valued finite query. -/
theorem expected_pushforward (weight : Ω → ℝ) (positive : ∀ world, 0 ≤ weight world)
    (normalized : ∑ world, weight world = 1) (observations : Ω → Fin n → Bool)
    (query : Fin (2 ^ n) → ℝ) :
    (∑ target, (pushforward weight positive normalized observations).prob target * query target) =
      ∑ world, weight world * query (encode observations world) := by
  simp only [pushforward, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem event_pushforward (weight : Ω → ℝ) (positive : ∀ world, 0 ≤ weight world)
    (normalized : ∑ world, weight world = 1) (observations : Ω → Fin n → Bool)
    (event : Fin (2 ^ n) → Bool) :
    mass (pushforward weight positive normalized observations).prob event =
      mass weight (fun world => event (encode observations world)) := by
  have expectation := expected_pushforward weight positive normalized observations
    (fun target => if event target then 1 else 0)
  simpa only [mass, mul_ite, mul_one, mul_zero] using expectation

theorem marginal_pushforward (weight : Ω → ℝ) (positive : ∀ world, 0 ≤ weight world)
    (normalized : ∑ world, weight world = 1) (observations : Ω → Fin n → Bool) (i : Fin n) :
    marginalProb (pushforward weight positive normalized observations) i =
      mass weight (fun world => observations world i) := by
  simpa only [marginalProb, mass, decode_encode] using
    event_pushforward weight positive normalized observations (worldToAssignment n · i)

theorem joint_pushforward (weight : Ω → ℝ) (positive : ∀ world, 0 ≤ weight world)
    (normalized : ∑ world, weight world = 1) (observations : Ω → Fin n → Bool) (i j : Fin n) :
    jointProb2 (pushforward weight positive normalized observations) i j =
      mass weight (fun world => observations world i && observations world j) := by
  simpa only [jointProb2, mass, Bool.and_eq_true, decode_encode] using
    event_pushforward weight positive normalized observations
      (fun target => worldToAssignment n target i && worldToAssignment n target j)

theorem conditional_pushforward (weight : Ω → ℝ) (positive : ∀ world, 0 ≤ weight world)
    (normalized : ∑ world, weight world = 1) (observations : Ω → Fin n → Bool) (i j : Fin n) :
    condProb (pushforward weight positive normalized observations) i j =
      mass weight (fun world => observations world i && observations world j) /
        mass weight (fun world => observations world j) := by
  unfold condProb
  rw [marginal_pushforward, joint_pushforward]
  dsimp only
  split_ifs with impossible
  · simp [impossible]
  · rfl

end Mettapedia.PLN.Core.FiniteJointPushforward
