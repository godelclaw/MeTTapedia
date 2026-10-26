import Mettapedia.UniversalAI.SelfModification.ValueFunctions

/-!
# World-action observations of fixed-policy evaluation

Ignoring installed policy names makes names observationally irrelevant to this
evaluator. Agreement of the fixed policies' world actions also preserves all
finite Q/V values. This is a statement about a prediction model, not a claim
that actual self-modification leaves the executed agent unchanged.
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents

def policiesAgreeOnWorldActions (π π' : SelfModPolicy) : Prop :=
  ∀ h : History, (π h).worldAction = (π' h).worldAction

theorem policiesAgreeOnWorldActions_refl (π : SelfModPolicy) :
    policiesAgreeOnWorldActions π π := fun _ => rfl

theorem policiesAgreeOnWorldActions_symm {π π' : SelfModPolicy}
    (h : policiesAgreeOnWorldActions π π') : policiesAgreeOnWorldActions π' π :=
  fun h' => (h h').symm

theorem ignorant_indifferent_to_selfmod (data : IgnorantValueData)
    (h : History) (a a' : PolicyModAction) (n : ℕ)
    (hworld : a.worldAction = a'.worldAction) :
    qValueIgnorant data h a n = qValueIgnorant data h a' n := by
  cases n <;> simp [qValueIgnorant, finiteQ, IgnorantValueData.toFinite, hworld]

/-- Fixed policies with the same world actions give the same predicted returns. -/
theorem ignorant_qValue_policy_congr (data : IgnorantValueData) (π : SelfModPolicy)
    (agree : policiesAgreeOnWorldActions data.fixedPolicy π)
    (h : History) (a b : PolicyModAction) (n : ℕ) (world : a.worldAction = b.worldAction) :
    qValueIgnorant data h a n = qValueIgnorant {data with fixedPolicy := π} h b n := by
  induction n generalizing h a b with
  | zero => rfl
  | succ n ih =>
      by_cases valid : h.wellFormed
      · simp only [qValueIgnorant, finiteQ, IgnorantValueData.toFinite,
          valid, not_true_eq_false, ↓reduceIte, world]
        apply Finset.sum_congr rfl
        intro e _
        congr 3
        exact ih _ _ _ (agree _)
      · simp [qValueIgnorant, finiteQ, valid]

theorem ignorant_vValue_policy_congr (data : IgnorantValueData) (π : SelfModPolicy)
    (agree : policiesAgreeOnWorldActions data.fixedPolicy π) (h : History) (n : ℕ) :
    vValueIgnorant data h n = vValueIgnorant {data with fixedPolicy := π} h n :=
  ignorant_qValue_policy_congr data π agree h _ _ n (agree h)

def isIgnorantOptimal (data : IgnorantValueData) (π : SelfModPolicy) (horizon : ℕ) : Prop :=
  ∀ h : History, ∀ a : PolicyModAction,
    qValueIgnorant data h a horizon ≤ qValueIgnorant data h (π h) horizon

/-- World-action-equivalent actions inherit optimality, not just equality to themselves. -/
theorem ignorant_optimal_selfmod_freedom (data : IgnorantValueData)
    (π : SelfModPolicy) (horizon : ℕ) (optimal : isIgnorantOptimal data π horizon)
    (h : History) (a : PolicyModAction) (world : a.worldAction = (π h).worldAction) :
    ∀ b, qValueIgnorant data h b horizon ≤ qValueIgnorant data h a horizon := by
  rw [ignorant_indifferent_to_selfmod data h a (π h) horizon world]
  exact optimal h

end Mettapedia.UniversalAI.SelfModification
