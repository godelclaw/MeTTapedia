import Mettapedia.UniversalAI.SelfModification.FiniteHorizon

/-!
# Three finite evaluation profiles

All profiles use the same Bellman recursion. Ignorant evaluation keeps its
prediction policy fixed; realistic evaluation follows the name selected by each
action. The hedonistic profile fixes the supplied future utility throughout the
horizon: it does not implement a sequence of utility-changing actions.

These are evaluations of supplied policies, not suprema over policies. Utilities
are real-valued and coefficients are raw weights unless `ProbabilityRows` holds.
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents
open scoped BigOperators

structure HedonisticValueData where
  envProb : History → Percept → ENNReal
  initialPolicy : SelfModPolicy
  γ : DiscountFactor

structure IgnorantValueData where
  envProb : History → Percept → ENNReal
  fixedPolicy : SelfModPolicy
  currentUtility : Utility
  γ : DiscountFactor

structure RealisticValueData where
  envProb : History → Percept → ENNReal
  policyInterp : PolicyInterpreter
  currentUtility : Utility
  γ : DiscountFactor

def HedonisticValueData.toFinite (data : HedonisticValueData) : FiniteValueData :=
  ⟨data.envProb, fun _ => data.initialPolicy, data.γ⟩

def IgnorantValueData.toFinite (data : IgnorantValueData) : FiniteValueData :=
  ⟨data.envProb, fun _ => data.fixedPolicy, data.γ⟩

def RealisticValueData.toFinite (data : RealisticValueData) : FiniteValueData :=
  ⟨data.envProb, fun a => data.policyInterp a.nextPolicyName, data.γ⟩

noncomputable def qValueHedonistic (data : HedonisticValueData)
    (h : History) (a : PolicyModAction) (nextUtility : Utility) (horizon : ℕ) : ℝ :=
  finiteQ data.toFinite nextUtility h a horizon

noncomputable def vValueHedonistic (data : HedonisticValueData)
    (h : History) (nextUtility : Utility) (horizon : ℕ) : ℝ :=
  qValueHedonistic data h (data.initialPolicy h) nextUtility horizon

noncomputable def qValueIgnorant (data : IgnorantValueData)
    (h : History) (a : PolicyModAction) (horizon : ℕ) : ℝ :=
  finiteQ data.toFinite data.currentUtility h a horizon

noncomputable def vValueIgnorant (data : IgnorantValueData)
    (h : History) (horizon : ℕ) : ℝ :=
  qValueIgnorant data h (data.fixedPolicy h) horizon

noncomputable def qValueRealistic (data : RealisticValueData)
    (h : History) (a : PolicyModAction) (horizon : ℕ) : ℝ :=
  finiteQ data.toFinite data.currentUtility h a horizon

/-- The initial policy selects the current action; its argument is essential. -/
noncomputable def vValueRealistic (data : RealisticValueData)
    (initialPolicy : SelfModPolicy) (h : History) (horizon : ℕ) : ℝ :=
  qValueRealistic data h (initialPolicy h) horizon

/-- Actual finite performance under the initial utility and selected continuations. -/
noncomputable def agentPerformance (rmd : RealisticMeasureData) (u₁ : Utility)
    (γ : DiscountFactor) (horizon : ℕ) : ℝ :=
  vValueRealistic ⟨rmd.envProb, rmd.interpret, u₁, γ⟩
    (rmd.interpret rmd.initialPolicy) [] horizon

/-- The selected name controls every immediate successor's action. -/
theorem qValueRealistic_succ (data : RealisticValueData) (h : History)
    (a : PolicyModAction) (n : ℕ) (valid : h.wellFormed) :
    qValueRealistic data h a (n+1) =
      ∑ e : Percept, branchWeight data.envProb h a.worldAction e *
        (data.currentUtility (nextHistory h a.worldAction e) + data.γ.val *
          qValueRealistic data (nextHistory h a.worldAction e)
            (data.policyInterp a.nextPolicyName (nextHistory h a.worldAction e)) n) := by
  simp only [qValueRealistic, finiteQ, valid, not_true_eq_false, ↓reduceIte,
    RealisticValueData.toFinite]

/-- Constant one is a utility value, not a claim that its discounted return is one. -/
def maxUtility : Utility := fun _ => 1

@[simp] theorem maxUtility_apply (h : History) : maxUtility h = 1 := rfl

end Mettapedia.UniversalAI.SelfModification
