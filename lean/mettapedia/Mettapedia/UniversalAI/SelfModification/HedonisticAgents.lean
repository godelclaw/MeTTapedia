import Mettapedia.UniversalAI.SelfModification.ValueFunctions

/-!
# Monotonicity in a fixed future utility

For the fixed-utility hedonistic specialization, pointwise larger utility gives
larger finite return. This does not construct a utility-modifying optimal policy
or prove the full utility-modification dynamics of Everitt et al., Theorem 14.
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents

theorem utility_bounded_by_max (u : Utility) (h : History) (hbound : u h ≤ 1) :
    u h ≤ maxUtility h := hbound

theorem qValueHedonistic_maxUtility_nonneg (data : HedonisticValueData)
    (h : History) (a : PolicyModAction) (n : ℕ) :
    0 ≤ qValueHedonistic data h a maxUtility n :=
  finiteQ_nonneg data.toFinite maxUtility (fun _ => by simp) h a n

theorem hedonistic_maxUtility_dominates_immediate (u : Utility) (h : History)
    (hbound : ∀ h', u h' ≤ 1) : u h ≤ maxUtility h := hbound h

theorem hedonistic_prefers_maxUtility (data : HedonisticValueData)
    (h : History) (a : PolicyModAction) (u : Utility) (n : ℕ)
    (hbound : ∀ h', u h' ≤ 1) :
    qValueHedonistic data h a u n ≤ qValueHedonistic data h a maxUtility n :=
  finiteQ_mono data.toFinite u maxUtility hbound h a n

/-- Optimality within the supplied fixed-utility evaluation profile. -/
def isHedonisticOptimal (data : HedonisticValueData) (π : SelfModPolicy)
    (u : Utility) (horizon : ℕ) : Prop :=
  ∀ h : History, ∀ a : PolicyModAction,
    qValueHedonistic data h a u horizon ≤ qValueHedonistic data h (π h) u horizon

end Mettapedia.UniversalAI.SelfModification
