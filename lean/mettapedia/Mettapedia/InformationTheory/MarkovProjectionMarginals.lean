import Mettapedia.InformationTheory.MarkovProjection

/-!
# Both endpoint marginals of the finite Markov projection

Marginalizing the projected `(A,B,C)` law over the middle variable preserves
both endpoint laws. Empty middle branches are covered by the existing
projection marginal identities.
-/

set_option autoImplicit false

namespace Mettapedia.InformationTheory.FiniteRV

open scoped BigOperators

variable {Ω α β γ : Type*} [Fintype Ω]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-- The endpoint pair retains the second marginal as well as the first. -/
theorem sum_markovProjectionAC_left (p : Ω → ℝ) (positive : ∀ world, 0 ≤ p world)
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) (c : γ) :
    (∑ a, markovProjectionAC p f g h (a, c)) = pushforward p h c := by
  rw [← pushforward_snd, markovProjectionAC, pushforward_pushforward]
  change pushforward (markovProjection p f g h) (Prod.snd ∘ Prod.snd) c = _
  rw [← pushforward_pushforward, pushforward_snd]
  simp_rw [pushforward_snd]
  simp_rw [sum_markovProjection_left p positive f g h]
  exact sum_law2_left p g h c

end Mettapedia.InformationTheory.FiniteRV
