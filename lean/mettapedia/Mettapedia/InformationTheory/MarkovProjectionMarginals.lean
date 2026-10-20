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
  unfold markovProjectionAC
  simp only [pushforward_eq_sum_ite]
  rw [Finset.sum_comm]
  have fiber (world : α × β × γ) :
      (∑ a, if (world.1, world.2.2) = (a, c) then markovProjection p f g h world else 0) =
        if world.2.2 = c then markovProjection p f g h world else 0 := by
    by_cases found : world.2.2 = c <;> simp [Prod.mk.injEq, found]
  simp_rw [fiber]
  simp only [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp_rw [sum_markovProjection_left p positive f g h]
  simpa only [pushforward_eq_sum_ite] using sum_law2_left p g h c

end Mettapedia.InformationTheory.FiniteRV
