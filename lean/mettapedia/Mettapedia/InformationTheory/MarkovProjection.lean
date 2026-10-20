import Mettapedia.InformationTheory.ConditionalMutualInformation

/-!
# Probability laws of the finite Markov projection

Nonnegativity, normalization and support of the pair projection belong to the
finite information-theoretic construction. They do not require a PLN reading.
-/

namespace Mettapedia.InformationTheory.FiniteRV

open scoped BigOperators

variable {Ω α β γ : Type*} [Fintype Ω]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Numerical division by zero agrees with the guarded projection value.
This identity does not interpret a zero-mass conditional as an observation. -/
theorem markovProjection_eq_ratio (p : Ω → ℝ) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) (x : α × β × γ) :
    markovProjection p f g h x =
      law2 p f g (x.1, x.2.1) * law2 p g h (x.2.1, x.2.2) / pushforward p g x.2.1 := by
  unfold markovProjection
  split_ifs with zero
  · simp [zero]
  · rfl

/-- Both Boolean branches contribute to the projected pair mass. Empty
branches contribute zero under the established numerical convention. -/
theorem markovProjectionAC_bool_true_true (p : Ω → ℝ) (f g h : Ω → Bool) :
    markovProjectionAC p f g h (true, true) =
      law2 p f g (true, true) * law2 p g h (true, true) / pushforward p g true +
      law2 p f g (true, false) * law2 p g h (false, true) / pushforward p g false := by
  unfold markovProjectionAC
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Prod.mk.injEq, if_true, if_false,
    true_and, false_and, add_zero, Bool.false_eq_true, markovProjection_eq_ratio]

theorem markovProjectionAC_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) (x : α × γ) : 0 ≤ markovProjectionAC p f g h x :=
  pushforward_nonneg _ (fun y => markovProjection_nonneg p hp f g h y) _ x

theorem sum_markovProjectionAC (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) : ∑ x, markovProjectionAC p f g h x = ∑ ω, p ω := by
  unfold markovProjectionAC
  rw [sum_pushforward, sum_markovProjection p hp f g h]

/-- Wherever the true `(A, C)` law is positive, so is the projected one. -/
theorem markovProjectionAC_pos_of_law2_pos (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α)
    (g : Ω → β) (h : Ω → γ) {x : α × γ} (hx : 0 < law2 p f h x) :
    0 < markovProjectionAC p f g h x := by
  rw [law2_fh_eq_pushforward_law3 p f g h] at hx
  unfold markovProjectionAC
  -- some triple with positive `law3` lies over `x`; the Markov projection is positive there
  unfold pushforward at hx ⊢
  obtain ⟨y, hy, hpos⟩ : ∃ y ∈ Finset.univ.filter (fun y : α × β × γ => (y.1, y.2.2) = x),
      0 < law3 p f g h y := by
    by_contra hcon
    have hall : ∀ y ∈ Finset.univ.filter (fun y : α × β × γ => (y.1, y.2.2) = x),
        law3 p f g h y = 0 := fun y hy =>
      le_antisymm (not_lt.1 fun hlt => hcon ⟨y, hy, hlt⟩) (pushforward_nonneg p hp _ y)
    rw [Finset.sum_eq_zero hall] at hx
    exact lt_irrefl _ hx
  exact lt_of_lt_of_le (markovProjection_pos_of_law3_pos p hp f g h hpos)
    (Finset.single_le_sum (f := markovProjection p f g h)
      (fun y _ => markovProjection_nonneg p hp f g h y) hy)

/-- The source pair law as an existing finite probability vector. -/
noncomputable def law2Prob (p : Prob Ω) (f : Ω → α) (h : Ω → γ) : Prob (α × γ) :=
  ⟨law2 p.1 f h, pushforward_nonneg p.1 p.2.1 _, by
    unfold law2
    rw [sum_pushforward, p.2.2]⟩

/-- The projected pair law carries the same normalization proof discipline. -/
noncomputable def markovProjectionACProb (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    Prob (α × γ) :=
  ⟨markovProjectionAC p.1 f g h, markovProjectionAC_nonneg p.1 p.2.1 f g h, by
    rw [sum_markovProjectionAC p.1 p.2.1 f g h, p.2.2]⟩

/-- The end-to-end Markov projection preserves the entire first marginal,
including outcomes of zero probability. -/
theorem sum_markovProjectionAC_right (p : Ω → ℝ) (hp : ∀ world, 0 ≤ p world)
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) (a : α) :
    (∑ c, markovProjectionAC p f g h (a, c)) = pushforward p f a := by
  unfold markovProjectionAC
  simp only [pushforward_eq_sum_ite]
  rw [Finset.sum_comm]
  have fiber (x : α × β × γ) :
      (∑ c, if (x.1, x.2.2) = (a, c) then markovProjection p f g h x else 0) =
        if x.1 = a then markovProjection p f g h x else 0 := by
    by_cases found : x.1 = a <;> simp [Prod.mk.injEq, found]
  simp_rw [fiber]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp only [if_true]
    simp_rw [sum_markovProjection_right p hp f g h]
    simpa only [pushforward_eq_sum_ite] using sum_law2_right p f g a
  · intro other _ different
    simp [different]
  · simp

end Mettapedia.InformationTheory.FiniteRV
