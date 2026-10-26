import Mettapedia.InformationTheory.FiniteDivergence

/-!
# Markov projection and conditional information

The projection preserves both adjacent pair laws and imposes conditional
independence. Its divergence from the joint law is conditional mutual
information. These constructions use finite probability and divergence only;
path decomposition is developed separately in `ConditionalMutualInformation`.
-/

namespace Mettapedia.InformationTheory.FiniteRV

open Real Finset BigOperators

variable {Ω : Type*} [Fintype Ω]
variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ## The Markov projection and conditional mutual information -/

/-- The distribution on `(A, B, C)` that keeps the `(A,B)` and `(B,C)` laws of `p` and imposes
`A ⊥ C | B`: `P_R(a,b,c) = P(a,b) · P(b,c) / P(b)`. -/
noncomputable def markovProjection (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    α × β × γ → ℝ := fun x =>
  if pushforward p g x.2.1 = 0 then 0
  else law2 p f g (x.1, x.2.1) * law2 p g h (x.2.1, x.2.2) / pushforward p g x.2.1

/-- `A ⊥ C | B` under `p`, stated multiplicatively so that it needs no division. -/
def CondIndep (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) : Prop :=
  ∀ x : α × β × γ, law3 p f g h x * pushforward p g x.2.1 =
    law2 p f g (x.1, x.2.1) * law2 p g h (x.2.1, x.2.2)

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

theorem markovProjection_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) (x : α × β × γ) : 0 ≤ markovProjection p f g h x := by
  rw [markovProjection_eq_ratio]
  exact div_nonneg (mul_nonneg (pushforward_nonneg p hp _ _) (pushforward_nonneg p hp _ _))
    (pushforward_nonneg p hp _ _)

variable [Fintype α] [Fintype β] [Fintype γ]

/-- Conditional mutual information `I(f ; h | g)` under the weights `p`, as a sum over the
joint law of the triple. -/
noncomputable def condMutualInfo (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) : ℝ :=
  ∑ x : α × β × γ, law3 p f g h x *
    Real.log (law3 p f g h x * pushforward p g x.2.1 /
      (law2 p f g (x.1, x.2.1) * law2 p g h (x.2.1, x.2.2)))

omit [Fintype β] in
theorem markovProjection_pos_of_law3_pos (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α)
    (g : Ω → β) (h : Ω → γ) {x : α × β × γ} (hx : 0 < law3 p f g h x) :
    0 < markovProjection p f g h x := by
  have h1 : 0 < law2 p f g (x.1, x.2.1) := lt_of_lt_of_le hx (law3_le_law2_fg p hp f g h x)
  have h2 : 0 < law2 p g h (x.2.1, x.2.2) := lt_of_lt_of_le hx (law3_le_law2_gh p hp f g h x)
  have h3 : 0 < pushforward p g x.2.1 :=
    lt_of_lt_of_le h1 (law2_le_pushforward_snd p hp f g (x.1, x.2.1))
  unfold markovProjection
  rw [if_neg h3.ne']
  exact div_pos (mul_pos h1 h2) h3

omit [Fintype β] in
/-- The Markov projection keeps the `(A,B)` law. -/
theorem sum_markovProjection_right (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) (a : α) (b : β) :
    ∑ c, markovProjection p f g h (a, b, c) = law2 p f g (a, b) := by
  unfold markovProjection
  by_cases hz : pushforward p g b = 0
  · simp only [hz, if_true, Finset.sum_const_zero]
    have h1 : law2 p f g (a, b) ≤ pushforward p g b := law2_le_pushforward_snd p hp f g (a, b)
    have h2 : 0 ≤ law2 p f g (a, b) := pushforward_nonneg p hp _ _
    rw [hz] at h1
    linarith
  · simp only [hz, if_false, div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_law2_right p g h b]
    field_simp

omit [Fintype β] in
/-- The Markov projection keeps the `(B,C)` law. -/
theorem sum_markovProjection_left (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) (b : β) (c : γ) :
    ∑ a, markovProjection p f g h (a, b, c) = law2 p g h (b, c) := by
  unfold markovProjection
  by_cases hz : pushforward p g b = 0
  · simp only [hz, if_true, Finset.sum_const_zero]
    have h1 : law2 p g h (b, c) ≤ pushforward p g b := law2_le_pushforward_fst p hp g h (b, c)
    have h2 : 0 ≤ law2 p g h (b, c) := pushforward_nonneg p hp _ _
    rw [hz] at h1
    linarith
  · simp only [hz, if_false, div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_law2_left p f g b]
    field_simp

/-- The Markov projection is a probability distribution whenever `p` is. -/
theorem sum_markovProjection (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) : ∑ x, markovProjection p f g h x = ∑ ω, p ω := by
  simp only [Fintype.sum_prod_type]
  simp_rw [sum_markovProjection_right p hp f g h, sum_law2_right p f g]
  exact sum_pushforward p f

theorem sum_law3 (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    ∑ x, law3 p f g h x = ∑ ω, p ω := sum_pushforward p _

/-- The Markov coarsening identity: `KL(P ∥ P_R) = I(A ; C | B)`. -/
theorem klSum_law3_markovProjection_eq_condMutualInfo (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    klSum (law3 p f g h) (markovProjection p f g h) = condMutualInfo p f g h := by
  have _ := hp
  simp only [klSum_eq_sum, markovProjection_eq_ratio, div_div_eq_mul_div, condMutualInfo]

theorem condMutualInfo_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) : 0 ≤ condMutualInfo p f g h := by
  rw [← klSum_law3_markovProjection_eq_condMutualInfo p hp f g h]
  unfold klSum
  refine klSumOn_nonneg _ _ _ (fun x _ => pushforward_nonneg p hp _ x)
    (fun x _ => markovProjection_nonneg p hp f g h x)
    (fun x _ hx => markovProjection_pos_of_law3_pos p hp f g h hx) ?_
  rw [sum_markovProjection p hp f g h, sum_law3]

omit [Fintype β] in
theorem condIndep_iff_law3_eq_markovProjection (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α)
    (g : Ω → β) (h : Ω → γ) :
    CondIndep p f g h ↔ ∀ x, law3 p f g h x = markovProjection p f g h x := by
  unfold CondIndep
  simp_rw [markovProjection_eq_ratio]
  apply forall_congr'
  intro x
  by_cases hz : pushforward p g x.2.1 = 0
  · have hab := law2_le_pushforward_snd p hp f g (x.1, x.2.1)
    have hab0 : law2 p f g (x.1, x.2.1) = 0 :=
      le_antisymm (hab.trans_eq hz) (pushforward_nonneg p hp _ _)
    have h3 : law3 p f g h x = 0 := le_antisymm
      ((law3_le_law2_fg p hp f g h x).trans_eq hab0) (pushforward_nonneg p hp _ _)
    simp [hz, hab0, h3]
  · exact (eq_div_iff hz).symm

/-- `I(A;C|B) = 0` exactly when `A ⊥ C | B` holds under `p`. -/
theorem condMutualInfo_eq_zero_iff (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) : condMutualInfo p f g h = 0 ↔ CondIndep p f g h := by
  rw [condIndep_iff_law3_eq_markovProjection p hp f g h,
    ← klSum_law3_markovProjection_eq_condMutualInfo p hp f g h]
  constructor
  · intro hzero
    exact fun x => klSumOn_eq_zero_imp Finset.univ _ _ (fun x _ => pushforward_nonneg p hp _ x)
      (fun x _ => markovProjection_nonneg p hp f g h x)
      (fun x _ hx => markovProjection_pos_of_law3_pos p hp f g h hx)
      (by rw [sum_markovProjection p hp f g h]; exact (sum_pushforward p _).symm) hzero x
      (Finset.mem_univ x)
  · intro heq
    rw [← funext heq]
    exact klSum_self_eq_zero _ (pushforward_nonneg p hp _)

/-- The `(A,C)` law of the Markov projection. -/
noncomputable def markovProjectionAC (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    α × γ → ℝ :=
  pushforward (markovProjection p f g h) (fun x => (x.1, x.2.2))

theorem law2_fh_eq_pushforward_law3 (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    law2 p f h = pushforward (law3 p f g h) (fun x => (x.1, x.2.2)) := by
  funext ac
  exact (pushforward_pushforward p (fun ω => (f ω, g ω, h ω)) (fun x => (x.1, x.2.2)) ac).symm

/-- Prop 4.7 (ii): the end-to-end loss on the `(A, C)` law is at most `I(A;C|B)`. -/
theorem klSum_law2_markovProjectionAC_le_condMutualInfo (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    klSum (law2 p f h) (markovProjectionAC p f g h) ≤ condMutualInfo p f g h := by
  rw [← klSum_law3_markovProjection_eq_condMutualInfo p hp f g h,
    law2_fh_eq_pushforward_law3 p f g h]
  unfold markovProjectionAC
  exact klSum_pushforward_le _ _ _ (fun x => pushforward_nonneg p hp _ x)
    (fun x => markovProjection_nonneg p hp f g h x)
    (fun x hx => markovProjection_pos_of_law3_pos p hp f g h hx)

/-- Under `A ⊥ C | B` the Markov projection reproduces the `(A, C)` law exactly. -/
theorem markovProjectionAC_eq_law2_of_condIndep (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α)
    (g : Ω → β) (h : Ω → γ) (hci : CondIndep p f g h) :
    markovProjectionAC p f g h = law2 p f h := by
  rw [law2_fh_eq_pushforward_law3 p f g h, markovProjectionAC,
    funext ((condIndep_iff_law3_eq_markovProjection p hp f g h).1 hci)]

/-- The conditional mutual information as an expectation over outcomes. -/
theorem condMutualInfo_eq_sum_omega (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    condMutualInfo p f g h = ∑ ω, p ω *
      Real.log (law3 p f g h (f ω, g ω, h ω) * pushforward p g (g ω) /
        (law2 p f g (f ω, g ω) * law2 p g h (g ω, h ω))) := by
  exact sum_pushforward_mul p (fun ω => (f ω, g ω, h ω))
    (fun x => Real.log (law3 p f g h x * pushforward p g x.2.1 /
      (law2 p f g (x.1, x.2.1) * law2 p g h (x.2.1, x.2.2))))

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
  rw [law2_fh_eq_pushforward_law3 p f g h, pushforward_pos_iff (law3 p f g h) (pushforward_nonneg p hp _)] at hx
  obtain ⟨y, hy, hpos⟩ := hx
  exact (pushforward_pos_iff _ (markovProjection_nonneg p hp f g h) _ _).2
    ⟨y, hy, markovProjection_pos_of_law3_pos p hp f g h hpos⟩

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
  rw [← pushforward_fst, markovProjectionAC, pushforward_pushforward]
  change pushforward (markovProjection p f g h) Prod.fst a = _
  rw [pushforward_fst]
  simp_rw [Fintype.sum_prod_type, sum_markovProjection_right p hp f g h]
  exact sum_law2_right p f g a

end Mettapedia.InformationTheory.FiniteRV
