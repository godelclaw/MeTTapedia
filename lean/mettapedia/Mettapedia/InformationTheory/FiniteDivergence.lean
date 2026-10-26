import Mettapedia.InformationTheory.FiniteProbability
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Finite divergence and information retained by observations

`klSum` is the raw real-valued sum of log ratios. Its data-processing laws
require support compatibility; normalization is separate. With unequal masses
the sum may be negative. Equality under an observation means that the two
weightings have proportional restrictions to each observed fibre.
-/

namespace Mettapedia.InformationTheory.FiniteRV

open Real Finset BigOperators

theorem mul_klFun_div (a b : ℝ) (hb : 0 < b) :
    b * _root_.InformationTheory.klFun (a / b) = a * Real.log (a / b) + b - a := by
  unfold _root_.InformationTheory.klFun
  field_simp

/-! ## Divergence sums -/

section DivergenceSums

variable {Ω : Type*}

/-- Divergence sum of `p` against `q` over the finset `s`.  Terms with `p ω = 0` vanish. -/
noncomputable def klSumOn (s : Finset Ω) (p q : Ω → ℝ) : ℝ :=
  ∑ ω ∈ s, p ω * Real.log (p ω / q ω)

/-- Pointwise Gibbs inequality: `a - b ≤ a * log (a / b)` for nonnegative `a, b` with
`b > 0` whenever `a > 0`. -/
theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a → 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  by_cases hb0 : b = 0
  · have ha0 : a = 0 := le_antisymm (not_lt.1 fun h => (hab h).ne' hb0) ha
    simp [ha0, hb0]
  · have h := mul_nonneg hb (_root_.InformationTheory.klFun_nonneg (div_nonneg ha hb))
    rw [mul_klFun_div _ _ (lt_of_le_of_ne hb (Ne.symm hb0))] at h
    linarith

/-- Strict pointwise Gibbs inequality away from `a = b`. -/
theorem sub_lt_mul_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    a - b < a * Real.log (a / b) := by
  have hn := _root_.InformationTheory.klFun_nonneg (div_pos ha hb).le
  have he := _root_.InformationTheory.klFun_eq_zero_iff (div_pos ha hb).le
  have hpos : 0 < _root_.InformationTheory.klFun (a / b) :=
    lt_of_le_of_ne hn (Ne.symm fun h => hne ((div_eq_one_iff_eq hb.ne').1 (he.1 h)))
  have := mul_pos hb hpos
  rw [mul_klFun_div _ _ hb] at this
  linarith

theorem sum_sub_le_klSumOn (s : Finset Ω) (p q : Ω → ℝ)
    (hp : ∀ ω ∈ s, 0 ≤ p ω) (hq : ∀ ω ∈ s, 0 ≤ q ω)
    (hac : ∀ ω ∈ s, 0 < p ω → 0 < q ω) :
    ∑ ω ∈ s, (p ω - q ω) ≤ klSumOn s p q := by
  unfold klSumOn
  exact Finset.sum_le_sum fun ω hω => sub_le_mul_log_div (hp ω hω) (hq ω hω) (hac ω hω)

/-- Gibbs' inequality: if `q` has no more total mass than `p` on `s`, the divergence sum is
nonnegative. -/
theorem klSumOn_nonneg (s : Finset Ω) (p q : Ω → ℝ)
    (hp : ∀ ω ∈ s, 0 ≤ p ω) (hq : ∀ ω ∈ s, 0 ≤ q ω)
    (hac : ∀ ω ∈ s, 0 < p ω → 0 < q ω)
    (hsum : ∑ ω ∈ s, q ω ≤ ∑ ω ∈ s, p ω) :
    0 ≤ klSumOn s p q := by
  have h := sum_sub_le_klSumOn s p q hp hq hac
  rw [Finset.sum_sub_distrib] at h
  linarith

/-- Equality case of Gibbs' inequality: with equal total masses, a vanishing divergence sum
forces `p = q` on `s`. -/
theorem klSumOn_eq_zero_imp (s : Finset Ω) (p q : Ω → ℝ)
    (hp : ∀ ω ∈ s, 0 ≤ p ω) (hq : ∀ ω ∈ s, 0 ≤ q ω)
    (hac : ∀ ω ∈ s, 0 < p ω → 0 < q ω)
    (hsum : ∑ ω ∈ s, q ω = ∑ ω ∈ s, p ω)
    (hzero : klSumOn s p q = 0) :
    ∀ ω ∈ s, p ω = q ω := by
  have hs : (∑ ω ∈ s, (p ω - q ω)) = ∑ ω ∈ s, p ω * log (p ω / q ω) := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]; exact hzero.symm
  have heach := (Finset.sum_eq_sum_iff_of_le (s := s)
    (fun ω hω => sub_le_mul_log_div (hp ω hω) (hq ω hω) (hac ω hω))).1 hs
  intro ω hω
  rcases (hp ω hω).lt_or_eq with hpos | hz
  · by_contra hne
    exact (ne_of_lt (sub_lt_mul_log_div hpos (hac ω hω hpos) hne)) (heach ω hω)
  · have he := heach ω hω
    simp only [← hz, zero_mul, zero_sub] at he
    linarith

/-- Scaling the reference weighting subtracts the logarithm of that scale,
weighted by the total source mass. Zero source entries remain zero. -/
theorem klSumOn_mul_right (s : Finset Ω) (p q : Ω → ℝ)
    (hp : ∀ ω ∈ s, 0 ≤ p ω) (hac : ∀ ω ∈ s, 0 < p ω → 0 < q ω)
    {c : ℝ} (hc : 0 < c) :
    klSumOn s p (fun ω => q ω * c) = klSumOn s p q - (∑ ω ∈ s, p ω) * log c := by
  unfold klSumOn
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ω hω => ?_
  rcases (hp ω hω).lt_or_eq with hpos | hz
  · rw [div_mul_eq_div_div, Real.log_div (div_pos hpos (hac ω hω hpos)).ne' hc.ne']
    ring
  · simp [← hz]

/-- Log-sum inequality; no normalization or equal-mass hypothesis is required. -/
theorem sum_mul_log_le_klSumOn (s : Finset Ω) (p q : Ω → ℝ)
    (hp : ∀ ω ∈ s, 0 ≤ p ω) (hq : ∀ ω ∈ s, 0 ≤ q ω)
    (hac : ∀ ω ∈ s, 0 < p ω → 0 < q ω) :
    (∑ ω ∈ s, p ω) * Real.log ((∑ ω ∈ s, p ω) / (∑ ω ∈ s, q ω)) ≤ klSumOn s p q := by
  by_cases hz : ∑ ω ∈ s, p ω = 0
  · have hall := (Finset.sum_eq_zero_iff_of_nonneg hp).1 hz
    simp +contextual [klSumOn, hall]
  · have hP := lt_of_le_of_ne (Finset.sum_nonneg hp) (Ne.symm hz)
    obtain ⟨ω, hω, hpos⟩ := (Finset.sum_pos_iff_of_nonneg hp).1 hP
    have hQ := lt_of_lt_of_le (hac ω hω hpos) (Finset.single_le_sum hq hω)
    have hc := div_pos hP hQ
    have hn := klSumOn_nonneg s p (fun ω => q ω * ((∑ ω ∈ s, p ω) / ∑ ω ∈ s, q ω)) hp
      (fun ω hω => mul_nonneg (hq ω hω) hc.le)
      (fun ω hω h => mul_pos (hac ω hω h) hc)
      (by rw [← Finset.sum_mul]; exact (mul_div_cancel₀ _ hQ.ne').le)
    rw [klSumOn_mul_right s p q hp hac hc] at hn
    linarith

/-- Equality in log-sum means proportional restrictions, including zero entries.
Cross multiplication also covers an empty fibre or zero source mass. -/
theorem sum_mul_log_eq_klSumOn_iff (s : Finset Ω) (p q : Ω → ℝ)
    (hp : ∀ ω ∈ s, 0 ≤ p ω) (hq : ∀ ω ∈ s, 0 ≤ q ω)
    (hac : ∀ ω ∈ s, 0 < p ω → 0 < q ω) :
    (∑ ω ∈ s, p ω) * log ((∑ ω ∈ s, p ω) / (∑ ω ∈ s, q ω)) = klSumOn s p q ↔
      ∀ ω ∈ s, p ω * (∑ ω ∈ s, q ω) = q ω * (∑ ω ∈ s, p ω) := by
  by_cases hz : ∑ ω ∈ s, p ω = 0
  · have hall := (Finset.sum_eq_zero_iff_of_nonneg hp).1 hz
    simp +contextual [klSumOn, hall]
  · have hP := lt_of_le_of_ne (Finset.sum_nonneg hp) (Ne.symm hz)
    obtain ⟨ω, hω, hpos⟩ := (Finset.sum_pos_iff_of_nonneg hp).1 hP
    have hQ := lt_of_lt_of_le (hac ω hω hpos) (Finset.single_le_sum hq hω)
    let q' := fun ω => q ω * ((∑ ω ∈ s, p ω) / ∑ ω ∈ s, q ω)
    have hc := div_pos hP hQ
    have hscale := klSumOn_mul_right s p q hp hac hc
    have hmass : ∑ ω ∈ s, q' ω = ∑ ω ∈ s, p ω := by
      dsimp [q']; rw [← Finset.sum_mul]; exact mul_div_cancel₀ _ hQ.ne'
    constructor
    · intro he ω hω
      have heq := klSumOn_eq_zero_imp s p q' hp
        (fun ω hω => mul_nonneg (hq ω hω) hc.le)
        (fun ω hω h => mul_pos (hac ω hω h) hc) hmass (by linarith) ω hω
      dsimp [q'] at heq
      rw [← mul_div_assoc] at heq
      exact (eq_div_iff hQ.ne').1 heq
    · intro he
      have same : ∀ ω ∈ s, q' ω = p ω := by
        intro ω hω
        dsimp [q']; rw [← mul_div_assoc, div_eq_iff hQ.ne']
        exact (he ω hω).symm
      have zero : klSumOn s p q' = 0 := by
        unfold klSumOn
        refine Finset.sum_eq_zero fun ω hω => ?_
        rw [same ω hω]
        by_cases h : p ω = 0 <;> simp [h]
      linarith

end DivergenceSums

section Pushforward

variable {Ω : Type*} [Fintype Ω]

/-- Divergence sum of `p` against `q` over the whole finite type. -/
noncomputable def klSum (p q : Ω → ℝ) : ℝ := klSumOn Finset.univ p q

theorem klSum_eq_klSumOn_univ (p q : Ω → ℝ) : klSum p q = klSumOn Finset.univ p q := rfl

theorem klSum_eq_sum (p q : Ω → ℝ) : klSum p q = ∑ ω, p ω * Real.log (p ω / q ω) := rfl

theorem klSum_self_eq_zero (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) : klSum p p = 0 := by
  have _ := hp
  simp [klSum, klSumOn]

/-! ## Pushforward (law of a random variable) -/

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Finite data processing: divergence does not increase under a common pushforward. -/
theorem klSum_pushforward_le [Fintype α] (p q : Ω → ℝ) (φ : Ω → α)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω) (hac : ∀ ω, 0 < p ω → 0 < q ω) :
    klSum (pushforward p φ) (pushforward q φ) ≤ klSum p q := by
  unfold klSum klSumOn
  rw [← Finset.sum_fiberwise Finset.univ φ (fun ω => p ω * Real.log (p ω / q ω))]
  refine Finset.sum_le_sum fun a _ => ?_
  have := sum_mul_log_le_klSumOn (Finset.univ.filter (fun ω => φ ω = a)) p q
    (fun ω _ => hp ω) (fun ω _ => hq ω) (fun ω _ => hac ω)
  unfold klSumOn at this
  exact this

/-- An observation preserves divergence exactly when each observed fibre has
proportional source and reference masses. The criterion concerns this pair of
weightings; the observation need not be injective. -/
theorem klSum_pushforward_eq_iff [Fintype α] (p q : Ω → ℝ) (φ : Ω → α)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω) (hac : ∀ ω, 0 < p ω → 0 < q ω) :
    klSum (pushforward p φ) (pushforward q φ) = klSum p q ↔
      ∀ ω, p ω * pushforward q φ (φ ω) = q ω * pushforward p φ (φ ω) := by
  unfold klSum klSumOn
  rw [← Finset.sum_fiberwise Finset.univ φ (fun ω => p ω * log (p ω / q ω))]
  change (∑ a, (∑ ω ∈ Finset.univ.filter (fun ω => φ ω = a), p ω) *
    log ((∑ ω ∈ Finset.univ.filter (fun ω => φ ω = a), p ω) /
      ∑ ω ∈ Finset.univ.filter (fun ω => φ ω = a), q ω)) =
    (∑ a, klSumOn (Finset.univ.filter (fun ω => φ ω = a)) p q) ↔ _
  rw [Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun a _ => sum_mul_log_le_klSumOn
      (Finset.univ.filter (fun ω => φ ω = a)) p q
      (fun ω _ => hp ω) (fun ω _ => hq ω) (fun ω _ => hac ω))]
  simp only [Finset.mem_univ, forall_const]
  constructor
  · intro he ω
    exact (sum_mul_log_eq_klSumOn_iff _ p q (fun ω _ => hp ω)
      (fun ω _ => hq ω) (fun ω _ => hac ω)).1 (he (φ ω)) ω (by simp)
  · intro he a
    exact (sum_mul_log_eq_klSumOn_iff _ p q (fun ω _ => hp ω)
      (fun ω _ => hq ω) (fun ω _ => hac ω)).2 fun ω hω => by
        simpa only [pushforward, (Finset.mem_filter.1 hω).2] using he ω

/-- Injective observations lose no information about any support-compatible pair. -/
theorem klSum_pushforward_of_injective [Fintype α] (p q : Ω → ℝ) (φ : Ω → α)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω) (hac : ∀ ω, 0 < p ω → 0 < q ω)
    (hφ : Function.Injective φ) : klSum (pushforward p φ) (pushforward q φ) = klSum p q :=
  (klSum_pushforward_eq_iff p q φ hp hq hac).2 fun ω => by
    rw [pushforward_of_injective p φ hφ, pushforward_of_injective q φ hφ, mul_comm]

variable [Fintype α] [Fintype γ]

/-- Mutual information `I(f ; h)`: divergence of the joint law from the product of the
marginals.  Equivalently, the expected divergence of `P(C | A)` from the prior `P(C)`. -/
noncomputable def mutualInfo (p : Ω → ℝ) (f : Ω → α) (h : Ω → γ) : ℝ :=
  klSum (law2 p f h) (fun x => pushforward p f x.1 * pushforward p h x.2)

theorem mutualInfo_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1) (f : Ω → α)
    (h : Ω → γ) : 0 ≤ mutualInfo p f h := by
  unfold mutualInfo klSum
  refine klSumOn_nonneg _ _ _ (fun x _ => pushforward_nonneg p hp _ x)
    (fun x _ => mul_nonneg (pushforward_nonneg p hp f x.1) (pushforward_nonneg p hp h x.2))
    (fun x _ hx => mul_pos (lt_of_lt_of_le hx (law2_le_pushforward_fst p hp f h x))
      (lt_of_lt_of_le hx (law2_le_pushforward_snd p hp f h x))) ?_
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_pushforward, sum_pushforward, hsum, one_mul]
  unfold law2
  rw [sum_pushforward, hsum]

end Pushforward

end Mettapedia.InformationTheory.FiniteRV
