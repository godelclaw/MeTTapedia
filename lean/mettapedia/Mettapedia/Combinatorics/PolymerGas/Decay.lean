import Mettapedia.Combinatorics.PolymerGas.Basic

/-!
# Polymer gases: spatial decay under Dobrushin's criterion

Under Dobrushin's criterion the effect of removing a set `B` of polymers on the
partition functions near a disjoint set `A` is controlled by a supersolution of
an influence recursion.  With `σ(M, a) = Z(M ∖ {a}) / Z(M)`,

`|σ(M, a) - σ(M ∖ B, a)| ≤ e^{2 c a} (1 - e^{-c a}) ∑_s (e^{c s} - 1 or Φ s)`,

the sum running over the polymers `s` of `M` incompatible with `a`, with the
first alternative when `s ∈ B`.  Any `Φ ≥ 0` that dominates the right side bounds
the left side in every finite set of polymers
(`norm_removalRatio_sub_le_of_supersolution`).  The two-region ratio
`Z(Λ) Z(Λ ∖ (A ∪ B)) / (Z(Λ ∖ A) Z(Λ ∖ B))`, which measures the correlation
between the regions of `A` and `B`, then differs from `1` by at most
`e^{2 ∑_A c} ∑_{a ∈ A} Φ a` (`norm_twoRegionRatio_sub_one_le`).

If a distance `d` to `B` grows by at most a size `ℓ s` across each
incompatibility with `s`, and a weight `ρ ≥ 1` satisfies
`∑_{s ∈ S} influenceFactor c s · e^{κ ℓ s} · ρ s ≤ ρ a` for every finite set `S`
of polymers incompatible with a polymer `a`, then
`2 · influenceFactor · ρ · e^{-κ d}` is a supersolution, and the two-region ratio
decays exponentially in `d` (`norm_twoRegionRatio_sub_one_le_exp_weighted`).  On
a lattice the weight `ρ a = e^{τ |a|}` turns the condition into a bound on the
polymers through a single block; `ρ = 1` gives
`norm_twoRegionRatio_sub_one_le_exp`.  The proofs are inductions over finite sets
of polymers; no cluster expansion is used.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Mettapedia.Combinatorics.PolymerGas

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]



variable (G) in
/-- The single-removal ratio `Z(M ∖ {a}) / Z(M)`. -/
def removalRatio (w : V → ℂ) (M : Finset V) (a : V) : ℂ :=
  partitionFunction G w (M.erase a) / partitionFunction G w M

variable (G) in
/-- The set-removal ratio `Z(M ∖ S) / Z(M)`. -/
def sdiffRatio (w : V → ℂ) (M S : Finset V) : ℂ :=
  partitionFunction G w (M \ S) / partitionFunction G w M

section Ratios

variable {w : V → ℂ} {c : V → ℝ} (hD : DobrushinCondition G w c)
include hD

theorem partitionFunction_ne_zero (M : Finset V) : partitionFunction G w M ≠ 0 :=
  (removalBound_of_dobrushin hD M).1

theorem removalRatio_of_notMem {M : Finset V} {a : V} (ha : a ∉ M) :
    removalRatio G w M a = 1 := by
  rw [removalRatio, erase_eq_of_notMem ha, div_self (partitionFunction_ne_zero hD M)]

theorem norm_removalRatio_le (M : Finset V) (a : V) :
    ‖removalRatio G w M a‖ ≤ Real.exp (c a) := by
  rw [removalRatio, norm_div,
    div_le_iff₀ (norm_pos_iff.mpr (partitionFunction_ne_zero hD M))]
  by_cases ha : a ∈ M
  · exact (removalBound_of_dobrushin hD M).2 a ha
  · rw [erase_eq_of_notMem ha]
    have := Real.one_le_exp (hD.nonneg a)
    nlinarith [norm_nonneg (partitionFunction G w M)]

theorem norm_removalRatio_sub_one_le (M : Finset V) (a : V) :
    ‖removalRatio G w M a - 1‖ ≤ Real.exp (c a) - 1 := by
  have hZ := partitionFunction_ne_zero hD M
  rw [removalRatio, div_sub_one hZ, norm_div,
    div_le_iff₀ (norm_pos_iff.mpr hZ)]
  exact norm_partitionFunction_erase_sub_le hD M a

theorem norm_sdiffRatio_le (M S : Finset V) :
    ‖sdiffRatio G w M S‖ ≤ Real.exp (∑ u ∈ S, c u) := by
  rw [sdiffRatio, norm_div,
    div_le_iff₀ (norm_pos_iff.mpr (partitionFunction_ne_zero hD M))]
  exact norm_partitionFunction_sdiff_le_of_dobrushin hD M S

theorem exp_neg_le_norm_sdiffRatio (M S : Finset V) :
    Real.exp (-∑ u ∈ S, c u) ≤ ‖sdiffRatio G w M S‖ := by
  rw [sdiffRatio, norm_div,
    le_div_iff₀ (norm_pos_iff.mpr (partitionFunction_ne_zero hD M))]
  have h := norm_partitionFunction_le_exp_mul_sdiff hD M S
  calc Real.exp (-∑ u ∈ S, c u) * ‖partitionFunction G w M‖
      ≤ Real.exp (-∑ u ∈ S, c u) *
          (Real.exp (∑ u ∈ S, c u) * ‖partitionFunction G w (M \ S)‖) := by gcongr
    _ = ‖partitionFunction G w (M \ S)‖ := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

theorem sdiffRatio_empty (M : Finset V) : sdiffRatio G w M ∅ = 1 := by
  rw [sdiffRatio, sdiff_empty, div_self (partitionFunction_ne_zero hD M)]

theorem sdiffRatio_insert (M S : Finset V) (s : V) :
    sdiffRatio G w M (insert s S) = removalRatio G w (M \ S) s * sdiffRatio G w M S := by
  have hset : M \ insert s S = (M \ S).erase s := by
    ext u
    simp only [mem_sdiff, mem_insert, mem_erase]
    tauto
  rw [sdiffRatio, removalRatio, sdiffRatio, hset,
    div_mul_div_cancel₀ (partitionFunction_ne_zero hD (M \ S))]

/-- The single-removal ratio of a polymer `a ∈ M` solves
`ρ (1 + w a · Z(M' ∖ N)/Z(M')) = 1`, where `M' = M ∖ {a}` and `N` is the set of
polymers of `M'` incompatible with `a`. -/
theorem removalRatio_mul_eq_one {M : Finset V} {a : V} (ha : a ∈ M) :
    removalRatio G w M a *
        (1 + w a * sdiffRatio G w (M.erase a) ((M.erase a).filter (G.Adj a))) = 1 := by
  have hZ := partitionFunction_ne_zero hD M
  have hZe := partitionFunction_ne_zero hD (M.erase a)
  rw [removalRatio, sdiffRatio, sdiff_filter_adj, partitionFunction_eq_erase_add ha]
  rw [partitionFunction_eq_erase_add ha] at hZ
  field_simp

end Ratios

/-- The bound on the change of a single-removal ratio of `s` when a set `B` is
removed: `e^{c s} - 1` if `s ∈ B` itself, and `Φ s` otherwise. -/
def influenceWeight (B : Finset V) (c Φ : V → ℝ) (s : V) : ℝ :=
  if s ∈ B then Real.exp (c s) - 1 else Φ s

theorem influenceWeight_nonneg {B : Finset V} {c Φ : V → ℝ} (hc : ∀ γ, 0 ≤ c γ)
    (hΦ : ∀ γ, 0 ≤ Φ γ) (s : V) : 0 ≤ influenceWeight B c Φ s := by
  unfold influenceWeight
  split_ifs
  · have := Real.one_le_exp (hc s)
    linarith
  · exact hΦ s

section Influence

variable {w : V → ℂ} {c : V → ℝ} (hD : DobrushinCondition G w c)
include hD

/-- Removing `B` changes a set-removal ratio by at most `e^{∑_N c}` times the
sum of the influence weights, once single ratios are controlled below `T`. -/
theorem norm_sdiffRatio_sub_le {B : Finset V} {Φ : V → ℝ} (hΦ : ∀ γ, 0 ≤ Φ γ)
    {T : Finset V}
    (hT : ∀ T' ⊆ T, ∀ s, s ∉ B →
      ‖removalRatio G w T' s - removalRatio G w (T' \ B) s‖ ≤ Φ s)
    (N : Finset V) :
    ‖sdiffRatio G w T N - sdiffRatio G w (T \ B) N‖ ≤
      Real.exp (∑ u ∈ N, c u) * ∑ s ∈ N, influenceWeight B c Φ s := by
  induction N using Finset.induction_on with
  | empty => simp [sdiffRatio_empty hD]
  | insert s N hs ih =>
    rw [sdiffRatio_insert hD T N s, sdiffRatio_insert hD (T \ B) N s, sum_insert hs,
      sum_insert hs, Real.exp_add]
    have hswap : (T \ B) \ N = (T \ N) \ B := by
      ext u
      simp only [mem_sdiff]
      tauto
    rw [hswap]
    set x := removalRatio G w (T \ N) s
    set x' := removalRatio G w ((T \ N) \ B) s
    set y := sdiffRatio G w T N
    set y' := sdiffRatio G w (T \ B) N
    have hx : ‖x - x'‖ ≤ influenceWeight B c Φ s := by
      unfold influenceWeight
      split_ifs with hsB
      · have hx'1 : x' = 1 := removalRatio_of_notMem hD (fun h => (mem_sdiff.mp h).2 hsB)
        rw [hx'1]
        exact norm_removalRatio_sub_one_le hD (T \ N) s
      · exact hT (T \ N) sdiff_subset s hsB
    have hy : ‖y‖ ≤ Real.exp (∑ u ∈ N, c u) := norm_sdiffRatio_le hD T N
    have hx' : ‖x'‖ ≤ Real.exp (c s) := norm_removalRatio_le hD ((T \ N) \ B) s
    have hw := influenceWeight_nonneg (B := B) hD.nonneg hΦ s
    have hsum : 0 ≤ ∑ t ∈ N, influenceWeight B c Φ t :=
      sum_nonneg fun t _ => influenceWeight_nonneg hD.nonneg hΦ t
    have hone : 1 ≤ Real.exp (c s) := Real.one_le_exp (hD.nonneg s)
    have hEN := Real.exp_pos (∑ u ∈ N, c u)
    calc ‖x * y - x' * y'‖ = ‖(x - x') * y + x' * (y - y')‖ := by
          congr 1
          ring
      _ ≤ ‖x - x'‖ * ‖y‖ + ‖x'‖ * ‖y - y'‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ influenceWeight B c Φ s * Real.exp (∑ u ∈ N, c u) +
            Real.exp (c s) * (Real.exp (∑ u ∈ N, c u) * ∑ t ∈ N, influenceWeight B c Φ t) := by
          gcongr
      _ ≤ Real.exp (c s) * Real.exp (∑ u ∈ N, c u) *
            (influenceWeight B c Φ s + ∑ t ∈ N, influenceWeight B c Φ t) := by
          nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hone) hEN.le) hw]

/-- A supersolution of the influence recursion for removing `B`. -/
def IsInfluenceSupersolution (B : Finset V) (Φ : V → ℝ) : Prop :=
  (∀ γ, 0 ≤ Φ γ) ∧
    ∀ a, a ∉ B → ∀ S : Finset V, (∀ s ∈ S, G.Adj a s) →
      Real.exp (2 * c a) * (1 - Real.exp (-c a)) * ∑ s ∈ S, influenceWeight B c Φ s ≤ Φ a

/-- **Influence bound.**  If `Φ` is a supersolution of the influence recursion,
removing `B` changes the single-removal ratio of every polymer `a ∉ B` by at
most `Φ a`, in every finite set of polymers. -/
theorem norm_removalRatio_sub_le_of_supersolution {B : Finset V} {Φ : V → ℝ}
    (hΦ : IsInfluenceSupersolution (G := G) (c := c) B Φ) (M : Finset V) :
    ∀ a, a ∉ B → ‖removalRatio G w M a - removalRatio G w (M \ B) a‖ ≤ Φ a := by
  induction M using Finset.strongInduction with
  | H M ih =>
    intro a haB
    by_cases haM : a ∈ M
    · set T := M.erase a with hTdef
      have hTsub : ∀ T' ⊆ T, ∀ s, s ∉ B →
          ‖removalRatio G w T' s - removalRatio G w (T' \ B) s‖ ≤ Φ s := fun T' hT' s hs =>
        ih T' (_root_.ssubset_of_subset_of_ssubset hT' (erase_ssubset haM)) s hs
      set N := T.filter (G.Adj a)
      have haMB : a ∈ M \ B := mem_sdiff.mpr ⟨haM, haB⟩
      have hTB : (M \ B).erase a = T \ B := by
        ext u
        simp only [mem_erase, mem_sdiff, hTdef]
        tauto
      have hNB : ((M \ B).erase a).filter (G.Adj a) = N \ B := by
        rw [hTB]
        ext u
        simp only [mem_filter, mem_sdiff, N]
        tauto
      have hqB : sdiffRatio G w ((M \ B).erase a) (((M \ B).erase a).filter (G.Adj a)) =
          sdiffRatio G w (T \ B) N := by
        rw [hNB, hTB]
        unfold sdiffRatio
        rw [show (T \ B) \ (N \ B) = (T \ B) \ N by
          ext u
          simp only [mem_sdiff]
          tauto]
      have hρ := removalRatio_mul_eq_one hD haM
      have hρB := removalRatio_mul_eq_one hD haMB
      rw [hqB] at hρB
      set q := sdiffRatio G w T N
      set qB := sdiffRatio G w (T \ B) N
      set ρ := removalRatio G w M a
      set ρB := removalRatio G w (M \ B) a
      have hdiff : ρ - ρB = ρ * ρB * (w a * (qB - q)) := by
        linear_combination ρB * hρ - ρ * hρB
      have hρn : ‖ρ‖ ≤ Real.exp (c a) := norm_removalRatio_le hD M a
      have hρBn : ‖ρB‖ ≤ Real.exp (c a) := norm_removalRatio_le hD (M \ B) a
      have hqdiff := norm_sdiffRatio_sub_le hD hΦ.1 hTsub N
      have hw := hD.bound a N fun s hs => (mem_filter.mp hs).2
      have hsum : 0 ≤ ∑ s ∈ N, influenceWeight B c Φ s :=
        sum_nonneg fun t _ => influenceWeight_nonneg hD.nonneg hΦ.1 t
      have hsup := hΦ.2 a haB N fun s hs => (mem_filter.mp hs).2
      have hfac : 0 ≤ 1 - Real.exp (-c a) := by
        have : Real.exp (-c a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hD.nonneg a])
        linarith
      rw [hdiff]
      have hmain : ‖ρ‖ * ‖ρB‖ * (‖w a‖ * ‖q - qB‖) ≤ Real.exp (c a) * Real.exp (c a) *
          (((1 - Real.exp (-c a)) * Real.exp (-∑ u ∈ N, c u)) *
            (Real.exp (∑ u ∈ N, c u) * ∑ s ∈ N, influenceWeight B c Φ s)) :=
        mul_le_mul (mul_le_mul hρn hρBn (norm_nonneg _) (Real.exp_pos _).le)
          (mul_le_mul hw hqdiff (norm_nonneg _) (mul_nonneg hfac (Real.exp_pos _).le))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      have h1 : Real.exp (c a) * Real.exp (c a) = Real.exp (2 * c a) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h2 : Real.exp (-∑ u ∈ N, c u) * Real.exp (∑ u ∈ N, c u) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      calc ‖ρ * ρB * (w a * (qB - q))‖ = ‖ρ‖ * ‖ρB‖ * (‖w a‖ * ‖q - qB‖) := by
            rw [norm_mul, norm_mul, norm_mul, norm_sub_rev]
        _ ≤ Real.exp (c a) * Real.exp (c a) *
              (((1 - Real.exp (-c a)) * Real.exp (-∑ u ∈ N, c u)) *
                (Real.exp (∑ u ∈ N, c u) * ∑ s ∈ N, influenceWeight B c Φ s)) := hmain
        _ = (Real.exp (c a) * Real.exp (c a)) * (1 - Real.exp (-c a)) *
              (Real.exp (-∑ u ∈ N, c u) * Real.exp (∑ u ∈ N, c u)) *
                ∑ s ∈ N, influenceWeight B c Φ s := by ring
        _ = Real.exp (2 * c a) * (1 - Real.exp (-c a)) *
              ∑ s ∈ N, influenceWeight B c Φ s := by rw [h1, h2, mul_one]
        _ ≤ Φ a := hsup
    · have h1 : removalRatio G w M a = 1 := removalRatio_of_notMem hD haM
      have h2 : removalRatio G w (M \ B) a = 1 :=
        removalRatio_of_notMem hD fun h => haM (mem_sdiff.mp h).1
      rw [h1, h2, sub_self, norm_zero]
      exact hΦ.1 a

end Influence

section TwoRegion

variable {w : V → ℂ} {c : V → ℝ} (hD : DobrushinCondition G w c)
include hD

/-- **Two-region decay.**  If `Φ` is a supersolution of the influence recursion
for removing `B`, then for every finite `Λ` and every finite `A` disjoint from
`B`, the ratio `Z(Λ) Z(Λ ∖ (A ∪ B)) / (Z(Λ ∖ A) Z(Λ ∖ B))` differs from `1` by at
most `e^{2 ∑_{a∈A} c a} ∑_{a ∈ A} Φ a`. -/
theorem norm_twoRegionRatio_sub_one_le {A B : Finset V} (hAB : Disjoint A B) {Φ : V → ℝ}
    (hΦ : IsInfluenceSupersolution (G := G) (c := c) B Φ) (Λ : Finset V) :
    ‖partitionFunction G w Λ * partitionFunction G w (Λ \ (A ∪ B)) /
        (partitionFunction G w (Λ \ A) * partitionFunction G w (Λ \ B)) - 1‖ ≤
      Real.exp (2 * ∑ a ∈ A, c a) * ∑ a ∈ A, Φ a := by
  have hinf : ∀ T' ⊆ Λ, ∀ s, s ∉ B →
      ‖removalRatio G w T' s - removalRatio G w (T' \ B) s‖ ≤ Φ s :=
    fun T' _ s hs => norm_removalRatio_sub_le_of_supersolution hD hΦ T' s hs
  have hdiff := norm_sdiffRatio_sub_le hD hΦ.1 hinf A
  have hweights : ∑ s ∈ A, influenceWeight B c Φ s = ∑ s ∈ A, Φ s := by
    apply sum_congr rfl
    intro s hs
    simp [influenceWeight, Finset.disjoint_left.mp hAB hs]
  rw [hweights] at hdiff
  have hZΛ := partitionFunction_ne_zero hD Λ
  have hZA := partitionFunction_ne_zero hD (Λ \ A)
  have hZB := partitionFunction_ne_zero hD (Λ \ B)
  set P := sdiffRatio G w Λ A with hPdef
  set PB := sdiffRatio G w (Λ \ B) A with hPBdef
  have hPlow : Real.exp (-∑ u ∈ A, c u) ≤ ‖P‖ := exp_neg_le_norm_sdiffRatio hD Λ A
  have hPne : P ≠ 0 := by
    intro h
    rw [h, norm_zero] at hPlow
    linarith [Real.exp_pos (-∑ u ∈ A, c u)]
  have hratio : partitionFunction G w Λ * partitionFunction G w (Λ \ (A ∪ B)) /
      (partitionFunction G w (Λ \ A) * partitionFunction G w (Λ \ B)) = PB / P := by
    have hset : Λ \ (A ∪ B) = (Λ \ B) \ A := by
      ext u
      simp only [mem_sdiff, mem_union]
      tauto
    rw [hset, hPdef, hPBdef, sdiffRatio, sdiffRatio]
    field_simp
  have hsumΦ : 0 ≤ ∑ a ∈ A, Φ a := sum_nonneg fun a _ => hΦ.1 a
  rw [hratio, div_sub_one hPne, norm_div, div_le_iff₀ (norm_pos_iff.mpr hPne), norm_sub_rev]
  have hexp : Real.exp (∑ u ∈ A, c u) ≤ Real.exp (2 * ∑ a ∈ A, c a) * ‖P‖ := by
    calc Real.exp (∑ u ∈ A, c u)
        = Real.exp (2 * ∑ a ∈ A, c a) * Real.exp (-∑ u ∈ A, c u) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (2 * ∑ a ∈ A, c a) * ‖P‖ := by gcongr
  calc ‖P - PB‖ ≤ Real.exp (∑ u ∈ A, c u) * ∑ a ∈ A, Φ a := hdiff
    _ ≤ Real.exp (2 * ∑ a ∈ A, c a) * ‖P‖ * ∑ a ∈ A, Φ a := by gcongr
    _ = Real.exp (2 * ∑ a ∈ A, c a) * (∑ a ∈ A, Φ a) * ‖P‖ := by ring

end TwoRegion

/-! ## Exponential decay from a size-weighted smallness condition -/

/-- The factor `e^{2c} (1 - e^{-c})` of the influence recursion. -/
def influenceFactor (c : V → ℝ) (a : V) : ℝ :=
  Real.exp (2 * c a) * (1 - Real.exp (-c a))

omit [DecidableEq V] in
theorem influenceFactor_nonneg {c : V → ℝ} {a : V} (hc : 0 ≤ c a) :
    0 ≤ influenceFactor c a := by
  unfold influenceFactor
  have : Real.exp (-c a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact mul_nonneg (Real.exp_pos _).le (by linarith)

omit [DecidableEq V] in
theorem exp_sub_one_le_influenceFactor {c : V → ℝ} {a : V} (hc : 0 ≤ c a) :
    Real.exp (c a) - 1 ≤ influenceFactor c a := by
  unfold influenceFactor
  have h1 : Real.exp (2 * c a) * (1 - Real.exp (-c a)) =
      Real.exp (c a) * (Real.exp (c a) - 1) := by
    rw [show 2 * c a = c a + c a by ring, Real.exp_add]
    have : Real.exp (c a) * Real.exp (-c a) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    linear_combination (-Real.exp (c a)) * this
  rw [h1]
  have hone := Real.one_le_exp hc
  nlinarith

omit [DecidableRel G.Adj] in
/-- **Exponential supersolution.**  Let `d` be a distance to `B` that grows by at
most `ℓ s` across an incompatibility with `s`, and let `ρ ≥ 1` be a weight such
that for every polymer `a` and every finite set `S` of polymers incompatible
with it, `∑_{s ∈ S} influenceFactor c s · e^{κ ℓ s} · ρ s ≤ ρ a`.  Then
`2 · influenceFactor · ρ · e^{-κ d}` is a supersolution of the influence
recursion for removing `B`.  On a lattice the weight `ρ a = e^{τ |a|}` makes the
condition a bound on the sum over polymers through one block. -/
theorem isInfluenceSupersolution_exp_weighted {c : V → ℝ} (hc : ∀ γ, 0 ≤ c γ)
    {B : Finset V} {d ℓ ρ : V → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) (hρ : ∀ γ, 1 ≤ ρ γ)
    (hlip : ∀ a, a ∉ B → ∀ s, G.Adj a s → d a ≤ (if s ∈ B then 0 else d s) + ℓ s)
    (hsmall : ∀ a (S : Finset V), (∀ s ∈ S, G.Adj a s) →
      ∑ s ∈ S, influenceFactor c s * Real.exp (κ * ℓ s) * ρ s ≤ ρ a) :
    IsInfluenceSupersolution (G := G) (c := c) B
      fun a => 2 * influenceFactor c a * ρ a * Real.exp (-κ * d a) := by
  have hΦnn : ∀ a, 0 ≤ 2 * influenceFactor c a * ρ a * Real.exp (-κ * d a) := fun a =>
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (influenceFactor_nonneg (hc a)))
      (by linarith [hρ a])) (Real.exp_pos _).le
  refine ⟨hΦnn, fun a haB S hS => ?_⟩
  have hterm : ∀ s ∈ S, influenceWeight B c
      (fun a => 2 * influenceFactor c a * ρ a * Real.exp (-κ * d a)) s ≤
        2 * Real.exp (-κ * d a) * (influenceFactor c s * Real.exp (κ * ℓ s) * ρ s) := by
    intro s hs
    have hlips := hlip a haB s (hS s hs)
    have hfs := influenceFactor_nonneg (hc s)
    have hρs := hρ s
    have hfρ : 0 ≤ influenceFactor c s * ρ s := mul_nonneg hfs (by linarith)
    have hrhs : 2 * Real.exp (-κ * d a) * (influenceFactor c s * Real.exp (κ * ℓ s) * ρ s) =
        2 * (Real.exp (-κ * d a) * Real.exp (κ * ℓ s)) * (influenceFactor c s * ρ s) := by
      ring
    rw [hrhs]
    unfold influenceWeight
    split_ifs with hsB
    · simp only [hsB, ↓reduceIte, zero_add] at hlips
      have hle := exp_sub_one_le_influenceFactor (hc s)
      have hexp : 1 ≤ Real.exp (-κ * d a) * Real.exp (κ * ℓ s) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      calc Real.exp (c s) - 1 ≤ influenceFactor c s := hle
        _ ≤ influenceFactor c s * ρ s := le_mul_of_one_le_right hfs hρs
        _ ≤ 2 * (Real.exp (-κ * d a) * Real.exp (κ * ℓ s)) * (influenceFactor c s * ρ s) := by
            have : 1 ≤ 2 * (Real.exp (-κ * d a) * Real.exp (κ * ℓ s)) := by linarith
            exact le_mul_of_one_le_left hfρ this
    · simp only [hsB, ↓reduceIte] at hlips
      have hexp : Real.exp (-κ * d s) ≤ Real.exp (-κ * d a) * Real.exp (κ * ℓ s) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      calc 2 * influenceFactor c s * ρ s * Real.exp (-κ * d s)
          = 2 * Real.exp (-κ * d s) * (influenceFactor c s * ρ s) := by ring
        _ ≤ 2 * (Real.exp (-κ * d a) * Real.exp (κ * ℓ s)) * (influenceFactor c s * ρ s) := by
            gcongr
  have hsum : ∑ s ∈ S, influenceWeight B c
      (fun a => 2 * influenceFactor c a * ρ a * Real.exp (-κ * d a)) s ≤
        2 * Real.exp (-κ * d a) * ρ a := by
    calc ∑ s ∈ S, influenceWeight B c
          (fun a => 2 * influenceFactor c a * ρ a * Real.exp (-κ * d a)) s
        ≤ ∑ s ∈ S, 2 * Real.exp (-κ * d a) *
            (influenceFactor c s * Real.exp (κ * ℓ s) * ρ s) := sum_le_sum hterm
      _ = 2 * Real.exp (-κ * d a) *
            ∑ s ∈ S, influenceFactor c s * Real.exp (κ * ℓ s) * ρ s := by rw [mul_sum]
      _ ≤ 2 * Real.exp (-κ * d a) * ρ a := by
          gcongr
          exact hsmall a S hS
  show influenceFactor c a * _ ≤ _
  have hfa := influenceFactor_nonneg (hc a)
  calc influenceFactor c a * ∑ s ∈ S, influenceWeight B c
        (fun a => 2 * influenceFactor c a * ρ a * Real.exp (-κ * d a)) s
      ≤ influenceFactor c a * (2 * Real.exp (-κ * d a) * ρ a) := by gcongr
    _ = 2 * influenceFactor c a * ρ a * Real.exp (-κ * d a) := by ring

omit [DecidableRel G.Adj] in
/-- The unweighted case `ρ = 1`. -/
theorem isInfluenceSupersolution_exp {c : V → ℝ} (hc : ∀ γ, 0 ≤ c γ) {B : Finset V}
    {d ℓ : V → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hlip : ∀ a, a ∉ B → ∀ s, G.Adj a s → d a ≤ (if s ∈ B then 0 else d s) + ℓ s)
    (hsmall : ∀ a (S : Finset V), (∀ s ∈ S, G.Adj a s) →
      ∑ s ∈ S, influenceFactor c s * Real.exp (κ * ℓ s) ≤ 1) :
    IsInfluenceSupersolution (G := G) (c := c) B
      fun a => 2 * influenceFactor c a * Real.exp (-κ * d a) := by
  have h := isInfluenceSupersolution_exp_weighted (G := G) hc (ρ := fun _ => 1) hκ
    (fun _ => le_refl 1) hlip (by simpa using hsmall)
  simpa using h

/-- **Exponential two-region decay.**  Under Dobrushin's criterion and the
hypotheses of `isInfluenceSupersolution_exp_weighted`, the two-region ratio
differs from `1` by at most
`e^{2 ∑_A c} ∑_{a∈A} 2 · influenceFactor c a · ρ a · e^{-κ d a}`. -/
theorem norm_twoRegionRatio_sub_one_le_exp_weighted {w : V → ℂ} {c : V → ℝ}
    (hD : DobrushinCondition G w c) {A B : Finset V} (hAB : Disjoint A B)
    {d ℓ ρ : V → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) (hρ : ∀ γ, 1 ≤ ρ γ)
    (hlip : ∀ a, a ∉ B → ∀ s, G.Adj a s → d a ≤ (if s ∈ B then 0 else d s) + ℓ s)
    (hsmall : ∀ a (S : Finset V), (∀ s ∈ S, G.Adj a s) →
      ∑ s ∈ S, influenceFactor c s * Real.exp (κ * ℓ s) * ρ s ≤ ρ a) (Λ : Finset V) :
    ‖partitionFunction G w Λ * partitionFunction G w (Λ \ (A ∪ B)) /
        (partitionFunction G w (Λ \ A) * partitionFunction G w (Λ \ B)) - 1‖ ≤
      Real.exp (2 * ∑ a ∈ A, c a) *
        ∑ a ∈ A, 2 * influenceFactor c a * ρ a * Real.exp (-κ * d a) :=
  norm_twoRegionRatio_sub_one_le hD hAB
    (isInfluenceSupersolution_exp_weighted hD.nonneg hκ hρ hlip hsmall) Λ

/-- **Exponential two-region decay**, unweighted. -/
theorem norm_twoRegionRatio_sub_one_le_exp {w : V → ℂ} {c : V → ℝ}
    (hD : DobrushinCondition G w c) {A B : Finset V} (hAB : Disjoint A B)
    {d ℓ : V → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hlip : ∀ a, a ∉ B → ∀ s, G.Adj a s → d a ≤ (if s ∈ B then 0 else d s) + ℓ s)
    (hsmall : ∀ a (S : Finset V), (∀ s ∈ S, G.Adj a s) →
      ∑ s ∈ S, influenceFactor c s * Real.exp (κ * ℓ s) ≤ 1) (Λ : Finset V) :
    ‖partitionFunction G w Λ * partitionFunction G w (Λ \ (A ∪ B)) /
        (partitionFunction G w (Λ \ A) * partitionFunction G w (Λ \ B)) - 1‖ ≤
      Real.exp (2 * ∑ a ∈ A, c a) *
        ∑ a ∈ A, 2 * influenceFactor c a * Real.exp (-κ * d a) :=
  norm_twoRegionRatio_sub_one_le hD hAB
    (isInfluenceSupersolution_exp hD.nonneg hκ hlip hsmall) Λ

#print axioms norm_removalRatio_sub_le_of_supersolution
#print axioms norm_twoRegionRatio_sub_one_le
#print axioms norm_twoRegionRatio_sub_one_le_exp
#print axioms norm_twoRegionRatio_sub_one_le_exp_weighted

end Mettapedia.Combinatorics.PolymerGas
