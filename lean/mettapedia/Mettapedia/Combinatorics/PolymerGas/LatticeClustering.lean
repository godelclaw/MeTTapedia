import Mettapedia.Combinatorics.PolymerGas.Clustering
import Mettapedia.Combinatorics.PolymerGas.Lattice

/-!
# Exponential clustering of Kotecký–Preiss-small polymer gases

Consider a polymer representation over a product reference measure on a finite
pseudometric space of blocks (`PolymerGas.Measure`), with activity bounds `k`
satisfying the per-block smallness

`∑_{γ ∋ x} k γ e^{4 |γ| + κ diam γ} ≤ ε` at every block `x`, with `ε e ≤ 1`,
`k ∅ = 0` and `κ ≥ 0` (`ActivitySmall`).

Then the integrated gas satisfies the Kotecký–Preiss criterion with `a γ = |γ|`,
hence Dobrushin's criterion (`dobrushin_of_activitySmall`), and
`2 · influenceFactor · e^{|b|} · e^{-κ d(b, Y)}` is a supersolution of the
influence recursion for removing the polymers meeting any block set `Y`
(`isInfluenceSupersolution_lattice`).  Combining the decomposition of the
truncated two-point function (`PolymerGas.Clustering`) with the distance bounds
of `PolymerGas.Lattice`, each family of polymers meeting `S₁` contributes at most
`3 C₁ C₂ e^{2|S₁| + 3|S₂|} e^{-κ d(S₁, S₂)}` times its weighted activity product,
and summing over families gives

`|E[F₁ F₂] - E[F₁] E[F₂]| ≤ 3 C₁ C₂ e^{3(|S₁| + |S₂|)} e^{-κ d(S₁, S₂)}`

for bounded observables `F₁`, `F₂` on block sets `S₁`, `S₂`
(`norm_truncated_le_exp`), uniformly in the set of blocks and in the polymer set.
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory

namespace Mettapedia.Combinatorics.PolymerGas

variable {X : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
variable {E : Type*} [MeasurableSpace E] [Nonempty E]
variable (ν₀ : Measure E) [IsProbabilityMeasure ν₀]

theorem norm_integratedActivity_le (K : ∀ S : Finset X, (S → E) → ℂ) (k : Finset X → ℝ)
    (hk : ∀ S v, ‖K S v‖ ≤ k S) (S : Finset X) :
    ‖integratedActivity ν₀ K S‖ ≤ k S := by
  unfold integratedActivity
  calc ‖∫ ω, K S (restrictTo S ω) ∂(Measure.pi fun _ : X => ν₀)‖
      ≤ k S * (Measure.pi fun _ : X => ν₀).real Set.univ :=
        norm_integral_le_of_norm_le_const (ae_of_all _ fun ω => hk S _)
    _ = k S := by simp

/-- The Dobrushin weights produced by the Kotecký–Preiss criterion with `a γ = |γ|`. -/
def latticeWeight (w : Finset X → ℂ) (γ : Finset X) : ℝ :=
  Real.log (1 + ‖w γ‖ * Real.exp γ.card)

theorem latticeWeight_nonneg (w : Finset X → ℂ) (γ : Finset X) : 0 ≤ latticeWeight w γ :=
  Real.log_nonneg (by
    have := mul_nonneg (norm_nonneg (w γ)) (Real.exp_pos (γ.card : ℝ)).le
    linarith)

theorem latticeWeight_le (w : Finset X → ℂ) (γ : Finset X) :
    latticeWeight w γ ≤ ‖w γ‖ * Real.exp γ.card := by
  unfold latticeWeight
  have h := Real.log_le_sub_one_of_pos
    (show 0 < 1 + ‖w γ‖ * Real.exp γ.card by
      have := mul_nonneg (norm_nonneg (w γ)) (Real.exp_pos (γ.card : ℝ)).le
      linarith)
  linarith

/-- The influence factor of a weight at most `1/2` is at most `e` times the weight. -/
theorem influenceFactor_le_exp_one_mul {c : Finset X → ℝ} {γ : Finset X} (hc : 0 ≤ c γ)
    (hc2 : c γ ≤ 1 / 2) : influenceFactor c γ ≤ Real.exp 1 * c γ := by
  unfold influenceFactor
  have h1 : 1 - Real.exp (-c γ) ≤ c γ := by
    have := Real.add_one_le_exp (-c γ)
    linarith
  have h2 : Real.exp (2 * c γ) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
  have h3 : 0 ≤ 1 - Real.exp (-c γ) := by
    have : Real.exp (-c γ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  calc Real.exp (2 * c γ) * (1 - Real.exp (-c γ)) ≤ Real.exp 1 * c γ :=
    mul_le_mul h2 h1 h3 (Real.exp_pos _).le

omit [PseudoMetricSpace X] in
theorem blockSum_mono {f g : Finset X → ℝ} (hfg : ∀ γ, f γ ≤ g γ) (x : X) :
    blockSum f x ≤ blockSum g x :=
  sum_le_sum fun γ _ => hfg γ

/-- The per-block smallness of the activity bounds at decay rate `κ`: weighted by
`e^{4 |γ| + κ diam γ}`, they sum to at most `ε` over the polymers through every
block. -/
def ActivitySmall (k : Finset X → ℝ) (κ ε : ℝ) : Prop :=
  ∀ x, blockSum (fun γ => k γ * Real.exp (4 * γ.card + κ * polymerDiam γ)) x ≤ ε

section Consequences

variable {k : Finset X → ℝ} {κ ε : ℝ}

theorem weight_le_small (hkn : ∀ γ, 0 ≤ k γ) (hκ : 0 ≤ κ) {m : ℝ} (hm : m ≤ 4)
    (γ : Finset X) :
    k γ * Real.exp (m * γ.card + κ * polymerDiam γ) ≤
      k γ * Real.exp (4 * γ.card + κ * polymerDiam γ) := by
  apply mul_le_mul_of_nonneg_left _ (hkn γ)
  apply Real.exp_le_exp.mpr
  have : (0 : ℝ) ≤ γ.card := Nat.cast_nonneg _
  nlinarith

/-- A polymer's weighted activity is bounded by the block sum through any of its
blocks. -/
theorem weighted_le_blockSum {f : Finset X → ℝ} (hf : ∀ γ, 0 ≤ f γ) {γ : Finset X} {x : X}
    (hx : x ∈ γ) : f γ ≤ blockSum f x := by
  unfold blockSum
  exact single_le_sum (f := f) (fun γ _ => hf γ) (mem_filter.mpr ⟨mem_univ _, hx⟩)

end Consequences

/-! ## Helper bounds for the assembly -/

section Helpers

omit [PseudoMetricSpace X] in
theorem sum_meeting_le_card {f : Finset X → ℝ} (hf : ∀ γ, 0 ≤ f γ) {η : ℝ}
    (hη : ∀ x, blockSum f x ≤ η) (Λ : Finset (Finset X)) (Y : Finset X) :
    ∑ γ ∈ meeting Λ Y, f γ ≤ Y.card * η :=
  (sum_meeting_le hf Λ Y).trans (sum_blockSum_le hη Y)

omit [Fintype X] [PseudoMetricSpace X] in
theorem exp_card_union_le (S : Finset X) (Γ : Finset (Finset X)) :
    Real.exp ((S ∪ Γ.biUnion id).card) ≤
      Real.exp S.card * ∏ γ ∈ Γ, Real.exp γ.card := by
  rw [← Real.exp_sum, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (card_union_biUnion_le S Γ)

omit [Fintype X] [DecidableEq X] [PseudoMetricSpace X] in
theorem prod_mul_exp (Γ : Finset (Finset X)) (k a : Finset X → ℝ) :
    ∏ γ ∈ Γ, (k γ * Real.exp (a γ)) = (∏ γ ∈ Γ, k γ) * Real.exp (∑ γ ∈ Γ, a γ) := by
  rw [prod_mul_distrib, Real.exp_sum]

omit [PseudoMetricSpace X] in
/-- Sums over families of polymers meeting `S` of products of a weight whose block
sums are at most `η` are at most `exp (|S| η)`. -/
theorem sum_powerset_meeting_le {v : Finset X → ℝ} (hv : ∀ γ, 0 ≤ v γ) {η : ℝ}
    (hη : ∀ x, blockSum v x ≤ η) (Λ : Finset (Finset X)) (S : Finset X) :
    ∑ Γ ∈ (meeting Λ S).powerset, ∏ γ ∈ Γ, v γ ≤ Real.exp (S.card * η) :=
  (sum_powerset_prod_le_exp hv).trans (Real.exp_le_exp.mpr (sum_meeting_le_card hv hη Λ S))

theorem one_add_two_mul_le_three_exp (m : ℝ) (hm : 0 ≤ m) : 1 + 2 * m ≤ 3 * Real.exp m := by
  have := Real.add_one_le_exp m
  linarith

end Helpers

/-! ## The integrated gas under per-block smallness -/

section Setup

variable (K : ∀ S : Finset X, (S → E) → ℂ) (k : Finset X → ℝ)
  (hk : ∀ S v, ‖K S v‖ ≤ k S) (hk0 : k ∅ = 0) {κ ε : ℝ} (hκ : 0 ≤ κ) (hε0 : 0 ≤ ε)
  (hε : ε * Real.exp 1 ≤ 1) (hsmall : ActivitySmall k κ ε)

include hk hκ hε0 hε hsmall in
theorem blockSum_card_le_half :
    ∀ x, blockSum (fun γ => k γ * Real.exp γ.card) x ≤ 1 / 2 := by
  have hkn : ∀ γ, 0 ≤ k γ := activityBound_nonneg hk
  intro x
  have h1 : blockSum (fun γ => k γ * Real.exp γ.card) x ≤
      blockSum (fun γ => k γ * Real.exp (4 * γ.card + κ * polymerDiam γ)) x := by
    apply blockSum_mono
    intro γ
    have := weight_le_small (k := k) hkn hκ (m := 1) (by norm_num) γ
    have hd : κ * polymerDiam γ ≥ 0 := mul_nonneg hκ (polymerDiam_nonneg γ)
    calc k γ * Real.exp γ.card ≤ k γ * Real.exp (1 * γ.card + κ * polymerDiam γ) := by
          apply mul_le_mul_of_nonneg_left _ (hkn γ)
          exact Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := this
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hε2 : ε ≤ 1 / 2 := by nlinarith
  exact h1.trans ((hsmall x).trans hε2)

include hk hk0 hκ hε0 hε hsmall in
/-- Under per-block smallness the integrated gas satisfies Dobrushin's criterion
with the weights `latticeWeight`. -/
theorem dobrushin_of_activitySmall :
    DobrushinCondition (overlapGraph X) (integratedActivity ν₀ K)
      (latticeWeight (integratedActivity ν₀ K)) :=
  dobrushinCondition_of_koteckyPreiss
    (koteckyPreiss_of_blockSum (norm_integratedActivity_le ν₀ K k hk) hk0
      (blockSum_card_le_half K k hk hκ hε0 hε hsmall))

include hk in
theorem latticeWeight_le_activity (γ : Finset X) :
    latticeWeight (integratedActivity ν₀ K) γ ≤ k γ * Real.exp γ.card :=
  (latticeWeight_le _ γ).trans
    (mul_le_mul_of_nonneg_right (norm_integratedActivity_le ν₀ K k hk γ) (Real.exp_pos _).le)

include hk hk0 hκ hε0 hε hsmall in
theorem latticeWeight_le_half (γ : Finset X) :
    latticeWeight (integratedActivity ν₀ K) γ ≤ 1 / 2 := by
  have hkn : ∀ γ, 0 ≤ k γ := activityBound_nonneg hk
  rcases γ.eq_empty_or_nonempty with hγ | ⟨x, hx⟩
  · subst hγ
    have := latticeWeight_le_activity ν₀ K k hk ∅
    rw [hk0] at this
    linarith
  · calc latticeWeight (integratedActivity ν₀ K) γ ≤ k γ * Real.exp γ.card :=
          latticeWeight_le_activity ν₀ K k hk γ
      _ ≤ blockSum (fun γ => k γ * Real.exp γ.card) x :=
          weighted_le_blockSum (f := fun γ => k γ * Real.exp γ.card)
            (fun γ => mul_nonneg (hkn γ) (Real.exp_pos _).le) hx
      _ ≤ 1 / 2 := blockSum_card_le_half K k hk hκ hε0 hε hsmall x

include hk hκ hsmall in
theorem blockSum_latticeWeight_le (x : X) :
    blockSum (latticeWeight (integratedActivity ν₀ K)) x ≤ ε := by
  have hkn : ∀ γ, 0 ≤ k γ := activityBound_nonneg hk
  refine (blockSum_mono (fun γ => ?_) x).trans (hsmall x)
  calc latticeWeight (integratedActivity ν₀ K) γ ≤ k γ * Real.exp γ.card :=
        latticeWeight_le_activity ν₀ K k hk γ
    _ ≤ k γ * Real.exp (4 * γ.card + κ * polymerDiam γ) := by
        apply mul_le_mul_of_nonneg_left _ (hkn γ)
        apply Real.exp_le_exp.mpr
        have : (0 : ℝ) ≤ γ.card := Nat.cast_nonneg _
        have := mul_nonneg hκ (polymerDiam_nonneg γ)
        linarith

include hk hk0 hκ hε0 hε hsmall in
/-- The influence factors weighted by `e^{|γ| + κ diam γ}` have block sums at most `1`. -/
theorem blockSum_influence_le (x : X) :
    blockSum (fun γ => influenceFactor (latticeWeight (integratedActivity ν₀ K)) γ *
      Real.exp (γ.card + κ * polymerDiam γ)) x ≤ 1 := by
  have hkn : ∀ γ, 0 ≤ k γ := activityBound_nonneg hk
  set c := latticeWeight (integratedActivity ν₀ K)
  have hterm : ∀ γ, influenceFactor c γ * Real.exp (γ.card + κ * polymerDiam γ) ≤
      Real.exp 1 * (k γ * Real.exp (4 * γ.card + κ * polymerDiam γ)) := by
    intro γ
    have h1 := influenceFactor_le_exp_one_mul (latticeWeight_nonneg _ γ)
      (latticeWeight_le_half ν₀ K k hk hk0 hκ hε0 hε hsmall γ)
    have h2 := latticeWeight_le_activity ν₀ K k hk γ
    have hexp : Real.exp γ.card * Real.exp (γ.card + κ * polymerDiam γ) ≤
        Real.exp (4 * γ.card + κ * polymerDiam γ) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : (0 : ℝ) ≤ γ.card := Nat.cast_nonneg _
      linarith
    calc influenceFactor c γ * Real.exp (γ.card + κ * polymerDiam γ)
        ≤ (Real.exp 1 * c γ) * Real.exp (γ.card + κ * polymerDiam γ) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ (Real.exp 1 * (k γ * Real.exp γ.card)) * Real.exp (γ.card + κ * polymerDiam γ) := by
          gcongr
      _ = Real.exp 1 * (k γ * (Real.exp γ.card * Real.exp (γ.card + κ * polymerDiam γ))) := by
          ring
      _ ≤ Real.exp 1 * (k γ * Real.exp (4 * γ.card + κ * polymerDiam γ)) := by
          gcongr
          exact hkn γ
  calc blockSum (fun γ => influenceFactor c γ * Real.exp (γ.card + κ * polymerDiam γ)) x
      ≤ blockSum (fun γ => Real.exp 1 * (k γ * Real.exp (4 * γ.card + κ * polymerDiam γ))) x :=
        blockSum_mono hterm x
    _ = Real.exp 1 * blockSum (fun γ => k γ * Real.exp (4 * γ.card + κ * polymerDiam γ)) x := by
        unfold blockSum
        rw [mul_sum]
    _ ≤ Real.exp 1 * ε := mul_le_mul_of_nonneg_left (hsmall x) (Real.exp_pos _).le
    _ ≤ 1 := by linarith

end Setup

/-! ## The supersolution for removing the polymers meeting a block set -/

/-- The supersolution for removing the polymers meeting `Y`:
`2 · influenceFactor · e^{|b|} · e^{-κ d(b, Y)}`. -/
def latticeSupersolution (c : Finset X → ℝ) (κ : ℝ) (Y : Finset X) (b : Finset X) : ℝ :=
  2 * influenceFactor c b * Real.exp b.card * Real.exp (-κ * polymerDist Y b)

section Supersolution

variable (K : ∀ S : Finset X, (S → E) → ℂ) (k : Finset X → ℝ)
  (hk : ∀ S v, ‖K S v‖ ≤ k S) (hk0 : k ∅ = 0) {κ ε : ℝ} (hκ : 0 ≤ κ) (hε0 : 0 ≤ ε)
  (hε : ε * Real.exp 1 ≤ 1) (hsmall : ActivitySmall k κ ε)

include hk hk0 hκ hε0 hε hsmall in
theorem isInfluenceSupersolution_lattice (Λ : Finset (Finset X)) (Y : Finset X) :
    IsInfluenceSupersolution (G := overlapGraph X)
      (c := latticeWeight (integratedActivity ν₀ K)) (meeting Λ Y)
      (latticeSupersolution (latticeWeight (integratedActivity ν₀ K)) κ Y) := by
  set c := latticeWeight (integratedActivity ν₀ K) with hcdef
  have hlip : ∀ a, a ∉ meeting Λ Y → ∀ s, (overlapGraph X).Adj a s →
      polymerDist Y a ≤ (if s ∈ meeting Λ Y then 0 else polymerDist Y s) + polymerDiam s := by
    intro a _ s hadj
    have hls := polymerDist_le_add_polymerDiam (Y := Y) hadj.2
    split_ifs with hs
    · have h0 := polymerDist_eq_zero_of_not_disjoint (mem_filter.mp hs).2
      linarith
    · exact hls
  have hsm : ∀ a (S : Finset (Finset X)), (∀ s ∈ S, (overlapGraph X).Adj a s) →
      ∑ s ∈ S, influenceFactor c s * Real.exp (κ * polymerDiam s) * Real.exp s.card ≤
        Real.exp a.card := by
    intro a S hS
    have hf : ∀ γ, 0 ≤ influenceFactor c γ * Real.exp (γ.card + κ * polymerDiam γ) := fun γ =>
      mul_nonneg (influenceFactor_nonneg (latticeWeight_nonneg _ γ)) (Real.exp_pos _).le
    have hrw : ∀ s : Finset X, influenceFactor c s * Real.exp (κ * polymerDiam s) *
        Real.exp s.card = influenceFactor c s * Real.exp (s.card + κ * polymerDiam s) := by
      intro s
      rw [mul_assoc, ← Real.exp_add, add_comm (κ * polymerDiam s)]
    simp_rw [hrw]
    calc ∑ s ∈ S, influenceFactor c s * Real.exp (s.card + κ * polymerDiam s)
        ≤ ∑ x ∈ a, blockSum (fun γ => influenceFactor c γ *
            Real.exp (γ.card + κ * polymerDiam γ)) x :=
          sum_le_sum_blockSum hf fun s hs => (hS s hs).2
      _ ≤ a.card * 1 := sum_blockSum_le (blockSum_influence_le ν₀ K k hk hk0 hκ hε0 hε hsmall) a
      _ ≤ Real.exp a.card := by
          have := Real.add_one_le_exp (a.card : ℝ)
          linarith
  have h := isInfluenceSupersolution_exp_weighted (G := overlapGraph X) (c := c)
    (fun γ => latticeWeight_nonneg _ γ) (B := meeting Λ Y) (d := polymerDist Y)
    (ℓ := polymerDiam) (ρ := fun a => Real.exp a.card) hκ
    (fun a => Real.one_le_exp (Nat.cast_nonneg _)) hlip hsm
  exact h

end Supersolution

/-! ## The separated families -/

section Separated

variable (K : ∀ S : Finset X, (S → E) → ℂ) (hK : ∀ S, Measurable (K S)) (k : Finset X → ℝ)
  (hk : ∀ S v, ‖K S v‖ ≤ k S) (hk0 : k ∅ = 0) {κ ε : ℝ} (hκ : 0 ≤ κ) (hε0 : 0 ≤ ε)
  (hε : ε * Real.exp 1 ≤ 1) (hsmall : ActivitySmall k κ ε)

include hk hk0 hκ hε0 hε hsmall in
/-- The contribution of one family `Γ₂` of polymers meeting `S₂` to the change of
`E[F₂]` when the polymers meeting `S₁ ∪ ⋃ Γ₁` are removed. -/
theorem family_term_le (S₁ S₂ : Finset X) (hS₁ : S₁.Nonempty) (C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (Λ Γ₁ Γ₂ : Finset (Finset X)) (hΓ₁ : ∀ γ ∈ Γ₁, ¬ Disjoint γ S₁)
    (hΓ₂ : Γ₂ ⊆ meeting Λ S₂) :
    C₂ * (∏ γ ∈ Γ₂, k γ) *
        Real.exp (∑ b ∈ meeting Λ (S₂ ∪ Γ₂.biUnion id),
          latticeWeight (integratedActivity ν₀ K) b) *
        (if Disjoint Γ₂ (meeting Λ (S₁ ∪ Γ₁.biUnion id)) then
          ∑ b ∈ meeting Λ (S₂ ∪ Γ₂.biUnion id),
            influenceWeight (meeting Λ (S₁ ∪ Γ₁.biUnion id))
              (latticeWeight (integratedActivity ν₀ K))
              (latticeSupersolution (latticeWeight (integratedActivity ν₀ K)) κ
                (S₁ ∪ Γ₁.biUnion id)) b
        else 1) ≤
      3 * C₂ * Real.exp (2 * S₂.card) *
        Real.exp (κ * (familyExtent Γ₁ - polymerDist S₁ S₂)) *
        ∏ γ ∈ Γ₂, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := by
  have hkn : ∀ γ, 0 ≤ k γ := activityBound_nonneg hk
  set c := latticeWeight (integratedActivity ν₀ K) with hcdef
  set Y₁ : Finset X := S₁ ∪ Γ₁.biUnion id with hY₁
  set Y₂ : Finset X := S₂ ∪ Γ₂.biUnion id with hY₂
  set A₁ := meeting Λ Y₁ with hA₁
  set D := polymerDist S₁ S₂ with hD
  set e₁ := familyExtent Γ₁ with he₁
  set e₂ := familyExtent Γ₂ with he₂
  have hΓ₂m : ∀ γ ∈ Γ₂, ¬ Disjoint γ S₂ := fun γ hγ => (mem_filter.mp (hΓ₂ hγ)).2
  have hε1 : ε ≤ 1 := by
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have hY₂card : (0 : ℝ) ≤ Y₂.card := Nat.cast_nonneg _
  -- (i) the weights of the polymers meeting `Y₂`
  have hcY₂ : ∑ b ∈ meeting Λ Y₂, c b ≤ Y₂.card := by
    have := sum_meeting_le_card (fun γ => latticeWeight_nonneg _ γ)
      (blockSum_latticeWeight_le ν₀ K k hk hκ hsmall) Λ Y₂
    nlinarith
  -- (ii) the influence part
  have hif : (if Disjoint Γ₂ A₁ then
        ∑ b ∈ meeting Λ Y₂, influenceWeight A₁ c (latticeSupersolution c κ Y₁) b else 1) ≤
      Real.exp (κ * (e₁ + e₂ - D)) * (1 + 2 * Y₂.card) := by
    split_ifs with hdA
    · have hterm : ∀ b ∈ meeting Λ Y₂, influenceWeight A₁ c (latticeSupersolution c κ Y₁) b ≤
          2 * Real.exp (κ * (e₁ + e₂ - D)) *
            (influenceFactor c b * Real.exp (b.card + κ * polymerDiam b)) := by
        intro b hb
        have hbY₂ : ¬ Disjoint b Y₂ := (mem_filter.mp hb).2
        have hdist : D - e₁ - e₂ - polymerDiam b ≤ polymerDist Y₁ b :=
          polymerDist_ge_of_meeting hS₁ hΓ₁ hΓ₂m hbY₂
        have hfb := influenceFactor_nonneg (c := c) (a := b) (latticeWeight_nonneg _ b)
        have hsplit : 2 * Real.exp (κ * (e₁ + e₂ - D)) *
            (influenceFactor c b * Real.exp (b.card + κ * polymerDiam b)) =
            2 * influenceFactor c b * Real.exp b.card *
              Real.exp (κ * (e₁ + e₂ + polymerDiam b - D)) := by
          rw [show κ * (e₁ + e₂ + polymerDiam b - D) = κ * (e₁ + e₂ - D) + κ * polymerDiam b by
            ring, Real.exp_add, Real.exp_add]
          ring
        rw [hsplit]
        unfold influenceWeight
        split_ifs with hbA
        · have h0 : polymerDist Y₁ b = 0 :=
            polymerDist_eq_zero_of_not_disjoint (mem_filter.mp hbA).2
          have hge : 1 ≤ Real.exp (κ * (e₁ + e₂ + polymerDiam b - D)) :=
            Real.one_le_exp (by nlinarith)
          have hcb : 1 ≤ Real.exp b.card := Real.one_le_exp (Nat.cast_nonneg _)
          have hle := exp_sub_one_le_influenceFactor (c := c) (a := b) (latticeWeight_nonneg _ b)
          calc Real.exp (c b) - 1 ≤ influenceFactor c b := hle
            _ ≤ 2 * influenceFactor c b * Real.exp b.card *
                  Real.exp (κ * (e₁ + e₂ + polymerDiam b - D)) := by
                have h2 : influenceFactor c b ≤ 2 * influenceFactor c b := by linarith
                have h3 : 2 * influenceFactor c b ≤ 2 * influenceFactor c b * Real.exp b.card :=
                  le_mul_of_one_le_right (by linarith) hcb
                exact h2.trans (h3.trans (le_mul_of_one_le_right (by positivity) hge))
        · unfold latticeSupersolution
          have hexp : Real.exp (-κ * polymerDist Y₁ b) ≤
              Real.exp (κ * (e₁ + e₂ + polymerDiam b - D)) :=
            Real.exp_le_exp.mpr (by nlinarith)
          have hnn : 0 ≤ 2 * influenceFactor c b * Real.exp b.card := by positivity
          exact mul_le_mul_of_nonneg_left hexp hnn
      calc ∑ b ∈ meeting Λ Y₂, influenceWeight A₁ c (latticeSupersolution c κ Y₁) b
          ≤ ∑ b ∈ meeting Λ Y₂, 2 * Real.exp (κ * (e₁ + e₂ - D)) *
              (influenceFactor c b * Real.exp (b.card + κ * polymerDiam b)) := sum_le_sum hterm
        _ = 2 * Real.exp (κ * (e₁ + e₂ - D)) *
              ∑ b ∈ meeting Λ Y₂, influenceFactor c b * Real.exp (b.card + κ * polymerDiam b) := by
            rw [mul_sum]
        _ ≤ 2 * Real.exp (κ * (e₁ + e₂ - D)) * (Y₂.card * 1) := by
            gcongr
            exact sum_meeting_le_card (fun γ => mul_nonneg
              (influenceFactor_nonneg (latticeWeight_nonneg _ γ)) (Real.exp_pos _).le)
              (blockSum_influence_le ν₀ K k hk hk0 hκ hε0 hε hsmall) Λ Y₂
        _ ≤ Real.exp (κ * (e₁ + e₂ - D)) * (1 + 2 * Y₂.card) := by
            have := Real.exp_pos (κ * (e₁ + e₂ - D))
            nlinarith
    · obtain ⟨γ₂, hγ₂, hγ₂A⟩ := Finset.not_disjoint_iff.mp hdA
      have hmeet : ¬ Disjoint γ₂ Y₁ := (mem_filter.mp hγ₂A).2
      have hD' := polymerDist_le_familyExtent_add_of_meet hS₁ hΓ₁ hΓ₂m hγ₂ hmeet
      have hge : 1 ≤ Real.exp (κ * (e₁ + e₂ - D)) := Real.one_le_exp (by nlinarith)
      nlinarith
  -- (iii) assemble
  have hexpY : Real.exp (∑ b ∈ meeting Λ Y₂, c b) * (1 + 2 * Y₂.card) ≤
      3 * (Real.exp (2 * S₂.card) * ∏ γ ∈ Γ₂, Real.exp (2 * γ.card)) := by
    have h1 : Real.exp (∑ b ∈ meeting Λ Y₂, c b) ≤ Real.exp Y₂.card := Real.exp_le_exp.mpr hcY₂
    have h2 := one_add_two_mul_le_three_exp (Y₂.card : ℝ) hY₂card
    have h3 : Real.exp (2 * Y₂.card) ≤ Real.exp (2 * S₂.card) * ∏ γ ∈ Γ₂, Real.exp (2 * γ.card) := by
      rw [← Real.exp_sum, ← Real.exp_add, ← mul_sum]
      apply Real.exp_le_exp.mpr
      have := card_union_biUnion_le S₂ Γ₂
      linarith
    calc Real.exp (∑ b ∈ meeting Λ Y₂, c b) * (1 + 2 * Y₂.card)
        ≤ Real.exp Y₂.card * (3 * Real.exp Y₂.card) := by
          gcongr
      _ = 3 * Real.exp (2 * Y₂.card) := by
          rw [show (2 : ℝ) * Y₂.card = Y₂.card + Y₂.card by ring, Real.exp_add]
          ring
      _ ≤ 3 * (Real.exp (2 * S₂.card) * ∏ γ ∈ Γ₂, Real.exp (2 * γ.card)) := by gcongr
  have hprod : (∏ γ ∈ Γ₂, k γ) * (∏ γ ∈ Γ₂, Real.exp (2 * γ.card)) * Real.exp (κ * e₂) =
      ∏ γ ∈ Γ₂, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := by
    rw [prod_mul_exp, mul_assoc, ← Real.exp_sum, ← Real.exp_add]
    congr 2
    rw [he₂]
    simp only [familyExtent, sum_add_distrib, mul_sum]
    ring
  have hPk : 0 ≤ ∏ γ ∈ Γ₂, k γ := Finset.prod_nonneg fun γ _ => hkn γ
  calc C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (∑ b ∈ meeting Λ Y₂, c b) *
        (if Disjoint Γ₂ A₁ then ∑ b ∈ meeting Λ Y₂,
          influenceWeight A₁ c (latticeSupersolution c κ Y₁) b else 1)
      ≤ C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (∑ b ∈ meeting Λ Y₂, c b) *
          (Real.exp (κ * (e₁ + e₂ - D)) * (1 + 2 * Y₂.card)) := by
        gcongr
    _ = C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (κ * (e₁ + e₂ - D)) *
          (Real.exp (∑ b ∈ meeting Λ Y₂, c b) * (1 + 2 * Y₂.card)) := by ring
    _ ≤ C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (κ * (e₁ + e₂ - D)) *
          (3 * (Real.exp (2 * S₂.card) * ∏ γ ∈ Γ₂, Real.exp (2 * γ.card))) := by
        gcongr
    _ = 3 * C₂ * Real.exp (2 * S₂.card) * Real.exp (κ * (e₁ - D)) *
          ((∏ γ ∈ Γ₂, k γ) * (∏ γ ∈ Γ₂, Real.exp (2 * γ.card)) * Real.exp (κ * e₂)) := by
        rw [show κ * (e₁ + e₂ - D) = κ * (e₁ - D) + κ * e₂ by ring, Real.exp_add]
        ring
    _ = 3 * C₂ * Real.exp (2 * S₂.card) * Real.exp (κ * (e₁ - D)) *
          ∏ γ ∈ Γ₂, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := by rw [hprod]

end Separated

/-! ## The bridging families and the clustering theorem -/

section Final

variable (K : ∀ S : Finset X, (S → E) → ℂ) (hK : ∀ S, Measurable (K S)) (k : Finset X → ℝ)
  (hk : ∀ S v, ‖K S v‖ ≤ k S) (hk0 : k ∅ = 0) {κ ε : ℝ} (hκ : 0 ≤ κ) (hε0 : 0 ≤ ε)
  (hε : ε * Real.exp 1 ≤ 1) (hsmall : ActivitySmall k κ ε)

include hk hκ hsmall in
theorem sum_powerset_meeting_weight_le (Λ : Finset (Finset X)) (S : Finset X) {m : ℝ}
    (hm0 : 0 ≤ m) (hm : m ≤ 4) :
    ∑ Γ ∈ (meeting Λ S).powerset, ∏ γ ∈ Γ, (k γ * Real.exp (κ * polymerDiam γ + m * γ.card)) ≤
      Real.exp (S.card * ε) := by
  have hkn : ∀ γ, 0 ≤ k γ := activityBound_nonneg hk
  refine sum_powerset_meeting_le (fun γ => mul_nonneg (hkn γ) (Real.exp_pos _).le)
    (fun x => (blockSum_mono (fun γ => ?_) x).trans (hsmall x)) Λ S
  have := weight_le_small (k := k) hkn hκ hm γ
  rw [add_comm (κ * polymerDiam γ)]
  exact this

include hK hk hk0 hκ hε0 hε hsmall in
/-- The bridging term of a family whose union with `S₁` reaches `S₂`. -/
theorem norm_bridgeTerm_le_lattice (S₁ S₂ : Finset X) (F₁ : (S₁ → E) → ℂ)
    (hF₁ : Measurable F₁) (C₁ : ℝ) (hF₁b : ∀ v, ‖F₁ v‖ ≤ C₁) (F₂ : (S₂ → E) → ℂ)
    (hF₂ : Measurable F₂) (C₂ : ℝ) (hF₂b : ∀ v, ‖F₂ v‖ ≤ C₂) (Λ Γ₁ : Finset (Finset X))
    (hΓ₁ : ∀ γ ∈ Γ₁, ¬ Disjoint γ S₁) (hreach : ¬ Disjoint (S₁ ∪ Γ₁.biUnion id) S₂) :
    ‖bridgeTerm ν₀ S₁ S₂ F₁ F₂ K Λ Γ₁‖ ≤
      2 * C₁ * C₂ * Real.exp (2 * S₁.card + 2 * S₂.card) * Real.exp (-κ * polymerDist S₁ S₂) *
        ∏ γ ∈ Γ₁, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (hF₁b fun _ => e₀)
  have hC₂ : 0 ≤ C₂ := (norm_nonneg _).trans (hF₂b fun _ => e₀)
  have hkn : ∀ γ, 0 ≤ k γ := activityBound_nonneg hk
  have hD := dobrushin_of_activitySmall ν₀ K k hk hk0 hκ hε0 hε hsmall
  set c := latticeWeight (integratedActivity ν₀ K) with hcdef
  have hε1 : ε ≤ 1 := by
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have hcblock := blockSum_latticeWeight_le ν₀ K k hk hκ hsmall
  have hsumc : ∀ Y : Finset X, Real.exp (∑ b ∈ meeting Λ Y, c b) ≤ Real.exp Y.card := by
    intro Y
    apply Real.exp_le_exp.mpr
    have := sum_meeting_le_card (fun γ => latticeWeight_nonneg _ γ) hcblock Λ Y
    have : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
    nlinarith
  have hPk : 0 ≤ ∏ γ ∈ Γ₁, k γ := Finset.prod_nonneg fun γ _ => hkn γ
  set W : Finset X := (S₁ ∪ S₂) ∪ Γ₁.biUnion id with hW
  -- the first piece
  have hT1 : ∑ Γ' ∈ (meeting Λ W).powerset, (∏ γ ∈ Γ', k γ) *
      Real.exp (∑ b ∈ meeting Λ (W ∪ Γ'.biUnion id), c b) ≤
      Real.exp (2 * S₁.card + 2 * S₂.card) * ∏ γ ∈ Γ₁, Real.exp (2 * γ.card) := by
    have hterm : ∀ Γ' ∈ (meeting Λ W).powerset, (∏ γ ∈ Γ', k γ) *
        Real.exp (∑ b ∈ meeting Λ (W ∪ Γ'.biUnion id), c b) ≤
        Real.exp W.card * ∏ γ ∈ Γ', (k γ * Real.exp (κ * polymerDiam γ + 1 * γ.card)) := by
      intro Γ' _
      have h1 := (hsumc (W ∪ Γ'.biUnion id)).trans (exp_card_union_le W Γ')
      have h2 : (∏ γ ∈ Γ', k γ) * ∏ γ ∈ Γ', Real.exp γ.card ≤
          ∏ γ ∈ Γ', (k γ * Real.exp (κ * polymerDiam γ + 1 * γ.card)) := by
        rw [← prod_mul_distrib]
        exact Finset.prod_le_prod (fun γ _ => mul_nonneg (hkn γ) (Real.exp_pos _).le)
          fun γ _ => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
            have := mul_nonneg hκ (polymerDiam_nonneg γ)
            linarith)) (hkn γ)
      calc (∏ γ ∈ Γ', k γ) * Real.exp (∑ b ∈ meeting Λ (W ∪ Γ'.biUnion id), c b)
          ≤ (∏ γ ∈ Γ', k γ) * (Real.exp W.card * ∏ γ ∈ Γ', Real.exp γ.card) :=
            mul_le_mul_of_nonneg_left h1 (Finset.prod_nonneg fun γ _ => hkn γ)
        _ = Real.exp W.card * ((∏ γ ∈ Γ', k γ) * ∏ γ ∈ Γ', Real.exp γ.card) := by ring
        _ ≤ Real.exp W.card * ∏ γ ∈ Γ', (k γ * Real.exp (κ * polymerDiam γ + 1 * γ.card)) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    have hWcard : (W.card : ℝ) ≤ S₁.card + S₂.card + ∑ γ ∈ Γ₁, (γ.card : ℝ) := by
      have h1 := card_union_biUnion_le (S₁ ∪ S₂) Γ₁
      have h2 : ((S₁ ∪ S₂).card : ℝ) ≤ S₁.card + S₂.card := by
        exact_mod_cast Finset.card_union_le S₁ S₂
      linarith
    calc ∑ Γ' ∈ (meeting Λ W).powerset, (∏ γ ∈ Γ', k γ) *
          Real.exp (∑ b ∈ meeting Λ (W ∪ Γ'.biUnion id), c b)
        ≤ ∑ Γ' ∈ (meeting Λ W).powerset,
            Real.exp W.card * ∏ γ ∈ Γ', (k γ * Real.exp (κ * polymerDiam γ + 1 * γ.card)) :=
          sum_le_sum hterm
      _ = Real.exp W.card * ∑ Γ' ∈ (meeting Λ W).powerset,
            ∏ γ ∈ Γ', (k γ * Real.exp (κ * polymerDiam γ + 1 * γ.card)) := by rw [mul_sum]
      _ ≤ Real.exp W.card * Real.exp (W.card * ε) :=
          mul_le_mul_of_nonneg_left (sum_powerset_meeting_weight_le K k hk hκ hsmall Λ W
            (by norm_num) (by norm_num)) (Real.exp_pos _).le
      _ ≤ Real.exp (2 * S₁.card + 2 * S₂.card) * ∏ γ ∈ Γ₁, Real.exp (2 * γ.card) := by
          rw [← Real.exp_add, ← Real.exp_sum, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
          rw [← mul_sum]
          nlinarith
  -- the second piece
  have hT2 : Real.exp (∑ b ∈ meeting Λ (S₁ ∪ Γ₁.biUnion id), c b) *
      ∑ Γ₂ ∈ (meeting Λ S₂).powerset,
        C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (∑ b ∈ meeting Λ (S₂ ∪ Γ₂.biUnion id), c b) ≤
      C₂ * (Real.exp (2 * S₁.card + 2 * S₂.card) * ∏ γ ∈ Γ₁, Real.exp (2 * γ.card)) := by
    have hA := (hsumc (S₁ ∪ Γ₁.biUnion id)).trans (exp_card_union_le S₁ Γ₁)
    have hB : ∑ Γ₂ ∈ (meeting Λ S₂).powerset,
        C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (∑ b ∈ meeting Λ (S₂ ∪ Γ₂.biUnion id), c b) ≤
        C₂ * Real.exp (2 * S₂.card) := by
      calc ∑ Γ₂ ∈ (meeting Λ S₂).powerset,
            C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (∑ b ∈ meeting Λ (S₂ ∪ Γ₂.biUnion id), c b)
          ≤ ∑ Γ₂ ∈ (meeting Λ S₂).powerset, C₂ * Real.exp S₂.card *
              ∏ γ ∈ Γ₂, (k γ * Real.exp (κ * polymerDiam γ + 1 * γ.card)) := by
            refine sum_le_sum fun Γ₂ _ => ?_
            have h1 := (hsumc (S₂ ∪ Γ₂.biUnion id)).trans (exp_card_union_le S₂ Γ₂)
            have h2 : (∏ γ ∈ Γ₂, k γ) * ∏ γ ∈ Γ₂, Real.exp γ.card ≤
                ∏ γ ∈ Γ₂, (k γ * Real.exp (κ * polymerDiam γ + 1 * γ.card)) := by
              rw [← prod_mul_distrib]
              exact Finset.prod_le_prod (fun γ _ => mul_nonneg (hkn γ) (Real.exp_pos _).le)
                fun γ _ => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
                  have := mul_nonneg hκ (polymerDiam_nonneg γ)
                  linarith)) (hkn γ)
            calc C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (∑ b ∈ meeting Λ (S₂ ∪ Γ₂.biUnion id), c b)
                ≤ C₂ * (∏ γ ∈ Γ₂, k γ) * (Real.exp S₂.card * ∏ γ ∈ Γ₂, Real.exp γ.card) :=
                  mul_le_mul_of_nonneg_left h1
                    (mul_nonneg hC₂ (Finset.prod_nonneg fun γ _ => hkn γ))
              _ = C₂ * Real.exp S₂.card * ((∏ γ ∈ Γ₂, k γ) * ∏ γ ∈ Γ₂, Real.exp γ.card) := by
                  ring
              _ ≤ C₂ * Real.exp S₂.card *
                    ∏ γ ∈ Γ₂, (k γ * Real.exp (κ * polymerDiam γ + 1 * γ.card)) :=
                  mul_le_mul_of_nonneg_left h2 (mul_nonneg hC₂ (Real.exp_pos _).le)
        _ = C₂ * Real.exp S₂.card * ∑ Γ₂ ∈ (meeting Λ S₂).powerset,
              ∏ γ ∈ Γ₂, (k γ * Real.exp (κ * polymerDiam γ + 1 * γ.card)) := by rw [mul_sum]
        _ ≤ C₂ * Real.exp S₂.card * Real.exp (S₂.card * ε) :=
            mul_le_mul_of_nonneg_left (sum_powerset_meeting_weight_le K k hk hκ hsmall Λ S₂
              (by norm_num) (by norm_num)) (mul_nonneg hC₂ (Real.exp_pos _).le)
        _ ≤ C₂ * Real.exp (2 * S₂.card) := by
            rw [mul_assoc, ← Real.exp_add]
            apply mul_le_mul_of_nonneg_left _ hC₂
            apply Real.exp_le_exp.mpr
            have : (0 : ℝ) ≤ S₂.card := Nat.cast_nonneg _
            nlinarith
    have hBnn : 0 ≤ ∑ Γ₂ ∈ (meeting Λ S₂).powerset,
        C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (∑ b ∈ meeting Λ (S₂ ∪ Γ₂.biUnion id), c b) :=
      sum_nonneg fun Γ₂ _ => mul_nonneg (mul_nonneg hC₂ (Finset.prod_nonneg fun γ _ => hkn γ))
        (Real.exp_pos _).le
    calc Real.exp (∑ b ∈ meeting Λ (S₁ ∪ Γ₁.biUnion id), c b) *
          ∑ Γ₂ ∈ (meeting Λ S₂).powerset,
            C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (∑ b ∈ meeting Λ (S₂ ∪ Γ₂.biUnion id), c b)
        ≤ (Real.exp S₁.card * ∏ γ ∈ Γ₁, Real.exp γ.card) * (C₂ * Real.exp (2 * S₂.card)) :=
          mul_le_mul hA hB hBnn (by positivity)
      _ ≤ C₂ * (Real.exp (2 * S₁.card + 2 * S₂.card) * ∏ γ ∈ Γ₁, Real.exp (2 * γ.card)) := by
          rw [show C₂ * (Real.exp (2 * S₁.card + 2 * S₂.card) * ∏ γ ∈ Γ₁, Real.exp (2 * γ.card)) =
            (Real.exp (2 * S₁.card) * ∏ γ ∈ Γ₁, Real.exp (2 * γ.card)) *
              (C₂ * Real.exp (2 * S₂.card)) by rw [Real.exp_add]; ring]
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC₂ (Real.exp_pos _).le)
          apply mul_le_mul (Real.exp_le_exp.mpr (by
            have : (0 : ℝ) ≤ S₁.card := Nat.cast_nonneg _
            linarith)) (Finset.prod_le_prod (fun γ _ => (Real.exp_pos _).le) fun γ _ =>
              Real.exp_le_exp.mpr (by
                have : (0 : ℝ) ≤ γ.card := Nat.cast_nonneg _
                linarith)) (Finset.prod_nonneg fun γ _ => (Real.exp_pos _).le)
            (Real.exp_pos _).le
  have hreachD := polymerDist_le_familyExtent_of_reach hΓ₁ hreach
  have hge : 1 ≤ Real.exp (κ * (familyExtent Γ₁ - polymerDist S₁ S₂)) :=
    Real.one_le_exp (by nlinarith)
  have hprod : (∏ γ ∈ Γ₁, k γ) * (∏ γ ∈ Γ₁, Real.exp (2 * γ.card)) *
      Real.exp (κ * familyExtent Γ₁) =
      ∏ γ ∈ Γ₁, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := by
    rw [prod_mul_exp, mul_assoc, ← Real.exp_sum, ← Real.exp_add]
    congr 2
    simp only [familyExtent, sum_add_distrib, mul_sum]
    ring
  have hmain := norm_bridgeTerm_le ν₀ S₁ S₂ F₁ hF₁ C₁ hF₁b F₂ hF₂ C₂ hF₂b K hK k hk hD Λ Γ₁
  calc ‖bridgeTerm ν₀ S₁ S₂ F₁ F₂ K Λ Γ₁‖
      ≤ C₁ * C₂ * (∏ γ ∈ Γ₁, k γ) *
          (∑ Γ' ∈ (meeting Λ W).powerset, (∏ γ ∈ Γ', k γ) *
            Real.exp (∑ b ∈ meeting Λ (W ∪ Γ'.biUnion id), c b)) +
        C₁ * (∏ γ ∈ Γ₁, k γ) *
          (Real.exp (∑ b ∈ meeting Λ (S₁ ∪ Γ₁.biUnion id), c b) *
            ∑ Γ₂ ∈ (meeting Λ S₂).powerset,
              C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (∑ b ∈ meeting Λ (S₂ ∪ Γ₂.biUnion id), c b)) := by
        refine hmain.trans (le_of_eq ?_)
        ring
    _ ≤ C₁ * C₂ * (∏ γ ∈ Γ₁, k γ) *
          (Real.exp (2 * S₁.card + 2 * S₂.card) * ∏ γ ∈ Γ₁, Real.exp (2 * γ.card)) +
        C₁ * (∏ γ ∈ Γ₁, k γ) *
          (C₂ * (Real.exp (2 * S₁.card + 2 * S₂.card) * ∏ γ ∈ Γ₁, Real.exp (2 * γ.card))) := by
        gcongr
    _ = 2 * C₁ * C₂ * Real.exp (2 * S₁.card + 2 * S₂.card) *
          ((∏ γ ∈ Γ₁, k γ) * ∏ γ ∈ Γ₁, Real.exp (2 * γ.card)) := by ring
    _ ≤ 2 * C₁ * C₂ * Real.exp (2 * S₁.card + 2 * S₂.card) *
          ((∏ γ ∈ Γ₁, k γ) * (∏ γ ∈ Γ₁, Real.exp (2 * γ.card)) *
            Real.exp (κ * (familyExtent Γ₁ - polymerDist S₁ S₂))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_mul_of_one_le_right
          (mul_nonneg hPk (Finset.prod_nonneg fun γ _ => (Real.exp_pos _).le)) hge
    _ = 2 * C₁ * C₂ * Real.exp (2 * S₁.card + 2 * S₂.card) * Real.exp (-κ * polymerDist S₁ S₂) *
          ((∏ γ ∈ Γ₁, k γ) * (∏ γ ∈ Γ₁, Real.exp (2 * γ.card)) *
            Real.exp (κ * familyExtent Γ₁)) := by
        rw [show κ * (familyExtent Γ₁ - polymerDist S₁ S₂) =
          κ * familyExtent Γ₁ + -κ * polymerDist S₁ S₂ by ring,
          Real.exp_add (κ * familyExtent Γ₁) (-κ * polymerDist S₁ S₂)]
        ring
    _ = 2 * C₁ * C₂ * Real.exp (2 * S₁.card + 2 * S₂.card) * Real.exp (-κ * polymerDist S₁ S₂) *
          ∏ γ ∈ Γ₁, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := by rw [hprod]

end Final

section Theorem

variable (K : ∀ S : Finset X, (S → E) → ℂ) (hK : ∀ S, Measurable (K S)) (k : Finset X → ℝ)
  (hk : ∀ S v, ‖K S v‖ ≤ k S) (hk0 : k ∅ = 0) {κ ε : ℝ} (hκ : 0 ≤ κ) (hε0 : 0 ≤ ε)
  (hε : ε * Real.exp 1 ≤ 1) (hsmall : ActivitySmall k κ ε)

include hK hk hk0 hκ hε0 hε hsmall in
/-- **Exponential clustering of a Kotecký–Preiss-small polymer gas.**  If the
activity bounds of a polymer representation over a product reference measure
satisfy the per-block smallness `∑_{γ ∋ x} k γ e^{4|γ| + κ diam γ} ≤ ε` with
`ε e ≤ 1` and `k ∅ = 0`, then for bounded observables `F₁`, `F₂` on block sets
`S₁`, `S₂` the truncated two-point function is at most
`3 C₁ C₂ e^{3(|S₁| + |S₂|)} e^{-κ d(S₁, S₂)}`, uniformly in the set of blocks and
in the polymer set. -/
theorem norm_truncated_le_exp (S₁ S₂ : Finset X) (hS₁ : S₁.Nonempty) (F₁ : (S₁ → E) → ℂ)
    (hF₁ : Measurable F₁) (C₁ : ℝ) (hF₁b : ∀ v, ‖F₁ v‖ ≤ C₁) (F₂ : (S₂ → E) → ℂ)
    (hF₂ : Measurable F₂) (C₂ : ℝ) (hF₂b : ∀ v, ‖F₂ v‖ ≤ C₂) (Λ : Finset (Finset X)) :
    ‖expectation ν₀ (fun ω => F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) K Λ -
        expectation ν₀ (fun ω => F₁ (restrictTo S₁ ω)) K Λ *
          expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K Λ‖ ≤
      3 * C₁ * C₂ * Real.exp (3 * S₁.card + 3 * S₂.card) *
        Real.exp (-κ * polymerDist S₁ S₂) := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (hF₁b fun _ => e₀)
  have hC₂ : 0 ≤ C₂ := (norm_nonneg _).trans (hF₂b fun _ => e₀)
  have hkn : ∀ γ, 0 ≤ k γ := activityBound_nonneg hk
  have hD := dobrushin_of_activitySmall ν₀ K k hk hk0 hκ hε0 hε hsmall
  have hZ := partitionFunction_ne_zero hD
  set c := latticeWeight (integratedActivity ν₀ K) with hcdef
  have hε1 : ε ≤ 1 := by
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  rw [truncated_eq_sum ν₀ S₁ S₂ F₁ hF₁ C₁ hF₁b F₂ hF₂ C₂ hF₂b K hK k hk Λ hZ]
  set B : ℝ := 3 * C₁ * C₂ * Real.exp (2 * S₁.card + 3 * S₂.card) *
    Real.exp (-κ * polymerDist S₁ S₂) with hBdef
  have hBnn : 0 ≤ B := by positivity
  have hterm : ∀ Γ₁ ∈ (meeting Λ S₁).powerset,
      ‖(if IsCompatible (overlapGraph X) Γ₁ then
        (if Disjoint (S₁ ∪ Γ₁.biUnion id) S₂ then
          familyWeight ν₀ S₁ F₁ K Γ₁ *
            sdiffRatio (overlapGraph X) (integratedActivity ν₀ K) Λ
              (meeting Λ (S₁ ∪ Γ₁.biUnion id)) *
            (expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K
                (Λ \ meeting Λ (S₁ ∪ Γ₁.biUnion id)) -
              expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K Λ)
        else bridgeTerm ν₀ S₁ S₂ F₁ F₂ K Λ Γ₁)
      else 0)‖ ≤ B * ∏ γ ∈ Γ₁, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := by
    intro Γ₁ hΓ₁
    have hΓ₁m : ∀ γ ∈ Γ₁, ¬ Disjoint γ S₁ := fun γ hγ =>
      (mem_filter.mp (mem_powerset.mp hΓ₁ hγ)).2
    have hPnn : 0 ≤ ∏ γ ∈ Γ₁, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) :=
      Finset.prod_nonneg fun γ _ => mul_nonneg (hkn γ) (Real.exp_pos _).le
    split_ifs with hc hdisj
    · -- separated families
      set Y₁ : Finset X := S₁ ∪ Γ₁.biUnion id with hY₁
      set A₁ := meeting Λ Y₁ with hA₁
      set D := polymerDist S₁ S₂ with hD'
      set e₁ := familyExtent Γ₁ with he₁
      have hΔ := norm_expectation_sdiff_sub_le ν₀ S₂ F₂ hF₂ C₂ hF₂b K hK k hk hD A₁
        (isInfluenceSupersolution_lattice ν₀ K k hk hk0 hκ hε0 hε hsmall Λ Y₁) Λ
      have hΔ' : ‖expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K (Λ \ A₁) -
          expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K Λ‖ ≤
          3 * C₂ * Real.exp (3 * S₂.card) * Real.exp (κ * (e₁ - D)) := by
        refine hΔ.trans ?_
        calc _ ≤ ∑ Γ₂ ∈ (meeting Λ S₂).powerset, 3 * C₂ * Real.exp (2 * S₂.card) *
              Real.exp (κ * (e₁ - D)) *
                ∏ γ ∈ Γ₂, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) :=
            sum_le_sum fun Γ₂ hΓ₂ => family_term_le ν₀ K k hk hk0 hκ hε0 hε hsmall S₁ S₂ hS₁ C₂
              hC₂ Λ Γ₁ Γ₂ hΓ₁m (mem_powerset.mp hΓ₂)
          _ = 3 * C₂ * Real.exp (2 * S₂.card) * Real.exp (κ * (e₁ - D)) *
              ∑ Γ₂ ∈ (meeting Λ S₂).powerset,
                ∏ γ ∈ Γ₂, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := by
            rw [mul_sum]
          _ ≤ 3 * C₂ * Real.exp (2 * S₂.card) * Real.exp (κ * (e₁ - D)) *
              Real.exp (S₂.card * ε) :=
            mul_le_mul_of_nonneg_left (sum_powerset_meeting_weight_le K k hk hκ hsmall Λ S₂
              (by norm_num) (by norm_num)) (by positivity)
          _ ≤ 3 * C₂ * Real.exp (3 * S₂.card) * Real.exp (κ * (e₁ - D)) := by
            rw [show 3 * C₂ * Real.exp (2 * S₂.card) * Real.exp (κ * (e₁ - D)) *
                Real.exp (S₂.card * ε) =
                3 * C₂ * Real.exp (κ * (e₁ - D)) * Real.exp (2 * S₂.card + S₂.card * ε) by
              rw [Real.exp_add (2 * S₂.card) (S₂.card * ε)]; ring,
              show 3 * C₂ * Real.exp (3 * S₂.card) * Real.exp (κ * (e₁ - D)) =
                3 * C₂ * Real.exp (κ * (e₁ - D)) * Real.exp (3 * S₂.card) by ring]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.exp_le_exp.mpr
            have : (0 : ℝ) ≤ S₂.card := Nat.cast_nonneg _
            nlinarith
      have hA : Real.exp (∑ b ∈ A₁, c b) ≤ Real.exp S₁.card * ∏ γ ∈ Γ₁, Real.exp γ.card := by
        refine (Real.exp_le_exp.mpr ?_).trans (exp_card_union_le S₁ Γ₁)
        have := sum_meeting_le_card (fun γ => latticeWeight_nonneg _ γ)
          (blockSum_latticeWeight_le ν₀ K k hk hκ hsmall) Λ Y₁
        have : (0 : ℝ) ≤ Y₁.card := Nat.cast_nonneg _
        nlinarith
      have hfw := norm_familyWeight_le ν₀ S₁ F₁ C₁ hF₁b hC₁ K k hk hkn Γ₁
      have hsr := norm_sdiffRatio_le hD Λ A₁
      have hPk : 0 ≤ ∏ γ ∈ Γ₁, k γ := Finset.prod_nonneg fun γ _ => hkn γ
      have hprod : (∏ γ ∈ Γ₁, k γ) * (∏ γ ∈ Γ₁, Real.exp γ.card) * Real.exp (κ * e₁) ≤
          ∏ γ ∈ Γ₁, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := by
        rw [prod_mul_exp, mul_assoc, ← Real.exp_sum, ← Real.exp_add]
        apply mul_le_mul_of_nonneg_left _ hPk
        apply Real.exp_le_exp.mpr
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, he₁]
        unfold familyExtent
        have : (0 : ℝ) ≤ ∑ γ ∈ Γ₁, (γ.card : ℝ) := sum_nonneg fun γ _ => Nat.cast_nonneg _
        linarith
      rw [norm_mul, norm_mul]
      calc ‖familyWeight ν₀ S₁ F₁ K Γ₁‖ *
            ‖sdiffRatio (overlapGraph X) (integratedActivity ν₀ K) Λ A₁‖ *
            ‖expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K (Λ \ A₁) -
              expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K Λ‖
          ≤ (C₁ * ∏ γ ∈ Γ₁, k γ) * (Real.exp S₁.card * ∏ γ ∈ Γ₁, Real.exp γ.card) *
              (3 * C₂ * Real.exp (3 * S₂.card) * Real.exp (κ * (e₁ - D))) := by
            gcongr
            exact hsr.trans hA
        _ = 3 * C₁ * C₂ * Real.exp (S₁.card + 3 * S₂.card) * Real.exp (-κ * D) *
              ((∏ γ ∈ Γ₁, k γ) * (∏ γ ∈ Γ₁, Real.exp γ.card) * Real.exp (κ * e₁)) := by
            rw [show κ * (e₁ - D) = κ * e₁ + -κ * D by ring, Real.exp_add (κ * e₁) (-κ * D),
              Real.exp_add (S₁.card : ℝ) (3 * S₂.card)]
            ring
        _ ≤ 3 * C₁ * C₂ * Real.exp (S₁.card + 3 * S₂.card) * Real.exp (-κ * D) *
              ∏ γ ∈ Γ₁, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := by
            gcongr
        _ ≤ B * ∏ γ ∈ Γ₁, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := by
            rw [hBdef]
            gcongr
            have : (0 : ℝ) ≤ S₁.card := Nat.cast_nonneg _
            linarith
    · -- bridging families
      refine (norm_bridgeTerm_le_lattice ν₀ K hK k hk hk0 hκ hε0 hε hsmall S₁ S₂ F₁ hF₁ C₁ hF₁b
        F₂ hF₂ C₂ hF₂b Λ Γ₁ hΓ₁m hdisj).trans ?_
      rw [hBdef]
      gcongr
      · norm_num
      · have : (0 : ℝ) ≤ S₂.card := Nat.cast_nonneg _
        linarith
    · simp only [norm_zero]
      exact mul_nonneg hBnn hPnn
  calc _ ≤ ∑ Γ₁ ∈ (meeting Λ S₁).powerset,
        ‖(if IsCompatible (overlapGraph X) Γ₁ then
          (if Disjoint (S₁ ∪ Γ₁.biUnion id) S₂ then
            familyWeight ν₀ S₁ F₁ K Γ₁ *
              sdiffRatio (overlapGraph X) (integratedActivity ν₀ K) Λ
                (meeting Λ (S₁ ∪ Γ₁.biUnion id)) *
              (expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K
                  (Λ \ meeting Λ (S₁ ∪ Γ₁.biUnion id)) -
                expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K Λ)
          else bridgeTerm ν₀ S₁ S₂ F₁ F₂ K Λ Γ₁)
        else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ Γ₁ ∈ (meeting Λ S₁).powerset,
          B * ∏ γ ∈ Γ₁, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := sum_le_sum hterm
    _ = B * ∑ Γ₁ ∈ (meeting Λ S₁).powerset,
          ∏ γ ∈ Γ₁, (k γ * Real.exp (κ * polymerDiam γ + 2 * γ.card)) := by rw [mul_sum]
    _ ≤ B * Real.exp (S₁.card * ε) :=
        mul_le_mul_of_nonneg_left (sum_powerset_meeting_weight_le K k hk hκ hsmall Λ S₁
          (by norm_num) (by norm_num)) hBnn
    _ ≤ 3 * C₁ * C₂ * Real.exp (3 * S₁.card + 3 * S₂.card) *
          Real.exp (-κ * polymerDist S₁ S₂) := by
        rw [hBdef, show 3 * C₁ * C₂ * Real.exp (2 * S₁.card + 3 * S₂.card) *
            Real.exp (-κ * polymerDist S₁ S₂) * Real.exp (S₁.card * ε) =
            3 * C₁ * C₂ * Real.exp (-κ * polymerDist S₁ S₂) *
              Real.exp (2 * S₁.card + 3 * S₂.card + S₁.card * ε) by
            rw [Real.exp_add (2 * S₁.card + 3 * S₂.card) (S₁.card * ε)]; ring,
          show 3 * C₁ * C₂ * Real.exp (3 * S₁.card + 3 * S₂.card) *
            Real.exp (-κ * polymerDist S₁ S₂) =
            3 * C₁ * C₂ * Real.exp (-κ * polymerDist S₁ S₂) *
              Real.exp (3 * S₁.card + 3 * S₂.card) by ring]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        have : (0 : ℝ) ≤ S₁.card := Nat.cast_nonneg _
        nlinarith

end Theorem

#print axioms dobrushin_of_activitySmall
#print axioms isInfluenceSupersolution_lattice
#print axioms norm_truncated_le_exp

end Mettapedia.Combinatorics.PolymerGas
