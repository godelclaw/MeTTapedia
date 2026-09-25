import Mettapedia.Combinatorics.PolymerGas.LatticeClustering

/-!
# Polymer gases: partition functions barely see changes of large polymers

If two polymer weights agree off a set `W` of polymers and satisfy Dobrushin's
criterion with weights `c` and `c'`, their partition functions over any finite set
of polymers differ by a factor between `e^{-s}` and `e^{s}`, where
`s = ∑_W c + ∑_W c'` (`abs_log_norm_div_le_of_eqOn`).  The proof removes `W`,
where the two gases agree, and puts it back; no cluster expansion is used.

Under per-block smallness at decay rate `κ` (`ActivitySmall`), polymers that all
meet a block set `Y` and all have diameter at least `D` carry total weight at
most `|Y| ε e^{-κ D}` (`sum_latticeWeight_le_of_meet_of_diam`).  Hence two
polymer representations over the same product reference measure, with the same
activity bounds, whose integrated activities differ only on such polymers have
partition functions whose ratio has logarithm at most `2 |Y| ε e^{-κ D}` in
absolute value (`abs_log_norm_partitionFunction_div_le`).

On a torus, a twist that changes the integrated activities only of polymers
winding around it therefore has a free energy that decays exponentially in the
side length, up to the size of a cut.
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory

namespace Mettapedia.Combinatorics.PolymerGas

section General

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- The partition function over `Λ` depends only on the weights of the polymers
of `Λ`. -/
theorem partitionFunction_congr {w w' : V → ℂ} {Λ : Finset V}
    (h : ∀ γ ∈ Λ, w γ = w' γ) : partitionFunction G w Λ = partitionFunction G w' Λ := by
  unfold partitionFunction
  refine sum_congr rfl fun I hI => ?_
  have hsub : I ⊆ Λ := mem_powerset.mp hI
  split_ifs
  · exact prod_congr rfl fun γ hγ => h γ (hsub hγ)
  · rfl

/-- **Changing the weights on a set of polymers.**  If `w` and `w'` agree on
`Λ ∖ W`, then `‖Z_{w'}(Λ)‖ ≤ e^{∑_W c + ∑_W c'} ‖Z_w(Λ)‖`. -/
theorem norm_partitionFunction_le_of_eqOn {w w' : V → ℂ} {c c' : V → ℝ}
    (hD : DobrushinCondition G w c) (hD' : DobrushinCondition G w' c')
    (Λ W : Finset V) (hw : ∀ γ ∈ Λ \ W, w γ = w' γ) :
    ‖partitionFunction G w' Λ‖ ≤
      Real.exp (∑ u ∈ W, c u + ∑ u ∈ W, c' u) * ‖partitionFunction G w Λ‖ := by
  calc ‖partitionFunction G w' Λ‖
      ≤ Real.exp (∑ u ∈ W, c' u) * ‖partitionFunction G w' (Λ \ W)‖ :=
        norm_partitionFunction_le_exp_mul_sdiff hD' Λ W
    _ = Real.exp (∑ u ∈ W, c' u) * ‖partitionFunction G w (Λ \ W)‖ := by
        rw [partitionFunction_congr (fun γ hγ => (hw γ hγ).symm)]
    _ ≤ Real.exp (∑ u ∈ W, c' u) *
          (Real.exp (∑ u ∈ W, c u) * ‖partitionFunction G w Λ‖) :=
        mul_le_mul_of_nonneg_left (norm_partitionFunction_sdiff_le_of_dobrushin hD Λ W)
          (Real.exp_pos _).le
    _ = Real.exp (∑ u ∈ W, c u + ∑ u ∈ W, c' u) * ‖partitionFunction G w Λ‖ := by
        rw [← mul_assoc, ← Real.exp_add, add_comm]

/-- The logarithm of the ratio of the two partition functions is at most
`∑_W c + ∑_W c'` in absolute value. -/
theorem abs_log_norm_div_le_of_eqOn {w w' : V → ℂ} {c c' : V → ℝ}
    (hD : DobrushinCondition G w c) (hD' : DobrushinCondition G w' c')
    (Λ W : Finset V) (hw : ∀ γ ∈ Λ \ W, w γ = w' γ) :
    |Real.log (‖partitionFunction G w' Λ‖ / ‖partitionFunction G w Λ‖)| ≤
      ∑ u ∈ W, c u + ∑ u ∈ W, c' u := by
  have hZ : 0 < ‖partitionFunction G w Λ‖ := norm_pos_iff.mpr (partitionFunction_ne_zero hD Λ)
  have hZ' : 0 < ‖partitionFunction G w' Λ‖ :=
    norm_pos_iff.mpr (partitionFunction_ne_zero hD' Λ)
  have hup := norm_partitionFunction_le_of_eqOn hD hD' Λ W hw
  have hdown := norm_partitionFunction_le_of_eqOn hD' hD Λ W (fun γ hγ => (hw γ hγ).symm)
  rw [add_comm (∑ u ∈ W, c' u)] at hdown
  set s := ∑ u ∈ W, c u + ∑ u ∈ W, c' u
  have hq : 0 < ‖partitionFunction G w' Λ‖ / ‖partitionFunction G w Λ‖ := div_pos hZ' hZ
  rw [abs_le]
  constructor
  · rw [Real.le_log_iff_exp_le hq, le_div_iff₀ hZ]
    have hexp : Real.exp (-s) * Real.exp s = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc Real.exp (-s) * ‖partitionFunction G w Λ‖
        ≤ Real.exp (-s) * (Real.exp s * ‖partitionFunction G w' Λ‖) :=
          mul_le_mul_of_nonneg_left hdown (Real.exp_pos _).le
      _ = ‖partitionFunction G w' Λ‖ := by rw [← mul_assoc, hexp, one_mul]
  · rw [Real.log_le_iff_le_exp hq, div_le_iff₀ hZ]
    exact hup

end General

section Lattice

variable {X : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
variable {E : Type*} [MeasurableSpace E] [Nonempty E]
variable (ν₀ : Measure E) [IsProbabilityMeasure ν₀]

/-- **Large polymers through a cut.**  Under per-block smallness at rate `κ ≥ 0`,
the polymers that meet `Y` and have diameter at least `D` carry total Dobrushin
weight at most `|Y| ε e^{-κ D}`. -/
theorem sum_latticeWeight_le_of_meet_of_diam (K : ∀ S : Finset X, (S → E) → ℂ)
    (k : Finset X → ℝ) (hk : ∀ S v, ‖K S v‖ ≤ k S) {κ ε : ℝ} (hκ : 0 ≤ κ)
    (hsmall : ActivitySmall k κ ε) (Y : Finset X) (D : ℝ) (W : Finset (Finset X))
    (hmeet : ∀ γ ∈ W, ¬ Disjoint Y γ) (hdiam : ∀ γ ∈ W, D ≤ polymerDiam γ) :
    ∑ γ ∈ W, latticeWeight (integratedActivity ν₀ K) γ ≤
      Y.card * ε * Real.exp (-κ * D) := by
  have hkn : ∀ γ, 0 ≤ k γ := activityBound_nonneg hk
  set f : Finset X → ℝ := fun γ => k γ * Real.exp (4 * γ.card + κ * polymerDiam γ) with hf
  have hfn : ∀ γ, 0 ≤ f γ := fun γ => mul_nonneg (hkn γ) (Real.exp_pos _).le
  have hterm : ∀ γ ∈ W, latticeWeight (integratedActivity ν₀ K) γ ≤
      Real.exp (-κ * D) * f γ := by
    intro γ hγ
    have hcard : (0 : ℝ) ≤ γ.card := Nat.cast_nonneg _
    have hκD : κ * D ≤ κ * polymerDiam γ := mul_le_mul_of_nonneg_left (hdiam γ hγ) hκ
    calc latticeWeight (integratedActivity ν₀ K) γ ≤ k γ * Real.exp γ.card :=
          latticeWeight_le_activity ν₀ K k hk γ
      _ ≤ k γ * Real.exp (-κ * D + (4 * γ.card + κ * polymerDiam γ)) := by
          apply mul_le_mul_of_nonneg_left _ (hkn γ)
          apply Real.exp_le_exp.mpr
          linarith
      _ = Real.exp (-κ * D) * f γ := by
          rw [hf, Real.exp_add]
          ring
  calc ∑ γ ∈ W, latticeWeight (integratedActivity ν₀ K) γ
      ≤ ∑ γ ∈ W, Real.exp (-κ * D) * f γ := sum_le_sum hterm
    _ = Real.exp (-κ * D) * ∑ γ ∈ W, f γ := by rw [mul_sum]
    _ ≤ Real.exp (-κ * D) * ∑ x ∈ Y, blockSum f x :=
        mul_le_mul_of_nonneg_left (sum_le_sum_blockSum hfn hmeet) (Real.exp_pos _).le
    _ ≤ Real.exp (-κ * D) * (Y.card * ε) :=
        mul_le_mul_of_nonneg_left (sum_blockSum_le hsmall Y) (Real.exp_pos _).le
    _ = Y.card * ε * Real.exp (-κ * D) := by ring

/-- **Twist insensitivity.**  Two polymer representations over the same product
reference measure, with activity bounds `k` satisfying per-block smallness at
rate `κ`, whose integrated activities differ only on polymers of `Λ` that meet
`Y` and have diameter at least `D`, have partition functions over `Λ` whose ratio
has logarithm at most `2 |Y| ε e^{-κ D}` in absolute value. -/
theorem abs_log_norm_partitionFunction_div_le (K K' : ∀ S : Finset X, (S → E) → ℂ)
    (k : Finset X → ℝ) (hk : ∀ S v, ‖K S v‖ ≤ k S) (hk' : ∀ S v, ‖K' S v‖ ≤ k S)
    (hk0 : k ∅ = 0) {κ ε : ℝ} (hκ : 0 ≤ κ) (hε0 : 0 ≤ ε) (hε : ε * Real.exp 1 ≤ 1)
    (hsmall : ActivitySmall k κ ε) (Λ : Finset (Finset X)) (Y : Finset X) (D : ℝ)
    (hdiff : ∀ γ ∈ Λ, integratedActivity ν₀ K γ ≠ integratedActivity ν₀ K' γ →
      ¬ Disjoint Y γ ∧ D ≤ polymerDiam γ) :
    |Real.log (‖partitionFunction (overlapGraph X) (integratedActivity ν₀ K') Λ‖ /
        ‖partitionFunction (overlapGraph X) (integratedActivity ν₀ K) Λ‖)| ≤
      2 * (Y.card * ε * Real.exp (-κ * D)) := by
  classical
  set W := Λ.filter fun γ => integratedActivity ν₀ K γ ≠ integratedActivity ν₀ K' γ with hW
  have hD := dobrushin_of_activitySmall ν₀ K k hk hk0 hκ hε0 hε hsmall
  have hD' := dobrushin_of_activitySmall ν₀ K' k hk' hk0 hκ hε0 hε hsmall
  have hagree : ∀ γ ∈ Λ \ W, integratedActivity ν₀ K γ = integratedActivity ν₀ K' γ := by
    intro γ hγ
    rw [mem_sdiff, hW, mem_filter] at hγ
    by_contra hne
    exact hγ.2 ⟨hγ.1, hne⟩
  have hmeet : ∀ γ ∈ W, ¬ Disjoint Y γ := fun γ hγ => by
    rw [hW, mem_filter] at hγ
    exact (hdiff γ hγ.1 hγ.2).1
  have hdiam : ∀ γ ∈ W, D ≤ polymerDiam γ := fun γ hγ => by
    rw [hW, mem_filter] at hγ
    exact (hdiff γ hγ.1 hγ.2).2
  refine (abs_log_norm_div_le_of_eqOn hD hD' Λ W hagree).trans ?_
  have h1 := sum_latticeWeight_le_of_meet_of_diam ν₀ K k hk hκ hsmall Y D W hmeet hdiam
  have h2 := sum_latticeWeight_le_of_meet_of_diam ν₀ K' k hk' hκ hsmall Y D W hmeet hdiam
  linarith

end Lattice

#print axioms abs_log_norm_div_le_of_eqOn
#print axioms abs_log_norm_partitionFunction_div_le

end Mettapedia.Combinatorics.PolymerGas
