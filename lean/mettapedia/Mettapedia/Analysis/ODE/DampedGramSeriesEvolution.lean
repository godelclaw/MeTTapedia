import Mettapedia.Analysis.ODE.DampedGramSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Time evolution of an infinite correlated Gram energy

Uniform summable envelopes on a compact time interval justify passage
from the finite correlated identities to the entire series. The
result retains the signed nonlinear work. Envelope existence is a
local convergence hypothesis, not a global bound on that work.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DampedGramEnergy

open scoped Topology
open Filter MeasureTheory

variable {ι E : Type*} [Countable ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [Countable ι] [InnerProductSpace ℝ E] in
theorem intervalIntegrable_norm_tsum_sq (x : ℝ → ι → E) (t : ℝ) (ht : 0 ≤ t)
    (hx : ∀ i, ContinuousOn (fun τ ↦ x τ i) (Set.Icc 0 t))
    (a : ι → ℝ) (ha : Summable a)
    (hxa : ∀ τ ∈ Set.Icc 0 t, ∀ i, ‖x τ i‖ ≤ a i) :
    IntervalIntegrable (fun τ ↦ ‖∑' i, x τ i‖ ^ 2) volume 0 t :=
  ((continuousOn_tsum hx ha (fun i τ hτ ↦ hxa τ hτ i)).norm.pow 2).intervalIntegrable_of_Icc ht

omit [Countable ι] [CompleteSpace E] in
theorem intervalIntegrable_seriesPairing (γ : ι → ℝ) {c : ℝ}
    (hc : 0 < c) (hγ : ∀ i, c ≤ γ i) (x y : ℝ → ι → E) (t : ℝ) (ht : 0 ≤ t)
    (hx : ∀ i, ContinuousOn (fun τ ↦ x τ i) (Set.Icc 0 t))
    (hy : ∀ i, ContinuousOn (fun τ ↦ y τ i) (Set.Icc 0 t))
    (a b : ι → ℝ) (ha : Summable a) (hb : Summable b)
    (hxa : ∀ τ ∈ Set.Icc 0 t, ∀ i, ‖x τ i‖ ≤ a i)
    (hyb : ∀ τ ∈ Set.Icc 0 t, ∀ i, ‖y τ i‖ ≤ b i) :
    IntervalIntegrable (fun τ ↦ seriesPairing γ (x τ) (y τ)) volume 0 t := by
  have ha0 (i : ι) : 0 ≤ a i := (norm_nonneg _).trans (hxa 0 ⟨le_rfl, ht⟩ i)
  have hb0 (i : ι) : 0 ≤ b i := (norm_nonneg _).trans (hyb 0 ⟨le_rfl, ht⟩ i)
  have hs := (ha.mul_of_nonneg hb ha0 hb0).div_const (2 * c)
  have hc' (p : ι × ι) : ContinuousOn (fun τ ↦ pairTerm γ (x τ) (y τ) p) (Set.Icc 0 t) :=
    ((hx p.1).inner (hy p.2)).div_const _
  have hbound (p : ι × ι) (τ : ℝ) (hτ : τ ∈ Set.Icc 0 t) :
      ‖pairTerm γ (x τ) (y τ) p‖ ≤ (a p.1 * b p.2) / (2 * c) :=
    (norm_pairTerm_le γ (x τ) (y τ) hc hγ p).trans
      (div_le_div_of_nonneg_right (mul_le_mul (hxa τ hτ p.1) (hyb τ hτ p.2)
        (norm_nonneg _) (ha0 p.1)) (by positivity))
  exact (continuousOn_tsum hc' hs hbound).intervalIntegrable_of_Icc ht

omit [Countable ι] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem summable_norm_of_envelope (x : ι → E) (a : ι → ℝ)
    (ha : Summable a) (hxa : ∀ i, ‖x i‖ ≤ a i) : Summable (fun i ↦ ‖x i‖) :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hxa ha

omit [Countable ι] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem norm_partialSum_le_envelope (P : Finset ι) (x : ι → E) (a : ι → ℝ)
    (ha : Summable a) (hxa : ∀ i, ‖x i‖ ≤ a i) : ‖∑ i ∈ P, x i‖ ≤ ∑' i, a i :=
  (norm_sum_le_of_le P (fun i _ ↦ hxa i)).trans
    (ha.sum_le_tsum P (fun i _ ↦ (norm_nonneg _).trans (hxa i)))

omit [InnerProductSpace ℝ E] in
theorem tendsto_integral_norm_partialSum_sq (x : ℝ → ι → E) (t : ℝ) (ht : 0 ≤ t)
    (hx : ∀ i, ContinuousOn (fun τ ↦ x τ i) (Set.Icc 0 t))
    (a : ι → ℝ) (ha : Summable a)
    (hxa : ∀ τ ∈ Set.Icc 0 t, ∀ i, ‖x τ i‖ ≤ a i) :
    Tendsto (fun P : Finset ι ↦ ∫ τ in (0 : ℝ)..t, ‖∑ i ∈ P, x τ i‖ ^ 2)
      atTop (𝓝 (∫ τ in (0 : ℝ)..t, ‖∑' i, x τ i‖ ^ 2)) := by
  have hs : Set.uIoc (0 : ℝ) t ⊆ Set.Icc 0 t := by
    rw [Set.uIoc_of_le ht]
    exact Set.Ioc_subset_Icc_self
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ ↦ (∑' i, a i) ^ 2)
  · exact Eventually.of_forall (fun P ↦
      (((continuousOn_finsetSum P (fun i _ ↦ hx i)).norm.pow 2).mono hs).aestronglyMeasurable
        measurableSet_uIoc)
  · exact Eventually.of_forall (fun P ↦ ae_of_all _ (fun τ hτ ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_partialSum_le_envelope P (x τ) a ha
        (hxa τ (hs hτ))) 2))
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun τ hτ ↦
      (summable_norm_of_envelope (x τ) a ha (hxa τ (hs hτ))).of_norm.hasSum.norm.pow 2)

omit [CompleteSpace E] in
theorem tendsto_integral_pairing (γ : ι → ℝ) {c : ℝ}
    (hc : 0 < c) (hγ : ∀ i, c ≤ γ i) (x y : ℝ → ι → E) (t : ℝ) (ht : 0 ≤ t)
    (hx : ∀ i, ContinuousOn (fun τ ↦ x τ i) (Set.Icc 0 t))
    (hy : ∀ i, ContinuousOn (fun τ ↦ y τ i) (Set.Icc 0 t))
    (a b : ι → ℝ) (ha : Summable a) (hb : Summable b)
    (hxa : ∀ τ ∈ Set.Icc 0 t, ∀ i, ‖x τ i‖ ≤ a i)
    (hyb : ∀ τ ∈ Set.Icc 0 t, ∀ i, ‖y τ i‖ ≤ b i) :
    Tendsto (fun P : Finset ι ↦ ∫ τ in (0 : ℝ)..t, pairing P γ (x τ) (y τ))
      atTop (𝓝 (∫ τ in (0 : ℝ)..t, seriesPairing γ (x τ) (y τ))) := by
  have hs : Set.uIoc (0 : ℝ) t ⊆ Set.Icc 0 t := by
    rw [Set.uIoc_of_le ht]
    exact Set.Ioc_subset_Icc_self
  have hcont (P : Finset ι) :
      ContinuousOn (fun τ ↦ pairing P γ (x τ) (y τ)) (Set.Icc 0 t) :=
    continuousOn_iff_continuous_restrict.mpr (continuous_pairing P γ _ _
      (fun i _ ↦ continuousOn_iff_continuous_restrict.mp (hx i))
      (fun i _ ↦ continuousOn_iff_continuous_restrict.mp (hy i)))
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ ↦ ((∑' i, a i) * (∑' i, b i)) / (2 * c))
  · exact Eventually.of_forall (fun P ↦ ((hcont P).mono hs).aestronglyMeasurable measurableSet_uIoc)
  · exact Eventually.of_forall (fun P ↦ ae_of_all _ (fun τ hτ ↦
      norm_pairing_le_envelopes P γ (x τ) (y τ) hc hγ a b ha hb
        (hxa τ (hs hτ)) (hyb τ (hs hτ))))
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun τ hτ ↦ tendsto_pairing γ (x τ) (y τ) hc hγ
      (summable_norm_of_envelope (x τ) a ha (hxa τ (hs hτ)))
      (summable_norm_of_envelope (y τ) b hb (hyb τ (hs hτ))))

theorem series_energy_identity_of_damped (γ : ι → ℝ) {c : ℝ}
    (hc : 0 < c) (hγ : ∀ i, c ≤ γ i) (x r : ℝ → ι → E) (t : ℝ) (ht : 0 ≤ t)
    (hx : ∀ i, ContinuousOn (fun τ ↦ x τ i) (Set.Icc 0 t))
    (hr : ∀ i, ContinuousOn (fun τ ↦ r τ i) (Set.Icc 0 t))
    (a b : ι → ℝ) (ha : Summable a) (hb : Summable b)
    (hxa : ∀ τ ∈ Set.Icc 0 t, ∀ i, ‖x τ i‖ ≤ a i)
    (hrb : ∀ τ ∈ Set.Icc 0 t, ∀ i, ‖r τ i‖ ≤ b i)
    (he : ∀ τ ∈ Set.Ioo 0 t, ∀ i,
      HasDerivAt (fun s ↦ x s i) (r τ i - γ i • x τ i) τ) :
    seriesEnergy γ (x t) + (∫ τ in (0 : ℝ)..t, ‖∑' i, x τ i‖ ^ 2) =
      seriesEnergy γ (x 0) + 2 * (∫ τ in (0 : ℝ)..t, seriesPairing γ (r τ) (x τ)) := by
  have hs (τ : ℝ) (hτ : τ ∈ Set.Icc 0 t) :=
    summable_norm_of_envelope (x τ) a ha (hxa τ hτ)
  have hL := (tendsto_pairing γ (x t) (x t) hc hγ (hs t ⟨ht, le_rfl⟩)
    (hs t ⟨ht, le_rfl⟩)).add (tendsto_integral_norm_partialSum_sq x t ht hx a ha hxa)
  have hR := (tendsto_pairing γ (x 0) (x 0) hc hγ (hs 0 ⟨le_rfl, ht⟩)
    (hs 0 ⟨le_rfl, ht⟩)).add ((tendsto_integral_pairing γ hc hγ r x t ht hr hx b a hb ha
      hrb hxa).const_mul 2)
  apply tendsto_nhds_unique hL
  have hEq (P : Finset ι) := energy_identity_of_damped P γ
    (fun i _ ↦ hc.trans_le (hγ i)) x r t ht (fun i _ ↦ hx i) (fun i _ ↦ hr i)
    (fun τ hτ i _ ↦ he τ hτ i)
  exact hR.congr (fun P ↦ (hEq P).symm)

theorem integral_norm_tsum_sq_le_of_damped (γ : ι → ℝ) {c : ℝ}
    (hc : 0 < c) (hγ : ∀ i, c ≤ γ i) (x r : ℝ → ι → E) (t : ℝ) (ht : 0 ≤ t)
    (hx : ∀ i, ContinuousOn (fun τ ↦ x τ i) (Set.Icc 0 t))
    (hr : ∀ i, ContinuousOn (fun τ ↦ r τ i) (Set.Icc 0 t))
    (a b : ι → ℝ) (ha : Summable a) (hb : Summable b)
    (hxa : ∀ τ ∈ Set.Icc 0 t, ∀ i, ‖x τ i‖ ≤ a i)
    (hrb : ∀ τ ∈ Set.Icc 0 t, ∀ i, ‖r τ i‖ ≤ b i)
    (he : ∀ τ ∈ Set.Ioo 0 t, ∀ i,
      HasDerivAt (fun s ↦ x s i) (r τ i - γ i • x τ i) τ) :
    (∫ τ in (0 : ℝ)..t, ‖∑' i, x τ i‖ ^ 2) ≤
      seriesEnergy γ (x 0) + 2 * (∫ τ in (0 : ℝ)..t, seriesPairing γ (r τ) (x τ)) := by
  have h := series_energy_identity_of_damped γ hc hγ x r t ht hx hr a b ha hb hxa hrb he
  have hn := seriesEnergy_nonneg γ (x t) hc hγ
    (summable_norm_of_envelope (x t) a ha (hxa t ⟨ht, le_rfl⟩))
  linarith

end Mettapedia.Analysis.DampedGramEnergy
