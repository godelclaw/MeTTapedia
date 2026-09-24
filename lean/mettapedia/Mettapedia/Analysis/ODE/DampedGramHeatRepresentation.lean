import Mettapedia.Analysis.ODE.DampedGramSeriesEvolution

/-!
# Heat representation of the full correlated Gram pairing

The reciprocal sum of damping rates is realized by an integral over
auxiliary heat time. Absolute summability justifies the infinite family,
with all correlations retained before integration.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DampedGramEnergy

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def decaySeries (γ : ι → ℝ) (x : ι → E) (t : ℝ) : E :=
  ∑' i, Real.exp (-γ i * t) • x i

theorem inner_decaySum (P : Finset ι) (γ : ι → ℝ) (x y : ι → E) (t : ℝ) :
    ⟪decaySum P γ x t, decaySum P γ y t⟫ =
      ∑ i ∈ P, ∑ j ∈ P, Real.exp (-(γ i + γ j) * t) * ⟪x i, y j⟫ := by
  simp only [decaySum]
  rw [sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem pairing_eq_integral_decay_inner (P : Finset ι) (γ : ι → ℝ) (x y : ι → E)
    (hγ : ∀ i ∈ P, 0 < γ i) :
    pairing P γ x y = ∫ t : ℝ in Set.Ioi 0, ⟪decaySum P γ x t, decaySum P γ y t⟫ := by
  simp_rw [inner_decaySum]
  rw [integral_finsetSum P (fun i hi ↦ integrable_finsetSum P
    (fun j hj ↦ integrableOn_decay_entry γ x y i j (hγ i hi) (hγ j hj)))]
  unfold pairing
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum P (fun j hj ↦ integrableOn_decay_entry γ x y i j (hγ i hi) (hγ j hj))]
  exact Finset.sum_congr rfl (fun j hj ↦ (integral_decay_entry γ x y i j (hγ i hi) (hγ j hj)).symm)

theorem continuous_decaySum (P : Finset ι) (γ : ι → ℝ) (x : ι → E) :
    Continuous (decaySum P γ x) :=
  continuous_finsetSum P (fun i _ ↦
    (Real.continuous_exp.comp ((continuous_const (y := -γ i)).mul continuous_id)).smul continuous_const)

theorem summable_norm_decay (γ : ι → ℝ) (x : ι → E)
    (hγ : ∀ i, 0 ≤ γ i) (hx : Summable (fun i ↦ ‖x i‖)) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun i ↦ ‖Real.exp (-γ i * t) • x i‖) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_ hx
  intro i
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hγ i)) ht))

theorem norm_decaySum_le (P : Finset ι) (γ : ι → ℝ) (x : ι → E) {c t : ℝ}
    (hγ : ∀ i, c ≤ γ i) (ht : 0 ≤ t) (hx : Summable (fun i ↦ ‖x i‖)) :
    ‖decaySum P γ x t‖ ≤ Real.exp (-c * t) * ∑' i, ‖x i‖ := by
  calc
    _ ≤ ∑ i ∈ P, Real.exp (-c * t) * ‖x i‖ := by
      apply norm_sum_le_of_le P
      intro i _
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      gcongr
      nlinarith [hγ i]
    _ = Real.exp (-c * t) * ∑ i ∈ P, ‖x i‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hx.sum_le_tsum P (fun i _ ↦ norm_nonneg _)) (Real.exp_pos _).le

variable [Countable ι] [CompleteSpace E]

omit [Countable ι] in
theorem norm_decaySeries_le (γ : ι → ℝ) (x : ι → E) {c t : ℝ}
    (hc : 0 ≤ c) (hγ : ∀ i, c ≤ γ i) (ht : 0 ≤ t)
    (hx : Summable (fun i ↦ ‖x i‖)) :
    ‖decaySeries γ x t‖ ≤ Real.exp (-c * t) * ∑' i, ‖x i‖ :=
  le_of_tendsto ((summable_norm_decay γ x (fun i ↦ hc.trans (hγ i)) hx ht).of_norm.hasSum.norm)
    (Eventually.of_forall (fun P ↦ norm_decaySum_le P γ x hγ ht hx))

omit [Countable ι] in
theorem continuousOn_decaySeries (γ : ι → ℝ) (x : ι → E)
    (hγ : ∀ i, 0 ≤ γ i) (hx : Summable (fun i ↦ ‖x i‖)) :
    ContinuousOn (decaySeries γ x) (Set.Ici 0) := by
  apply continuousOn_tsum (fun i ↦
    ((Real.continuous_exp.comp ((continuous_const (y := -γ i)).mul continuous_id)).smul
      continuous_const).continuousOn) hx
  intro i t ht
  change ‖Real.exp (-γ i * t) • x i‖ ≤ ‖x i‖
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hγ i)) ht))

omit [Countable ι] in
theorem integrableOn_decay_inner (γ : ι → ℝ) (x y : ι → E) {c : ℝ}
    (hc : 0 < c) (hγ : ∀ i, c ≤ γ i)
    (hx : Summable (fun i ↦ ‖x i‖)) (hy : Summable (fun i ↦ ‖y i‖)) :
    IntegrableOn (fun t ↦ ⟪decaySeries γ x t, decaySeries γ y t⟫) (Set.Ioi 0) := by
  have hγ0 (i : ι) : 0 ≤ γ i := hc.le.trans (hγ i)
  have hcont : ContinuousOn (fun t ↦ ⟪decaySeries γ x t, decaySeries γ y t⟫) (Set.Ici 0) :=
    (continuousOn_decaySeries γ x hγ0 hx).inner (continuousOn_decaySeries γ y hγ0 hy)
  have hm := (hcont.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable (μ := volume) measurableSet_Ioi
  apply ((integrableOn_exp_mul_Ioi (by linarith : -(2 * c) < 0) 0).mul_const
    ((∑' i, ‖x i‖) * (∑' i, ‖y i‖))).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  calc
    _ ≤ ‖decaySeries γ x t‖ * ‖decaySeries γ y t‖ := norm_inner_le_norm _ _
    _ ≤ (Real.exp (-c * t) * ∑' i, ‖x i‖) *
        (Real.exp (-c * t) * ∑' i, ‖y i‖) :=
      mul_le_mul (norm_decaySeries_le γ x hc.le hγ ht.le hx)
        (norm_decaySeries_le γ y hc.le hγ ht.le hy) (norm_nonneg _)
        (mul_nonneg (Real.exp_pos _).le (tsum_nonneg (fun _ ↦ norm_nonneg _)))
    _ = _ := by
      rw [mul_mul_mul_comm, ← Real.exp_add]
      congr 2
      ring


theorem seriesPairing_eq_integral_decay_inner (γ : ι → ℝ) (x y : ι → E) {c : ℝ}
    (hc : 0 < c) (hγ : ∀ i, c ≤ γ i)
    (hx : Summable (fun i ↦ ‖x i‖)) (hy : Summable (fun i ↦ ‖y i‖)) :
    seriesPairing γ x y = ∫ t : ℝ in Set.Ioi 0, ⟪decaySeries γ x t, decaySeries γ y t⟫ := by
  have hγ0 (i : ι) : 0 ≤ γ i := hc.le.trans (hγ i)
  have hdec (z : ι → E) (hz : Summable (fun i ↦ ‖z i‖)) (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun P : Finset ι ↦ decaySum P γ z t) atTop (𝓝 (decaySeries γ z t)) :=
    (summable_norm_decay γ z hγ0 hz ht).of_norm.hasSum
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (l := (atTop : Filter (Finset ι)))
    (F := fun P t ↦ ⟪decaySum P γ x t, decaySum P γ y t⟫)
    (f := fun t ↦ ⟪decaySeries γ x t, decaySeries γ y t⟫)
    (fun t ↦ Real.exp (-(2 * c) * t) * ((∑' i, ‖x i‖) * (∑' i, ‖y i‖)))
    (Eventually.of_forall (fun P ↦ ((continuous_decaySum P γ x).inner
      (continuous_decaySum P γ y)).aestronglyMeasurable)) ?_ ?_ ?_
  · have he (P : Finset ι) := pairing_eq_integral_decay_inner P γ x y
      (fun i _ ↦ hc.trans_le (hγ i))
    exact tendsto_nhds_unique (tendsto_pairing γ x y hc hγ hx hy)
      (hlim.congr (fun P ↦ (he P).symm))
  · exact Eventually.of_forall (fun P ↦ by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        _ ≤ ‖decaySum P γ x t‖ * ‖decaySum P γ y t‖ := norm_inner_le_norm _ _
        _ ≤ (Real.exp (-c * t) * ∑' i, ‖x i‖) *
            (Real.exp (-c * t) * ∑' i, ‖y i‖) :=
          mul_le_mul (norm_decaySum_le P γ x hγ ht.le hx)
            (norm_decaySum_le P γ y hγ ht.le hy) (norm_nonneg _)
            (mul_nonneg (Real.exp_pos _).le (tsum_nonneg (fun _ ↦ norm_nonneg _)))
        _ = _ := by
          rw [mul_mul_mul_comm, ← Real.exp_add]
          congr 2
          ring)
  · exact (integrableOn_exp_mul_Ioi (by linarith : -(2 * c) < 0) 0).mul_const _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hdec x hx t ht.le).inner (hdec y hy t ht.le)

theorem seriesEnergy_eq_integral_norm_decaySeries_sq (γ : ι → ℝ) (x : ι → E) {c : ℝ}
    (hc : 0 < c) (hγ : ∀ i, c ≤ γ i) (hx : Summable (fun i ↦ ‖x i‖)) :
    seriesEnergy γ x = ∫ t : ℝ in Set.Ioi 0, ‖decaySeries γ x t‖ ^ 2 := by
  simpa only [seriesEnergy, real_inner_self_eq_norm_sq] using
    seriesPairing_eq_integral_decay_inner γ x x hc hγ hx hx

end Mettapedia.Analysis.DampedGramEnergy
