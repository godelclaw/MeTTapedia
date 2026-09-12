import Mettapedia.Analysis.AnnularRieszSingularity
import Mettapedia.Analysis.PeriodicRieszSeparated

/-!
# Dimension-sharp bounds for the actual periodic Riesz kernels

Finitely many nearby lattice images use the dimension-sharp singularity
estimate. The remaining images use one extra power of Schwartz decay.
Thus periodization preserves the singularity order without a logarithm
or a constant depending on the highest Fourier cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRieszSingularity

open MeasureTheory Set UnitTorusLattice UnitTorusPeriodization UnitTorusSeparatedLattice

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Td" => UnitAddTorus (Fin d)
local notation "Lat" => LatticeSubmodule (ι := Fin d)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem finite_near_lattice : (Metric.closedBall (0 : Lat) (2 * (d : ℝ))).Finite := by
  have h := (ZSpan.setFinite_inter (standardBasis (ι := Fin d))
    (Metric.isBounded_closedBall (x := (0 : Rd)) (r := 2 * (d : ℝ)))).preimage_embedding
      (.subtype (fun x : Rd => x ∈ (LatticeSubmodule (ι := Fin d))))
  apply h.subset
  intro z hz
  constructor
  · change ‖(z : Rd) - 0‖ ≤ 2 * (d : ℝ)
    simpa only [sub_zero, Metric.mem_closedBall, dist_zero_right, Submodule.coe_norm] using hz
  · exact z.property

private theorem norm_torus_le_translate (q : Td) (z : Lat) :
    ‖q‖ ≤ ‖(z : Rd) + representative q‖ := by
  have he : torusProjection ((z : Rd) + representative q) = q :=
    (torusProjection_vadd (⟨z.1, z.2⟩ : Lattice (ι := Fin d)) (representative q)).trans
      (torusProjection_representative q)
  simpa only [he] using norm_torusProjection_le ((z : Rd) + representative q)

private theorem inverse_power_tail_le (q : Td) (z : Lat)
    (hz : z ∉ Metric.closedBall (0 : Lat) (2 * (d : ℝ))) :
    ‖(z : Rd) + representative q‖⁻¹ ^ (d + 1) ≤
      (2 : ℝ) ^ (d + 1) * ‖z‖⁻¹ ^ (d + 1) := by
  have hz' : 2 * (d : ℝ) < ‖z‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz
  have hx := norm_representative_le q
  have hn := norm_sub_le ((z : Rd) + representative q) (representative q)
  have hn' : ‖z‖ ≤ ‖(z : Rd) + representative q‖ + ‖representative q‖ := by
    simpa only [add_sub_cancel_right, Submodule.coe_norm] using hn
  have hnorm : ‖z‖ ≤ 2 * ‖(z : Rd) + representative q‖ := by linarith
  have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity : 0 ≤ 2 * (d : ℝ)) hz'
  have htpos : 0 < ‖(z : Rd) + representative q‖ := by linarith
  have hi : ‖(z : Rd) + representative q‖⁻¹ ≤ 2 * ‖z‖⁻¹ := by
    apply (inv_le_comm₀ htpos (by positivity : 0 < (2 : ℝ) * ‖z‖⁻¹)).mpr
    simp only [mul_inv_rev, inv_inv]
    nlinarith
  simpa only [mul_pow] using
    pow_le_pow_left₀ (by positivity : 0 ≤ ‖(z : Rd) + representative q‖⁻¹) hi (d + 1)

theorem exists_uniform_entry_bound :
    ∃ C : Fin d → Fin d → ℝ, (∀ i j, 0 ≤ C i j) ∧
      ∀ i j N (q : Td), ‖q‖ ^ d * ‖PeriodicRieszKernel.kernel i j N q‖ ≤ C i j := by
  classical
  have hdim : Module.finrank ℤ Lat = d := by
    simpa using Module.finrank_eq_card_basis (latticeBasis (ι := Fin d))
  have hs := ZLattice.summable_norm_pow_inv Lat (d + 1) (by simp [hdim])
  let g (i j : Fin d) (z : Lat) : ℝ :=
    (if z ∈ Metric.closedBall (0 : Lat) (2 * (d : ℝ)) then
      AnnularRieszKernel.singularityBound i j else 0) +
      ((d : ℝ) ^ d * AnnularRieszKernel.decayBound i j * (2 : ℝ) ^ (d + 1)) * ‖z‖⁻¹ ^ (d + 1)
  have hg (i j : Fin d) (z : Lat) : 0 ≤ g i j z := by
    dsimp [g]
    split_ifs <;> positivity [AnnularRieszKernel.singularityBound_nonneg i j,
      AnnularRieszKernel.decayBound_nonneg i j]
  have hsum (i j : Fin d) : Summable (g i j) := by
    have hnear : Summable (fun z : Lat =>
        if z ∈ Metric.closedBall (0 : Lat) (2 * (d : ℝ)) then
          AnnularRieszKernel.singularityBound i j else 0) := by
      exact summable_of_ne_finset_zero (s := finite_near_lattice.toFinset) (fun z hz => by
        simp only [Finite.mem_toFinset] at hz
        simp [hz])
    exact hnear.add (hs.mul_left _)
  refine ⟨fun i j => ∑' z, g i j z, fun i j => tsum_nonneg (hg i j), ?_⟩
  intro i j N q
  have hd : 0 < d := Nat.zero_lt_of_lt i.isLt
  by_cases hq : q = 0
  · simp [hq, zero_pow hd.ne', tsum_nonneg (hg i j)]
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hqbound : ‖q‖ ≤ d := by
    have h := norm_torusProjection_le (representative q)
    rw [torusProjection_representative] at h
    exact h.trans (norm_representative_le q)
  have hb (z : Lat) : ‖q‖ ^ d *
      ‖AnnularRieszKernel.partialKernel i j N ((z : Rd) + representative q)‖ ≤ g i j z := by
    have hsep := norm_torus_le_translate q z
    by_cases hz : z ∈ Metric.closedBall (0 : Lat) (2 * (d : ℝ))
    · have h := (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hsep d)
        (norm_nonneg (AnnularRieszKernel.partialKernel i j N ((z : Rd) + representative q)))).trans
          (AnnularRieszKernel.dimension_pow_mul_norm_partialKernel_le i j N _)
      exact h.trans (by dsimp [g]; rw [if_pos hz]; exact le_add_of_nonneg_right (by
        positivity [AnnularRieszKernel.decayBound_nonneg i j]))
    · have ht : (z : Rd) + representative q ≠ 0 := norm_pos_iff.mp (hqpos.trans_le hsep)
      calc
        _ ≤ (d : ℝ) ^ d * (AnnularRieszKernel.decayBound i j *
            ‖(z : Rd) + representative q‖⁻¹ ^ (d + 1)) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hqbound d)
            (AnnularRieszKernel.norm_partialKernel_le i j N _ ht)
            (norm_nonneg _) (by positivity)
        _ ≤ (d : ℝ) ^ d * (AnnularRieszKernel.decayBound i j *
            ((2 : ℝ) ^ (d + 1) * ‖z‖⁻¹ ^ (d + 1))) := by
          gcongr
          · exact AnnularRieszKernel.decayBound_nonneg i j
          · exact inverse_power_tail_le q z hz
        _ = g i j z := by simp only [g, if_neg hz, zero_add]; ring
  have hw := (hsum i j).of_nonneg_of_le (fun z => by positivity) hb
  have hn := (summable_mul_left_iff (pow_pos hqpos d).ne').mp hw
  change ‖q‖ ^ d * ‖∑' z : Lat, AnnularRieszKernel.partialKernel i j N
    ((z : Rd) + representative q)‖ ≤ _
  calc
    _ ≤ ‖q‖ ^ d * ∑' z : Lat, ‖AnnularRieszKernel.partialKernel i j N
        ((z : Rd) + representative q)‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn) (by positivity)
    _ = ∑' z : Lat, ‖q‖ ^ d * ‖AnnularRieszKernel.partialKernel i j N
        ((z : Rd) + representative q)‖ := (tsum_mul_left).symm
    _ ≤ _ := hw.tsum_le_tsum hb (hsum i j)

theorem exists_uniform_operator_bound :
    ∃ C ≥ (0 : ℝ), ∀ N (q : Td), ‖q‖ ^ d * ‖PeriodicRieszOperator.kernel N q‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_entry_bound (d := d)
  refine ⟨∑ i, ∑ j, C i j, Finset.sum_nonneg (fun i => fun _ =>
    Finset.sum_nonneg (fun j => fun _ => hC i j)), ?_⟩
  intro N q
  have hraw (x : Td) : ‖x‖ ^ d * ‖PeriodicRieszOperator.rawKernel N x‖ ≤ ∑ i, ∑ j, C i j := by
    calc
      _ ≤ ‖x‖ ^ d * ∑ i : Fin d, ∑ j : Fin d, ‖PeriodicRieszKernel.kernel i j N x‖ :=
        mul_le_mul_of_nonneg_left (PeriodicRieszOperator.norm_rawKernel_le N x) (by positivity)
      _ = ∑ i : Fin d, ∑ j : Fin d, ‖x‖ ^ d * ‖PeriodicRieszKernel.kernel i j N x‖ := by
        simp only [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j N x))
  have h := mul_le_mul_of_nonneg_left (PeriodicRieszOperator.norm_kernel_le N q)
    (show 0 ≤ ‖q‖ ^ d by positivity)
  have h₁ := hraw q
  have h₂ := hraw (-q)
  simp only [norm_neg] at h₂
  nlinarith only [h, h₁, h₂]

end Mettapedia.Analysis.PeriodicRieszSingularity
