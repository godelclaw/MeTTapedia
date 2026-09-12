import Mettapedia.Analysis.AnnularRieszDecay
import Mettapedia.Analysis.UnitTorusSeparatedLattice
import Mettapedia.Analysis.PeriodicRieszPolynomial

/-!
# Uniform bounds for separated periodic Riesz interactions

For every positive separation radius, the actual periodized kernel family
has one pointwise bound independent of its highest frequency cutoff.
The finite Fourier representatives inherit the same bound almost everywhere.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRieszSeparated

open MeasureTheory UnitTorusLattice UnitTorusPeriodization UnitTorusSeparatedLattice

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Td" => UnitAddTorus (Fin d)
local notation "Lat" => LatticeSubmodule (ι := Fin d)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_uniform_entry_bound (r : ℝ) (hr : 0 < r) :
    ∃ C : Fin d → Fin d → ℝ, (∀ i j, 0 ≤ C i j) ∧
      ∀ i j N (q : Td), r ≤ ‖q‖ → ‖PeriodicRieszKernel.kernel i j N q‖ ≤ C i j := by
  obtain ⟨g, hg, hsum, hb⟩ := exists_uniform_inverse_power_majorant (d := d) (d + 1) (by omega) d r hr
  refine ⟨fun i j ↦ AnnularRieszKernel.decayBound i j * ∑' z, g z,
    fun i j ↦ mul_nonneg (AnnularRieszKernel.decayBound_nonneg i j) (tsum_nonneg hg), ?_⟩
  intro i j N q hq
  have hsep (z : Lat) : r ≤ ‖(z : Rd) + representative q‖ := by
    have he : torusProjection ((z : Rd) + representative q) = q :=
      (torusProjection_vadd (⟨z.1, z.2⟩ : Lattice (ι := Fin d)) (representative q)).trans
        (torusProjection_representative q)
    have hn := norm_torusProjection_le ((z : Rd) + representative q)
    rw [he] at hn
    exact hq.trans hn
  have hz (z : Lat) : (z : Rd) + representative q ≠ 0 :=
    norm_pos_iff.mp (hr.trans_le (hsep z))
  have hmajor (z : Lat) :
      ‖AnnularRieszKernel.partialKernel i j N ((z : Rd) + representative q)‖ ≤
        AnnularRieszKernel.decayBound i j * g z :=
    (AnnularRieszKernel.norm_partialKernel_le i j N _ (hz z)).trans
      (mul_le_mul_of_nonneg_left
        (hb (representative q) (norm_representative_le q) hsep z)
        (AnnularRieszKernel.decayBound_nonneg i j))
  have hnorm := (hsum.mul_left (AnnularRieszKernel.decayBound i j)).of_nonneg_of_le
    (fun z ↦ norm_nonneg _) hmajor
  change ‖∑' z : Lat, AnnularRieszKernel.partialKernel i j N
    ((z : Rd) + representative q)‖ ≤ _
  exact (norm_tsum_le_tsum_norm hnorm).trans
    ((hnorm.tsum_le_tsum hmajor (hsum.mul_left _)).trans_eq (tsum_mul_left))

theorem exists_uniform_operator_bound (r : ℝ) (hr : 0 < r) :
    ∃ C ≥ (0 : ℝ), ∀ N (q : Td), r ≤ ‖q‖ →
      ‖PeriodicRieszOperator.kernel N q‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_entry_bound (d := d) r hr
  refine ⟨∑ i, ∑ j, C i j, Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hC i j)), ?_⟩
  intro N q hq
  have hraw (x : Td) (hx : r ≤ ‖x‖) : ‖PeriodicRieszOperator.rawKernel N x‖ ≤ ∑ i, ∑ j, C i j :=
    (PeriodicRieszOperator.norm_rawKernel_le N x).trans
      (Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hb i j N x hx)))
  have hp := PeriodicRieszOperator.norm_kernel_le N q
  have h1 := hraw q hq
  have h2 := hraw (-q) (by simpa only [norm_neg] using hq)
  linarith

theorem exists_uniform_polynomial_bound (r : ℝ) (hr : 0 < r) :
    ∃ C ≥ (0 : ℝ), ∀ N, ∀ᵐ q : Td, r ≤ ‖q‖ →
      ‖PeriodicRieszPolynomial.kernel N q‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_operator_bound (d := d) r hr
  refine ⟨C, hC, fun N ↦ ?_⟩
  filter_upwards [PeriodicRieszPolynomial.kernel_ae_eq (d := d) N] with q hq hsep
  rw [hq]
  exact hb N q hsep

end Mettapedia.Analysis.PeriodicRieszSeparated
