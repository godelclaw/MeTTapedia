import Mettapedia.Analysis.UnitTorusSeparatedLattice

/-!
# Absolute convergence of Schwartz lattice images

Away from the torus origin every lifted displacement is nonzero. Schwartz
decay and a summable lattice majorant give absolute convergence of the
actual image series. No uniformity in a family of Schwartz seminorms is
inferred.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusSchwartzLattice

open UnitTorusLattice UnitTorusPeriodization UnitTorusSeparatedLattice
open scoped SchwartzMap

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Td" => UnitAddTorus (Fin d)
local notation "Lat" => LatticeSubmodule (ι := Fin d)

def displacement (q : Td) (z : Lat) : Rd := (z : Rd) + representative q

theorem torusProjection_displacement (q : Td) (z : Lat) :
    torusProjection (displacement q z) = q :=
  (torusProjection_vadd (⟨z.1, z.2⟩ : Lattice (ι := Fin d)) (representative q)).trans
    (torusProjection_representative q)

theorem norm_le_displacement (q : Td) (z : Lat) : ‖q‖ ≤ ‖displacement q z‖ := by
  simpa only [torusProjection_displacement] using norm_torusProjection_le (displacement q z)

theorem displacement_ne_zero {q : Td} (hq : q ≠ 0) (z : Lat) : displacement q z ≠ 0 :=
  norm_pos_iff.mp ((norm_pos_iff.mpr hq).trans_le (norm_le_displacement q z))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem summable_norm_images (K : 𝓢(Rd, E)) {q : Td} (hq : q ≠ 0) :
    Summable (fun z : Lat ↦ ‖K (displacement q z)‖) := by
  obtain ⟨g, hg, hsum, hb⟩ := exists_uniform_inverse_power_majorant (d := d)
    (d + 1) (by omega) d ‖q‖ (norm_pos_iff.mpr hq)
  let C : ℝ := SchwartzMap.seminorm ℝ (d + 1) 0 K
  have hC : 0 ≤ C := apply_nonneg _ _
  apply (hsum.mul_left C).of_nonneg_of_le (fun z ↦ norm_nonneg _)
  intro z
  have hn : 0 < ‖displacement q z‖ := norm_pos_iff.mpr (displacement_ne_zero hq z)
  have hdecay : ‖K (displacement q z)‖ ≤ C * ‖displacement q z‖⁻¹ ^ (d + 1) := by
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hn _)]
    simpa only [mul_comm] using K.norm_pow_mul_le_seminorm ℝ (d + 1) (displacement q z)
  exact hdecay.trans (mul_le_mul_of_nonneg_left
    (hb (representative q) (norm_representative_le q) (norm_le_displacement q) z) hC)

end Mettapedia.Analysis.UnitTorusSchwartzLattice
