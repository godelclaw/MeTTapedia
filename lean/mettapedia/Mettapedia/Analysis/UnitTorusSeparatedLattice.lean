import Mettapedia.Analysis.UnitTorusPeriodization
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# Uniform lattice majorants away from the torus origin

A bounded set of representatives and a positive distance from every lattice
point give a single summable inverse-power majorant. The near lattice points
are finite; the tail is the ordinary lattice inverse-power series.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusSeparatedLattice

open UnitTorusLattice UnitTorusPeriodization Set

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Td" => UnitAddTorus (Fin d)
local notation "Lat" => LatticeSubmodule (ι := Fin d)

theorem norm_representative_le (q : Td) : ‖representative q‖ ≤ d := by
  have he : representative q = ∑ i : Fin d, EuclideanSpace.single i (representative q i) := by
    ext i
    simp
  calc
    _ = ‖∑ i : Fin d, EuclideanSpace.single i (representative q i)‖ := congrArg norm he
    _ ≤ ∑ i : Fin d, ‖EuclideanSpace.single i (representative q i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := (AddCircle.equivIoc 1 0 (q i)).2
      simpa only [representative, PiLp.toLp_apply, PiLp.norm_single,
        Real.norm_eq_abs, abs_of_pos hi.1, zero_add] using hi.2
    _ = d := by simp

theorem exists_uniform_inverse_power_majorant (m : ℕ) (hm : d < m)
    (R r : ℝ) (hr : 0 < r) :
    ∃ g : Lat → ℝ, (∀ z, 0 ≤ g z) ∧ Summable g ∧
      ∀ (x : Rd), ‖x‖ ≤ R → (∀ z : Lat, r ≤ ‖(z : Rd) + x‖) →
        ∀ z : Lat, ‖(z : Rd) + x‖⁻¹ ^ m ≤ g z := by
  classical
  have hdim : Module.finrank ℤ Lat = d := by
    simpa using Module.finrank_eq_card_basis (latticeBasis (ι := Fin d))
  have hs := ZLattice.summable_norm_pow_inv Lat m (by simpa [hdim] using hm)
  have hf : (Metric.closedBall (0 : Lat) (2 * R)).Finite := by
    have h := (ZSpan.setFinite_inter (standardBasis (ι := Fin d))
      (Metric.isBounded_closedBall (x := (0 : Rd)) (r := 2 * R))).preimage_embedding
        (.subtype (fun x : Rd ↦ x ∈ (LatticeSubmodule (ι := Fin d))))
    apply h.subset
    intro z hz
    constructor
    · change ‖(z : Rd) - 0‖ ≤ 2 * R
      simpa only [sub_zero, Metric.mem_closedBall, dist_zero_right, Submodule.coe_norm] using hz
    · exact z.property
  let g : Lat → ℝ := fun z ↦
    (if z ∈ Metric.closedBall (0 : Lat) (2 * R) then r⁻¹ ^ m else 0) +
      (2 : ℝ) ^ m * ‖z‖⁻¹ ^ m
  have hnear : Summable (fun z : Lat ↦
      if z ∈ Metric.closedBall (0 : Lat) (2 * R) then r⁻¹ ^ m else 0) := by
    exact summable_of_ne_finset_zero (s := hf.toFinset) (fun z hz ↦ by
      simp only [Finite.mem_toFinset] at hz
      simp [hz])
  refine ⟨g, fun z ↦ by dsimp [g]; split_ifs <;> positivity,
    hnear.add (hs.mul_left _), ?_⟩
  intro x hx hsep z
  by_cases hz : z ∈ Metric.closedBall (0 : Lat) (2 * R)
  · have hb : ‖(z : Rd) + x‖⁻¹ ^ m ≤ r⁻¹ ^ m := by
      gcongr
      exact hsep z
    exact hb.trans (by dsimp [g]; rw [if_pos hz]; exact le_add_of_nonneg_right (by positivity))
  · have hz' : 2 * R < ‖z‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz
    have hnorm : ‖z‖ ≤ 2 * ‖(z : Rd) + x‖ := by
      have hn := norm_sub_le ((z : Rd) + x) x
      have hn' : ‖z‖ ≤ ‖(z : Rd) + x‖ + ‖x‖ := by
        simpa only [add_sub_cancel_right, Submodule.coe_norm] using hn
      linarith
    have hzpos : 0 < ‖z‖ := by linarith [norm_nonneg x]
    have hi : ‖(z : Rd) + x‖⁻¹ ≤ 2 * ‖z‖⁻¹ := by
      apply (inv_le_comm₀ (hr.trans_le (hsep z)) (by positivity : 0 < (2 : ℝ) * ‖z‖⁻¹)).mpr
      simp only [mul_inv_rev, inv_inv]
      nlinarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ ‖(z : Rd) + x‖⁻¹) hi m
    simpa only [g, if_neg hz, zero_add, mul_pow] using hp

end Mettapedia.Analysis.UnitTorusSeparatedLattice
