import Mettapedia.Analysis.UnitTorusSchwartzLattice
import Mettapedia.Analysis.UnitTorusMaterialLifts
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Differentiating Schwartz lattice sums on real lifts

Schwartz decay gives summable majorants on every bounded set of real
lifts, including at lattice points. The derivative series converges
locally uniformly, justifying differentiation before projecting to the
torus. Changing the lift is an exact lattice reindexing.

The majorants depend on Schwartz seminorms of the input kernel. This
does not give a cutoff-independent bound for a family of kernels.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusSchwartzLattice

open UnitTorusLattice UnitTorusPeriodization UnitTorusSeparatedLattice Set Filter
open scoped SchwartzMap Topology ContDiff
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Td" => UnitAddTorus (Fin d)
local notation "Lat" => LatticeSubmodule (ι := Fin d)

theorem finite_closedBall_lattice (R : ℝ) : (Metric.closedBall (0 : Lat) R).Finite := by
  have h := (ZSpan.setFinite_inter (standardBasis (ι := Fin d))
    (Metric.isBounded_closedBall (x := (0 : Rd)) (r := R))).preimage_embedding
      (.subtype (fun x : Rd ↦ x ∈ (LatticeSubmodule (ι := Fin d))))
  apply h.subset
  intro z hz
  constructor
  · change ‖(z : Rd) - 0‖ ≤ R
    simpa only [sub_zero, Metric.mem_closedBall, dist_zero_right, Submodule.coe_norm] using hz
  · exact z.property

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_uniform_norm_majorant (K : 𝓢(Rd, E)) (R : ℝ) :
    ∃ g : Lat → ℝ, (∀ z, 0 ≤ g z) ∧ Summable g ∧
      ∀ x : Rd, ‖x‖ ≤ R → ∀ z : Lat, ‖K ((z : Rd) + x)‖ ≤ g z := by
  classical
  let m := d + 1
  let C₀ := SchwartzMap.seminorm ℝ 0 0 K
  let Cₘ := SchwartzMap.seminorm ℝ m 0 K
  have hC₀ : 0 ≤ C₀ := apply_nonneg _ _
  have hCₘ : 0 ≤ Cₘ := apply_nonneg _ _
  have hdim : Module.finrank ℤ Lat = d := by
    simpa using Module.finrank_eq_card_basis (latticeBasis (ι := Fin d))
  have hs := ZLattice.summable_norm_pow_inv Lat m (by simp [hdim, m])
  let g : Lat → ℝ := fun z ↦
    (if z ∈ Metric.closedBall (0 : Lat) (2 * R) then C₀ else 0) + Cₘ * 2 ^ m * ‖z‖⁻¹ ^ m
  have hn : Summable (fun z : Lat ↦ if z ∈ Metric.closedBall (0 : Lat) (2 * R) then C₀ else 0) := by
    exact summable_of_ne_finset_zero (s := (finite_closedBall_lattice (d := d) (2 * R)).toFinset)
      (fun z hz ↦ by simp only [Finite.mem_toFinset] at hz; simp [hz])
  refine ⟨g, fun z ↦ by dsimp [g]; split_ifs <;> positivity,
    hn.add (hs.mul_left (Cₘ * 2 ^ m)), ?_⟩
  intro x hx z
  by_cases hz : z ∈ Metric.closedBall (0 : Lat) (2 * R)
  · exact (K.norm_le_seminorm ℝ _).trans (by
      dsimp [g]
      rw [if_pos hz]
      exact le_add_of_nonneg_right (by positivity))
  · have hz' : 2 * R < ‖z‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz
    have hzpos : 0 < ‖z‖ := by linarith [norm_nonneg x]
    have hnorm : ‖z‖ ≤ 2 * ‖(z : Rd) + x‖ := by
      have hn' : ‖z‖ ≤ ‖(z : Rd) + x‖ + ‖x‖ := by
        simpa only [add_sub_cancel_right, Submodule.coe_norm] using norm_sub_le ((z : Rd) + x) x
      linarith
    have hp : 0 < ‖(z : Rd) + x‖ := by linarith
    have hi : ‖(z : Rd) + x‖⁻¹ ≤ 2 * ‖z‖⁻¹ := by
      apply (inv_le_comm₀ hp (by positivity : 0 < (2 : ℝ) * ‖z‖⁻¹)).mpr
      simp only [mul_inv_rev, inv_inv]
      nlinarith
    have hk : ‖K ((z : Rd) + x)‖ ≤ Cₘ * ‖(z : Rd) + x‖⁻¹ ^ m := by
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hp _)]
      simpa only [mul_comm] using K.norm_pow_mul_le_seminorm ℝ m ((z : Rd) + x)
    have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi m) hCₘ
    exact hk.trans (by simpa only [g, if_neg hz, zero_add, mul_pow, mul_assoc] using hb)

def liftSum (K : Rd → E) (x : Rd) : E := ∑' z : Lat, K ((z : Rd) + x)

theorem summable_norm_translates (K : 𝓢(Rd, E)) (x : Rd) :
    Summable (fun z : Lat ↦ ‖K ((z : Rd) + x)‖) := by
  obtain ⟨g, _, hg, hb⟩ := exists_uniform_norm_majorant K ‖x‖
  exact hg.of_nonneg_of_le (fun z ↦ norm_nonneg _) (hb x le_rfl)

omit [NormedSpace ℝ E] in
theorem liftSum_eq_periodize (K : Rd → E) (x : Rd) :
    liftSum K x = periodize K (torusProjection x) := by
  let c : Lat := ⟨x - representative (torusProjection x),
    sub_mem_lattice_of_projection_eq (torusProjection_representative _).symm⟩
  have hx : x = (c : Rd) + representative (torusProjection x) := (sub_add_cancel _ _).symm
  change (∑' z : Lat, K ((z : Rd) + x)) = ∑' z : Lat, K ((z : Rd) + representative (torusProjection x))
  calc
    _ = ∑' z : Lat, K (((z + c : Lat) : Rd) + representative (torusProjection x)) := by
      apply tsum_congr
      intro z
      conv_lhs => rw [hx]
      congr 1
      simp only [Submodule.coe_add]
      abel
    _ = _ := by
      simpa only [Equiv.coe_addRight] using (Equiv.addRight c).tsum_eq
        (fun z : Lat ↦ K ((z : Rd) + representative (torusProjection x)))

omit [NormedSpace ℝ E] in
theorem liftSum_eq_of_projection_eq (K : Rd → E) {x y : Rd}
    (h : torusProjection x = torusProjection y) : liftSum K x = liftSum K y := by
  rw [liftSum_eq_periodize, liftSum_eq_periodize, h]

variable [CompleteSpace E]

theorem hasFDerivAt_liftSum (K : 𝓢(Rd, E)) (x : Rd) :
    HasFDerivAt (liftSum K) (liftSum (SchwartzMap.fderivCLM ℝ Rd E K) x) x := by
  let K' := SchwartzMap.fderivCLM ℝ Rd E K
  let R := ‖x‖ + 1
  obtain ⟨g, _, hg, hb⟩ := exists_uniform_norm_majorant K' R
  have hx : x ∈ Metric.ball (0 : Rd) R := by simp [R, Metric.mem_ball]
  have hf (z : Lat) (y : Rd) : HasFDerivAt (fun v : Rd ↦ K ((z : Rd) + v)) (K' ((z : Rd) + y)) y := by
    simpa only [K', SchwartzMap.fderivCLM_apply, Function.comp_def, ContinuousLinearMap.comp_id] using
      (K.hasFDerivAt ((z : Rd) + y)).comp y ((hasFDerivAt_id y).const_add (z : Rd))
  exact hasFDerivAt_tsum_of_isPreconnected hg Metric.isOpen_ball (convex_ball (0 : Rd) R).isPreconnected
    (fun z y _ ↦ hf z y)
    (fun z y hy ↦ hb y (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hy)) z)
    hx (summable_norm_translates K x).of_norm hx

theorem continuous_liftSum (K : 𝓢(Rd, E)) : Continuous (liftSum K) :=
  continuous_iff_continuousAt.mpr (fun x ↦ (hasFDerivAt_liftSum K x).continuousAt)

/-- Continuity descends through the product quotient, not through a chosen representative. -/
theorem continuous_periodize (K : 𝓢(Rd, E)) : Continuous (periodize K) := by
  have hq := IsOpenQuotientMap.piMap (fun _ : Fin d ↦
    (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ))))
  apply hq.continuous_comp_iff.mp
  let L := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toContinuousLinearEquiv
  have hc := (continuous_liftSum K).comp L.continuous
  have he (x : Fin d → ℝ) : torusProjection (L x) =
      Pi.map (fun _ : Fin d ↦ (QuotientAddGroup.mk : ℝ → UnitAddCircle)) x := rfl
  simpa only [Function.comp_def, liftSum_eq_periodize, he] using hc

theorem contDiff_one_liftSum (K : 𝓢(Rd, E)) : ContDiff ℝ 1 (liftSum K) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x ↦ (hasFDerivAt_liftSum K x).differentiableAt, ?_⟩
  have he : fderiv ℝ (liftSum K) = liftSum (SchwartzMap.fderivCLM ℝ Rd E K) :=
    funext (fun x ↦ (hasFDerivAt_liftSum K x).fderiv)
  rw [he]
  exact continuous_liftSum _

end Mettapedia.Analysis.UnitTorusSchwartzLattice
