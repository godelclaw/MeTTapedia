import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationLattice
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# Navier-Stokes: Schwartz Periodization Series

Semantic layer split from `NavierStokesSchwartzPeriodizationConvergence`.
-/


set_option autoImplicit false

noncomputable section

open Filter

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped BigOperators

/-- Explicit order-4 Schwartz bound on the norm of a vector-valued initial datum. -/
theorem schwartz_norm_le_orderFour
    (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    ‖u₀ x‖ ≤
      ((2 : ℝ) ^ (4 : ℕ) *
        (Finset.Iic (4, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) u₀) /
        (1 + ‖x‖) ^ 4 := by
  refine (le_div_iff₀ (by positivity)).2 ?_
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (SchwartzMap.one_add_le_sup_seminorm_apply
      (m := (4, 0)) (k := 4) (n := 0) le_rfl le_rfl u₀ x)

/-- The uniform order-4 Schwartz seminorm constant used in the local
periodization estimates. -/
noncomputable def schwartzOrderFourConstant (u₀ : NSSchwartzInitialVelocity) : ℝ :=
  (2 : ℝ) ^ (4 : ℕ) *
    (Finset.Iic (4, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) u₀

theorem schwartzOrderFourConstant_nonneg (u₀ : NSSchwartzInitialVelocity) :
    0 ≤ schwartzOrderFourConstant u₀ := by
  dsimp [schwartzOrderFourConstant]
  positivity

/-- Recenter `x + c z` as a scaled translate of `z` when `c ≠ 0`. -/
theorem add_periodizationScale_eq_smul_sub
    {c : ℝ} (hc : c ≠ 0) (x z : NSSpace) :
    x + c • z = c • (z - (-(c⁻¹) • x)) := by
  calc
    x + c • z = c • (c⁻¹ • x) + c • z := by simp [hc, smul_smul]
    _ = c • (c⁻¹ • x + z) := by rw [smul_add]
    _ = c • (z + c⁻¹ • x) := by rw [add_comm]
    _ = c • (z - (-(c⁻¹) • x)) := by simp [sub_eq_add_neg]

/-- Only finitely many standard lattice points can lie in a fixed closed ball. -/
theorem finite_nsCoordinateLatticePoints_mem_closedBall
    (y : NSSpace) (r : ℝ) :
    Set.Finite {z : NSCoordinateLattice | ‖(z : NSSpace) - y‖ ≤ r} := by
  convert
    (ZSpan.setFinite_inter (b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
      (s := Metric.closedBall y r)
      (hs := Metric.isBounded_closedBall)).preimage_embedding (.subtype _)
  ext z
  constructor
  · intro hz
    exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hz, z.property⟩
  · intro hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz.1

/-- Off the small exceptional ball around `-(c⁻¹) • x`, a Schwartz translate is
dominated by the rank-3 lattice `‖·‖^{-4}` majorant needed for comparison. -/
theorem norm_schwartz_periodized_term_le_latticeDecay
    {c : ℝ} (hc : c ≠ 0) (u₀ : NSSchwartzInitialVelocity) (x : NSSpace)
    (z : NSCoordinateLattice)
    (hz :
      ‖(z : NSSpace) - (-(c⁻¹) • x)‖ > ‖c‖⁻¹) :
    ‖u₀ (x + c • (z : NSSpace))‖ ≤
      (schwartzOrderFourConstant u₀ * ‖c‖ ^ (-4 : ℤ)) *
        ‖(z : NSSpace) - (-(c⁻¹) • x)‖ ^ (-4 : ℤ) := by
  let y : NSSpace := -(c⁻¹) • x
  let C : ℝ := schwartzOrderFourConstant u₀
  have hCnonneg : 0 ≤ C := schwartzOrderFourConstant_nonneg u₀
  have hcnorm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hznorm_pos : 0 < ‖(z : NSSpace) - y‖ := by
    have hcinv_pos : 0 < ‖c‖⁻¹ := by positivity
    linarith
  have hznorm : ‖(z : NSSpace) - y‖ ≠ 0 := ne_of_gt hznorm_pos
  have hv :
      x + c • (z : NSSpace) =
        c • ((z : NSSpace) - y) := by
    simpa [y] using add_periodizationScale_eq_smul_sub hc x (z : NSSpace)
  have hnormv :
      ‖x + c • (z : NSSpace)‖ = ‖c‖ * ‖(z : NSSpace) - y‖ := by
    rw [hv, norm_smul]
  have hvnorm_pos : 0 < ‖x + c • (z : NSSpace)‖ := by
    rw [hnormv]
    positivity
  have hvnorm : ‖x + c • (z : NSSpace)‖ ≠ 0 := ne_of_gt hvnorm_pos
  have hdiv :
      ‖u₀ (x + c • (z : NSSpace))‖ ≤
        C / ‖x + c • (z : NSSpace)‖ ^ 4 := by
    have hbase :
        ‖u₀ (x + c • (z : NSSpace))‖ ≤
          C / (1 + ‖x + c • (z : NSSpace)‖) ^ 4 := by
      simpa [C, schwartzOrderFourConstant] using
        schwartz_norm_le_orderFour u₀ (x + c • (z : NSSpace))
    have hpow :
        ‖x + c • (z : NSSpace)‖ ^ 4 ≤
          (1 + ‖x + c • (z : NSSpace)‖) ^ 4 := by
      gcongr
      linarith
    exact hbase.trans <|
      div_le_div_of_nonneg_left hCnonneg (by positivity) hpow
  have hmajor :
      C / ‖x + c • (z : NSSpace)‖ ^ 4 =
        (C * ‖c‖ ^ (-4 : ℤ)) *
          ‖(z : NSSpace) - y‖ ^ (-4 : ℤ) := by
    rw [hnormv]
    rw [zpow_neg, zpow_neg]
    field_simp [hznorm, norm_ne_zero_iff.mpr hc]
  exact hdiv.trans_eq hmajor

/-- The rank-3 order-4 majorant used to control the Schwartz periodization terms
is summable on the coordinate lattice. -/
theorem summable_schwartz_coordinateLatticeMajorant
    {c : ℝ} (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    Summable
      (fun z : NSCoordinateLattice =>
        (schwartzOrderFourConstant u₀ * ‖c‖ ^ (-4 : ℤ)) *
          ‖(z : NSSpace) - (-(c⁻¹) • x)‖ ^ (-4 : ℤ)) := by
  have hdim : Module.finrank ℤ NSCoordinateLattice = 3 := by
    rw [Module.finrank_eq_card_basis nsCoordinateLatticeBasis]
    norm_num
  have hzpow :
      (-4 : ℤ) < -Module.finrank ℤ NSCoordinateLattice := by
    rw [hdim]
    norm_num
  simpa using
    (ZLattice.summable_norm_sub_zpow (L := NSCoordinateLattice) (-4) hzpow (-(c⁻¹) • x)).mul_left
      (schwartzOrderFourConstant u₀ * ‖c‖ ^ (-4 : ℤ))

/-- The translated Schwartz periodization terms are summable on the coordinate
lattice when the scale parameter is nonzero. -/
theorem summable_schwartz_coordinateLatticeSeries
    {c : ℝ} (hc : c ≠ 0) (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    Summable (fun z : NSCoordinateLattice => u₀ (x + c • (z : NSSpace))) := by
  let y : NSSpace := -(c⁻¹) • x
  have hsumLat := summable_schwartz_coordinateLatticeMajorant (c := c) u₀ x
  have hfiniteBad :
      Set.Finite {z : NSCoordinateLattice | ‖(z : NSSpace) - y‖ ≤ ‖c‖⁻¹} :=
    finite_nsCoordinateLatticePoints_mem_closedBall y (‖c‖⁻¹)
  refine Summable.of_norm_bounded_eventually hsumLat ?_
  filter_upwards [hfiniteBad.eventually_cofinite_notMem] with z hz
  have hzfar :
      ‖((z : NSCoordinateLattice) : NSSpace) - y‖ > ‖c‖⁻¹ := by
    have : ¬ ‖((z : NSCoordinateLattice) : NSSpace) - y‖ ≤ ‖c‖⁻¹ := by
      simpa using hz
    linarith
  simpa [y] using norm_schwartz_periodized_term_le_latticeDecay hc u₀ x z hzfar

/-- The formal infinite Schwartz periodization candidate associated to a lattice
period `2πL`. The substantive convergence theorem below shows this `tsum`
agrees with the boxed partial periodization limit on each fixed cube once
`L ≠ 0`. -/
noncomputable def schwartzPeriodizedInitialVelocity
    (L : ℝ) (u₀ : NSSchwartzInitialVelocity) :
    NSInitialVelocity :=
  fun x => ∑' n : NSLatticeIndex, u₀ (x + periodizationShift L n)

set_option maxHeartbeats 800000 in
/-- For nonzero period parameter `L`, the Schwartz lattice series is summable at
each fixed spatial point. -/
theorem summable_schwartzPeriodizedInitialVelocity
    {L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    Summable (fun n : NSLatticeIndex => u₀ (x + periodizationShift L n)) := by
  let c : ℝ := 2 * Real.pi * L
  have hc : c ≠ 0 := by
    refine mul_ne_zero ?_ hL
    positivity
  have hsumLatValue :
      Summable
        (fun z : NSCoordinateLattice =>
          u₀ (x + c • ((z : NSCoordinateLattice) : NSSpace))) :=
    summable_schwartz_coordinateLatticeSeries hc u₀ x
  have hsumIndex :
      Summable
        (fun n : NSLatticeIndex =>
          u₀ (x + c • ((nsCoordinateLatticePoint n : NSCoordinateLattice) : NSSpace))) := by
    have hsumIndex' :
        Summable
          (fun n : NSLatticeIndex =>
            u₀ (x + c • ((nsCoordinateLatticePointEquiv n : NSCoordinateLattice) : NSSpace))) :=
      nsCoordinateLatticePointEquiv.summable_iff.mpr hsumLatValue
    exact hsumIndex'.congr fun n => by rfl
  have hseriesEq :
      (fun n : NSLatticeIndex => u₀ (x + periodizationShift L n)) =
        (fun n : NSLatticeIndex =>
          u₀ (x + c • ((nsCoordinateLatticePoint n : NSCoordinateLattice) : NSSpace))) := by
    ext n
    simp [c, periodizationShift_eq_smul_nsCoordinateLatticePoint]
  exact hseriesEq.symm ▸ hsumIndex

/-- The `tsum` used in `schwartzPeriodizedInitialVelocity` is the actual sum of
the boxed periodization terms at each point once `L ≠ 0`. -/
theorem hasSum_schwartzPeriodizedInitialVelocity
    {L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    HasSum (fun n : NSLatticeIndex => u₀ (x + periodizationShift L n))
      (schwartzPeriodizedInitialVelocity L u₀ x) :=
  (summable_schwartzPeriodizedInitialVelocity hL u₀ x).hasSum

/-- The infinite Schwartz periodization is invariant under its period lattice
shifts. This is the concrete periodicity property needed for the large-torus
exhaustion route. -/
theorem schwartzPeriodizedInitialVelocity_add_periodizationShift
    (L : ℝ) (u₀ : NSSchwartzInitialVelocity) (k : NSLatticeIndex) (x : NSSpace) :
    schwartzPeriodizedInitialVelocity L u₀ (x + periodizationShift L k) =
      schwartzPeriodizedInitialVelocity L u₀ x := by
  unfold schwartzPeriodizedInitialVelocity
  calc
    (∑' n : NSLatticeIndex, u₀ (x + periodizationShift L k + periodizationShift L n))
        = ∑' n : NSLatticeIndex, u₀ (x + periodizationShift L (k + n)) := by
          apply tsum_congr
          intro n
          congr 1
          simp [periodizationShift_add, add_assoc]
    _ = ∑' n : NSLatticeIndex, u₀ (x + periodizationShift L n) := by
          simpa using
            (Equiv.tsum_eq (Equiv.addLeft k)
              (fun n : NSLatticeIndex => u₀ (x + periodizationShift L n)))

end NavierStokes
end FluidDynamics
end Mettapedia
