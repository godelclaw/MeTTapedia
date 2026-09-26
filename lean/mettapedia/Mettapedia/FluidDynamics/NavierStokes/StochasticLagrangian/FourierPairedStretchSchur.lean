import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPairedStretchIdentity

/-!
# From a paired angular kernel to a Fourier energy bound

For any nonnegative output weight `w`, the paired stretching kernel is
`w(p+r) sin(angle(p,r))`. Its symmetry turns a single row-sum bound into both
hypotheses of the existing finite Schur estimate. Consequently the weighted
sum of the actual stretching output coefficients is bounded by half the row
constant times the vorticity energy of the input modes.

The estimate has no cardinality factor and retains each pair's relative angle.
Proving a uniform row bound for a specified cone or collection of cones is a
separate geometric obligation. No time-integrated budget is assumed to follow.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPairedStretchSchur

open scoped BigOperators
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
  FourierRelaxation FourierTriadSineLaw FourierPancakePairDepletion FourierPairedStretchIdentity

/-- Summing selected convolution outputs uses each ordered input pair at most once. -/
theorem sum_output_pairs_le (P K : Finset Wavevector) (A : Wavevector → Wavevector → ℝ)
    (hA : ∀ p r, 0 ≤ A p r) :
    (∑ k ∈ K, ∑ p ∈ P.filter (fun p ↦ k - p ∈ P), A p (k - p)) ≤
      ∑ p ∈ P, ∑ r ∈ P, A p r := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun p _ ↦ ?_
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_injOn (fun k ↦ k - p)
  · intro k _ l _ h
    exact sub_left_injective h
  · intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    exact (Finset.mem_filter.mp hk).2
  · intro k _
    exact le_rfl
  · intro r _ _
    exact hA p r

/-- Output weight times the paired angular depletion. -/
def angularKernel (w : Wavevector → ℝ) (p r : Wavevector) : ℝ :=
  w (p + r) * sine p r

theorem angularKernel_comm (w : Wavevector → ℝ) (p r : Wavevector) :
    angularKernel w p r = angularKernel w r p := by
  rw [angularKernel, angularKernel, add_comm p r, sine_comm]

theorem angularKernel_nonneg (w : Wavevector → ℝ) (hw : ∀ k, 0 ≤ w k)
    (p r : Wavevector) : 0 ≤ angularKernel w p r :=
  mul_nonneg (hw _) (sine_nonneg _ _)

/-- A geometric row bound gives an actual weighted stretching bound by vorticity energy. -/
theorem weighted_stretch_le_of_schur (u : FourierVelocity) (P K : Finset Wavevector)
    (hP0 : (0 : Wavevector) ∉ P) (w : Wavevector → ℝ) (hw : ∀ k, 0 ≤ w k)
    (C : ℝ) (hrow : ∀ p ∈ P, ∑ r ∈ P, angularKernel w p r ≤ C) :
    (∑ k ∈ K, w k * ‖coefficientVec (pancakeStretch u P k)‖) ≤
      (C / 2) * ∑ p ∈ P, coefficientEnergy (fourierCurl u p) := by
  let A := fun p r ↦ angularKernel w p r * curlMass u p * curlMass u r
  have hA : ∀ p r, 0 ≤ A p r := fun p r ↦
    mul_nonneg (mul_nonneg (angularKernel_nonneg w hw p r) (curlMass_nonneg u p))
      (curlMass_nonneg u r)
  have hcol : ∀ r ∈ P, ∑ p ∈ P, angularKernel w p r ≤ C := by
    intro r hr
    simpa only [angularKernel_comm w _ r] using hrow r hr
  have hs := finite_schur_energy_bound P (angularKernel w) (curlMass u) C
    (angularKernel_nonneg w hw) hrow hcol
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ k ∈ K, ∑ p ∈ P.filter (fun p ↦ k - p ∈ P), A p (k - p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ ↦ ?_
      refine (mul_le_mul_of_nonneg_left (norm_pancakeStretch_le_weighted u P hP0 k)
        (hw k)).trans_eq ?_
      rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      simp only [A, angularKernel, show p + (k - p) = k from by abel]
      ring
    _ ≤ (1 / 2 : ℝ) * ∑ p ∈ P, ∑ r ∈ P, A p r :=
      mul_le_mul_of_nonneg_left (sum_output_pairs_le P K A hA) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (C * ∑ p ∈ P, curlMass u p ^ 2) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by
      simp only [curlMass, norm_coefficientVec_sq]
      ring

end Mettapedia.FluidDynamics.NavierStokes.FourierPairedStretchSchur
