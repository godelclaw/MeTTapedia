import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierSlabKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPairedStretchIdentity

/-!
# A uniform output-gain kernel for Fourier belts

Modes at radius `N²` in a belt of angular width `1/N` have sums in a slab of
width `4N` and radius `4N²`. An output-frequency gain converts the inverse-square
weight to an inverse-radius sum. Multiplying by the belt width gives a uniform
row bound.

This theorem is geometric. A belt alone does not supply the factor `1/N` in
the stretching symbol: the velocity polarization must also be controlled.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierBeltKernel

open scoped BigOperators
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator PancakeCurlOutputTail
  PancakeInfinitePressureCoefficients FourierAgmon FourierTubeKernel FourierSlabKernel

/-- A shell mode in an angular belt about the plane perpendicular to a real normal. -/
def InBeltShell (N : ℕ) (n : Fin 3 → ℝ) (k : Wavevector) : Prop :=
  (N : ℝ) ^ 2 ≤ ‖frequencyVec k‖ ∧ ‖frequencyVec k‖ ≤ 2 * (N : ℝ) ^ 2 ∧
    InSlab n (‖frequencyVec k‖ / N) k

theorem InBeltShell.inSlab {N : ℕ} (hN : 0 < N) {n : Fin 3 → ℝ} {k : Wavevector}
    (hk : InBeltShell N n k) : InSlab n (2 * N : ℕ) k := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine hk.2.2.trans ?_
  rw [div_le_iff₀ hN']
  push_cast
  nlinarith [hk.2.1]

/-- The inverse-square kernel with both angular width and output-frequency gain. -/
def beltKernel (N : ℕ) (p r : Wavevector) : ℝ :=
  (1 / (N : ℝ)) *
    (‖frequencyVec (p + r)‖ / max ‖frequencyVec p‖ ‖frequencyVec r‖) *
      (1 / ‖frequencyVec (p + r)‖ ^ 2)

theorem beltKernel_comm (N : ℕ) (p r : Wavevector) : beltKernel N p r = beltKernel N r p := by
  simp only [beltKernel, add_comm p r, max_comm]

theorem beltKernel_nonneg (N : ℕ) (p r : Wavevector) : 0 ≤ beltKernel N p r := by
  unfold beltKernel
  positivity

theorem beltKernel_le_inv_radius {N : ℕ} (hN : 0 < N) {p r : Wavevector}
    (hp : (N : ℝ) ^ 2 ≤ ‖frequencyVec p‖) :
    beltKernel N p r ≤ (1 / (N : ℝ) ^ 3) * (1 / ‖frequencyVec (p + r)‖) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmax : (N : ℝ) ^ 2 ≤ max ‖frequencyVec p‖ ‖frequencyVec r‖ := hp.trans (le_max_left _ _)
  by_cases hz : ‖frequencyVec (p + r)‖ = 0
  · simp [beltKernel, hz]
  have hq : 0 < ‖frequencyVec (p + r)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  calc
    beltKernel N p r ≤ (1 / (N : ℝ)) *
        (‖frequencyVec (p + r)‖ / (N : ℝ) ^ 2) * (1 / ‖frequencyVec (p + r)‖ ^ 2) := by
      unfold beltKernel
      gcongr
    _ = _ := by field_simp

/-- A belt kernel row is uniform in the frequency and the real axis. -/
theorem belt_row_le (P : Finset Wavevector) (N : ℕ) (hN : 0 < N)
    (n : Fin 3 → ℝ) (hn : ∑ i : Fin 3, (n i) ^ 2 = 1)
    (hP : ∀ k ∈ P, InBeltShell N n k) (p : Wavevector) (hp : p ∈ P) :
    ∑ r ∈ P, beltKernel N p r ≤ 864 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hslab : ∀ q ∈ P.image (fun r ↦ p + r), InSlab n (4 * N : ℕ) q := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    have h := (InBeltShell.inSlab hN (hP p hp)).add (InBeltShell.inSlab hN (hP r hr))
    convert h using 1
    push_cast
    ring
  have hrad : ∀ q ∈ P.image (fun r ↦ p + r), supRadius q ≤ 4 * N ^ 2 := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    have h : (supRadius (p + r) : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
      calc
        _ ≤ ‖frequencyVec (p + r)‖ := supRadius_le_norm _
        _ ≤ ‖frequencyVec p‖ + ‖frequencyVec r‖ := by
          rw [frequencyVec_add]
          exact norm_add_le _ _
        _ ≤ _ := by linarith [(hP p hp).2.1, (hP r hr).2.1]
    exact_mod_cast h
  have hsum := sum_inv_radius_slab_le_with_zero (P.image fun r ↦ p + r) n hn
    (4 * N) (4 * N ^ 2) (by positivity) (by positivity) hrad hslab
  rw [Finset.sum_image (fun r _ s _ hrs ↦ add_left_cancel hrs)] at hsum
  calc
    _ ≤ ∑ r ∈ P, (1 / (N : ℝ) ^ 3) * (1 / ‖frequencyVec (p + r)‖) :=
      Finset.sum_le_sum fun r _ ↦ beltKernel_le_inv_radius hN (hP p hp).1
    _ = (1 / (N : ℝ) ^ 3) * ∑ r ∈ P, 1 / ‖frequencyVec (p + r)‖ := by rw [Finset.mul_sum]
    _ ≤ (1 / (N : ℝ) ^ 3) * (54 * (4 * N : ℕ) * (4 * N ^ 2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 864 := by push_cast; field_simp; ring

end Mettapedia.FluidDynamics.NavierStokes.FourierBeltKernel
