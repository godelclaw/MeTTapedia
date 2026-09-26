import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPairedStretchSchur
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierTubeKernel

/-!
# Uniform paired stretching in one pancake cone

At shell radius `N²`, a cone of aperture `1/N` lies in a tube of width `2N`.
The sum of two such modes lies in a tube of width `4N`. Combining the paired
sine bound, the arbitrary-axis tube kernel and the finite Schur theorem gives
a scale-independent bound by the input vorticity energy.

The cone is specified by a real axial coefficient and a small Euclidean
remainder. All complex Fourier phases of the velocity remain unrestricted.
The theorem controls the stretching contribution at a fixed time; transport,
multiple cones and evolution of the geometry are separate obligations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierSingleConeStretch

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicComplexStretch PancakePeriodicCoherentSplit
  PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy FourierPancakePairDepletion
  FourierVorticitySource FourierTriadSineLaw FourierPairedStretchIdentity
  FourierPairedStretchSchur FourierShearedLatticeCount FourierTubeKernel
  PancakeInfinitePressureCoefficients

/-- A real axis viewed in the actual complex Fourier coefficient space. -/
def axisCoefficient (n : Fin 3 → ℝ) : VelocityCoefficient := fun i ↦ (n i : ℂ)

/-- A shell mode in a double cone of aperture `1/N`, described by an axial remainder. -/
def InConeShell (N : ℕ) (n : Fin 3 → ℝ) (k : Wavevector) : Prop :=
  (N : ℝ) ^ 2 ≤ ‖frequencyVec k‖ ∧ ‖frequencyVec k‖ ≤ 2 * (N : ℝ) ^ 2 ∧
    ∃ t : ℝ, |t| ≤ ‖frequencyVec k‖ ∧
      ‖coefficientVec (wavevectorCoefficient k - (t : ℂ) • axisCoefficient n)‖ ≤
        ‖frequencyVec k‖ / N

theorem InConeShell.inTube {N : ℕ} (hN : 0 < N) {n : Fin 3 → ℝ} {k : Wavevector}
    (hk : InConeShell N n k) : InTube n (2 * N : ℕ) k := by
  obtain ⟨_, hupper, t, _, herr⟩ := hk
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have herr' : ‖coefficientVec (wavevectorCoefficient k - (t : ℂ) • axisCoefficient n)‖ ≤
      2 * N := by
    refine herr.trans ?_
    rw [div_le_iff₀ hN']
    nlinarith [hupper]
  refine ⟨t, fun i ↦ ?_⟩
  have hi := (norm_coefficient_apply_le
    (wavevectorCoefficient k - (t : ℂ) • axisCoefficient n) i).trans herr'
  have he : (wavevectorCoefficient k - (t : ℂ) • axisCoefficient n) i =
      (((k i : ℝ) - t * n i : ℝ) : ℂ) := by
    simp [wavevectorCoefficient, axisCoefficient]
  rw [he] at hi
  simpa only [Complex.norm_real, Real.norm_eq_abs, Nat.cast_mul, Nat.cast_ofNat] using hi

/-- Algebraic decomposition of a cross product relative to an arbitrary axis. -/
theorem cross_axis_decomposition (a b n : VelocityCoefficient) (t s : ℂ) :
    coefficientCross a b = t • coefficientCross n (b - s • n) +
      coefficientCross (a - t • n) b := by
  ext i
  fin_cases i <;> simp [coefficientCross] <;> ring

/-- The cone angle bound includes both signs of the axis and arbitrary real axes. -/
theorem sine_le_of_cone {N : ℕ} (hN : 0 < N) {n : Fin 3 → ℝ}
    (hn : ‖coefficientVec (axisCoefficient n)‖ = 1)
    {p r : Wavevector} (hp : p ≠ 0) (hr : r ≠ 0)
    (hpc : InConeShell N n p) (hrc : InConeShell N n r) :
    sine p r ≤ 2 / (N : ℝ) := by
  obtain ⟨_, _, t, ht, hep⟩ := hpc
  obtain ⟨_, _, s, _, her⟩ := hrc
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : 0 < ‖frequencyVec p‖ := lt_of_lt_of_le zero_lt_one (one_le_norm_frequencyVec hp)
  have hr0 : 0 < ‖frequencyVec r‖ := lt_of_lt_of_le zero_lt_one (one_le_norm_frequencyVec hr)
  unfold sine
  rw [div_le_iff₀ (mul_pos hp0 hr0)]
  change ‖coefficientVec (wavevectorCoefficient (wavevectorCross p r))‖ ≤ _
  rw [wavevectorCoefficient_cross,
    cross_axis_decomposition (wavevectorCoefficient p) (wavevectorCoefficient r)
      (axisCoefficient n) (t : ℂ) (s : ℂ)]
  calc
    _ ≤ ‖coefficientVec ((t : ℂ) • coefficientCross (axisCoefficient n)
        (wavevectorCoefficient r - (s : ℂ) • axisCoefficient n))‖ +
        ‖coefficientVec (coefficientCross
          (wavevectorCoefficient p - (t : ℂ) • axisCoefficient n) (wavevectorCoefficient r))‖ :=
      norm_cv_add_le _ _
    _ ≤ |t| * (‖coefficientVec (axisCoefficient n)‖ *
        ‖coefficientVec (wavevectorCoefficient r - (s : ℂ) • axisCoefficient n)‖) +
        ‖coefficientVec (wavevectorCoefficient p - (t : ℂ) • axisCoefficient n)‖ *
          ‖frequencyVec r‖ := by
      rw [norm_cv_smul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (norm_coefficientCross_le _ _) (abs_nonneg _))
        (norm_coefficientCross_le _ _)
    _ ≤ ‖frequencyVec p‖ * (1 * (‖frequencyVec r‖ / N)) +
        (‖frequencyVec p‖ / N) * ‖frequencyVec r‖ := by
      rw [hn]
      gcongr
    _ = _ := by ring

/-- Each row of the inverse-square paired kernel is bounded independently of the shell and axis. -/
theorem cone_row_le (P : Finset Wavevector) (N : ℕ) (hN : 0 < N)
    (n : Fin 3 → ℝ) (hn : ‖coefficientVec (axisCoefficient n)‖ = 1)
    (hP0 : (0 : Wavevector) ∉ P) (hP : ∀ k ∈ P, InConeShell N n k)
    (p : Wavevector) (hp : p ∈ P) :
    ∑ r ∈ P, angularKernel (fun k ↦ 1 / ‖frequencyVec k‖ ^ 2) p r ≤ 1200 := by
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    have he : coefficientVec (axisCoefficient 0) = 0 := by
      ext i
      simp [coefficientVec, axisCoefficient]
    rw [he, norm_zero] at hn
    norm_num at hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hTube : ∀ q ∈ P.image (fun r ↦ p + r), InTube n (4 * N : ℕ) q := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    have h := (InConeShell.inTube hN (hP p hp)).add (InConeShell.inTube hN (hP r hr))
    convert h using 1
    push_cast
    ring
  have hsum := sum_inv_sq_tube_le_with_zero (P.image fun r ↦ p + r) n hn0 (4 * N)
    (by omega) hTube
  rw [Finset.sum_image (fun r _ s _ hrs ↦ add_left_cancel hrs)] at hsum
  calc
    _ ≤ ∑ r ∈ P, (2 / (N : ℝ)) * (1 / ‖frequencyVec (p + r)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [angularKernel, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (sine_le_of_cone hN hn (fun h ↦ hP0 (h ▸ hp)) (fun h ↦ hP0 (h ▸ hr))
          (hP p hp) (hP r hr)) (by positivity)
    _ = (2 / (N : ℝ)) * ∑ r ∈ P, 1 / ‖frequencyVec (p + r)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (2 / (N : ℝ)) * (150 * (4 * N : ℕ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1200 := by push_cast; field_simp; ring

/-- Actual paired stretching of a cone shell is bounded by its input vorticity energy. -/
theorem weighted_stretch_le_energy (u : FourierVelocity) (P K : Finset Wavevector)
    (N : ℕ) (hN : 0 < N) (n : Fin 3 → ℝ)
    (hn : ‖coefficientVec (axisCoefficient n)‖ = 1)
    (hP0 : (0 : Wavevector) ∉ P) (hP : ∀ k ∈ P, InConeShell N n k) :
    (∑ k ∈ K, (1 / ‖frequencyVec k‖ ^ 2) * ‖coefficientVec (pancakeStretch u P k)‖) ≤
      600 * ∑ p ∈ P, coefficientEnergy (fourierCurl u p) := by
  have h := weighted_stretch_le_of_schur u P K hP0 (fun k ↦ 1 / ‖frequencyVec k‖ ^ 2)
    (fun _ ↦ by positivity) 1200 (cone_row_le P N hN n hn hP0 hP)
  norm_num at h ⊢
  exact h

end Mettapedia.FluidDynamics.NavierStokes.FourierSingleConeStretch
