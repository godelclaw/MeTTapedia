import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCurlOutputTail
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeZeroModeCurlBridge

/-!
# Uniform disappearance of the actual discarded nonlinear field

A summable envelope of second absolute Fourier moments makes the actual
discarded mean-zero incompressible vorticity nonlinearity uniformly small.
The finite core is common to every coefficient field under that envelope.
Obtaining such an envelope on an interval is a separate smoothness task;
it is not an arbitrary-data a priori estimate or a Galerkin existence result.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeDiscardedNonlinearLimit

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeDyadicDirectionEvolution
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeZeroModeCurlBridge PancakeRetainedProjectionDefect PancakeTransverseEnergyFreezing
open PancakeSummableOutputTail PancakeExteriorReconstructionTail

local notation "T3" => UnitAddTorus (Fin 3)

def velocityCurlMajorant (g : Wavevector → ℝ) (p : Wavevector × Wavevector) : ℝ :=
  (2 * Real.pi) ^ 2 * (g p.1 * g p.2)

theorem velocityCurlMajorant_nonneg (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (p : Wavevector × Wavevector) : 0 ≤ velocityCurlMajorant g p :=
  mul_nonneg (sq_nonneg _) (mul_nonneg (hg _) (hg _))

theorem summable_velocityCurlMajorant (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) : Summable (velocityCurlMajorant g) :=
  (hSum.mul_of_nonneg hSum hg hg).mul_left ((2 * Real.pi) ^ 2)

theorem norm_velocityCurlPair_le_envelope (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (u : FourierVelocity) (hu : ∀ k, fourierMoment 2 u k ≤ g k) (p : Wavevector × Wavevector) :
    ‖coefficientVec (curlPair u (fourierCurl u) p)‖ ≤ velocityCurlMajorant g p := by
  have h1 := (firstMoment_le_second u p.1).trans (hu p.1)
  have h2 := (firstMoment_curl_le_second u p.2).trans
    (mul_le_mul_of_nonneg_left (hu p.2) (show 0 ≤ 2 * Real.pi by positivity))
  apply (norm_curlPair_le u (fourierCurl u) p).trans
  unfold curlMajorant velocityCurlMajorant
  calc
    _ ≤ (2 * Real.pi) * (g p.1 * ((2 * Real.pi) * g p.2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (fourierMoment_nonneg _ _ _) (hg _)) (by positivity)
    _ = _ := by ring

theorem norm_discardedNonlinearField_le_tail (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hzero : u 0 = 0) (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hbound : ∀ k, fourierMoment 2 u k ≤ g k) (x : T3) :
    ‖discardedNonlinearField modes outputs u x‖ ≤ outputTail (velocityCurlMajorant g) modes := by
  unfold discardedNonlinearField
  rw [nonlinearVorticityCoeff_eq_curl_meanZero modes u hzero hu, ← pairOutputCoeff_curlPair]
  exact norm_exterior_reconstruction_le_outputTail modes outputs _ _ _ (velocityCurlMajorant_nonneg g hg)
    (summable_velocityCurlMajorant g hg hSum) (fun p _ ↦ norm_velocityCurlPair_le_envelope g hg u hbound p) x

theorem exists_uniform_discardedNonlinearField_lt (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ core : Finset Wavevector, ∀ modes : Finset Wavevector, core ⊆ modes →
      ∀ (outputs : Finset Wavevector) (u : FourierVelocity), u 0 = 0 →
        (∀ k ∈ modes, modeDot k (u k) = 0) → (∀ k, fourierMoment 2 u k ≤ g k) →
        ∀ x : T3, ‖discardedNonlinearField modes outputs u x‖ < epsilon := by
  obtain ⟨core, hc⟩ := exists_outputTail_lt (velocityCurlMajorant g) (velocityCurlMajorant_nonneg g hg)
    (summable_velocityCurlMajorant g hg hSum) epsilon hepsilon
  exact ⟨core, fun modes hm outputs u hz hu hb x ↦
    (norm_discardedNonlinearField_le_tail g hg hSum modes outputs u hz hu hb x).trans_lt (hc modes hm)⟩

theorem exists_discardedNonlinearField_lt_of_secondMoment (u : FourierVelocity)
    (hu : ∀ k, modeDot k (u k) = 0) (hzero : u 0 = 0) (hSum : Summable (fourierMoment 2 u))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ core : Finset Wavevector, ∀ modes : Finset Wavevector, core ⊆ modes →
      ∀ (outputs : Finset Wavevector) (x : T3), ‖discardedNonlinearField modes outputs u x‖ < epsilon := by
  obtain ⟨core, hc⟩ := exists_uniform_discardedNonlinearField_lt (fourierMoment 2 u)
    (fourierMoment_nonneg _ _) hSum epsilon hepsilon
  exact ⟨core, fun modes hm outputs x ↦ hc modes hm outputs u hzero (fun k _ ↦ hu k) (fun _ ↦ le_refl _) x⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeDiscardedNonlinearLimit
