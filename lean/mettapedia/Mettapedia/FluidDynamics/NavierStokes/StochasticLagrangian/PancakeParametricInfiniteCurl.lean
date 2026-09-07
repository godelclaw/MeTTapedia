import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFullNonlinearConsistency

/-!
# Continuity of the infinite nonlinear field with parameters

Uniform absolute summability and continuous coefficient coordinates give
joint continuity of the full curl series. The parameter space may be a
compact time interval, so no global-in-time envelope is required.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeParametricInfiniteCurl

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeDyadicDirectionEvolution PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy
open PancakeCurlOutputTail PancakeDiscardedNonlinearLimit PancakeInfinitePairReconstruction
open PancakeFullNonlinearConsistency PancakeZeroModeCurlBridge PancakeInteractionTruncationTail

local notation "T3" => UnitAddTorus (Fin 3)

variable {P : Type*} [TopologicalSpace P]

theorem continuous_parametric_curlPair (u : P → FourierVelocity)
    (hu : ∀ k i, Continuous (fun t ↦ u t k i)) (p : Wavevector × Wavevector) :
    Continuous (fun t ↦ curlPair (u t) (fourierCurl (u t)) p) := by
  have hk0 := hu p.1 0
  have hk1 := hu p.1 1
  have hk2 := hu p.1 2
  have hl0 := hu p.2 0
  have hl1 := hu p.2 1
  have hl2 := hu p.2 2
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [curlPair, fourierCurl, coefficientCross, Pi.smul_apply, smul_eq_mul] <;> fun_prop

theorem continuous_parametric_realCurlPairWave (u : P → FourierVelocity)
    (hu : ∀ k i, Continuous (fun t ↦ u t k i)) (p : Wavevector × Wavevector) :
    Continuous (fun z : P × T3 ↦ realPairWave (curlPair (u z.1) (fourierCurl (u z.1))) p z.2) :=
  complexRealPartEuclideanCLM.continuous.comp
    (((UnitAddTorus.mFourier (p.1 + p.2)).continuous.comp continuous_snd).smul
      ((continuous_parametric_curlPair u hu p).comp continuous_fst))

theorem continuous_parametric_fullCurlNonlinearity
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (u : P → FourierVelocity) (hu : ∀ k i, Continuous (fun t ↦ u t k i))
    (hbound : ∀ t k, fourierMoment 2 (u t) k ≤ g k) :
    Continuous (fun z : P × T3 ↦ fullCurlNonlinearity (u z.1) z.2) :=
  continuous_tsum (continuous_parametric_realCurlPairWave u hu)
    (summable_velocityCurlMajorant g hg hSum)
    (fun p z ↦ (norm_realPairWave_le _ p z.2).trans
      (norm_velocityCurlPair_le_envelope g hg (u z.1) (hbound z.1) p))

theorem continuous_parametric_retainedCurlNonlinearity
    (M : Finset Wavevector) (u : P → FourierVelocity)
    (hc : ∀ k i, Continuous (fun t ↦ u t k i))
    (hzero : ∀ t, u t 0 = 0) (hu : ∀ t k, k ∈ M → modeDot k (u t k) = 0) :
    Continuous (fun z : P × T3 ↦ retainedCurlNonlinearity M (u z.1) z.2) := by
  have he (z : P × T3) : retainedCurlNonlinearity M (u z.1) z.2 =
      ∑ p ∈ retainedPairs M, realPairWave (curlPair (u z.1) (fourierCurl (u z.1))) p z.2 := by
    unfold retainedCurlNonlinearity
    rw [nonlinearVorticityCoeff_eq_curl_meanZero M (u z.1) (hzero z.1) (hu z.1), ← pairOutputCoeff_curlPair,
      finite_reconstruction_eq_retainedPairSum]
  simp_rw [he]
  exact continuous_finsetSum _ (fun p _ ↦ continuous_parametric_realCurlPairWave u hc p)

theorem continuous_parametric_fullNonlinearError
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (M : Finset Wavevector) (u : P → FourierVelocity)
    (hc : ∀ k i, Continuous (fun t ↦ u t k i))
    (hzero : ∀ t, u t 0 = 0) (hu : ∀ t k, k ∈ M → modeDot k (u t k) = 0)
    (hbound : ∀ t k, fourierMoment 2 (u t) k ≤ g k) :
    Continuous (fun z : P × T3 ↦ fullNonlinearError M (u z.1) z.2) :=
  (continuous_parametric_fullCurlNonlinearity g hg hSum u hc hbound).sub
    (continuous_parametric_retainedCurlNonlinearity M u hc hzero hu)

end Mettapedia.FluidDynamics.NavierStokes.PancakeParametricInfiniteCurl
