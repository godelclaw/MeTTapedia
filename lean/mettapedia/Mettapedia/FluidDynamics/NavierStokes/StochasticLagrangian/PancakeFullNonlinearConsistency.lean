import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfinitePairReconstruction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeZeroSafeInteractionTail

/-!
# The retained vorticity nonlinearity converges to its full Fourier series

The full field is constructed as an absolutely convergent series of curl
interactions. The retained field uses the actual existing vorticity RHS.
One common second-moment envelope pays both missing inputs and missing
outputs, including exhaustion through sets that omit the zero frequency.
Identifying this series with a continuum solution's differentiated PDE
and obtaining its envelope remain separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFullNonlinearConsistency

open Filter
open scoped Topology
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeDyadicDirectionEvolution
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail PancakeDiscardedNonlinearLimit
open PancakeZeroModeCurlBridge PancakeRetainedProjectionDefect PancakeInfinitePairReconstruction
open PancakeZeroSafeInteractionTail PancakeInteractionTruncationTail
open PancakeGalerkinKineticEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def fullCurlNonlinearity (u : FourierVelocity) : T3 → R3 :=
  infinitePairField (curlPair u (fourierCurl u))

def retainedCurlNonlinearity (M : Finset Wavevector) (u : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (finiteFourierReconstruction M (nonlinearVorticityCoeff M u) x)

def fullNonlinearError (M : Finset Wavevector) (u : FourierVelocity) (x : T3) : R3 :=
  fullCurlNonlinearity u x - retainedCurlNonlinearity M u x

theorem summable_fullCurlNonlinearity (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (u : FourierVelocity) (hbound : ∀ k, fourierMoment 2 u k ≤ g k) (x : T3) :
    Summable (fun p ↦ realPairWave (curlPair u (fourierCurl u)) p x) :=
  summable_realPairWave _ (velocityCurlMajorant g) (summable_velocityCurlMajorant g hg hSum)
    (norm_velocityCurlPair_le_envelope g hg u hbound) x

theorem continuous_fullCurlNonlinearity (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (u : FourierVelocity) (hbound : ∀ k, fourierMoment 2 u k ≤ g k) :
    Continuous (fullCurlNonlinearity u) :=
  continuous_infinitePairField _ (velocityCurlMajorant g) (summable_velocityCurlMajorant g hg hSum)
    (norm_velocityCurlPair_le_envelope g hg u hbound)

theorem continuous_retainedCurlNonlinearity (M : Finset Wavevector) (u : FourierVelocity) :
    Continuous (retainedCurlNonlinearity M u) :=
  complexRealPartEuclideanCLM.continuous.comp (continuous_finiteFourierReconstruction _ _)

theorem norm_fullNonlinearError_le_tail (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (M : Finset Wavevector) (u : FourierVelocity) (hzero : u 0 = 0)
    (hu : ∀ k ∈ M, modeDot k (u k) = 0) (hbound : ∀ k, fourierMoment 2 u k ≤ g k) (x : T3) :
    ‖fullNonlinearError M u x‖ ≤ interactionTail (nonzeroMajorant (velocityCurlMajorant g)) M := by
  unfold fullNonlinearError retainedCurlNonlinearity fullCurlNonlinearity
  rw [nonlinearVorticityCoeff_eq_curl_meanZero M u hzero hu, ← pairOutputCoeff_curlPair]
  exact norm_infinitePairField_sub_retained_le _ _
    (summable_nonzeroMajorant _ (velocityCurlMajorant_nonneg g hg) (summable_velocityCurlMajorant g hg hSum))
    (norm_velocityCurlPair_le_nonzeroMajorant g hg u hzero hbound) M x

theorem exists_uniform_fullNonlinearError_lt (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ core : Finset Wavevector, ∀ M : Finset Wavevector, core ⊆ M →
      ∀ u : FourierVelocity, u 0 = 0 → (∀ k ∈ M, modeDot k (u k) = 0) →
        (∀ k, fourierMoment 2 u k ≤ g k) → ∀ x : T3, ‖fullNonlinearError M u x‖ < epsilon := by
  obtain ⟨core, hc⟩ := exists_interactionTail_lt _ (nonzeroMajorant_nonneg _ (velocityCurlMajorant_nonneg g hg))
    (summable_nonzeroMajorant _ (velocityCurlMajorant_nonneg g hg) (summable_velocityCurlMajorant g hg hSum))
    epsilon hepsilon
  exact ⟨core, fun M hm u hz hu hb x ↦ (norm_fullNonlinearError_le_tail g hg hSum M u hz hu hb x).trans_lt (hc M hm)⟩

theorem exists_uniform_fullNonlinearError_erase_zero_lt (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ core : Finset Wavevector, ∀ M : Finset Wavevector, core ⊆ M →
      ∀ u : FourierVelocity, u 0 = 0 → (∀ k ∈ M.erase 0, modeDot k (u k) = 0) →
        (∀ k, fourierMoment 2 u k ≤ g k) → ∀ x : T3, ‖fullNonlinearError (M.erase 0) u x‖ < epsilon := by
  have ht := tendsto_interactionTail_erase_zero _ (velocityCurlMajorant_nonneg g hg)
    (summable_velocityCurlMajorant g hg hSum)
  obtain ⟨core, hc⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hepsilon))
  exact ⟨core, fun M hm u hz hu hb x ↦
    (norm_fullNonlinearError_le_tail g hg hSum (M.erase 0) u hz hu hb x).trans_lt (hc M hm)⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeFullNonlinearConsistency
