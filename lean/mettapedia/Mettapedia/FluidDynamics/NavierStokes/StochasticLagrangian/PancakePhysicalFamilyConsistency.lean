import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalFieldReconstruction

/-!
# Uniform nonlinear consistency for a compact regular physical family

The input is a family of physical fields with continuous coordinate jets,
not a supplied Fourier envelope. The envelope is constructed, the original
field is reconstructed, and the actual retained nonlinear RHS converges
uniformly to the derivative-defined physical nonlinearity. Reality,
mean-zero coefficients and transversality remain explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalFamilyConsistency

open scoped ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeArbitraryDataBlocks
open PancakeContinuousCoordinateJet PancakeCompactJetEnvelope PancakeCurlOutputTail
open PancakePhysicalFieldReconstruction PancakeInfiniteRealCurl PancakeFullNonlinearConsistency
open PancakeDyadicDirectionEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def fieldCurlNonlinearity (f : T3 → VelocityCoefficient) : T3 → R3 :=
  realSpatialCurl (fun x ↦ realCross (complexRealPartEuclideanCLM (f x))
    (realSpatialCurl (fun y ↦ complexRealPartEuclideanCLM (f y)) x))

theorem exists_uniform_physicalFamily_error_lt {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (f : P → T3 → VelocityCoefficient)
    (hf : ∀ p i, HasContinuousCoordinateJet 6 (fun x ↦ f p x i))
    (hc : ∀ i, Continuous (fun z : P × T3 ↦ f z.1 z.2 i))
    (h6 : ∀ i j, Continuous (fun z : P × T3 ↦ coordinateJet (fun x ↦ f z.1 x i) j 6 z.2))
    (hr : ∀ p x i, conj (f p x i) = f p x i)
    (hz : ∀ p, torusFourierVelocity (f p) 0 = 0)
    (hd : ∀ p k, modeDot k (torusFourierVelocity (f p) k) = 0)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ core : Finset Wavevector, ∀ M : Finset Wavevector, core ⊆ M → ∀ p x,
      ‖fieldCurlNonlinearity (f p) x - retainedCurlNonlinearity (M.erase 0) (torusFourierVelocity (f p)) x‖ < epsilon := by
  obtain ⟨g, hg, hSum, hb⟩ := exists_common_secondMoment_envelope f hf hc h6
  obtain ⟨core, hcore⟩ := exists_uniform_fullNonlinearError_erase_zero_lt g hg hSum epsilon hepsilon
  refine ⟨core, fun M hm p x ↦ ?_⟩
  have hs : Summable (fourierMoment 2 (torusFourierVelocity (f p))) :=
    Summable.of_nonneg_of_le (fourierMoment_nonneg _ _) (hb p) hSum
  have he := fullCurlNonlinearity_torusFourierVelocity (f p)
    (fun i ↦ (hc i).comp (continuous_const.prodMk continuous_id)) hs (hr p)
  change fullCurlNonlinearity (torusFourierVelocity (f p)) = fieldCurlNonlinearity (f p) at he
  rw [← he]
  exact hcore M hm _ (hz p) (fun k _ ↦ hd p k) (hb p) x

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalFamilyConsistency
