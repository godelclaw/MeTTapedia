import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRealFourierProjection
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteFourierLocalization

/-!
# Exact boundary output of a spatially localized retained field

The product is the existing collected Fourier convolution. Its output
outside the retained set is the only contribution to a frozen-weight
pairing with discarded nonlinear modes. Taking real parts is compatible
with the retained projection because that set is negation closed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalizedProjectionBoundary

open MeasureTheory
open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeMisalignmentEnergyBridge
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeBlockReality
open PancakeFiniteFourierLocalization PancakeRealFourierProjection PancakeRetainedProjectionDefect
open PancakePhysicalSpectralDefect PancakeGalerkinKineticEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def localizedBoundaryField (cutoff modes : Finset Wavevector) (c : Wavevector → ℂ)
    (w : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (finiteFourierReconstruction
    (finiteCutoffOutputModes cutoff modes \ modes) (finiteCutoffConvolutionCoeff cutoff modes c w) x)

theorem convolutionCoeff_eq_zero_outside (cutoff modes : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity) (q : Wavevector)
    (hq : q ∉ finiteCutoffOutputModes cutoff modes) :
    finiteCutoffConvolutionCoeff cutoff modes c w q = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro pk hpk
  obtain ⟨hmem, he⟩ := Finset.mem_filter.mp hpk
  obtain ⟨hp, hk⟩ := Finset.mem_product.mp hmem
  exact False.elim (hq ((mem_finiteCutoffOutputModes_iff cutoff modes q).mpr ⟨pk.1, hp, pk.2, hk, he⟩))

theorem reconstruction_subset_of_zero (s t : Finset Wavevector) (a : FourierVelocity)
    (hst : s ⊆ t) (hz : ∀ q ∈ t, q ∉ s → a q = 0) (x : T3) :
    finiteFourierReconstruction t a x = finiteFourierReconstruction s a x := by
  symm
  apply Finset.sum_subset hst
  intro q hq hqs
  rw [hz q hq hqs, smul_zero]

theorem localized_reconstruction_split (cutoff modes : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity) (x : T3) :
    finiteCutoffLocalizedReconstruction cutoff modes c w x =
      finiteFourierReconstruction modes (finiteCutoffConvolutionCoeff cutoff modes c w) x +
      finiteFourierReconstruction (finiteCutoffOutputModes cutoff modes \ modes)
        (finiteCutoffConvolutionCoeff cutoff modes c w) x := by
  classical
  let Q := finiteCutoffOutputModes cutoff modes
  let C := finiteCutoffConvolutionCoeff cutoff modes c w
  have he := reconstruction_subset_of_zero Q (Q ∪ modes) C Finset.subset_union_left
    (fun q _ hq ↦ convolutionCoeff_eq_zero_outside cutoff modes c w q hq) x
  have hs := reconstruction_sub_of_subset modes (Q ∪ modes) C x Finset.subset_union_right
  have hdiff : (Q ∪ modes) \ modes = Q \ modes := by ext q; simp; tauto
  rw [hdiff, he] at hs
  rw [← finiteFourierReconstruction_convolutionCoeff]
  change finiteFourierReconstruction Q C x = _
  rw [sub_eq_iff_eq_add] at hs
  rw [hs]
  abel

theorem realPart_smul_of_real (z : ℂ) (v : VelocityCoefficient) (hz : z.im = 0) :
    complexRealPartEuclideanCLM (z • v) = z.re • complexRealPartEuclidean v := by
  ext i
  change (z * v i).re = z.re * (v i).re
  simp [Complex.mul_re, hz]

theorem real_localized_split (cutoff modes : Finset Wavevector) (c : Wavevector → ℂ)
    (w : FourierVelocity) (x : T3)
    (hc : (finiteScalarFourierReconstruction cutoff c x).im = 0) :
    (finiteScalarFourierReconstruction cutoff c x).re • complexRealPartEuclidean (finiteFourierReconstruction modes w x) =
      complexRealPartEuclideanCLM (finiteFourierReconstruction modes (finiteCutoffConvolutionCoeff cutoff modes c w) x) +
        localizedBoundaryField cutoff modes c w x := by
  rw [← realPart_smul_of_real _ _ hc, finiteScalar_mul_finiteFourierReconstruction,
    localized_reconstruction_split, map_add]
  rfl

theorem continuous_localizedBoundaryField (cutoff modes : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity) : Continuous (localizedBoundaryField cutoff modes c w) :=
  complexRealPartEuclideanCLM.continuous.comp (continuous_finiteFourierReconstruction _ _)

theorem integral_localized_pairing_eq_boundary (cutoff modes outputs : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity) (u : FourierVelocity) (A : R3 →L[ℝ] R3)
    (hc : ∀ x : T3, (finiteScalarFourierReconstruction cutoff c x).im = 0)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, ⟪A ((finiteScalarFourierReconstruction cutoff c x).re •
      complexRealPartEuclidean (finiteFourierReconstruction modes w x)), discardedNonlinearField modes outputs u x⟫) =
      ∫ x : T3, ⟪A (localizedBoundaryField cutoff modes c w x), discardedNonlinearField modes outputs u x⟫ := by
  have hM : Continuous (fun x : T3 ↦ complexRealPartEuclideanCLM
      (finiteFourierReconstruction modes (finiteCutoffConvolutionCoeff cutoff modes c w) x)) :=
    complexRealPartEuclideanCLM.continuous.comp (continuous_finiteFourierReconstruction _ _)
  have hD := continuous_discardedNonlinearField modes outputs u
  have hMc : Continuous (fun x : T3 ↦ ⟪A (complexRealPartEuclideanCLM
      (finiteFourierReconstruction modes (finiteCutoffConvolutionCoeff cutoff modes c w) x)),
      discardedNonlinearField modes outputs u x⟫) := (A.continuous.comp hM).inner hD
  have hBc : Continuous (fun x : T3 ↦ ⟪A (localizedBoundaryField cutoff modes c w x),
      discardedNonlinearField modes outputs u x⟫) :=
    (A.continuous.comp (continuous_localizedBoundaryField cutoff modes c w)).inner hD
  simp only [real_localized_split cutoff modes c w _ (hc _), map_add, inner_add_left]
  rw [integral_add (hMc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hBc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have he := integral_constant_operator_disjoint_neg_closed modes (outputs \ modes)
    (finiteCutoffConvolutionCoeff cutoff modes c w) (nonlinearVorticityCoeff modes u) A
    (Finset.disjoint_left.mpr (fun q hq ho ↦ (Finset.mem_sdiff.mp ho).2 hq)) hs
  change (∫ x : T3, ⟪A (complexRealPartEuclideanCLM
    (finiteFourierReconstruction modes (finiteCutoffConvolutionCoeff cutoff modes c w) x)),
    discardedNonlinearField modes outputs u x⟫) = 0 at he
  rw [he, zero_add]

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalizedProjectionBoundary
