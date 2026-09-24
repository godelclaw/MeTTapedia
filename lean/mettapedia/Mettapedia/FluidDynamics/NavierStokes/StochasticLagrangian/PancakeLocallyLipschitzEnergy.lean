import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMaterialSpatialEstimate

/-!
# Local Lipschitz regularity of the actual alignment energy

The scalar energy is locally Lipschitz even when its largest strain
eigenvalue crosses another eigenvalue. Compact spacetime sets therefore
have a single Lipschitz constant, not point-dependent neighborhoods.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocallyLipschitzEnergy

open scoped Topology NNReal RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakePeriodicCoherentSplit
open PancakeFourierMaterialPaths PancakePhysicalSpectralDefect PancakeFilteredStrainDynamics
open PancakeMeasurableMaterialRate PancakePhysicalViscousSplit PancakeRegularizedDiffusion
open PancakeSpacetimeSpectralDifferentiability PancakeTopEigenvalueDerivative
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeFrequencyProjectorCommutator PancakeDyadicDirectionEvolution
open PancakeSpectralFiniteDifference PancakeGalerkinKineticEnergy PancakePeriodicComplexStretch

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "ST" => ℝ × (Fin 3 → ℝ)

theorem locallyLipschitz_mul_real {P : Type*} [PseudoMetricSpace P]
    (f g : P → ℝ) (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x ↦ f x * g x) := by
  have hm : ContDiff ℝ 1 (fun z : ℝ × ℝ ↦ z.1 * z.2) := by fun_prop
  exact hm.locallyLipschitz.comp (hf.prodMk hg)

theorem locallyLipschitz_topEigenvalue
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : E → SymmetricStrain) (hS : ContDiff ℝ 1 (fun x ↦ (S x).1)) :
    LocallyLipschitz (fun x ↦ topEigenvalue (S x)) := by
  intro x
  obtain ⟨C, s, hs, hC⟩ := hS.contDiffAt.exists_lipschitzOnWith
  have hCS : LipschitzOnWith C S s := hC
  exact ⟨1 * C, s, hs, lipschitzWith_topEigenvalue.comp_lipschitzOnWith hCS⟩

theorem locallyLipschitz_regularizedEnergy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : E → SymmetricStrain) (w : E → R3) (delta : ℝ)
    (hS : ContDiff ℝ 1 (fun x ↦ (S x).1)) (hw : ContDiff ℝ 1 w) :
    LocallyLipschitz (fun x ↦ regularizedEnergy (S x) delta (w x)) := by
  have hn : ContDiff ℝ 1 (fun x ↦ ‖w x‖ ^ 2) := by
    simp only [← real_inner_self_eq_norm_sq]
    exact hw.inner ℝ hw
  have hq : ContDiff ℝ 1 (fun x ↦ ⟪w x, (S x).1 (w x)⟫) :=
    hw.inner ℝ (hS.clm_apply hw)
  have hL := (locallyLipschitz_topEigenvalue S hS).add (LocallyLipschitz.const delta)
  have h := (locallyLipschitz_mul_real _ _ hL hn.locallyLipschitz).sub hq.locallyLipschitz
  simpa only [regularizedEnergy, regularizedGap, sub_apply, smul_apply, one_apply_eq_self,
    inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] using h

theorem contDiff_curl_coefficient (u : ℝ → FourierVelocity) (q : Wavevector)
    (hu : ∀ i, ContDiff ℝ 1 (fun t ↦ u t q i)) (i : Fin 3) :
    ContDiff ℝ 1 (fun t ↦ fourierCurl (u t) q i) := by
  fin_cases i <;> simp [fourierCurl, coefficientCross] <;> fun_prop

theorem contDiff_real_reconstruction (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hu : ∀ q ∈ modes, ∀ i, ContDiff ℝ 1 (fun t ↦ u t q i)) :
    ContDiff ℝ 1 (fun z : ST ↦ finiteFourierReconstruction modes (u z.1) (torusPoint z.2)) := by
  refine contDiff_pi.mpr (fun i ↦ ?_)
  simp only [finiteFourierReconstruction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply ContDiff.sum
  intro q hq
  exact (contDiff_real_character q).mul ((hu q hq i).comp contDiff_fst)

theorem contDiff_real_vorticity (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hu : ∀ q ∈ modes, ∀ i, ContDiff ℝ 1 (fun t ↦ u t q i)) :
    ContDiff ℝ 1 (fun z : ST ↦ spatialVorticity modes (u z.1) (torusPoint z.2)) := by
  exact complexRealPartEuclideanCLM.contDiff.comp
    (contDiff_real_reconstruction modes (fun t ↦ fourierCurl (u t))
      (fun q hq i ↦ contDiff_curl_coefficient u q (hu q hq) i))

theorem locallyLipschitz_real_energy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (delta : ℝ)
    (hu : ∀ q ∈ modes, ∀ i, ContDiff ℝ 1 (fun t ↦ u t q i)) :
    LocallyLipschitz (fun z : ST ↦ physicalRegularizedEnergy chi modes (u z.1) delta (torusPoint z.2)) :=
  locallyLipschitz_regularizedEnergy _ _ delta
    (contDiff_real_strain chi modes u hu) (contDiff_real_vorticity modes u hu)

theorem exists_lipschitzOnWith_real_energy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (delta : ℝ)
    (hu : ∀ q ∈ modes, ∀ i, ContDiff ℝ 1 (fun t ↦ u t q i))
    (K : Set ST) (hK : IsCompact K) :
    ∃ C, LipschitzOnWith C
      (fun z : ST ↦ physicalRegularizedEnergy chi modes (u z.1) delta (torusPoint z.2)) K :=
  (locallyLipschitz_real_energy chi modes u delta hu).locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocallyLipschitzEnergy
