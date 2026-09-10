import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalFilteredSpectralDefect
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMaterialDiffusionBudget

/-!
# Joint viscosity in the actual filtered spectral-defect equation

Filtered strain and full vorticity have different spatial frequency
content, but their viscous terms are retained as a single linear response
of the regularized spectral energy. The nonviscous remainder includes
actual unresolved feedback, transport and discarded-strain stretching.

The full material rate is integrable across eigenvalue collisions. Its
separate selected-eigenvector pieces are not assumed measurable. No
uniform bound on this rate or on the nonviscous terms is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalFilteredViscousDefect

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalMaterialTrajectories PancakeLocalSpatialVelocity PancakeFourierMaterialPaths
open PancakeCurlOutputTail PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics
open PancakeSpatialStrainEvolution PancakePhysicalViscousSplit PancakePhysicalLaplacian
open PancakeSpectralDefectEvolution PancakeSpectralDefectBudget
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeRegularizedMaterialRate PancakeRegularizedDiffusion PancakeSpectralFiniteDifference
open PancakeMaterialDiffusionBudget PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian
open PancakeDyadicDirectionEvolution LocalMaterialVorticity LocalMaterialStrain
open LocalFilteredSpectralDefect

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem filtered_forcingCoeff_viscous_split (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (nu : ℝ) :
    LocalFilteredStrain.forcingCoeff chi modes u nu = fun q ↦
      LocalFilteredStrain.forcingCoeff chi modes u 0 q +
        viscousStrainCoeff nu (filteredVelocity chi u) q := by
  funext q
  simp only [LocalFilteredStrain.forcingCoeff, viscousStrainCoeff_zero, add_zero]
  abel

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-- Evaluating the instantaneous coefficients at zero viscosity only
selects terms. The velocity remains the actual solution with viscosity nu. -/
def nonviscousRemainderAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (X : ℝ → X3) (t : ℝ) :
    R3 →L[ℝ] R3 :=
  -(spatialSpin modes (filteredVelocity chi (s.coefficients t)) (torusPoint (X t)) *
    spatialSpin modes (filteredVelocity chi (s.coefficients t)) (torusPoint (X t))) +
    realMatrixOperator (matrixReconstruction outputs
      (LocalFilteredStrain.forcingCoeff chi modes (s.coefficients t) 0) (torusPoint (X t))) +
    realMatrixOperator (matrixReconstruction outputs
      (LocalFilteredStrain.transportCorrectionCoeff modes (filteredVelocity chi (s.coefficients t))
        (liftedVelocity s t (X t)) (torusPoint (X t))) (torusPoint (X t)))

def strainLaplacianAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (X : ℝ → X3) (t : ℝ) : R3 →L[ℝ] R3 :=
  strainLaplacian modes (filteredVelocity chi (s.coefficients t)) (torusPoint (X t))

/-- Ordinary spatial Laplacian of the full actual curl. -/
def vorticityLaplacianAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) : R3 :=
  complexRealPartEuclideanCLM
    (spatialLaplacian (spatialCurl (spatialField s t)) (torusPoint (X t)))

theorem remainderAlong_viscous_split (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (hsub : modes ⊆ outputs) (hcut : ∀ q, q ∉ modes → chi q = 0) (X : ℝ → X3) (t : ℝ) :
    LocalFilteredStrain.remainderAlong s chi modes outputs X t =
      nonviscousRemainderAlong s chi modes outputs X t +
        nu • strainLaplacianAlong s chi modes X t := by
  unfold LocalFilteredStrain.remainderAlong nonviscousRemainderAlong strainLaplacianAlong
  rw [filtered_forcingCoeff_viscous_split, matrixReconstruction_add, realMatrixOperator_add,
    reconstructed_viscousStrain, strainLaplacian_filtered_subset modes outputs chi _ _ hsub hcut]
  abel

theorem forcingAlong_viscous_split (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (X : ℝ → X3) (t : ℝ) :
    forcingAlong s chi modes X t = strainMismatchAlong s chi modes X t +
      nu • vorticityLaplacianAlong s X t := rfl

def regularizedEnergyAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (delta : ℝ) (X : ℝ → X3) (t : ℝ) : ℝ :=
  regularizedEnergy (LocalFilteredStrain.strainAlong s chi modes X t) delta (vorticityAlong s X t)

/-- The two physical Laplacians enter together, before absolute values or
separate selected-frame integrations. -/
def jointDiffusionRateAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (delta : ℝ) (X : ℝ → X3) (t : ℝ) : ℝ :=
  linearRate (LocalFilteredStrain.strainAlong s chi modes X t) delta (vorticityAlong s X t)
    (strainLaplacianAlong s chi modes X t) (vorticityLaplacianAlong s X t)

/-- Full material rate, with every term fixed by the actual velocity. -/
def rateAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (delta : ℝ) (X : ℝ → X3) (t : ℝ) : ℝ :=
  let S := LocalFilteredStrain.strainAlong s chi modes X t
  let w := vorticityAlong s X t
  linearRate S delta w
    (-S.1 * S.1 + nonviscousRemainderAlong s chi modes outputs X t +
      nu • strainLaplacianAlong s chi modes X t)
    (S.1 w + strainMismatchAlong s chi modes X t + nu • vorticityLaplacianAlong s X t)

theorem rateAlong_eq (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (delta : ℝ) (X : ℝ → X3) (t : ℝ) :
    rateAlong s chi modes outputs delta X t =
      -‖LocalFilteredSpectralDefect.residualAlong s chi modes X t‖ ^ 2 +
      remainderAnisotropy (nonviscousRemainderAlong s chi modes outputs X t)
        (topVector (LocalFilteredStrain.strainAlong s chi modes X t)) (vorticityAlong s X t) +
      2 * ⟪LocalFilteredSpectralDefect.residualAlong s chi modes X t,
        strainMismatchAlong s chi modes X t⟫ +
      2 * delta * ⟪vorticityAlong s X t,
        (LocalFilteredStrain.strainAlong s chi modes X t).1 (vorticityAlong s X t) +
          strainMismatchAlong s chi modes X t⟫ +
      nu * jointDiffusionRateAlong s chi modes delta X t :=
  linearRate_viscous_split _ _ _ _ _ _ _ _

/-- Residual damping is kept while estimating only the nonviscous terms.
The joint diffusion response has not been replaced by its absolute value. -/
theorem rateAlong_le (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (delta : ℝ) (X : ℝ → X3) (t : ℝ) :
    rateAlong s chi modes outputs delta X t +
      (1 / 2 : ℝ) * ‖LocalFilteredSpectralDefect.residualAlong s chi modes X t‖ ^ 2 ≤
      nu * jointDiffusionRateAlong s chi modes delta X t +
      nonviscousEnvelope (LocalFilteredStrain.strainAlong s chi modes X t) (vorticityAlong s X t)
        (nonviscousRemainderAlong s chi modes outputs X t)
        (strainMismatchAlong s chi modes X t) delta :=
  material_linearRate_le _ _ _ _ _ _ _ _

variable (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
  (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
  (hchir : ∀ q, chi (-q) = conj (chi q))
  (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
  (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
  (delta : ℝ) (X : ℝ → X3)
  (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)

include hg hSum hu hchi hcut hchir hsub hout hs hk hX

theorem hasDerivAt_regularizedEnergyAlong (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hlambda : DifferentiableAt ℝ
      (fun τ ↦ topEigenvalue (LocalFilteredStrain.strainAlong s chi modes X τ)) t) :
    HasDerivAt (regularizedEnergyAlong s chi modes delta X)
      (rateAlong s chi modes outputs delta X t) t := by
  have hS := LocalFilteredStrain.hasDerivAt_strainAlong s chi C hchi modes outputs
    hcut hchir hsub hout hs hk X t ht (hX t ht)
  have hw := hasDerivAt_fullVorticity_filteredStrain s g hg hSum hu chi modes X hX t ht
  rw [remainderAlong_viscous_split s chi modes outputs hsub hcut X t, ← add_assoc] at hS
  rw [forcingAlong_viscous_split, ← add_assoc] at hw
  exact hasDerivAt_regularizedEnergy (LocalFilteredStrain.strainAlong s chi modes X)
    (vorticityAlong s X) _ _ delta t hS hw hlambda

include hB

theorem ae_hasDerivAt_regularizedEnergyAlong {a b : ℝ}
    (hI : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t, t ∈ Set.uIcc a b → HasDerivAt (regularizedEnergyAlong s chi modes delta X)
      (rateAlong s chi modes outputs delta X t) t := by
  have hAC := absolutelyContinuousOnInterval_topEigenvalue
    (LocalFilteredStrain.strainAlong s chi modes X) a b
    (contDiffOn_filteredStrainAlong s hB chi modes X hX hI)
  filter_upwards [hAC.ae_differentiableAt] with t ht hmem
  exact hasDerivAt_regularizedEnergyAlong s g hg hSum hu chi C hchi modes outputs hcut hchir
    hsub hout hs hk delta X hX t (hI hmem) (ht hmem)

omit hchi hcut hchir hsub hout hs hk in
theorem absolutelyContinuousOnInterval_regularizedEnergyAlong {a b : ℝ}
    (hI : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T) :
    AbsolutelyContinuousOnInterval (regularizedEnergyAlong s chi modes delta X) a b := by
  have hS := contDiffOn_filteredStrainAlong s hB chi modes X hX hI
  have hw := (contDiffOn_vorticityAlong s g hg hSum hu X hX).mono hI
  have hn : ContDiffOn ℝ 1 (fun t ↦ ‖vorticityAlong s X t‖ ^ 2) (Set.uIcc a b) := by
    simpa only [real_inner_self_eq_norm_sq] using hw.inner ℝ hw
  have h := (absolutelyContinuousOnInterval_topSpectralDefect
    (LocalFilteredStrain.strainAlong s chi modes X) (vorticityAlong s X) a b hS hw).add
      (hn.absolutelyContinuousOnInterval.const_mul delta)
  change AbsolutelyContinuousOnInterval (fun t ↦
    regularizedEnergy (LocalFilteredStrain.strainAlong s chi modes X t) delta (vorticityAlong s X t)) a b
  simp_rw [regularizedEnergy_eq]
  exact h

/-- Integrability is established for the FULL physical rate. No separate
measurability of its chosen-top-eigenvector components is assumed. -/
theorem integrated_regularizedEnergyAlong_identity {a b : ℝ}
    (hI : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T) :
    IntervalIntegrable (rateAlong s chi modes outputs delta X) volume a b ∧
      regularizedEnergyAlong s chi modes delta X b - regularizedEnergyAlong s chi modes delta X a =
        ∫ t in a..b, rateAlong s chi modes outputs delta X t := by
  have hAC := absolutelyContinuousOnInterval_regularizedEnergyAlong s hB g hg hSum hu
    chi modes delta X hX hI
  have hd := ae_hasDerivAt_regularizedEnergyAlong s hB g hg hSum hu chi C hchi modes outputs
    hcut hchir hsub hout hs hk delta X hX hI
  have heq : ∀ᵐ t, t ∈ Set.uIcc a b →
      deriv (regularizedEnergyAlong s chi modes delta X) t = rateAlong s chi modes outputs delta X t := by
    filter_upwards [hd] with t ht hmem
    exact (ht hmem).deriv
  have hi : IntervalIntegrable (rateAlong s chi modes outputs delta X) volume a b :=
    hAC.intervalIntegrable_deriv.congr_ae (by
      change ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
        deriv (regularizedEnergyAlong s chi modes delta X) t = rateAlong s chi modes outputs delta X t
      rw [ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [heq] with t ht hmem
      exact ht (Set.uIoc_subset_uIcc hmem))
  refine ⟨hi, ?_⟩
  rw [← hAC.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [heq] with t ht hmem
  exact ht (Set.uIoc_subset_uIcc hmem)

end Mettapedia.FluidDynamics.NavierStokes.LocalFilteredViscousDefect
