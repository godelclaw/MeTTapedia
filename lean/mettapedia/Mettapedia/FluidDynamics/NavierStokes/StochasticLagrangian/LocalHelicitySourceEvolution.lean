import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.CurlVorticitySource
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialCoherentBound

/-!
# Material helicity with the actual pressure and derivative sources

The common gradient action cancels in the material derivative of
`omega · curl omega`. The remaining source is constructed from the actual
velocity and pressure, and both viscous pairings are retained. This local
identity does not assert a sign or an initial-data budget for the source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalHelicitySourceEvolution

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakePeriodicCoherentSplit
open PancakeBlockReality LocalAlignmentForcing
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeSpatialGradientDifferentiation PancakeLocalGradientEquation
open PancakeGalerkinKineticEnergy PancakePeriodicComplexStretch
open PancakeInfiniteRealCurl PancakeLocalStrainReality PancakePhysicalNonlinearReconstruction
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeFourierMaterialPaths
open PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalMaterialVorticity
open LocalWeightedCurlCancellation LocalVorticitySeparation LocalHelicityCenterEvolution
open LocalVariableHelicityCenter CurlVorticitySource

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

def source (u : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (spatialSource u x)

theorem spatialTransport_eq_gradient_mulVec (u v : T3 → VelocityCoefficient) (x : T3) :
    spatialTransport u v x = (spatialVelocityGradient v x).mulVec (u x) := by
  ext i
  simp only [spatialTransport, spatialVelocityGradient, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The inviscid part of `D_t curl omega` is `-A curl omega + source`.
The sign of the common-gradient action is opposite to that in `D_t omega`. -/
theorem curlVorticityMaterialRate_inviscid (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    curlVorticityMaterialRate 0 u (fun i ↦ (fullFourierField id u x i).re) x =
      -gradient u x (fullVorticity (fourierCurl u) x) + source u x := by
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 4) hu
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hs := PancakeIndexedFourierMoments.summable_norm_coefficients id u
    (by simpa only [indexedFirstMoment_id] using hu1)
  have hp (i : Fin 3) : ((fullFourierField id u x i).re : ℂ) = fullFourierField id u x i := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (fullFourierField_im_zero u hs hr x i).symm
  have hA (i j : Fin 3) :
      (spatialVelocityGradient (fullFourierField id u) x i j).im = 0 := by
    have h := congrArg Complex.im (spatialVelocityGradient_reality u hu1 hr x i j)
    simp only [Complex.conj_im] at h
    linarith
  unfold curlVorticityMaterialRate
  rw [doubleCurl_material_inviscid u hu hd x hp, map_add, map_neg,
    spatialTransport_eq_gradient_mulVec, complexRealPart_mulVec _ _ hA]
  simp only [source, fullVorticity,
    spatialCurl_velocity _ (summable_fourierMoment_curl 1 u hu2)]
  rfl

theorem curlVorticityMaterialRate_eq (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    curlVorticityMaterialRate ν u (fun i ↦ (fullFourierField id u x i).re) x =
      -gradient u x (fullVorticity (fourierCurl u) x) + source u x +
        ν • fullVorticityLaplacian (fourierCurl u) x := by
  rw [curlVorticityMaterialRate_eq_inviscid_add_diffusion ν u hu,
    curlVorticityMaterialRate_inviscid u hu hd hr]

/-- The vorticity is the axial vector of this very gradient, not an
independent vector. That identification supplies this cancellation. -/
theorem inner_gradient_vorticity (u : FourierVelocity) (x : T3) (b : R3) :
    ⟪gradient u x (fullVorticity u x), b⟫ = ⟪fullVorticity u x, gradient u x b⟫ := by
  have h := LocalRadialCoherentBound.inner_gradient_add_inner_gradient u x (fullVorticity u x) b
  rw [gradient_vorticity] at h ⊢
  linarith only [h]

theorem hasDerivAt_curlVorticity_source {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ fullVorticity (fourierCurl (s.coefficients τ)) (torusPoint (X τ)))
      (-gradient (s.coefficients t) (torusPoint (X t))
          (fullVorticity (fourierCurl (s.coefficients t)) (torusPoint (X t))) +
        source (s.coefficients t) (torusPoint (X t)) +
        ν • fullVorticityLaplacian (fourierCurl (s.coefficients t)) (torusPoint (X t))) t := by
  have h := hasDerivAt_curlVorticityAlong s g hg hSum hu X hX t ht
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  change HasDerivAt _ (curlVorticityMaterialRate ν (s.coefficients t)
    (fun i ↦ (fullFourierField id (s.coefficients t) (torusPoint (X t)) i).re) _) t at h
  rwa [curlVorticityMaterialRate_eq ν _ hm (s.transverse t) (s.reality t)] at h

/-- The signed helicity source after the common-gradient cancellation. -/
def helicityRate (ν : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ⟪fullVorticity u x, source u x⟫ + ν *
    (⟪fullVorticityLaplacian u x, fullVorticity (fourierCurl u) x⟫ +
      ⟪fullVorticity u x, fullVorticityLaplacian (fourierCurl u) x⟫)

theorem helicityRate_eq (ν : ℝ) (u : FourierVelocity) (x : T3) :
    ⟪fullStrainOperator u x (fullVorticity u x) + ν • fullVorticityLaplacian u x,
        fullVorticity (fourierCurl u) x⟫ +
      ⟪fullVorticity u x, -gradient u x (fullVorticity (fourierCurl u) x) + source u x +
        ν • fullVorticityLaplacian (fourierCurl u) x⟫ = helicityRate ν u x := by
  rw [← gradient_vorticity]
  simp only [inner_add_left, inner_add_right, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, inner_gradient_vorticity, helicityRate]
  ring

theorem hasDerivAt_helicity_source {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ ⟪fullVorticity (s.coefficients τ) (torusPoint (X τ)),
      fullVorticity (fourierCurl (s.coefficients τ)) (torusPoint (X τ))⟫)
      (helicityRate ν (s.coefficients t) (torusPoint (X t))) t := by
  have ha := hasDerivAt_vorticityAlong s g hg hSum
    (fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ hτ q)) X hX t ht
  have hb := hasDerivAt_curlVorticity_source s g hg hSum hu X hX t ht
  have h := ha.inner ℝ hb
  change HasDerivAt (fun τ ↦ ⟪fullVorticity (s.coefficients τ) (torusPoint (X τ)),
      fullVorticity (fourierCurl (s.coefficients τ)) (torusPoint (X τ))⟫)
    (⟪fullVorticity (s.coefficients t) (torusPoint (X t)),
      -gradient (s.coefficients t) (torusPoint (X t))
          (fullVorticity (fourierCurl (s.coefficients t)) (torusPoint (X t))) +
        source (s.coefficients t) (torusPoint (X t)) +
        ν • fullVorticityLaplacian (fourierCurl (s.coefficients t)) (torusPoint (X t))⟫ +
      ⟪fullStrainOperator (s.coefficients t) (torusPoint (X t))
        (fullVorticity (s.coefficients t) (torusPoint (X t))) +
        ν • fullVorticityLaplacian (s.coefficients t) (torusPoint (X t)),
        fullVorticity (fourierCurl (s.coefficients t)) (torusPoint (X t))⟫) t at h
  rwa [add_comm, helicityRate_eq] at h

/-- The quotient-rule rate with the canceled helicity numerator made explicit.
The vorticity-amplitude rate in the denominator is not discarded. -/
def centerRate (δ ν : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  (helicityRate ν u x * (δ + ‖fullVorticity u x‖ ^ 2) -
    ⟪fullVorticity u x, fullVorticity (fourierCurl u) x⟫ *
      (2 * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x) +
        ν • fullVorticityLaplacian u x⟫)) / (δ + ‖fullVorticity u x‖ ^ 2) ^ 2

theorem hasDerivAt_center_source {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ regularizedCenter δ (s.coefficients τ) (torusPoint (X τ)))
      (centerRate δ ν (s.coefficients t) (torusPoint (X t))) t := by
  have ha := hasDerivAt_vorticityAlong s g hg hSum
    (fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ hτ q)) X hX t ht
  have hH := hasDerivAt_helicity_source s g hg hSum hu X hX t ht
  have hden : δ + ‖vorticityAlong s X t‖ ^ 2 ≠ 0 := by positivity
  have h := hH.fun_div ((hasDerivAt_const t δ).fun_add ha.norm_sq) hden
  simpa only [regularizedCenter, centerRate, vorticityAlong, fullVorticity,
    strainAlong, diffusionAlong, fullStrainOperator, fullVorticityLaplacian,
    spatialField, zero_add] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalHelicitySourceEvolution
