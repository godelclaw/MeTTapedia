import Mettapedia.Analysis.OperatorQuadraticForm
import Mettapedia.Analysis.IdempotentDerivatives
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialBottomProjector
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialVorticityJets
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalBottomEnergy

/-!
# The actual signed diffusion identity for bottom-projected vorticity

The Laplacian is the sum of ordinary coordinate second derivatives of the
actual energy. Its product rule retains the negative projected-gradient
square and all projector-gradient terms. No integration by parts or
uniform control of the remaining terms is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalBottomEnergyDiffusion

open scoped Topology ContDiff RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open PancakeHaarTransportRate PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy.SymmetricStrain
open PancakeEigenframePerturbation RankOneProjectorTangent BottomProjectorMotion
open LocalBottomEnergy LocalLowDiffusionBudget LocalJointDiffusionBudget LocalSpatialVorticityJets
open LocalAlignmentForcing LocalProjectorMotion

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def projectorCurve (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) (h : ℝ) : Op :=
  bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) (x + coordinateShift j h))

def projectorFirst (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) : Op := deriv (projectorCurve chi modes u j x) 0

def projectorSecond (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) : Op := deriv (deriv (projectorCurve chi modes u j x)) 0

def projectorLaplacian (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : Op := ∑ j : Fin 3, projectorSecond chi modes u j x

def energySecond (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  deriv (deriv (fun h : ℝ ↦ energy chi modes u (x + coordinateShift j h))) 0

def energyLaplacian (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ := ∑ j : Fin 3, energySecond chi modes u j x

def projectedGradientSquare (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, ‖bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x)
    (fullCurlGradient u j x)‖ ^ 2

def gradientCrossTerm (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, ⟪fullCurlGradient u j x, projectorFirst chi modes u j x (fullVorticity u x)⟫

theorem projectorSecond_idempotent_constraint (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let P := bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x)
    projectorSecond chi modes u j x * P + P * projectorSecond chi modes u j x +
      (2 : ℝ) • (projectorFirst chi modes u j x * projectorFirst chi modes u j x) =
      projectorSecond chi modes u j x := by
  have hP : ContDiffAt ℝ 2 (projectorCurve chi modes u j x) 0 :=
    (LocalSpatialBottomProjector.contDiffAt_projector_shift chi modes u x hg j).of_le (by decide)
  have h := Mettapedia.Analysis.second_derivative_idempotent hP
    (fun h ↦ lineProjector_mul_self _ (bottomVector_norm
      (spatialStrain modes (filteredVelocity chi u) (x + coordinateShift j h))))
  have hz : projectorCurve chi modes u j x 0 =
      bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x) := by
    simp only [projectorCurve, coordinateShift_zero, add_zero]
  simpa only [hz, projectorFirst, projectorSecond] using h

theorem projectorLaplacian_idempotent_constraint (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let P := bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x)
    projectorLaplacian chi modes u x * P + P * projectorLaplacian chi modes u x +
      (2 : ℝ) • (∑ j : Fin 3, projectorFirst chi modes u j x * projectorFirst chi modes u j x) =
      projectorLaplacian chi modes u x := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl
    (fun j _ ↦ projectorSecond_idempotent_constraint chi modes u j x hg)
  simpa only [projectorLaplacian, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum,
    Finset.sum_add_distrib] using h

/-- A material-minus-diffusion rate has a quadratic tangent defect.
The first-order projector-motion estimate cannot be applied to it unchanged. -/
theorem parabolic_projector_constraint (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) (D : Op) (nu : ℝ)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x))
    (hD : D * bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x) +
      bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x) * D = D) :
    let P := bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x)
    let W := D - nu • projectorLaplacian chi modes u x
    W * P + P * W = W +
      (2 * nu) • (∑ j : Fin 3, projectorFirst chi modes u j x * projectorFirst chi modes u j x) :=
  Mettapedia.Analysis.parabolic_idempotent_constraint _ D _ _ nu hD
    (projectorLaplacian_idempotent_constraint chi modes u x hg)

theorem projectedGradientSquare_nonneg (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : 0 ≤ projectedGradientSquare chi modes u x :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem energySecond_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (j : Fin 3) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let P := bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x)
    energySecond chi modes u j x =
      2 * ⟪P (fullVorticity u x), fullCurlSecond u j x⟫ + 2 * ‖P (fullCurlGradient u j x)‖ ^ 2 +
        4 * ⟪fullCurlGradient u j x, projectorFirst chi modes u j x (fullVorticity u x)⟫ +
        ⟪fullVorticity u x, projectorSecond chi modes u j x (fullVorticity u x)⟫ := by
  have hP : ContDiffAt ℝ 2 (projectorCurve chi modes u j x) 0 :=
    (LocalSpatialBottomProjector.contDiffAt_projector_shift chi modes u x hg j).of_le (by decide)
  have hw := (contDiff_fullVorticity_shift u hu j x).contDiffAt (x := 0)
  have hs : ∀ᶠ h in 𝓝 (0 : ℝ), ∀ a b : R3,
      ⟪projectorCurve chi modes u j x h a, b⟫ = ⟪a, projectorCurve chi modes u j x h b⟫ := by
    apply Filter.Eventually.of_forall
    intro h a b
    exact (lineProjector_isSelfAdjoint (bottomVector
      (spatialStrain modes (filteredVelocity chi u) (x + coordinateShift j h)))).isSymmetric a b
  have hh := Mettapedia.Analysis.OperatorQuadraticForm.deriv_deriv_value hP hw hs
  have he : (fun h : ℝ ↦ Mettapedia.Analysis.OperatorQuadraticForm.value
      (projectorCurve chi modes u j x h) (fullVorticity u (x + coordinateShift j h))) =
      fun h ↦ energy chi modes u (x + coordinateShift j h) := by
    funext h
    exact (BottomProjectedEnergy.energy_eq_inner _ _).symm
  rw [he, deriv_deriv_fullVorticity_shift u hu, deriv_fullVorticity_shift u hu] at hh
  simp only [coordinateShift_zero, add_zero] at hh
  have hsq := (BottomProjectedEnergy.energy_eq_inner
    (spatialStrain modes (filteredVelocity chi u) x) (fullCurlGradient u j x)).symm
  change ⟪fullCurlGradient u j x, bottomEigenlineProjector
    (spatialStrain modes (filteredVelocity chi u) x) (fullCurlGradient u j x)⟫ = _ at hsq
  simpa only [projectorCurve, coordinateShift_zero, add_zero, hsq, BottomProjectedEnergy.energy,
    projectorFirst, projectorSecond, energySecond] using hh

theorem energyLaplacian_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let P := bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x)
    energyLaplacian chi modes u x =
      2 * ⟪P (fullVorticity u x), fullVorticityLaplacian u x⟫ +
        2 * projectedGradientSquare chi modes u x + 4 * gradientCrossTerm chi modes u x +
        ⟪fullVorticity u x, projectorLaplacian chi modes u x (fullVorticity u x)⟫ := by
  simp only [energyLaplacian, energySecond_eq chi modes u hu _ x hg, projectedGradientSquare,
    gradientCrossTerm, projectorLaplacian, sum_apply, inner_sum,
    ← sum_fullCurlSecond u hu, Finset.mul_sum, Finset.sum_add_distrib]

theorem materialRate_sub_diffusion_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (hu : Summable (fourierMoment 3 (u t))) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x)) :
    let S := spatialStrain modes (filteredVelocity chi (u t)) x
    let w := fullVorticity (u t) x
    materialRate chi modes u nu t x - nu * energyLaplacian chi modes (u t) x =
      2 * thirdEigenvalue S * energy chi modes (u t) x +
        2 * ⟪bottomEigenlineProjector S w, strainMismatch chi modes (u t) x⟫ +
        ⟪w, (-planeRate chi modes u t x - nu • projectorLaplacian chi modes (u t) x) w⟫ -
        2 * nu * projectedGradientSquare chi modes (u t) x -
        4 * nu * gradientCrossTerm chi modes (u t) x := by
  rw [energyLaplacian_eq chi modes (u t) hu x hg]
  simp only [LocalBottomEnergy.materialRate, BottomProjectedEnergy.rate, inner_add_right, real_inner_smul_right,
    sub_apply, smul_apply, inner_sub_right, energy]
  ring

/-- The signed source after subtracting the actual energy Laplacian.
The projector's material-minus-diffusive rate is kept as one expression. -/
def parabolicSource (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi (u t)) x
  let w := fullVorticity (u t) x
  2 * ⟪bottomEigenlineProjector S w, strainMismatch chi modes (u t) x⟫ +
    ⟪w, (-planeRate chi modes u t x - nu • projectorLaplacian chi modes (u t) x) w⟫ -
    4 * nu * gradientCrossTerm chi modes (u t) x

theorem materialRate_sub_diffusion_add_gradient_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (hu : Summable (fourierMoment 3 (u t))) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x)) :
    LocalBottomEnergy.materialRate chi modes u nu t x - nu * energyLaplacian chi modes (u t) x +
      2 * nu * projectedGradientSquare chi modes (u t) x =
      2 * thirdEigenvalue (spatialStrain modes (filteredVelocity chi (u t)) x) * energy chi modes (u t) x +
        parabolicSource chi modes u nu t x := by
  rw [materialRate_sub_diffusion_eq chi modes u nu t hu x hg]
  unfold parabolicSource
  ring

theorem materialRate_sub_diffusion_add_damping_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (hu : Summable (fourierMoment 3 (u t)))
    (hdiv : ∀ q, modeDot q (u t q) = 0) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x)) :
    LocalBottomEnergy.materialRate chi modes u nu t x - nu * energyLaplacian chi modes (u t) x +
      2 * nu * projectedGradientSquare chi modes (u t) x +
      (4 / 3 : ℝ) * bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x) *
        energy chi modes (u t) x ≤ parabolicSource chi modes u nu t x := by
  rw [materialRate_sub_diffusion_add_gradient_eq chi modes u nu t hu x hg]
  have hmu := FilteredStrainTrace.thirdEigenvalue_le_neg_two_thirds_bottomGap _
    (FilteredStrainTrace.trace_filteredStrain_eq_zero chi modes (u t) hdiv x)
  have he := BottomProjectedEnergy.energy_nonneg
    (spatialStrain modes (filteredVelocity chi (u t)) x) (fullVorticity (u t) x)
  change 0 ≤ energy chi modes (u t) x at he
  nlinarith [mul_le_mul_of_nonneg_right hmu he]

end Mettapedia.FluidDynamics.NavierStokes.LocalBottomEnergyDiffusion
