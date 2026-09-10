import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalInitialGradient
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMatrixCurlAlgebra
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAlignmentForcing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralEigenvalueWithin

/-!
# Initial strain and vorticity rates of the local Navier–Stokes solution

Symmetric gradient and curl are linear contractions of the actual velocity
gradient. Their initial right derivatives are consequently the same
contractions of the physical Navier–Stokes right-hand side.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalInitialSpectral

open scoped Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCoefficientLimitEquation
open PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity PancakeInfiniteFourierDerivative
open PancakeLocalGradientEquation PancakeLocalStrainEquation PancakeFilteredStrainDynamics
open PancakeFourierMaterialPaths PancakeTransverseEnergyFreezing PancakeMatrixCurlAlgebra
open PancakeDyadicDirectionEvolution
open PancakeCurlOutputTail PancakeSpectralProjectorRegularity LocalInitialGradient
open LocalLowDiffusionBudget LocalAlignmentForcing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "M3" => Matrix (Fin 3) (Fin 3) ℂ

/-- The ordinary full symmetric velocity gradient, without a finite filter. -/
def fullSymmetricStrain (u : FourierVelocity) (x : T3) : SymmetricStrain :=
  ⟨fullStrainOperator u x, realMatrixOperator_symmetric _
    (spatialStrain_symmetric (fullFourierField id u) x)⟩

theorem hasDerivWithinAt_symmetrize (a : ℝ → M3) (da : M3) (domain : Set ℝ) (t : ℝ)
    (ha : HasDerivWithinAt a da domain t) :
    HasDerivWithinAt (fun tau ↦ symmetrize (a tau)) (symmetrize da) domain t := by
  exact ((LinearMap.toContinuousLinearMap symmetrize).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t ha

theorem hasDerivWithinAt_matrixCurl (a : ℝ → M3) (da : M3) (domain : Set ℝ) (t : ℝ)
    (ha : HasDerivWithinAt a da domain t) :
    HasDerivWithinAt (fun tau ↦ matrixCurl (a tau)) (matrixCurl da) domain t := by
  exact ((LinearMap.toContinuousLinearMap matrixCurl).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t ha

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
  (hu : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 3 (s.coefficients t) k ≤ g k)

include hg hSum hu

theorem fullStrainOperator_hasDerivWithinAt_initial (hT : 0 < T) (hB : 0 ≤ B) (x : T3) :
    HasDerivWithinAt (fun t ↦ fullStrainOperator (s.coefficients t) x)
      (fullStrainOperator (infiniteVelocityRHS nu u₀) x) (Set.Ici (0 : ℝ)) 0 := by
  exact realMatrixOperatorCLM.hasFDerivAt.comp_hasDerivWithinAt 0
    (hasDerivWithinAt_symmetrize _ _ _ 0
      (velocityGradient_hasDerivWithinAt_initial s g hg hSum hu hT hB x))

theorem fullVorticity_hasDerivWithinAt_initial (hT : 0 < T) (hB : 0 ≤ B) (x : T3) :
    HasDerivWithinAt (fun t ↦ fullVorticity (s.coefficients t) x)
      (fullVorticity (infiniteVelocityRHS nu u₀) x) (Set.Ici (0 : ℝ)) 0 := by
  exact complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivWithinAt 0
    (hasDerivWithinAt_matrixCurl _ _ _ 0
      (velocityGradient_hasDerivWithinAt_initial s g hg hSum hu hT hB x))

end Mettapedia.FluidDynamics.NavierStokes.LocalInitialSpectral
