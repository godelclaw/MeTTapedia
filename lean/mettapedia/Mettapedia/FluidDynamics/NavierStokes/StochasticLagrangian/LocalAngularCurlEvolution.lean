import Mettapedia.Analysis.AngularCurlEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAngularCurlBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityGradientEvolution

/-!
# Polynomial angular curl along the actual unforced material flow

The first-jet rate is reconstructed from the infinite NS equation and
actual path motion. Both the angular subtraction and the outer squared
amplitude are differentiated. No sign, coercivity or time budget for
the resulting rate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAngularCurlEvolution

open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalJointDiffusionBudget LocalAlignmentForcing
open LocalMaterialVorticity LocalVorticityGradientEvolution LocalAngularCurlBudget
open Mettapedia.Analysis

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def materialAngularCurlRate (ν : ℝ) (u : FourierVelocity) (v : X3) (x : T3) : R3 :=
  AngularCurlDecomposition.angularCurlRate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (fullStrainOperator u x (fullVorticity u x) + ν • fullVorticityLaplacian u x)
    (fun j ↦ gradientMaterialRate ν u v j x)

def materialDensityRate (ν : ℝ) (u : FourierVelocity) (v : X3) (x : T3) : ℝ :=
  AngularCurlDecomposition.angularCurlDensityRate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (fullStrainOperator u x (fullVorticity u x) + ν • fullVorticityLaplacian u x)
    (fun j ↦ gradientMaterialRate ν u v j x)

/-- The exact linear viscous contribution; no sign is assigned to it. -/
def viscousDensityRate (u : FourierVelocity) (x : T3) : ℝ :=
  AngularCurlDecomposition.angularCurlDensityRate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (fullVorticityLaplacian u x) (fun j ↦ gradientLaplacian u j x)

theorem materialDensityRate_eq_inviscid_add_diffusion (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (v : X3) (x : T3) :
    materialDensityRate ν u v x = materialDensityRate 0 u v x + ν * viscousDensityRate u x := by
  unfold materialDensityRate
  simp only [gradientMaterialRate_eq_inviscid_add_diffusion ν u hu v,
    AngularCurlDecomposition.angularCurlDensityRate_add,
    AngularCurlDecomposition.angularCurlDensityRate_smul, zero_smul, add_zero]
  rfl

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
  (X : ℝ → X3)
  (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)

include hg hSum hu hX

theorem hasDerivAt_angularCurl_material (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ angularCurl (s.coefficients τ) (torusPoint (X τ)))
      (materialAngularCurlRate ν (s.coefficients t) (liftedVelocity s t (X t)) (torusPoint (X t))) t := by
  have ha := hasDerivAt_vorticityAlong s g hg hSum
    (fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ hτ q)) X hX t ht
  have hD := fun j ↦ hasDerivAt_fullCurlGradient_material s g hg hSum hu X hX j t ht
  exact AngularCurlDecomposition.hasDerivAt_angularCurl ha hD

theorem hasDerivAt_angularCurlDensity_material (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ angularCurlDensity (s.coefficients τ) (torusPoint (X τ)))
      (materialDensityRate ν (s.coefficients t) (liftedVelocity s t (X t)) (torusPoint (X t))) t := by
  have ha := hasDerivAt_vorticityAlong s g hg hSum
    (fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ hτ q)) X hX t ht
  have hD := fun j ↦ hasDerivAt_fullCurlGradient_material s g hg hSum hu X hX j t ht
  exact AngularCurlDecomposition.hasDerivAt_angularCurlDensity ha hD

/-- Actual material evolution, with the viscous term separated rather than discarded. -/
theorem hasDerivAt_angularCurlDensity_material_split (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ angularCurlDensity (s.coefficients τ) (torusPoint (X τ)))
      (materialDensityRate 0 (s.coefficients t) (liftedVelocity s t (X t)) (torusPoint (X t)) +
        ν * viscousDensityRate (s.coefficients t) (torusPoint (X t))) t := by
  have h := hasDerivAt_angularCurlDensity_material s g hg hSum hu X hX t ht
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  rwa [materialDensityRate_eq_inviscid_add_diffusion ν _ hm] at h

end Mettapedia.FluidDynamics.NavierStokes.LocalAngularCurlEvolution
