import Mettapedia.Analysis.LongitudinalJetEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullVorticityGradientTransport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullLambGradientWork

/-!
# Longitudinal vorticity evolution on the actual material flow

The velocity-gradient commutator cancels exactly. The remaining inviscid
source is the velocity Hessian contracted twice with vorticity, alongside
linear deformation of the longitudinal derivative. The viscous product
rate is retained without assigning it a sign or a global budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalLongitudinalVorticity

open scoped RealInnerProductSpace ComplexConjugate
open Mettapedia.Analysis LongitudinalJetEvolution
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeBlockReality
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalJointDiffusionBudget LocalAlignmentForcing
open LocalMaterialVorticity LocalVorticityGradientEvolution FullVorticityGradientTransport FullLambVector
open LocalVorticitySeparation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def longitudinalVorticity (u : FourierVelocity) (x : T3) : R3 :=
  longitudinal (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)

def curvatureSource (u : FourierVelocity) (x : T3) : R3 :=
  velocityCurvature (fullVorticity u x) (fun j k ↦ mixedGradient u j k x)

def inviscidRate (u : FourierVelocity) (x : T3) : R3 :=
  gradient u x (longitudinalVorticity u x) + curvatureSource u x

def viscousRate (u : FourierVelocity) (x : T3) : R3 :=
  rate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (fullVorticityLaplacian u x) (fun j ↦ gradientLaplacian u j x)

def materialRate (ν : ℝ) (u : FourierVelocity) (v : X3) (x : T3) : R3 :=
  rate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (fullStrainOperator u x (fullVorticity u x) + ν • fullVorticityLaplacian u x)
    (fun j ↦ gradientMaterialRate ν u v j x)

theorem materialRate_eq (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    materialRate ν u (fun j ↦ PancakeInfiniteRealCurl.realFullField u x j) x =
      inviscidRate u x + ν • viscousRate u x := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 4) hu
  unfold materialRate
  rw [← gradient_vorticity, ← directional_velocityJet u hu1]
  simp_rw [gradientMaterialRate_eq ν u hu hd hr]
  change rate _ _ (longitudinal (fullVorticity u x) (fun j ↦ velocityJet u j x) + _) (fun j ↦
    stretchingJet (fullVorticity u x) (fun k ↦ fullCurlGradient u k x)
      (fun k ↦ velocityJet u k x) (fun k l ↦ mixedGradient u k l x) j + _) = _
  rw [rate_add, rate_smul, rate_stretching]
  change longitudinal (longitudinalVorticity u x) (fun j ↦ velocityJet u j x) +
    curvatureSource u x + ν • viscousRate u x = _
  rw [longitudinal, directional_velocityJet u hu1]
  rfl

theorem radialLongitudinal_eq (u : FourierVelocity) (x : T3) :
    OcticCurlCancellation.longitudinalRate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) =
      RadialPower.evenRadialRate 2 (fullVorticity u x) (longitudinalVorticity u x) :=
  OcticCurlCancellation.longitudinalRate_eq _ _

variable {ν T B : ℝ} {u₀ : FourierVelocity}

theorem hasDerivAt_longitudinal_material (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ longitudinalVorticity (s.coefficients τ) (torusPoint (X τ)))
      (materialRate ν (s.coefficients t) (liftedVelocity s t (X t)) (torusPoint (X t))) t := by
  have ha := hasDerivAt_vorticityAlong s g hg hSum
    (fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ hτ q)) X hX t ht
  exact hasDerivAt_longitudinal ha
    (fun j ↦ hasDerivAt_fullCurlGradient_material s g hg hSum hu X hX j t ht)

theorem hasDerivAt_longitudinal_material_split (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ longitudinalVorticity (s.coefficients τ) (torusPoint (X τ)))
      (inviscidRate (s.coefficients t) (torusPoint (X t)) +
        ν • viscousRate (s.coefficients t) (torusPoint (X t))) t := by
  have h := hasDerivAt_longitudinal_material s g hg hSum hu X hX t ht
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  have hv : liftedVelocity s t (X t) =
      fun j ↦ PancakeInfiniteRealCurl.realFullField (s.coefficients t) (torusPoint (X t)) j := rfl
  rwa [hv, materialRate_eq ν _ hm (s.transverse t) (s.reality t)] at h

end Mettapedia.FluidDynamics.NavierStokes.LocalLongitudinalVorticity
