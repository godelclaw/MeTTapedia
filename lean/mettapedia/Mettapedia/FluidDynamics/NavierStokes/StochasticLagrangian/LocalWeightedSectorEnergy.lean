import Mettapedia.Analysis.SecondDerivative
import Mettapedia.Analysis.OrthogonalProjectionWeightedDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalEnstrophyDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalBottomSectorBudget

/-!
# Actual two-sector energy with a constant complementary weight

The density is `|Pω|² + θ|Qω|²`. Its material derivative and coordinate
Laplacian are proved from the actual fields. The weight is constant in
space and time; an adaptive weight would require additional product terms.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedSectorEnergy

open scoped Topology ContDiff RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open PancakeHaarTransportRate PancakeLocalInfiniteVelocity
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy.SymmetricStrain LocalClusterAnisotropy
open RankOneProjectorTangent BottomProjectorMotion LocalSpatialVorticityJets
open LocalBottomEnergyDiffusion LocalLowDiffusionBudget LocalFrozenVorticity

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def energy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (theta : ℝ) (x : T3) : ℝ :=
  theta * LocalEnstrophyDiffusion.energy u x + (1 - theta) * LocalBottomEnergy.energy chi modes u x

def frozenEnergy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (theta t : ℝ) (x : T3) (h : ℝ) : ℝ :=
  theta * LocalEnstrophyDiffusion.frozenEnergy u t x h +
    (1 - theta) * LocalBottomEnergy.frozenEnergy chi modes u t x h

def materialRate (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu theta t : ℝ) (x : T3) : ℝ :=
  theta * LocalEnstrophyDiffusion.materialRate (u t) nu x +
    (1 - theta) * LocalBottomEnergy.materialRate chi modes u nu t x

def energySecond (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (theta : ℝ) (j : Fin 3) (x : T3) : ℝ :=
  deriv (deriv (fun h : ℝ ↦ energy chi modes u theta (x + coordinateShift j h))) 0

def energyLaplacian (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (theta : ℝ) (x : T3) : ℝ :=
  ∑ j : Fin 3, energySecond chi modes u theta j x

theorem energy_eq_sectors (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (theta : ℝ) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    energy chi modes u theta x = LocalBottomEnergy.energy chi modes u x +
      theta * ‖expandingPlaneProjector S (fullVorticity u x)‖ ^ 2 := by
  have h := Mettapedia.Analysis.OrthogonalProjectionWeightedDiffusion.norm_sq_eq_add
    (bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x))
    (lineProjector_mul_self _ (bottomVector_norm _))
    (fun a b ↦ (lineProjector_isSelfAdjoint (bottomVector _)).isSymmetric a b) (fullVorticity u x)
  unfold energy LocalEnstrophyDiffusion.energy LocalBottomEnergy.energy BottomProjectedEnergy.energy
  dsimp only
  change _ = _ + theta * ‖(1 - bottomEigenlineProjector _) (fullVorticity u x)‖ ^ 2
  rw [h]
  ring

theorem energy_nonneg (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (theta : ℝ) (htheta : 0 ≤ theta) (x : T3) :
    0 ≤ energy chi modes u theta x := by
  rw [energy_eq_sectors]
  exact add_nonneg (BottomProjectedEnergy.energy_nonneg _ _) (mul_nonneg htheta (sq_nonneg _))

theorem energy_one (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : energy chi modes u 1 x = LocalEnstrophyDiffusion.energy u x := by
  simp only [energy, sub_self, one_mul, zero_mul, add_zero]

theorem weighted_enstrophy_le_energy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (theta : ℝ) (htheta1 : theta ≤ 1) (x : T3) :
    theta * LocalEnstrophyDiffusion.energy u x ≤ energy chi modes u theta x :=
  le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr htheta1) (BottomProjectedEnergy.energy_nonneg _ _))

theorem energy_le_enstrophy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (theta : ℝ) (htheta1 : theta ≤ 1) (x : T3) :
    energy chi modes u theta x ≤ LocalEnstrophyDiffusion.energy u x := by
  have h := energy_eq_sectors chi modes u 1 x
  dsimp only at h
  rw [energy_one, one_mul] at h
  rw [energy_eq_sectors, h]
  exact add_le_add le_rfl (mul_le_of_le_one_left (sq_nonneg _) htheta1)

theorem energySecond_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (theta : ℝ) (j : Fin 3) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    energySecond chi modes u theta j x = theta * LocalEnstrophyDiffusion.energySecond u j x +
      (1 - theta) * LocalBottomEnergyDiffusion.energySecond chi modes u j x := by
  have hP : ContDiffAt ℝ 2 (projectorCurve chi modes u j x) 0 :=
    (LocalSpatialBottomProjector.contDiffAt_projector_shift chi modes u x hg j).of_le (by decide)
  have hw := (contDiff_fullVorticity_shift u hu j x).contDiffAt (x := 0)
  have he : ContDiffAt ℝ 2 (fun h : ℝ ↦ LocalBottomEnergy.energy chi modes u (x + coordinateShift j h)) 0 :=
    (hP.clm_apply hw).norm_sq ℝ
  exact Mettapedia.Analysis.deriv_deriv_linearCombination
    ((LocalEnstrophyDiffusion.contDiff_energy_shift u hu j x).contDiffAt) he theta (1 - theta)

theorem energyLaplacian_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (theta : ℝ) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    energyLaplacian chi modes u theta x = theta * LocalEnstrophyDiffusion.energyLaplacian u x +
      (1 - theta) * LocalBottomEnergyDiffusion.energyLaplacian chi modes u x := by
  simp only [energyLaplacian, energySecond_eq chi modes u hu theta _ x hg,
    LocalEnstrophyDiffusion.energyLaplacian, LocalBottomEnergyDiffusion.energyLaplacian,
    Finset.mul_sum, Finset.sum_add_distrib]

theorem hasDerivAt_frozenEnergy {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (theta : ℝ)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3)
    (hP : DifferentiableAt ℝ
      (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes s.coefficients t x h)) 0) :
    HasDerivAt (fun h ↦ frozenEnergy chi modes s.coefficients theta t x h)
      (materialRate chi modes s.coefficients nu theta t x) 0 :=
  ((LocalEnstrophyDiffusion.hasDerivAt_frozenEnergy s g hg hSum hu a b hab hI t ht x).const_mul theta).add
    ((LocalBottomEnergy.hasDerivAt_frozenEnergy s g hg hSum hu chi modes a b hab hI t ht x hP).const_mul (1 - theta))

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedSectorEnergy
