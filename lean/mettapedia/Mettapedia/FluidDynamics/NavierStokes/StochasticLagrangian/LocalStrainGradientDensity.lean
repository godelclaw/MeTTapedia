import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialSpectralBounds
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLowDiffusionBudget

/-!
# Continuity and domination of the actual strain-gradient density

The density is the same sum of squared operator norms used in the local
spectral diffusion identity. Its Fourier amplitude bound is a majorant,
not the definition of the density.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalStrainGradientDensity

open scoped Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierStrainGradient PancakeFilteredStrainDynamics PancakeLowDiffusionBudget
open LocalSpatialSpectralBounds
open PancakePhysicalDiffusionLimit PancakeFourierMaterialPaths PancakeFourierPressureStrain
open PancakeMappedFourierDiffusion

local notation "T3" => UnitAddTorus (Fin 3)

theorem continuous_strainGradient (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) :
    Continuous (fun x ↦ strainGradient modes (filteredVelocity chi u) x j) := by
  rw [← mappedField_strainGradient]
  exact continuous_mappedField _ _ _

theorem continuous_strainGradientSquare (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) : Continuous (strainGradientSquare chi modes u) :=
  continuous_finsetSum _ (fun j _ ↦ (continuous_strainGradient chi modes u j).norm.pow 2)

theorem continuous_parametric_strainGradientSquare {P : Type*} [TopologicalSpace P]
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : P → FourierVelocity)
    (hu : ∀ q ∈ modes, ∀ i, Continuous (fun p ↦ u p q i)) :
    Continuous (fun z : P × T3 ↦ strainGradientSquare chi modes (u z.1) z.2) :=
  continuous_finsetSum _ (fun j _ ↦ (continuous_parametric_strainGradient modes chi u j hu).norm.pow 2)

theorem strainGradientSquare_le_amplitude (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    strainGradientSquare chi modes u x ≤ 3 * strainGradientAmplitude modes chi u ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    pow_le_pow_left₀ (norm_nonneg _) (norm_strainGradient_le_amplitude modes chi u x j) 2)
  simpa only [strainGradientSquare, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalStrainGradientDensity
