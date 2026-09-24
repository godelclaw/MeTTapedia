import Mettapedia.Analysis.RadialPancakeCoherence
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialImageEvolution

/-!
# Plane-defect control of the actual coherent radial image rate

The full velocity gradient is used. Its skew part cancels from the normal
pairing; the symmetric part is the actual strain. Each image retains its
own separation and coefficient derivative. The geometric defects below are
constructed from those fields, not assumed small or time-integrable.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRadialCoherentBound

open PeriodicFourierTriad PancakeCurlOutputTail PancakeFourierMaterialPaths
open PancakeLocalGradientEquation PancakeLocalStrainEquation PancakeFilteredStrainDynamics
open PancakeInfiniteFourierDerivative
open LocalAlignmentForcing LocalLowDiffusionBudget LocalVorticitySeparation LocalRadialImageEvolution
open Mettapedia.Analysis RadialPancakeCoherence RadialPower EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

theorem inner_gradient_add_inner_gradient (u : FourierVelocity) (x : T3) (h v : R3) :
    ⟪gradient u x h, v⟫ + ⟪h, gradient u x v⟫ = 2 * ⟪fullStrainOperator u x h, v⟫ := by
  change ⟪realMatrixOperator (spatialVelocityGradient (fullFourierField id u) x) h, v⟫ +
    ⟪h, realMatrixOperator (spatialVelocityGradient (fullFourierField id u) x) v⟫ = _
  simp only [fullStrainOperator, PancakeLocalStrainEquation.spatialStrain, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, dotProduct, Fin.sum_univ_three, realMatrixOperator_apply, symmetrize,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    smul_eq_mul, Complex.mul_re, Complex.add_re]
  norm_num
  ring

theorem abs_inner_gradient_le (u : FourierVelocity) (x : T3) (a : R3) :
    |⟪a, gradient u x a⟫| ≤ ‖fullStrainOperator u x‖ * ‖a‖ ^ 2 := by
  have h := inner_gradient_add_inner_gradient u x a a
  have he : ⟪a, gradient u x a⟫ = ⟪a, fullStrainOperator u x a⟫ := by
    linarith only [h, real_inner_comm (gradient u x a) a,
      real_inner_comm (fullStrainOperator u x a) a]
  rw [he]
  exact (abs_real_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left
    ((fullStrainOperator u x).le_opNorm a) (norm_nonneg a)).trans_eq (by ring))

def normalDefect (u : FourierVelocity) (x : T3) (σ : ℝ) (h : R3) : R3 :=
  fullStrainOperator u x h - σ • h

theorem symmetric_normal_action (u : FourierVelocity) (x : T3) (σ : ℝ) (h v : R3) :
    ⟪gradient u x h, v⟫ + ⟪h, gradient u x v⟫ =
      2 * ⟪σ • h + normalDefect u x σ h, v⟫ := by
  rw [normalDefect, add_sub_cancel, inner_gradient_add_inner_gradient]

def coherentCost (n N : ℕ) (z : R3) (u : FourierVelocity) (x y : X3) (σ : ℝ) : ℝ :=
  let a := fullVorticity u (torusPoint x)
  let b := fullVorticity u (torusPoint y)
  let h := imageSeparation z x y
  |tripleProduct a b h| *
    ((|coefficientRate N z u x y| + |coefficient N z x y| *
      (2 * |σ| + (2 * (n + 1) : ℝ) * ‖fullStrainOperator u (torusPoint x)‖)) *
        normalMoment (2 * (n + 1)) a b h +
      2 * |coefficient N z x y| * ‖normalDefect u (torusPoint x) σ h‖ *
        ‖radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b‖)

theorem abs_coherent_rate_le (n N : ℕ) (z : R3) (u : FourierVelocity) (x y : X3) (σ : ℝ) :
    |kernelTransport n N z u x y + commonDeformation n N z u x y| ≤
      coherentCost n N z u x y σ :=
  RadialPancakeCoherence.abs_coherentRate_le n (gradient u (torusPoint x))
    (coefficient N z x y) (coefficientRate N z u x y)
    (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (imageSeparation z x y)
    (normalDefect u (torusPoint x) σ (imageSeparation z x y)) σ ‖fullStrainOperator u (torusPoint x)‖
    (symmetric_normal_action u (torusPoint x) σ (imageSeparation z x y))
    (abs_inner_gradient_le u (torusPoint x) _) (abs_inner_gradient_le u (torusPoint x) _)

/-- The noncoherent and viscous contributions remain signed and grouped. -/
theorem materialRate_le_coherentCost_add_signed_remainder (n N : ℕ) (z : R3)
    (u : FourierVelocity) (nu : ℝ) (x y : X3) (σ : ℝ) :
    materialRate n N z u nu x y ≤ coherentCost n N z u x y σ +
      nonviscousImageRate n N z u x y + nu * viscousImageRate n N z u x y := by
  exact add_le_add (add_le_add
    ((le_abs_self _).trans (abs_coherent_rate_le n N z u x y σ)) le_rfl) le_rfl

theorem coherent_rate_eq_zero_of_plane (n N : ℕ) (z : R3) (u : FourierVelocity)
    (x y : X3) (σ : ℝ)
    (he : fullStrainOperator u (torusPoint x) (imageSeparation z x y) = σ • imageSeparation z x y)
    (ha : ⟪imageSeparation z x y, fullVorticity u (torusPoint x)⟫ = 0)
    (hb : ⟪imageSeparation z x y, fullVorticity u (torusPoint y)⟫ = 0) :
    kernelTransport n N z u x y + commonDeformation n N z u x y = 0 := by
  apply RadialPancakeCoherence.coherentRate_eq_zero_of_plane n (gradient u (torusPoint x))
    (coefficient N z x y) (coefficientRate N z u x y) _ _ _ σ _ ha hb
  intro v
  rw [inner_gradient_add_inner_gradient, he]

end Mettapedia.FluidDynamics.NavierStokes.LocalRadialCoherentBound
