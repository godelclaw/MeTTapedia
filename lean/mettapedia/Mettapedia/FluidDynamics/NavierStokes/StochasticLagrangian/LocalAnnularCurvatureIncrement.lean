import Mettapedia.Analysis.SignedCrossKernelCurvatureIncrement
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityNegation

/-!
# Gradient increments in the actual annular curvature

Equal endpoint vorticities leave an explicit gradient-increment channel.
Negating all velocity coefficients reverses the spatially integrated
curvature, with the actual kernel unchanged. No claim of nonzero curvature
for a particular fluid field or of a uniform budget is made here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularCurvatureIncrement

open MeasureTheory Mettapedia.Analysis SignedCrossKernel
open PeriodicFourierTriad LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalAnnularDiffusion LocalVorticityNegation
open scoped RealInnerProductSpace

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem curvatureDensity_of_equal_vorticity (n N : ℕ) (u : FourierVelocity) (x y : T3)
    (h : fullVorticity u x = fullVorticity u y) :
    curvatureDensity n N u x y = ∑ j : Fin 3,
      2 * ⟪EuclideanCrossProduct.cross (fullCurlGradient u j x - fullCurlGradient u j y)
          (fullVorticity u x),
        PeriodicRieszPolynomial.kernel N (x - y)
          (RadialPower.evenRadialRate (n + 1) (fullVorticity u x)
            (fullCurlGradient u j x - fullCurlGradient u j y))⟫ := by
  simp only [curvatureDensity, ← h, pairedCurvature_same_value]

theorem abs_curvatureDensity_of_equal_vorticity_le (N : ℕ) (u : FourierVelocity) (x y : T3)
    (h : fullVorticity u x = fullVorticity u y) :
    |curvatureDensity 1 N u x y| ≤ ∑ j : Fin 3,
      14 * ‖fullVorticity u x‖ ^ 6 *
        ‖EuclideanCrossProduct.cross (fullCurlGradient u j x - fullCurlGradient u j y)
          (fullVorticity u x)‖ * ‖PeriodicRieszPolynomial.kernel N (x - y)‖ *
        ‖fullCurlGradient u j x - fullCurlGradient u j y‖ := by
  unfold curvatureDensity
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ ↦ ?_))
  rw [← h]
  have hh := abs_pairedCurvature_same_value_le 1 (PeriodicRieszPolynomial.kernel N (x - y))
    (fullVorticity u x) (fullCurlGradient u j x) (fullCurlGradient u j y)
  norm_num at hh
  exact hh

theorem curvatureDensity_neg (n N : ℕ) (u : FourierVelocity) (x y : T3) :
    curvatureDensity n N (-u) x y = -curvatureDensity n N u x y := by
  simp only [curvatureDensity, fullVorticity_neg, fullCurlGradient_neg,
    pairedCurvature_neg_all, Finset.sum_neg_distrib]

theorem curvatureSource_neg (n N : ℕ) (u : FourierVelocity) :
    curvatureSource n N (-u) = -curvatureSource n N u := by
  simp only [curvatureSource, curvatureDensity_neg, integral_neg]
  ring

theorem curvatureSource_eq_zero_of_nonneg (n N : ℕ)
    (h : ∀ u : FourierVelocity, 0 ≤ curvatureSource n N u) (u : FourierVelocity) :
    curvatureSource n N u = 0 := by
  have hn := h (-u)
  rw [curvatureSource_neg] at hn
  exact le_antisymm (by linarith) (h u)

theorem curvatureSource_eq_zero_of_nonneg_on_neg_closed (n N : ℕ) (A : Set FourierVelocity)
    (hneg : ∀ u ∈ A, -u ∈ A) (h : ∀ u ∈ A, 0 ≤ curvatureSource n N u)
    (u : FourierVelocity) (hu : u ∈ A) : curvatureSource n N u = 0 := by
  have hn := h (-u) (hneg u hu)
  rw [curvatureSource_neg] at hn
  exact le_antisymm (by linarith) (h u hu)

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularCurvatureIncrement
