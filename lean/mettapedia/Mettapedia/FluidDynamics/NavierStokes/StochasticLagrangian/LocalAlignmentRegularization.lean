import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalInitialAlignmentBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.RegularizedSpectralEnergySplitting

/-!
# Regularization bookkeeping for the actual full-vorticity fields

The extra energy is exactly the regularizer times spatial enstrophy.
Its material derivative includes full-strain stretching and viscosity.
In particular, regularization does not supply enstrophy control without
accounting for the extra stretching retained in the signed source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentRegularization

open scoped RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths PancakeLocalMaterialTrajectories
open PancakeLocalSpatialVelocity PancakeRegularizedMaterialRate
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentTransport
open LocalAlignmentForcing LocalSignedAlignmentBudget LocalMeanAlignmentBalance
open RegularizedSpectralEnergySplitting

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def vorticityNormRate (u : FourierVelocity) (nu : ℝ) (x : T3) : ℝ :=
  2 * ⟪fullVorticity u x,
    fullStrainOperator u x (fullVorticity u x) + nu • fullVorticityLaplacian u x⟫

theorem materialRate_eq_zero_add (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) :
    materialRate chi modes outputs u delta nu x =
      materialRate chi modes outputs u 0 nu x + delta * vorticityNormRate u nu x := by
  unfold materialRate
  rw [linearRate_eq_zero_add]
  simp only [resolved_add_strainMismatch, vorticityNormRate]
  ring

theorem signedForcingEnvelope_eq_zero_add (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) :
    signedForcingEnvelope chi modes outputs u delta x =
      signedForcingEnvelope chi modes outputs u 0 x +
        2 * delta * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫ := by
  simp only [signedForcingEnvelope, mul_zero, zero_mul, add_zero]

theorem meanEnergy_eq_zero_add (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta : ℝ) :
    meanEnergy chi modes u delta = meanEnergy chi modes u 0 +
      delta * ∫ x : T3, ‖fullVorticity u x‖ ^ 2 := by
  have hA : Integrable (alignmentEnergy chi modes u 0) :=
    (continuous_alignmentEnergy chi modes u hu 0).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hw : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 2) :=
    ((continuous_fullVorticity u hu).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (x : T3) : alignmentEnergy chi modes u delta x =
      alignmentEnergy chi modes u 0 x + delta * ‖fullVorticity u x‖ ^ 2 :=
    regularizedEnergy_eq_zero_add _ delta _
  unfold meanEnergy
  simp_rw [he]
  rw [integral_add hA (hw.const_mul delta), integral_const_mul]

/-- The extra material rate is the derivative of actual squared vorticity,
with only instantaneous tangency required of the path. -/
theorem hasDerivAt_norm_fullVorticity_sq_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t) :
    HasDerivAt (fun τ ↦ ‖fullVorticity (s.coefficients τ) (torusPoint (X τ))‖ ^ 2)
      (vorticityNormRate (s.coefficients t) nu (torusPoint (X t))) t := by
  have hw := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  simpa only [real_inner_self_eq_norm_sq, vorticityNormRate, two_mul, real_inner_comm]
    using hw.inner ℝ hw

end Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentRegularization
