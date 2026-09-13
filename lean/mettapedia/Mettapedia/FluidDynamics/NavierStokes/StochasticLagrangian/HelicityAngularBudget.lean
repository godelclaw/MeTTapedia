import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.HelicityAngularSource
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRegularizedHelicityBudget

/-!
# Spatial payment for the angular helicity source

The fourth-power-weighted absolute inviscid helicity source is charged to
the angular part of the eighth-moment dissipation and an explicit mixed
velocity-gradient integral. This is not a bound for the full weighted
material derivative, whose changing weight and viscous terms remain.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.HelicityAngularBudget

open scoped RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeDyadicDirectionEvolution PancakeBlockReality
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityEighthMoment
open GaussianRootWeightedIncrement LocalHelicityAbsorption
open Mettapedia.Analysis.EuclideanCrossProduct HelicityAngularSource

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def mixedGradientDensity (u : FourierVelocity) (x : T3) : ℝ :=
  ‖fullVorticity u x‖ ^ 4 * ∑ m : Fin 3, ‖realComponentGradient u m x‖ ^ 2

def mixedGradientCost (u : FourierVelocity) : ℝ := ∫ x : T3, mixedGradientDensity u x

def weightedSource (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ 4 *
    |⟪fullVorticity u x, LocalHelicitySourceEvolution.source u x⟫|

theorem continuous_realComponentGradient (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (m : Fin 3) : Continuous (realComponentGradient u m) := by
  have he : componentGradient u m = fun x : T3 ↦
      (fun j : Fin 3 ↦ fullFourierField id (indexedDerivativeCoeff id j u) x m) := by
    funext x j
    exact coordinateDerivative_fullFourierField id u
      (by simpa only [indexedFirstMoment_id] using hu) j x ▸ rfl
  unfold realComponentGradient
  rw [he]
  exact complexRealPartEuclideanCLM.continuous.comp (continuous_pi (fun j ↦
    (continuous_apply m).comp (fullFourierField id (indexedDerivativeCoeff id j u)).continuous))

theorem continuous_mixedGradientDensity (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (mixedGradientDensity u) :=
  ((continuous_fullVorticity u hu).norm.pow 4).mul
    (continuous_finsetSum _ (fun m _ ↦ ((continuous_realComponentGradient u hu m).norm.pow 2)))

theorem continuous_sourcePairing (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    Continuous (fun x : T3 ↦ ⟪fullVorticity u x, LocalHelicitySourceEvolution.source u x⟫) := by
  have hu1 := summable_firstMoment_of_second u hu
  have hw := continuous_fullVorticity u hu1
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have hc (m : Fin 3) : Continuous (fun x : T3 ↦ cross (fullVorticity u x) (fullCurlGradient u m x)) := by
    unfold cross
    fun_prop
  simp only [inner_vorticity_source u hu hd hr]
  exact (continuous_finsetSum _ (fun m _ ↦
    (continuous_realComponentGradient u hu1 m).inner (hc m))).const_mul 2

theorem weightedSource_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (η : ℝ) (hη : 0 < η) :
    weightedSource u ≤ η * (weightedPalinstrophy u - radialDissipation u) + mixedGradientCost u / η := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu
  have hu1 := summable_firstMoment_of_second u hu2
  have hS : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 4 *
      |⟪fullVorticity u x, LocalHelicitySourceEvolution.source u x⟫|) :=
    (((continuous_fullVorticity u hu1).norm.pow 4).mul
      (continuous_sourcePairing u hu2 hd hr).abs).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (weightedPalinstrophyDensity u) :=
    (continuous_weightedPalinstrophyDensity u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (radialGradientDensity u) :=
    (continuous_radialGradientDensity u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hM : Integrable (mixedGradientDensity u) :=
    (continuous_mixedGradientDensity u hu1).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hGR : Integrable (fun x : T3 ↦ weightedPalinstrophyDensity u x - radialGradientDensity u x) := by
    apply (hG.sub hR).congr
    filter_upwards with x
    rfl
  calc
    _ ≤ ∫ x : T3, η * (weightedPalinstrophyDensity u x - radialGradientDensity u x) +
        mixedGradientDensity u x / η := by
      apply integral_mono hS ((hGR.const_mul η).add (hM.div_const η))
      intro x
      exact (weighted_abs_source_le u hu2 hd hr x η hη).trans_eq (by
        unfold weightedPalinstrophyDensity radialGradientDensity mixedGradientDensity
        simp only [Pi.add_apply]
        ring)
    _ = _ := by
      rw [integral_add (hGR.const_mul η) (hM.div_const η), integral_const_mul,
        integral_sub hG hR, integral_div]
      rfl

end Mettapedia.FluidDynamics.NavierStokes.HelicityAngularBudget
