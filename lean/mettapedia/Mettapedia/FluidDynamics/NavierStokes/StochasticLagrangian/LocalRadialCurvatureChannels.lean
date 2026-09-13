import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialSolenoidal
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialMeanChannels
import Mettapedia.Analysis.RadialAmplitudeCurvature

/-!
# The actual radial curvature after solenoidal cancellation

The isotropic derivative channel is replaced, after integration, by a
background increment. The amplitude and unequal-endpoint channels remain
explicit. This is an exact decomposition of the signed viscous contribution
to the actual joint source rate, not an initial-data-controlled bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRadialCurvatureChannels

open MeasureTheory Mettapedia.Analysis EuclideanCrossProduct SignedCrossKernel RadialPower
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget LocalSpatialVorticityJets
open scoped RealInnerProductSpace
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def backgroundDensity (n N : ℕ) (u : FourierVelocity) (j : Fin 3) (x y : T3) : ℝ :=
  ⟪cross (fullCurlGradient u j x)
    (radialPower (2 * (n + 2)) (fullVorticity u y) -
      radialPower (2 * (n + 2)) (fullVorticity u x)),
    PeriodicRadialRiesz.tensor N (x - y) (fullCurlGradient u j x - fullCurlGradient u j y)⟫

def amplitudeDensity (n N : ℕ) (u : FourierVelocity) (j : Fin 3) (x y : T3) : ℝ :=
  amplitudeCurvature n (PeriodicRadialRiesz.tensor N (x - y))
    (fullVorticity u x) (fullCurlGradient u j x) (fullCurlGradient u j y)

def endpointDensity (n N : ℕ) (u : FourierVelocity) (j : Fin 3) (x y : T3) : ℝ :=
  endpointCurvatureRemainder n (PeriodicRadialRiesz.tensor N (x - y))
    (fullVorticity u x) (fullVorticity u y) (fullCurlGradient u j x) (fullCurlGradient u j y)

def channelSource (n N : ℕ) (u : FourierVelocity) (j : Fin 3) : ℝ :=
  (∫ x : T3, ∫ y : T3, backgroundDensity n N u j x y) +
    (1 / 2 : ℝ) * (∫ x : T3, ∫ y : T3, amplitudeDensity n N u j x y) +
    (1 / 2 : ℝ) * (∫ x : T3, ∫ y : T3, endpointDensity n N u j x y)

def reducedCurvatureSource (n N : ℕ) (u : FourierVelocity) : ℝ :=
  ∑ j : Fin 3, channelSource n N u j

theorem amplitudeDensity_eq_images (n N : ℕ) (u : FourierVelocity) (j : Fin 3)
    (x y : T3) (hxy : x ≠ y) :
    amplitudeDensity n N u j x y =
      ∑' z : UnitTorusLattice.LatticeSubmodule (ι := Fin 3),
        2 * (2 * (n + 2) : ℝ) * RadialRieszRegularization.radialCoefficient N
          (EuclideanSpace.single 0 1) (UnitTorusSchwartzLattice.displacement (x - y) z) *
          ‖fullVorticity u x‖ ^ (2 * (n + 1)) *
          ⟪fullVorticity u x, fullCurlGradient u j x - fullCurlGradient u j y⟫ *
          tripleProduct (fullCurlGradient u j x - fullCurlGradient u j y) (fullVorticity u x)
            (UnitTorusSchwartzLattice.displacement (x - y) z) *
          ⟪UnitTorusSchwartzLattice.displacement (x - y) z, fullVorticity u x⟫ :=
  (RadialPancakeCurvature.hasSum_amplitudeCurvature_images N n (EuclideanSpace.single 0 1)
    (by simp) (sub_ne_zero.mpr hxy) _ _ _).tsum_eq.symm

theorem continuous_backgroundDensity (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) :
    Continuous (backgroundDensity n N u j).uncurry := by
  have hw := continuous_fullVorticity u hu
  have hg := LocalSquaredGapGradient.continuous_fullCurlGradient u j
  have hq := (continuous_radialPower (2 * (n + 2))).comp hw
  exact (continuous_cross.comp ((hg.comp continuous_fst).prodMk
    ((hq.comp continuous_snd).sub (hq.comp continuous_fst)))).inner
      (((PeriodicRadialRiesz.continuous_tensor N).comp (continuous_fst.sub continuous_snd)).clm_apply
        ((hg.comp continuous_fst).sub (hg.comp continuous_snd)))

theorem continuous_amplitudeDensity (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) :
    Continuous (amplitudeDensity n N u j).uncurry :=
  continuous_amplitudeCurvature n
    ((PeriodicRadialRiesz.continuous_tensor N).comp (continuous_fst.sub continuous_snd))
    ((continuous_fullVorticity u hu).comp continuous_fst)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_fst)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_snd)

theorem continuous_endpointDensity (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) :
    Continuous (endpointDensity n N u j).uncurry :=
  continuous_endpointCurvatureRemainder n
    ((PeriodicRadialRiesz.continuous_tensor N).comp (continuous_fst.sub continuous_snd))
    ((continuous_fullVorticity u hu).comp continuous_fst)
    ((continuous_fullVorticity u hu).comp continuous_snd)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_fst)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_snd)

theorem integral_curvature_eq_channels (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) :
    (∫ x : T3, ∫ y : T3, pairedCurvature n (PeriodicRadialRiesz.tensor N (x - y))
      (fullVorticity u x) (fullVorticity u y) (fullCurlGradient u j x) (fullCurlGradient u j y)) =
      2 * (∫ x : T3, ∫ y : T3, backgroundDensity n N u j x y) +
        (∫ x : T3, ∫ y : T3, amplitudeDensity n N u j x y) +
        (∫ x : T3, ∫ y : T3, endpointDensity n N u j x y) :=
  SolenoidalCrossIncrement.integral_pairedCurvature_eq_channels n _
    (PeriodicRadialRiesz.continuous_tensor N) (PeriodicRadialRiesz.tensor_neg N)
    (PeriodicRadialRiesz.integral_tensor_eq_zero N) _ _
    (continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
    (LocalRadialSolenoidal.integral_tensor_fullCurlGradient_eq_zero N u hu j)

theorem curvatureSource_eq_reducedCurvatureSource (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    LocalRadialMeanChannels.curvatureSource n N u = reducedCurvatureSource n N u := by
  let f (j : Fin 3) (x y : T3) := pairedCurvature n (PeriodicRadialRiesz.tensor N (x - y))
    (fullVorticity u x) (fullVorticity u y) (fullCurlGradient u j x) (fullCurlGradient u j y)
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hf (j : Fin 3) : Continuous (f j).uncurry := continuous_pairedCurvature n
    ((PeriodicRadialRiesz.continuous_tensor N).comp (continuous_fst.sub continuous_snd))
    (hw.comp continuous_fst) (hw.comp continuous_snd)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_fst)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_snd)
  have hi (j : Fin 3) : Integrable (f j).uncurry ((volume : Measure T3).prod volume) :=
    (hf j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr (j : Fin 3) (x : T3) : Integrable (f j x) :=
    ((hf j).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have ho (j : Fin 3) : Integrable (fun x : T3 ↦ ∫ y : T3, f j x y) :=
    (hi j).integral_prod_left
  change (1 / 2 : ℝ) * (∫ x : T3, ∫ y : T3, ∑ j : Fin 3, f j x y) = _
  have he (x : T3) : (∫ y : T3, ∑ j : Fin 3, f j x y) =
      ∑ j : Fin 3, ∫ y : T3, f j x y := integral_finsetSum _ (fun j _ ↦ hr j x)
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ ↦ ho j), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [f]
  rw [integral_curvature_eq_channels n N u hu j]
  unfold channelSource
  ring

theorem jointRate_eq_reduced_channels (n N : ℕ) (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    LocalRadialMeanChannels.jointRate n N nu u =
      (∫ x : T6, LocalRadialMeanChannels.nonviscousRate n N u x) -
        nu * reducedCurvatureSource n N u := by
  rw [LocalRadialMeanChannels.jointRate, curvatureSource_eq_reducedCurvatureSource n N u hu]

end Mettapedia.FluidDynamics.NavierStokes.LocalRadialCurvatureChannels
