import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalBottomEnergy

/-!
# Spatial integrability on bottom-gap-separated regions

The actual projector energy and signed source are continuous wherever the
bottom gap is positive. On each closed positive-gap region they are
integrable. This supplies spatial measurability without selecting a
measurable eigenbasis; it does not make the bounds uniform as the gap
threshold tends to zero or time approaches a singular endpoint.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalBottomEnergyRegularity

open scoped RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeSpectralProjectorRegularity
open PancakeSpectralClusterDichotomy.SymmetricStrain StrainEigenvalueContinuity
open LocalLowDiffusionBudget LocalAlignmentForcing LocalClusterAnisotropy LocalClusterMaterialRate
open LocalBottomEnergy BottomProjectorMotion
open PancakeMaterialDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuousAt_bottomProjector_of_gap_pos (S : SymmetricStrain) (hg : 0 < bottomGap S) :
    ContinuousAt bottomEigenlineProjector S := by
  have h := (continuousAt_const (y := ContinuousLinearMap.id ℝ R3)).sub
    (continuousAt_expandingPlaneProjector_of_bottomGap_pos S hg)
  simpa only [expandingPlaneProjector, sub_sub_cancel] using h

theorem continuousAt_energy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    ContinuousAt (energy chi modes u) x := by
  have hS := (continuous_strain modes (filteredVelocity chi u)).continuousAt (x := x)
  have hP := (continuousAt_bottomProjector_of_gap_pos _ hg).comp hS
  exact (hP.clm_apply (continuous_fullVorticity u hu).continuousAt).norm.pow 2

theorem continuousAt_source (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (nu : ℝ) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    ContinuousAt (source chi modes outputs u nu) x := by
  have hu1 := PancakeHigherDerivativeMoments.summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hS := (continuous_strain modes (filteredVelocity chi u)).continuousAt (x := x)
  have hP := (continuousAt_bottomProjector_of_gap_pos _ hg).comp hS
  have hQ := (continuousAt_expandingPlaneProjector_of_bottomGap_pos _ hg).comp hS
  have hR := (continuous_jointRemainder chi modes outputs u nu).continuousAt (x := x)
  have hK := (hQ.mul hR).mul hP
  have hw := (continuous_fullVorticity u hu1).continuousAt (x := x)
  have hf := (continuous_strainMismatch chi modes u hu1).continuousAt (x := x)
  have hd := (continuous_fullVorticityLaplacian u hu).continuousAt (x := x)
  have hgap := continuous_bottomGap.continuousAt.comp hS
  exact (continuousAt_const.mul ((hP.clm_apply hw).inner (hf.add (continuousAt_const.smul hd)))).add
    (((continuousAt_const.mul (hK.norm.pow 2)).div (hgap.pow 3) (pow_ne_zero 3 (ne_of_gt hg))).mul
      ((hQ.clm_apply hw).norm.pow 2))

def gapRegion (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (eta : ℝ) : Set T3 :=
  {x | eta ≤ bottomGap (spatialStrain modes (filteredVelocity chi u) x)}

theorem isCompact_gapRegion (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (eta : ℝ) : IsCompact (gapRegion chi modes u eta) :=
  (isClosed_le continuous_const (continuous_bottomGap.comp (continuous_strain modes (filteredVelocity chi u)))).isCompact

theorem integrableOn_energy_gapRegion (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (eta : ℝ) (heta : 0 < eta) :
    IntegrableOn (energy chi modes u) (gapRegion chi modes u eta) := by
  have h : ContinuousOn (energy chi modes u) (gapRegion chi modes u eta) := fun x hx ↦
    (continuousAt_energy chi modes u hu x (lt_of_lt_of_le heta hx)).continuousWithinAt
  exact h.integrableOn_compact (isCompact_gapRegion chi modes u eta)

theorem integrableOn_source_gapRegion (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (nu eta : ℝ) (heta : 0 < eta) :
    IntegrableOn (source chi modes outputs u nu) (gapRegion chi modes u eta) := by
  have h : ContinuousOn (source chi modes outputs u nu) (gapRegion chi modes u eta) := fun x hx ↦
    (continuousAt_source chi modes outputs u hu nu x (lt_of_lt_of_le heta hx)).continuousWithinAt
  exact h.integrableOn_compact (isCompact_gapRegion chi modes u eta)

end Mettapedia.FluidDynamics.NavierStokes.LocalBottomEnergyRegularity
