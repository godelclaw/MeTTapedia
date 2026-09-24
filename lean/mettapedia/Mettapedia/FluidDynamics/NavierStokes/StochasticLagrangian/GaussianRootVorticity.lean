import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalGaussianPressurePartition
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.QuarticGapTiltWeight
import Mettapedia.Analysis.RadialSquareRoot
import Mettapedia.Analysis.LocallyLipschitzComposition

/-!
# Square-root patches multiplied by the actual vorticity

The extra gap ramp is outside the square root. The vorticity factor repairs
the radial square-root singularity at zero. The resulting fields are locally
Lipschitz, although no such claim is made for the scalar root patches alone.
Their fourth-power weights recover the quartic-gated pressure weight exactly.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootVorticity

open scoped BigOperators
open Mettapedia.Analysis.RadialSquareRoot Mettapedia.Analysis.GaussianPartitionEnergy
open Mettapedia.Analysis.EuclideanOperatorCoordinates Mettapedia.Analysis.FiniteExponentialWeights
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeSpectralFiniteDifference
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open LocalLowDiffusionBudget LocalSquaredGapPressure LocalGaussianPressurePartition
open SpectralGapTiltWeight GapTruncatedProjector

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

def rootGapFactor (gamma : ℝ) (S : SymmetricStrain) : ℝ :=
  gapCutoff gamma (topGap S) / Real.sqrt (max (topGap S) gamma)

def gaussianFactor (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x : T3) : ℝ :=
  gaussianAmplitude (fun j : ↑centers ↦ coordinates (localProjector gamma chi modes u j.1)) tau
    (coordinates (localProjector gamma chi modes u x)) i

def rootPatch (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x : T3) : ℝ :=
  rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x) *
    Real.sqrt ‖fullVorticity u x‖ * Real.sqrt (gaussianFactor gamma chi modes u centers tau i x)

def rootVorticity (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x : T3) : R3 :=
  rootPatch gamma chi modes u centers tau i x • fullVorticity u x

def rootFieldFactor (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x : T3) : ℝ :=
  rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x) *
    Real.sqrt (gaussianFactor gamma chi modes u centers tau i x)

theorem rootVorticity_eq_factor (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x : T3) :
    rootVorticity gamma chi modes u centers tau i x =
      (rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x) *
        Real.sqrt (gaussianFactor gamma chi modes u centers tau i x)) • radialSqrt (fullVorticity u x) := by
  simp only [rootVorticity, rootPatch, radialSqrt, smul_smul]
  congr 1
  ring

theorem locallyLipschitz_topGap : LocallyLipschitz (topGap : SymmetricStrain → ℝ) := by
  have h : LipschitzWith 6 (topGap : SymmetricStrain → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro A B
    simpa only [Real.dist_eq, Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_ofNat] using abs_topGap_sub_le A B
  exact h.locallyLipschitz

theorem locallyLipschitz_gapCutoff (gamma : ℝ) (hg : 0 < gamma) :
    LocallyLipschitz (gapCutoff gamma) := by
  have h : LipschitzWith ⟨gamma⁻¹, inv_nonneg.mpr hg.le⟩ (gapCutoff gamma) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    change |gapCutoff gamma a - gapCutoff gamma b| ≤ gamma⁻¹ * |a - b|
    simpa only [div_eq_mul_inv, mul_comm] using abs_gapCutoff_sub_le gamma hg a b
  exact h.locallyLipschitz

theorem locallyLipschitz_rootGapFactor (gamma : ℝ) (hg : 0 < gamma) :
    LocallyLipschitz (rootGapFactor gamma) := by
  have hm := locallyLipschitz_topGap.max_const gamma
  have hpos (S : SymmetricStrain) : 0 < max (topGap S) gamma := hg.trans_le (le_max_right _ _)
  exact ((locallyLipschitz_gapCutoff gamma hg).comp locallyLipschitz_topGap).div_real
    (hm.sqrt (fun S ↦ ne_of_gt (hpos S))) (fun S ↦ ne_of_gt (Real.sqrt_pos.mpr (hpos S)))

theorem gaussianFactor_pos (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) (x : T3) : 0 < gaussianFactor gamma chi modes u centers tau i x := by
  letI : Nonempty ↑centers := ⟨⟨hc.choose, hc.choose_spec⟩⟩
  exact amplitude_pos _ i

theorem patch_eq_amplitude_mul_gaussianFactor (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x : T3) :
    patch gamma chi modes u centers tau i x =
      localAmplitude gamma chi modes u x * gaussianFactor gamma chi modes u centers tau i x := by
  have hn : ‖coordinates (localProjector gamma chi modes u x)‖ = localAmplitude gamma chi modes u x := by
    rw [localProjector_eq gamma hg]
    exact GaussianWeightedLinePartition.norm_coordinateProjector _
      (SquaredGapTiltWeight.amplitude_nonneg gamma hg _ _) _ (topVector_norm _)
  simp only [patch, normScaledAmplitude, hn, gaussianFactor]

theorem rootPatch_sq_eq_gated_patch (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (i : ↑centers) (x : T3) :
    rootPatch gamma chi modes u centers tau i x ^ 2 =
      gapCutoff gamma (topGap (spatialStrain modes (filteredVelocity chi u) x)) *
        patch gamma chi modes u centers tau i x := by
  rw [patch_eq_amplitude_mul_gaussianFactor gamma hg]
  have hm : 0 ≤ max (topGap (spatialStrain modes (filteredVelocity chi u) x)) gamma :=
    (hg.trans_le (le_max_right _ _)).le
  simp only [rootPatch, rootGapFactor, mul_pow, div_pow, Real.sq_sqrt hm,
    Real.sq_sqrt (norm_nonneg _), Real.sq_sqrt (gaussianFactor_pos gamma chi modes u centers hc tau i x).le,
    localAmplitude, SquaredGapTiltWeight.amplitude]
  ring

theorem locallyLipschitz_rootFieldFactor (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) :
    LocallyLipschitz (fun r : X3 ↦ rootFieldFactor gamma chi modes u centers tau i (torusPoint r)) := by
  letI : Nonempty ↑centers := ⟨⟨hc.choose, hc.choose_spec⟩⟩
  have hS : LocallyLipschitz (fun r : X3 ↦ spatialStrain modes (filteredVelocity chi u) (torusPoint r)) :=
    fun r ↦ (LocalSpatialBottomProjector.contDiff_spatialStrain (n := 1) chi modes u).locallyLipschitz r
  have hM := (coordinates (ι := Fin 3)).lipschitz.locallyLipschitz.comp
    (locallyLipschitz_localProjector gamma hg chi modes u hu)
  have htheta := (contDiff_gaussianAmplitude
    (fun j : ↑centers ↦ coordinates (localProjector gamma chi modes u j.1)) tau i 1).locallyLipschitz.comp hM
  have hroot := htheta.sqrt (fun r ↦ ne_of_gt (gaussianFactor_pos gamma chi modes u centers hc tau i (torusPoint r)))
  simpa only [rootFieldFactor, Function.comp_def, gaussianFactor] using
    ((locallyLipschitz_rootGapFactor gamma hg).comp hS).mul_algebra hroot

theorem locallyLipschitz_rootVorticity (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) :
    LocallyLipschitz (fun r : X3 ↦ rootVorticity gamma chi modes u centers tau i (torusPoint r)) := by
  have hw := locallyLipschitz_radialSqrt.comp (LocalAlignmentTransport.locallyLipschitz_fullVorticity u hu)
  simpa only [rootVorticity_eq_factor, rootFieldFactor, Function.comp_def] using
    (locallyLipschitz_rootFieldFactor gamma hg chi modes u hu centers hc tau i).smul_real hw

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootVorticity
