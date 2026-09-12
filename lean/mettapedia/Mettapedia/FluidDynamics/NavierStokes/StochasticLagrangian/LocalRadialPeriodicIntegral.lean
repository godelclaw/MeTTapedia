import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialPeriodicEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpaceTimeExtension
import Mettapedia.Analysis.SignedCrossKernelRegularity

/-!
# Time identity for the complete periodic signed pairing

For fixed cutoff the full periodic pairing is absolutely continuous along
the actual material paths. Its increment is the time integral of the sum
of all signed image rates. This includes coincident endpoints and requires
no chosen representative to be differentiable. The image sum is inside
the integral; a termwise time-integral exchange is not asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRadialPeriodicIntegral

open MeasureTheory
open PeriodicFourierTriad PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakeCurlOutputTail PancakeFourierMaterialPaths PancakeLocalMaterialTrajectories
open LocalLowDiffusionBudget LocalRadialPeriodicEvolution
open Mettapedia.Analysis SignedCrossKernel UnitTorusLattice UnitTorusPeriodization
local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Lat" => LatticeSubmodule (ι := Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem torusPoint_representative (x : T3) : torusPoint (WithLp.ofLp (representative x)) = x :=
  torusProjection_representative x

/-- This is a snapshot identity, not a derivative of the representative. -/
theorem source_eq_integral_periodicDensity (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    VorticityRadialSource.source (2 * (n + 1)) N u =
      (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3, periodicDensity n N u
        (WithLp.ofLp (representative x)) (WithLp.ofLp (representative y)) := by
  rw [VorticityRadialPairing.source_eq_pairedSource _ N u hu]
  simp only [VorticityRadialPairing.pairedSource, periodicDensity, torusPoint_representative]

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : PeriodicFourierTriad.Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (X Y : ℝ → X3) (hX : LocallyLipschitz X) (hY : LocallyLipschitz Y)

include hg hSum hu hab hI hX hY

theorem absolutelyContinuousOnInterval_periodicDensity_path (n N : ℕ) :
    AbsolutelyContinuousOnInterval
      (fun τ ↦ periodicDensity n N (s.coefficients τ) (X τ) (Y τ)) a b := by
  let w : ℝ × X3 → R3 := fun p ↦
    fullVorticity (LocalSpaceTimeExtension.coefficients s a b hab p.1) (torusPoint p.2)
  have hw : LocallyLipschitz w :=
    LocalSpaceTimeExtension.locallyLipschitz_fullVorticity s a b hab hI g hg hSum hu
  have hx : LocallyLipschitz (fun τ ↦ w (τ, X τ)) :=
    hw.comp (g := fun τ ↦ (τ, X τ)) (LocallyLipschitz.id.prodMk hX)
  have hy : LocallyLipschitz (fun τ ↦ w (τ, Y τ)) :=
    hw.comp (g := fun τ ↦ (τ, Y τ)) (LocallyLipschitz.id.prodMk hY)
  have hkernel : LocallyLipschitz (fun τ ↦
      PeriodicRadialRiesz.tensor N (torusPoint (X τ) - torusPoint (Y τ))) := by
    have hk := (PeriodicRadialRiesz.contDiff_one_tensor_lift (d := 3) N).locallyLipschitz
    let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
    have hsep : LocallyLipschitz (fun τ ↦ LocalVorticitySeparation.separation (X τ) (Y τ)) :=
      L.lipschitz.locallyLipschitz.comp (g := fun τ ↦ X τ - Y τ) (hX.sub hY)
    simpa only [Function.comp_def, torusProjection_separation] using hk.comp hsep
  have hac := AbsolutelyContinuousComposition.of_locallyLipschitz
    (a := a) (b := b) (locallyLipschitz_pairedStretch_even (n + 1) hkernel hx hy)
  apply AbsolutelyContinuousComposition.congr hac
  intro τ hτ
  have hm : τ ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hτ
  simp only [periodicDensity, w, LocalSpaceTimeExtension.coefficients_eq s a b hab τ hm]

theorem integrated_periodicDensity_imageSum
    (hDX : ∀ t ∈ Set.Ioo a b, HasDerivAt X (liftedVelocity s t (X t)) t)
    (hDY : ∀ t ∈ Set.Ioo a b, HasDerivAt Y (liftedVelocity s t (Y t)) t) (n N : ℕ) :
    IntervalIntegrable (fun τ ↦ ∑' z : Lat, LocalRadialImageEvolution.materialRate n N (z : R3)
      (s.coefficients τ) nu (X τ) (Y τ)) volume a b ∧
      (∫ τ in a..b, ∑' z : Lat, LocalRadialImageEvolution.materialRate n N (z : R3)
        (s.coefficients τ) nu (X τ) (Y τ)) =
        periodicDensity n N (s.coefficients b) (X b) (Y b) -
          periodicDensity n N (s.coefficients a) (X a) (Y a) := by
  have hac := absolutelyContinuousOnInterval_periodicDensity_path s g hg hSum hu a b hab hI X Y hX hY n N
  have heq : ∀ᵐ t, t ∈ Set.uIcc a b →
      deriv (fun τ ↦ periodicDensity n N (s.coefficients τ) (X τ) (Y τ)) t =
        ∑' z : Lat, LocalRadialImageEvolution.materialRate n N (z : R3)
          (s.coefficients t) nu (X t) (Y t) := by
    filter_upwards [(Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))] with t he hmem
    have hm : t ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hmem
    have ht : t ∈ Set.Ioo a b := he.mpr hm
    exact (hasDerivAt_periodicDensity_imageSum s g hg hSum hu a b hab hI X Y t ht
      (hDX t ht) (hDY t ht) n N).deriv
  refine ⟨hac.intervalIntegrable_deriv.congr_ae ?_, ?_⟩
  · apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [heq] with t ht hmem
    exact ht (Set.uIoc_subset_uIcc hmem)
  · rw [← hac.integral_deriv_eq_sub]
    symm
    apply intervalIntegral.integral_congr_ae
    filter_upwards [heq] with t ht hmem
    exact ht (Set.uIoc_subset_uIcc hmem)

end Mettapedia.FluidDynamics.NavierStokes.LocalRadialPeriodicIntegral
