import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFourierParseval
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalLowFrequencyBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityDiffusion

/-!
# Fixed-low diffusion cost against the full actual vorticity

Only the strain is filtered. The receiver is the ordinary spatial curl of
the full infinite velocity, and Parseval pays its entire spatial energy.
The actual unforced energy-squared identity supplies the time integral.
No closed finite-mode evolution or independent enstrophy budget is assumed.

The cutoff weight and inverse regularization parameter remain explicit.
The result does not bound the high-strain mismatch or justify removing
the strain cutoff or the regularization.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalLowDiffusionBudget

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy
open PancakeFourierStrainGradient PancakeFilteredStrainDynamics
open PancakeSpatialStrainEvolution PancakeLowDiffusionBudget
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeCurlOutputTail
open InfiniteConvectionEnergy InfiniteKineticCancellation InfiniteFourierParseval
open LocalLowFrequencyBudget LocalKineticEnergy LocalVorticityDiffusion
open PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity PancakeTransverseEnergyFreezing
open PancakeDyadicDirectionEvolution PancakeHigherDerivativeMoments
open PancakePeriodicComplexStretch

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Ordinary spatial curl, in real Euclidean coordinates. -/
def fullVorticity (u : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (spatialCurl (fullFourierField id u) x)

def lowDiffusionDensity (modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) : ℝ :=
  (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2) *
    ‖fullVorticity u x‖ ^ 2

theorem continuous_fullVorticity (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (fullVorticity u) := by
  unfold fullVorticity
  rw [spatialCurl_velocity u hu]
  exact complexRealPartEuclideanCLM.continuous.comp (fullFourierField id _).continuous

theorem integral_norm_fullVorticity_sq_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T3, ‖fullVorticity u x‖ ^ 2) ≤ kineticEnergy (fourierCurl u) :=
  integral_norm_spatialCurl_sq_le u hu

theorem integral_lowDiffusionDensity_le (modes : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T3, lowDiffusionDensity modes chi u x) ≤
      strainGradientCutoffWeight modes chi * kineticEnergy u * kineticEnergy (fourierCurl u) := by
  have hE := fullEnergy_le_kineticEnergy modes u
    (summable_coefficientEnergy u (summable_amplitude u hu))
  have hK := strainGradientCutoffWeight_nonneg modes chi
  have hp (x : T3) : lowDiffusionDensity modes chi u x ≤
      (strainGradientCutoffWeight modes chi * kineticEnergy u) * ‖fullVorticity u x‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (sum_norm_strainGradient_sq_le modes modes chi u x (fun _ h ↦ h)).trans
      (mul_le_mul_of_nonneg_left hE hK)
  have hi : Integrable (fun x : T3 ↦
      (strainGradientCutoffWeight modes chi * kineticEnergy u) * ‖fullVorticity u x‖ ^ 2) volume :=
    ((continuous_const.mul ((continuous_fullVorticity u hu).norm.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hm := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x : T3 ↦ by
    dsimp only [lowDiffusionDensity]
    positivity)) hi (Filter.Eventually.of_forall hp)
  rw [integral_const_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (integral_norm_fullVorticity_sq_le u hu)
    (mul_nonneg hK (kineticEnergy_nonneg u)))

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-- A common second moment makes the full curl jointly continuous through
both endpoints of the local time interval. -/
theorem continuous_fullVorticity_spaceTime (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ fullVorticity (s.coefficients z.1) z.2) := by
  have hc : Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      fullFourierField id (fourierCurl (s.coefficients t))) := by
    refine continuous_fullFourierField_of_norm_le _ ?_ (fun q ↦ (2 * Real.pi) * g q)
      (hSum.mul_left _) ?_
    · intro q i
      have hc (j : Fin 3) : Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q j) :=
        (s.continuous q j).comp continuous_subtype_val
      fin_cases i <;> simp only [fourierCurl, coefficientCross, Pi.smul_apply, smul_eq_mul] <;> fun_prop
    · intro t q
      calc
        _ ≤ fourierMoment 0 (fourierCurl (s.coefficients t)) q := by
          simpa only [fourierMoment, pow_zero, one_mul] using
            PancakeIndexedFourierMoments.norm_coefficient_sup_le_euclidean
              (fourierCurl (s.coefficients t) q)
        _ ≤ (2 * Real.pi) * fourierMoment 1 (s.coefficients t) q := fourierMoment_curl_le 0 _ q
        _ ≤ (2 * Real.pi) * g q := mul_le_mul_of_nonneg_left
          ((fourierMoment_mono _ (by omega : 1 ≤ 2) q).trans (hu t t.2 q)) (by positivity)
  have he (t : Set.Icc (0 : ℝ) T) :
      spatialCurl (fullFourierField id (s.coefficients t)) =
        fullFourierField id (fourierCurl (s.coefficients t)) :=
    spatialCurl_velocity _ (summable_firstMoment_of_second _
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t t.2)))
  simp only [fullVorticity, he]
  exact complexRealPartEuclideanCLM.continuous.comp
    (continuous_eval.comp ((hc.comp continuous_fst).prodMk continuous_snd))

theorem continuousOn_integral_lowDiffusionDensity (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (modes : Finset Wavevector) (chi : Wavevector → ℂ) :
    ContinuousOn (fun t ↦ ∫ x : T3, lowDiffusionDensity modes chi (s.coefficients t) x)
      (Set.Icc (0 : ℝ) T) := by
  have hd : Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      lowDiffusionDensity modes chi (s.coefficients z.1) z.2) := by
    apply Continuous.mul _ ((continuous_fullVorticity_spaceTime s g hSum hu).norm.pow 2)
    apply continuous_finsetSum
    intro j _
    exact (continuous_parametric_strainGradient modes chi
      (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t) j
      (fun q _ i ↦ (s.continuous q i).comp continuous_subtype_val)).norm.pow 2
  apply continuousOn_iff_continuous_restrict.mpr
  change Continuous (fun t : Set.Icc (0 : ℝ) T ↦
    ∫ x : T3, lowDiffusionDensity modes chi (s.coefficients t) x)
  have hi := continuous_parametric_integral_of_continuous (μ := (volume : Measure T3))
    (f := fun t : Set.Icc (0 : ℝ) T ↦ fun x ↦ lowDiffusionDensity modes chi (s.coefficients t) x)
    hd isCompact_univ
  simpa only [Measure.restrict_univ] using hi

/-- The bound depends on initial energy, not on the local moment envelope
or any receiver resolution. The strain cutoff remains fixed. -/
theorem spacetime_lowDiffusionDensity_le_initial (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hnu : 0 < nu) (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (modes : Finset Wavevector) (chi : Wavevector → ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ ∫ x : T3, lowDiffusionDensity modes chi (s.coefficients τ) x)
      volume 0 t ∧
    (∫ τ in (0 : ℝ)..t, ∫ x : T3, lowDiffusionDensity modes chi (s.coefficients τ) x) ≤
      strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / (4 * nu) := by
  have hi : IntervalIntegrable
      (fun τ ↦ ∫ x : T3, lowDiffusionDensity modes chi (s.coefficients τ) x) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1
      ((continuousOn_integral_lowDiffusionDensity s g hSum hu modes chi).mono
        (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩))
  refine ⟨hi, integral_le_of_energy_enstrophy_majorant s hnu g hg hSum hu t ht _
    (strainGradientCutoffWeight modes chi) (strainGradientCutoffWeight_nonneg modes chi) hi ?_⟩
  intro τ hτ
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ ⟨hτ.1, hτ.2.trans ht.2⟩)
  simpa only [mul_assoc] using integral_lowDiffusionDensity_le modes chi _
    (summable_firstMoment_of_second _ hm)

theorem regularized_lowDiffusion_payment (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hnu : 0 < nu) (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (modes : Finset Wavevector) (chi : Wavevector → ℂ) (delta : ℝ) (hd : 0 < delta)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (16 * nu / delta) *
      (∫ τ in (0 : ℝ)..t, ∫ x : T3, lowDiffusionDensity modes chi (s.coefficients τ) x) ≤
        4 * strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / delta := by
  have h := (spacetime_lowDiffusionDensity_le_initial s hnu g hg hSum hu modes chi t ht).2
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 16 * nu / delta)
  convert hh using 1 <;> first | rfl | field_simp; ring

end Mettapedia.FluidDynamics.NavierStokes.LocalLowDiffusionBudget
