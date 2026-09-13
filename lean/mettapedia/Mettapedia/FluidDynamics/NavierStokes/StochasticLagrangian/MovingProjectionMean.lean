import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionScaleMotion

/-!
# Actual filtered mean balance with a moving scalar normalization

The multiplier is fixed. The solution satisfies the full infinite
Fourier equation, while the scalar normalization may vary in time.
Its derivative contributes the explicit signed scale work.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MovingProjectionMean

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open RegularizedProjectionParameter WeightedProjectionParabolic
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakePeriodicVorticityEquation
open PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity PancakeCoefficientLimitEquation
open LocalLowDiffusionBudget LocalWeightedProjectionEvolution LocalHelicityProjectionEvolution
open LocalHelicityProjectionDiffusion FiniteVorticityVariation FilteredProjectionMean
open LocalProjectionScaleMotion FourierFiniteSupport
open PancakeGalerkinVorticityBridge PancakeInfiniteFourierTime
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def movingRate (ν κ dκ : ℝ) (u v : FourierVelocity) (x : T3) : ℝ :=
  correctedDensityRate (ν ^ 2 * κ ^ 2 / 3) κ u v x + scaleDensity ν κ dκ u x

section Continuity
variable {Y : Type*} [TopologicalSpace Y]

theorem continuous_density (ν : ℝ) (hν : 0 < ν) (κ : Y → ℝ)
    (hκ : ∀ y, 0 < κ y) (hk : Continuous κ)
    (P : Finset Wavevector) (u : Y → FourierVelocity)
    (hs : ∀ y q, q ∉ P → u y q = 0)
    (hu : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ u y q i)) :
    Continuous (fun z : Y × T3 ↦ correctedDensity (ν ^ 2 * κ z.1 ^ 2 / 3) (κ z.1) (u z.1) z.2) := by
  have ha := FilteredProjectionMean.continuous_fullVorticity P u hs hu
  have hb := FilteredProjectionMean.continuous_fullVorticity P (fun y ↦ fourierCurl (u y))
    (fun y ↦ fourierCurl_eq_zero P _ (hs y)) (fun q hq ↦ continuous_curl_component u q (hu q hq))
  have hk' : Continuous (fun z : Y × T3 ↦ κ z.1) := hk.comp continuous_fst
  unfold correctedDensity weightedProjectionDensity projectionEnergy RegularizedProjection.energy
    RegularizedProjection.residual RegularizedProjection.coefficient
  fun_prop (disch := intro z; have hz := hκ z.1; positivity)

theorem continuous_rate (ν : ℝ) (hν : 0 < ν) (κ dκ : Y → ℝ)
    (hκ : ∀ y, 0 < κ y) (hk : Continuous κ) (hdk : Continuous dκ)
    (P : Finset Wavevector) (u v : Y → FourierVelocity)
    (hs : ∀ y q, q ∉ P → u y q = 0) (ht : ∀ y q, q ∉ P → v y q = 0)
    (hu : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ u y q i))
    (hv : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ v y q i)) :
    Continuous (fun z : Y × T3 ↦ movingRate ν (κ z.1) (dκ z.1) (u z.1) (v z.1) z.2) := by
  have ha := FilteredProjectionMean.continuous_fullVorticity P u hs hu
  have hb := FilteredProjectionMean.continuous_fullVorticity P (fun y ↦ fourierCurl (u y))
    (fun y ↦ fourierCurl_eq_zero P _ (hs y)) (fun q hq ↦ continuous_curl_component u q (hu q hq))
  have hf := FilteredProjectionMean.continuous_fullVorticity P v ht hv
  have hg := FilteredProjectionMean.continuous_fullVorticity P (fun y ↦ fourierCurl (v y))
    (fun y ↦ fourierCurl_eq_zero P _ (ht y)) (fun q hq ↦ continuous_curl_component v q (hv q hq))
  have hk' : Continuous (fun z : Y × T3 ↦ κ z.1) := hk.comp continuous_fst
  have hdk' : Continuous (fun z : Y × T3 ↦ dκ z.1) := hdk.comp continuous_fst
  unfold movingRate correctedDensityRate densityRate scaleDensity scaleRate weightedRate
    RegularizedProjectionParabolic.energyRate RegularizedProjection.energy
    RegularizedProjection.residual RegularizedProjection.coefficient
  fun_prop (disch := intro z; have hz := hκ z.1; positivity)

end Continuity

theorem integral_movingRate_eq (ν κ dκ : ℝ) (hν : 0 < ν) (hκ : 0 < κ)
    (P : Finset Wavevector) (u v : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (hv : ∀ q, q ∉ P → v q = 0) :
    (∫ x : T3, movingRate ν κ dκ u v x) =
      (∫ x : T3, correctedDensityRate (ν ^ 2 * κ ^ 2 / 3) κ u v x) + scaleWork ν κ dκ u := by
  have hδ : 0 < ν ^ 2 * κ ^ 2 / 3 := by positivity
  have hc0 := continuous_correctedDensityRate (ν ^ 2 * κ ^ 2 / 3) hδ κ P
    (fun _ : Unit ↦ u) (fun _ : Unit ↦ v) (fun _ ↦ hs) (fun _ ↦ hv)
    (fun _ _ _ ↦ continuous_const) (fun _ _ _ ↦ continuous_const)
  have hc1 := hc0.comp (show Continuous (fun x : T3 ↦ ((() : Unit), x)) from
    continuous_const.prodMk continuous_id)
  have hc : Continuous (correctedDensityRate (ν ^ 2 * κ ^ 2 / 3) κ u v) := hc1
  have hI : Integrable (correctedDensityRate (ν ^ 2 * κ ^ 2 / 3) κ u v) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJ : Integrable (scaleDensity ν κ dκ u) :=
    (continuous_scaleDensity ν κ dκ hν hκ u (summable_fourierMoment P u hs 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold movingRate scaleWork
  exact integral_add hI hJ

theorem hasDerivAt_density (ν : ℝ) (hν : 0 < ν) (κ : ℝ → ℝ) (dκ t : ℝ)
    (hκ : 0 < κ t) (hk : HasDerivAt κ dκ t)
    (P : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hs : ∀ τ q, q ∉ P → u τ q = 0) (v : FourierVelocity) (x : T3)
    (hd : ∀ q ∈ P, ∀ i, HasDerivAt (fun τ ↦ u τ q i) (v q i) t) :
    HasDerivAt (fun τ ↦ correctedDensity (ν ^ 2 * κ τ ^ 2 / 3) (κ τ) (u τ) x)
      (movingRate ν (κ t) dκ (u t) (restrictVelocity P v) x) t := by
  have ha := FiniteVorticityVariation.hasDerivAt_fullVorticity P u hs v t x hd
  have hb := FiniteVorticityVariation.hasDerivAt_fullVorticity P (fun τ ↦ fourierCurl (u τ))
    (fun τ ↦ fourierCurl_eq_zero P (u τ) (hs τ)) (fourierCurl v) t x
    (fun q hq ↦ hasDerivAt_fourierCurl u v t q (hd q hq))
  rw [← fourierCurl_restrictVelocity] at hb
  exact hasDerivAt_normalizedDensity ν hν hκ hk ha hb

/-- This differentiates the actual solution, not a frozen or Galerkin path. -/
theorem hasDerivAt_mean {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (κ dκ : ℝ → ℝ) (hk : ContinuousOn κ (Set.Icc (0 : ℝ) T))
    (hdk : ContinuousOn dκ (Set.Icc (0 : ℝ) T))
    (hκ : ∀ τ ∈ Set.Icc (0 : ℝ) T, 0 < κ τ)
    (hder : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt κ (dκ τ) τ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ meanCorrectedEnergy (ν ^ 2 * κ τ ^ 2 / 3) (κ τ)
      (filteredVelocity χ (s.coefficients τ)))
      (∫ x : T3, movingRate ν (κ t) (dκ t) (filteredVelocity χ (s.coefficients t))
        (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients t))) x) t := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  apply CompactMeanContinuousRate.hasDerivAt_integral
    (fun τ x ↦ correctedDensity (ν ^ 2 * κ τ ^ 2 / 3) (κ τ)
      (filteredVelocity χ (s.coefficients τ)) x)
    (fun τ x ↦ movingRate ν (κ τ) (dκ τ) (filteredVelocity χ (s.coefficients τ))
      (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ))) x) 0 T t ht
  · exact continuous_density ν hν (fun τ : Set.Icc (0 : ℝ) T ↦ κ τ)
      (fun τ ↦ hκ τ τ.2) (continuousOn_iff_continuous_restrict.mp hk) P
      (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ))
      (fun τ ↦ hs _) (fun q _ i ↦
        continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
  · exact continuous_rate ν hν (fun τ : Set.Icc (0 : ℝ) T ↦ κ τ) (fun τ ↦ dκ τ)
      (fun τ ↦ hκ τ τ.2) (continuousOn_iff_continuous_restrict.mp hk)
      (continuousOn_iff_continuous_restrict.mp hdk) P
      (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ))
      (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ)))
      (fun τ ↦ hs _) (fun τ ↦ hs _)
      (fun q _ i ↦ continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
      (fun q _ i ↦ continuous_const.mul (continuous_velocityRHS_component s hB q i))
  · intro τ hτ x
    have h := hasDerivAt_density ν hν κ (dκ τ) τ (hκ τ (Set.Ioo_subset_Icc_self hτ))
      (hder τ hτ) P (fun r ↦ filteredVelocity χ (s.coefficients r)) (fun r ↦ hs _)
      (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ))) x
      (fun q _ i ↦ (s.equation τ hτ q i).const_mul (χ q))
    rwa [restrictVelocity_eq_self P _ (hs _)] at h

/-- Exact initial-data balance with the signed scale term retained inside
the time integral. Local continuity is not a lifespan-uniform budget. -/
theorem mean_balance {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (κ dκ : ℝ → ℝ) (hk : ContinuousOn κ (Set.Icc (0 : ℝ) T))
    (hdk : ContinuousOn dκ (Set.Icc (0 : ℝ) T))
    (hκ : ∀ τ ∈ Set.Icc (0 : ℝ) T, 0 < κ τ)
    (hder : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt κ (dκ τ) τ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    meanCorrectedEnergy (ν ^ 2 * κ t ^ 2 / 3) (κ t) (filteredVelocity χ (s.coefficients t)) =
      meanCorrectedEnergy (ν ^ 2 * κ 0 ^ 2 / 3) (κ 0) (filteredVelocity χ u₀) +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, movingRate ν (κ τ) (dκ τ)
          (filteredVelocity χ (s.coefficients τ))
          (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ))) x := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hf := continuous_density ν hν (fun τ : Set.Icc (0 : ℝ) T ↦ κ τ)
    (fun τ ↦ hκ τ τ.2) hk.restrict P
    (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ))
    (fun τ ↦ hs _) (fun q _ i ↦ continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
  have hr := continuous_rate ν hν (fun τ : Set.Icc (0 : ℝ) T ↦ κ τ) (fun τ ↦ dκ τ)
    (fun τ ↦ hκ τ τ.2) hk.restrict hdk.restrict P
    (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ))
    (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ)))
    (fun τ ↦ hs _) (fun τ ↦ hs _)
    (fun q _ i ↦ continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
    (fun q _ i ↦ continuous_const.mul (continuous_velocityRHS_component s hB q i))
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hcf := (LocalAlignmentContinuity.continuousOn_spatialIntegral
    (fun τ x ↦ correctedDensity (ν ^ 2 * κ τ ^ 2 / 3) (κ τ)
      (filteredVelocity χ (s.coefficients τ)) x) hf).mono hsub
  have hcr := (LocalAlignmentContinuity.continuousOn_spatialIntegral
    (fun τ x ↦ movingRate ν (κ τ) (dκ τ) (filteredVelocity χ (s.coefficients τ))
      (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ))) x) hr).mono hsub
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcf
    (fun τ hτ ↦ hasDerivAt_mean s hν hB κ dκ hk hdk hκ hder P χ hcut τ
      ⟨hτ.1, hτ.2.trans_le ht.2⟩) (hcr.intervalIntegrable_of_Icc (μ := volume) ht.1)
  change _ = meanCorrectedEnergy (ν ^ 2 * κ t ^ 2 / 3) (κ t)
    (filteredVelocity χ (s.coefficients t)) -
      meanCorrectedEnergy (ν ^ 2 * κ 0 ^ 2 / 3) (κ 0) (filteredVelocity χ (s.coefficients 0)) at he
  rw [s.initial] at he
  linarith only [he]

end Mettapedia.FluidDynamics.NavierStokes.MovingProjectionMean
