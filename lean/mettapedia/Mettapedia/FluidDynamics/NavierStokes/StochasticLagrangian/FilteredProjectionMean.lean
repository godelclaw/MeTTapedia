import Mettapedia.Analysis.CompactMeanContinuousRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionSourceWork

/-!
# Spatial mean of the actual filtered projection evolution

Finite output support and continuity of the actual coefficient RHS justify
the time derivative under the spatial integral. No high-order envelope for
the full solution or bound for the subgrid work is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredProjectionMean

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis WeightedProjectionParabolic
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakePeriodicVorticityEquation
open PancakePeriodicComplexStretch PancakeCurlOutputTail
open PancakeLowDiffusionBudget PancakeFilteredStrainDynamics PancakeInfiniteFourierTime
open PancakeLocalInfiniteVelocity PancakeCoefficientLimitEquation
open LocalLowDiffusionBudget LocalHelicityProjectionDiffusion LocalWeightedProjectionEvolution
open FourierFiniteSupport FiniteVorticityVariation LocalVorticityEighthMoment
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem restrictVelocity_eq_self (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) : restrictVelocity P u = u := by
  funext q
  by_cases hq : q ∈ P
  · simp [restrictVelocity, filteredVelocity, InfiniteFilteredEquation.sharpFilter, hq]
  · simp [restrictVelocity_eq_zero P u q hq, hs q hq]

section Continuity

variable {Y : Type*} [TopologicalSpace Y]

theorem continuous_curl_component (u : Y → FourierVelocity) (q : Wavevector)
    (hu : ∀ i, Continuous (fun y ↦ u y q i)) (i : Fin 3) :
    Continuous (fun y ↦ fourierCurl (u y) q i) := by
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  fin_cases i <;> simp only [fourierCurl, coefficientCross, Pi.smul_apply, smul_eq_mul] <;> fun_prop

theorem continuous_fullVorticity (P : Finset Wavevector) (u : Y → FourierVelocity)
    (hs : ∀ y q, q ∉ P → u y q = 0)
    (hu : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ u y q i)) :
    Continuous (fun z : Y × T3 ↦ LocalLowDiffusionBudget.fullVorticity (u z.1) z.2) := by
  simp_rw [fullVorticity_eq_spatialVorticity P _ (hs _)]
  exact continuous_parametric_spatialVorticity P u hu

theorem continuous_correctedDensity (δ : ℝ) (hδ : 0 < δ) (κ : ℝ)
    (P : Finset Wavevector) (u : Y → FourierVelocity)
    (hs : ∀ y q, q ∉ P → u y q = 0)
    (hu : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ u y q i)) :
    Continuous (fun z : Y × T3 ↦ correctedDensity δ κ (u z.1) z.2) := by
  have ha := continuous_fullVorticity P u hs hu
  have hb := continuous_fullVorticity P (fun y ↦ fourierCurl (u y))
    (fun y ↦ fourierCurl_eq_zero P _ (hs y)) (fun q hq ↦ continuous_curl_component u q (hu q hq))
  unfold correctedDensity weightedProjectionDensity projectionEnergy RegularizedProjection.energy
    RegularizedProjection.residual RegularizedProjection.coefficient
  fun_prop (disch := intro z; positivity)

theorem continuous_correctedDensityRate (δ : ℝ) (hδ : 0 < δ) (κ : ℝ)
    (P : Finset Wavevector) (u v : Y → FourierVelocity)
    (hs : ∀ y q, q ∉ P → u y q = 0) (ht : ∀ y q, q ∉ P → v y q = 0)
    (hu : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ u y q i))
    (hv : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ v y q i)) :
    Continuous (fun z : Y × T3 ↦ correctedDensityRate δ κ (u z.1) (v z.1) z.2) := by
  have ha := continuous_fullVorticity P u hs hu
  have hb := continuous_fullVorticity P (fun y ↦ fourierCurl (u y))
    (fun y ↦ fourierCurl_eq_zero P _ (hs y)) (fun q hq ↦ continuous_curl_component u q (hu q hq))
  have hf := continuous_fullVorticity P v ht hv
  have hg := continuous_fullVorticity P (fun y ↦ fourierCurl (v y))
    (fun y ↦ fourierCurl_eq_zero P _ (ht y)) (fun q hq ↦ continuous_curl_component v q (hv q hq))
  exact ((ha.norm.pow 6).mul (ha.inner hf)).sub ((continuous_weightedRate δ hδ ha hb hf hg).const_mul _)

end Continuity

def meanCorrectedEnergy (δ κ : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, correctedDensity δ κ u x

theorem meanCorrectedEnergy_eq (δ : ℝ) (hδ : 0 < δ) (κ : ℝ)
    (P : Finset Wavevector) (u : FourierVelocity) (hs : ∀ q, q ∉ P → u q = 0) :
    meanCorrectedEnergy δ κ u = meanEnergy u / 8 - 3 / κ * weightedProjectionEnergy δ u := by
  have hu := summable_fourierMoment P u hs 2
  have ha := LocalLowDiffusionBudget.continuous_fullVorticity u
    (summable_firstMoment_of_second u hu)
  have hA : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 8) :=
    (ha.norm.pow 8).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK : Integrable (weightedProjectionDensity δ u) :=
    (continuous_weightedProjectionDensity δ hδ u hu).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  unfold meanCorrectedEnergy correctedDensity
  rw [integral_sub (hA.div_const 8) (hK.const_mul _), integral_div, integral_const_mul]
  simp only [meanEnergy, LocalVorticityEighthMoment.energy_eq_norm_pow, weightedProjectionEnergy]

/-- Mean differentiation uses the full solution's actual RHS, filtered on
the output. The local Sobolev bound only supplies continuity, not S4. -/
theorem hasDerivAt_meanCorrectedEnergy {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B)
    (δ : ℝ) (hδ : 0 < δ) (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ meanCorrectedEnergy δ κ (filteredVelocity χ (s.coefficients τ)))
      (∫ x : T3, correctedDensityRate δ κ (filteredVelocity χ (s.coefficients t))
        (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients t))) x) t := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  apply CompactMeanContinuousRate.hasDerivAt_integral
    (fun τ x ↦ correctedDensity δ κ (filteredVelocity χ (s.coefficients τ)) x)
    (fun τ x ↦ correctedDensityRate δ κ (filteredVelocity χ (s.coefficients τ))
      (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ))) x) 0 T t ht
  · exact continuous_correctedDensity δ hδ κ P
      (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ))
      (fun τ ↦ hs _) (fun q _ i ↦
      continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
  · exact continuous_correctedDensityRate δ hδ κ P
      (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ))
      (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ)))
      (fun τ ↦ hs _) (fun τ ↦ hs _)
      (fun q _ i ↦ continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
      (fun q _ i ↦ continuous_const.mul (continuous_velocityRHS_component s hB q i))
  · intro τ hτ x
    have h := hasDerivAt_correctedDensity δ hδ κ P (fun r ↦ filteredVelocity χ (s.coefficients r))
      (fun r ↦ hs _) (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ))) τ x
      (fun q _ i ↦ (s.equation τ hτ q i).const_mul (χ q))
    rwa [restrictVelocity_eq_self P _ (hs _)] at h

open InfiniteFilteredEquation LocalProjectionSourceWork

/-- The derivative of the spatial mean, with both exact signed work terms.
The additional curl of the subgrid vorticity source has been integrated by
parts onto the resolved variational gradient. -/
theorem hasDerivAt_meanCorrectedEnergy_split {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B)
    (δ : ℝ) (hδ : 0 < δ) (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ meanCorrectedEnergy δ κ (filteredVelocity χ (s.coefficients τ)))
      ((∫ x : T3, ⟪correctedGradient δ κ (filteredVelocity χ (s.coefficients t)) x,
        fullVorticity (restrictVelocity P (infiniteVelocityRHS ν (filteredVelocity χ (s.coefficients t)))) x⟫) +
      ∫ x : T3, ⟪correctedGradient δ κ (filteredVelocity χ (s.coefficients t)) x,
        fullVorticity (restrictVelocity P (subgridForce χ (s.coefficients t))) x⟫) t := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hu := summable_fourierMoment P _ (hs (s.coefficients t)) 4
  have hv := summable_fourierMoment P _ (hs (infiniteVelocityRHS ν (s.coefficients t))) 3
  have h := hasDerivAt_meanCorrectedEnergy s hB δ hδ κ P χ hcut t ht
  rw [integral_correctedDensityRate_eq δ hδ κ _ _ hu hv] at h
  have he : filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients t)) =
      infiniteVelocityRHS ν (filteredVelocity χ (s.coefficients t)) + subgridForce χ (s.coefficients t) := by
    funext q
    exact filtered_infiniteVelocityRHS χ _ C hχ ν q
      (s.summable_convection t (Set.Ioo_subset_Icc_self ht) q)
  have heω (x : T3) : fullVorticity (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients t))) x =
      fullVorticity (restrictVelocity P (infiniteVelocityRHS ν (filteredVelocity χ (s.coefficients t)))) x +
      fullVorticity (restrictVelocity P (subgridForce χ (s.coefficients t))) x := by
    rw [fullVorticity_eq_spatialVorticity P _ (hs _), he, spatialVorticity_add,
      fullVorticity_restrictVelocity, fullVorticity_restrictVelocity]
  have hu2 := summable_fourierMoment P _ (hs (s.coefficients t)) 2
  have hω := LocalLowDiffusionBudget.continuous_fullVorticity _
    (summable_firstMoment_of_second _ hu2)
  have hG : Continuous (correctedGradient δ κ (filteredVelocity χ (s.coefficients t))) :=
    ((hω.norm.pow 6).smul hω).sub ((continuous_projectionGradient δ hδ _ hu2).const_smul _)
  have hIv (v : FourierVelocity) : Integrable (fun x : T3 ↦
      ⟪correctedGradient δ κ (filteredVelocity χ (s.coefficients t)) x,
        fullVorticity (restrictVelocity P v) x⟫) :=
    (hG.inner (LocalLowDiffusionBudget.continuous_fullVorticity _
      (summable_fourierMoment P _ (restrictVelocity_eq_zero P v) 1))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [heω, inner_add_right] at h
  rwa [integral_add (hIv _) (hIv _)] at h

/-- The same mean derivative for the frequency-normalized energy whose
two-sided coercivity was proved separately. -/
theorem hasDerivAt_normalizedEnergy {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (R : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ FiniteBandProjectionEnergy.correctedEnergy ν R (filteredVelocity χ (s.coefficients τ)))
      (∫ x : T3, correctedDensityRate (ν ^ 2 * FiniteBandProjectionEnergy.normalization R ^ 2 / 3)
        (FiniteBandProjectionEnergy.normalization R) (filteredVelocity χ (s.coefficients t))
        (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients t))) x) t := by
  have hκ := FiniteBandProjectionEnergy.normalization_pos R
  have hδ : 0 < ν ^ 2 * FiniteBandProjectionEnergy.normalization R ^ 2 / 3 := by positivity
  have h := hasDerivAt_meanCorrectedEnergy s hB _ hδ
    (FiniteBandProjectionEnergy.normalization R) P χ hcut t ht
  have hs (τ q) (hq : q ∉ P) : filteredVelocity χ (s.coefficients τ) q = 0 := by
    simp [filteredVelocity, hcut q hq]
  simp_rw [meanCorrectedEnergy_eq _ hδ _ P _ (hs _)] at h
  exact h

/-- Exact initial-time balance. The signed work integral is retained;
its finiteness on the supplied local interval is not an a priori S4 bound. -/
theorem meanCorrectedEnergy_balance {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B)
    (δ : ℝ) (hδ : 0 < δ) (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    meanCorrectedEnergy δ κ (filteredVelocity χ (s.coefficients t)) =
      meanCorrectedEnergy δ κ (filteredVelocity χ u₀) +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, correctedDensityRate δ κ
          (filteredVelocity χ (s.coefficients τ))
          (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ))) x := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hf := continuous_correctedDensity δ hδ κ P
    (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ))
    (fun τ ↦ hs _) (fun q _ i ↦ continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
  have hr := continuous_correctedDensityRate δ hδ κ P
    (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ))
    (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ)))
    (fun τ ↦ hs _) (fun τ ↦ hs _)
    (fun q _ i ↦ continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
    (fun q _ i ↦ continuous_const.mul (continuous_velocityRHS_component s hB q i))
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hcf := (LocalAlignmentContinuity.continuousOn_spatialIntegral
    (fun τ x ↦ correctedDensity δ κ (filteredVelocity χ (s.coefficients τ)) x) hf).mono hsub
  have hcr := (LocalAlignmentContinuity.continuousOn_spatialIntegral
    (fun τ x ↦ correctedDensityRate δ κ (filteredVelocity χ (s.coefficients τ))
      (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ))) x) hr).mono hsub
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcf
    (fun τ hτ ↦ hasDerivAt_meanCorrectedEnergy s hB δ hδ κ P χ hcut τ ⟨hτ.1, hτ.2.trans_le ht.2⟩)
    (hcr.intervalIntegrable_of_Icc (μ := volume) ht.1)
  change _ = meanCorrectedEnergy δ κ (filteredVelocity χ (s.coefficients t)) -
    meanCorrectedEnergy δ κ (filteredVelocity χ (s.coefficients 0)) at he
  rw [s.initial] at he
  linarith only [he]

end Mettapedia.FluidDynamics.NavierStokes.FilteredProjectionMean
