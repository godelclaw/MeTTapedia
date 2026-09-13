import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularCurlVariation

/-!
# Actual spatial-mean evolution of the filtered angular correction

The coercive finite-band functional is differentiated under the spatial
mean using the actual filtered infinite NS RHS. Resolved and subgrid
work are kept separately. No time bound or sign for either work is
inferred from the static angular estimate or the coercivity bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredAngularMean

open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeInfiniteFourierTime
open PancakeLocalInfiniteVelocity PancakeCoefficientLimitEquation PancakeFilteredStrainDynamics
open FourierFiniteSupport FiniteAngularCurlVariation LocalAngularCurlBudget FiniteBandAngularEnergy
open LocalVorticityEighthMoment
open InfiniteFilteredEquation

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def meanWork (κ : ℝ) (u v : FourierVelocity) : ℝ := ∫ x : T3, correctedDensityRate κ u v x

theorem integral_correctedDensity_eq (κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    (∫ x : T3, correctedDensity κ u x) = correctedEnergy κ u := by
  have hu := summable_fourierMoment P u hs 1
  have hE : Integrable (LocalVorticityEighthMoment.energy u) :=
    (((LocalLowDiffusionBudget.continuous_fullVorticity u hu).norm.pow 2).pow 4).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hK : Integrable (angularCurlDensity u) :=
    (LocalAngularCurlBudget.continuous_angularCurlDensity u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold correctedDensity correctedEnergy
  rw [integral_sub (hE.div_const 8) (hK.const_mul _), integral_div, integral_const_mul]
  rfl

theorem hasDerivAt_correctedEnergy {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B) (κ : ℝ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ correctedEnergy κ (filteredVelocity χ (s.coefficients τ)))
      (meanWork κ (filteredVelocity χ (s.coefficients t))
        (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients t)))) t := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have he : (fun τ ↦ ∫ x : T3, correctedDensity κ (filteredVelocity χ (s.coefficients τ)) x) =
      (fun τ ↦ correctedEnergy κ (filteredVelocity χ (s.coefficients τ))) := by
    funext τ
    exact integral_correctedDensity_eq κ P _ (hs _)
  rw [← he]
  apply CompactMeanContinuousRate.hasDerivAt_integral
    (fun τ x ↦ correctedDensity κ (filteredVelocity χ (s.coefficients τ)) x)
    (fun τ x ↦ correctedDensityRate κ (filteredVelocity χ (s.coefficients τ))
      (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ))) x) 0 T t ht
  · exact continuous_correctedDensity κ P
      (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ))
      (fun τ ↦ hs _) (fun q _ i ↦ continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
  · exact continuous_correctedDensityRate κ P
      (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ))
      (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ)))
      (fun τ ↦ hs _) (fun τ ↦ hs _)
      (fun q _ i ↦ continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
      (fun q _ i ↦ continuous_const.mul (continuous_velocityRHS_component s hB q i))
  · intro τ hτ x
    exact hasDerivAt_correctedDensity κ P (fun r ↦ filteredVelocity χ (s.coefficients r))
      (fun r ↦ hs _) (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ))) (hs _) τ x
      (fun q _ i ↦ (s.equation τ hτ q i).const_mul (χ q))

theorem meanWork_restrict_add (κ : ℝ) (P : Finset Wavevector) (u v w : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    meanWork κ u (FiniteVorticityVariation.restrictVelocity P (v + w)) =
      meanWork κ u (FiniteVorticityVariation.restrictVelocity P v) +
        meanWork κ u (FiniteVorticityVariation.restrictVelocity P w) := by
  have hi (v : FourierVelocity) : Integrable (correctedDensityRate κ u (FiniteVorticityVariation.restrictVelocity P v)) := by
    have hc := continuous_correctedDensityRate κ P (fun _ : Unit ↦ u)
      (fun _ : Unit ↦ FiniteVorticityVariation.restrictVelocity P v)
      (fun _ ↦ hs) (fun _ ↦ FiniteVorticityVariation.restrictVelocity_eq_zero P v)
      (fun _ _ _ ↦ continuous_const) (fun _ _ _ ↦ continuous_const)
    exact (hc.comp ((continuous_const (y := ())).prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold meanWork
  simp_rw [correctedDensityRate_restrict_add]
  exact integral_add (hi v) (hi w)

/-- Both work terms are evaluated on the same retained field. The subgrid
term contains all original input frequencies. -/
theorem hasDerivAt_correctedEnergy_split {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B) (κ : ℝ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ correctedEnergy κ (filteredVelocity χ (s.coefficients τ)))
      (meanWork κ (filteredVelocity χ (s.coefficients t))
          (FiniteVorticityVariation.restrictVelocity P (infiniteVelocityRHS ν (filteredVelocity χ (s.coefficients t)))) +
        meanWork κ (filteredVelocity χ (s.coefficients t))
          (FiniteVorticityVariation.restrictVelocity P (subgridForce χ (s.coefficients t)))) t := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have he : filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients t)) =
      infiniteVelocityRHS ν (filteredVelocity χ (s.coefficients t)) + subgridForce χ (s.coefficients t) := by
    funext q
    exact filtered_infiniteVelocityRHS χ _ C hχ ν q
      (s.summable_convection t (Set.Ioo_subset_Icc_self ht) q)
  have hr : filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients t)) =
      FiniteVorticityVariation.restrictVelocity P
        (infiniteVelocityRHS ν (filteredVelocity χ (s.coefficients t)) + subgridForce χ (s.coefficients t)) := by
    rw [← he, FilteredProjectionMean.restrictVelocity_eq_self P _ (hs _)]
  have h := hasDerivAt_correctedEnergy s hB κ P χ hcut t ht
  rwa [hr, meanWork_restrict_add κ P _ _ _ (hs _)] at h

/-- The exact mean balance reaches the initial endpoint. The integrated
work is signed and is not asserted bounded by the initial value. -/
theorem mean_balance {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B) (κ : ℝ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    correctedEnergy κ (filteredVelocity χ (s.coefficients t)) = correctedEnergy κ (filteredVelocity χ u₀) +
      ∫ τ in (0 : ℝ)..t, meanWork κ (filteredVelocity χ (s.coefficients τ))
        (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ))) := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hf := continuous_correctedDensity κ P
    (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ))
    (fun τ ↦ hs _) (fun q _ i ↦ continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
  have hr := continuous_correctedDensityRate κ P
    (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ))
    (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ)))
    (fun τ ↦ hs _) (fun τ ↦ hs _)
    (fun q _ i ↦ continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
    (fun q _ i ↦ continuous_const.mul (continuous_velocityRHS_component s hB q i))
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hcf := (LocalAlignmentContinuity.continuousOn_spatialIntegral
    (fun τ x ↦ correctedDensity κ (filteredVelocity χ (s.coefficients τ)) x) hf).mono hsub
  have hcr := (LocalAlignmentContinuity.continuousOn_spatialIntegral
    (fun τ x ↦ correctedDensityRate κ (filteredVelocity χ (s.coefficients τ))
      (filteredVelocity χ (infiniteVelocityRHS ν (s.coefficients τ))) x) hr).mono hsub
  have hefun : (fun τ ↦ ∫ x : T3, correctedDensity κ (filteredVelocity χ (s.coefficients τ)) x) =
      (fun τ ↦ correctedEnergy κ (filteredVelocity χ (s.coefficients τ))) := by
    funext τ
    exact integral_correctedDensity_eq κ P _ (hs _)
  rw [hefun] at hcf
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcf
    (fun τ hτ ↦ hasDerivAt_correctedEnergy s hB κ P χ hcut τ ⟨hτ.1, hτ.2.trans_le ht.2⟩)
    (hcr.intervalIntegrable_of_Icc (μ := volume) ht.1)
  change _ = correctedEnergy κ (filteredVelocity χ (s.coefficients t)) -
    correctedEnergy κ (filteredVelocity χ (s.coefficients 0)) at he
  rw [s.initial] at he
  linarith only [he]

end Mettapedia.FluidDynamics.NavierStokes.FilteredAngularMean
