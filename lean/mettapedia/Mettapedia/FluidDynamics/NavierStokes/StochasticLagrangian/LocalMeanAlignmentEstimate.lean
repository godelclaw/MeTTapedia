import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMeanAlignmentBalance
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSignedAlignmentBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalEnergySubinterval

/-!
# A signed endpoint estimate for the actual mean alignment energy

The derivative in this statement is the actual frozen material derivative,
not an arbitrary integrable lower bound. Its spatial integrability, time
integrability and endpoint balance are supplied by the local solution.

The remaining comparison with the algebraic strain/vorticity rate is explicit.
No scale-uniform estimate on the signed nonlinear forcing is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalMeanAlignmentEstimate

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierStrainGradient InfiniteConvectionEnergy
open PancakeGalerkinKineticEnergy
open LocalAlignmentForcing LocalAlignmentContinuity LocalSignedAlignmentBudget
open LocalMeanAlignmentBalance

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A conditional dynamical estimate with no assumed scalar integrability
or assumed fundamental theorem of calculus. -/
theorem meanEnergy_add_integral_residual_le {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu) (hB : 0 ≤ B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (delta : ℝ) (hd : 0 < delta)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (hpoint : ∀ᵐ τ ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      frozenMaterialRate chi modes s.coefficients delta τ x ≤
        materialRate chi modes outputs (s.coefficients τ) delta nu x) :
    meanEnergy chi modes (s.coefficients b) delta +
      (∫ τ in a..b, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes (s.coefficients a) delta +
        4 * strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / delta +
        ∫ τ in a..b, ∫ x : T3, signedForcingEnvelope chi modes outputs (s.coefficients τ) delta x := by
  have ha := (hI (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)).1.le
  have hb := (hI (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩)).2.le
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) T :=
    fun _ hτ ↦ Set.Ioo_subset_Icc_self (hI hτ)
  have hR : IntervalIntegrable (fun τ ↦ ∫ x : T3,
      signedForcingEnvelope chi modes outputs (s.coefficients τ) delta x) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((continuousOn_spatialIntegral _
      (continuous_signedForcingEnvelope_spaceTime s g hg hSum hu2 chi C hchi modes outputs delta)).mono hsub)
  have hz : IntervalIntegrable (fun τ ↦ ∫ x : T3,
      ‖residual chi modes (s.coefficients τ) x‖ ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((continuousOn_spatialIntegral _
      ((continuous_residual_spaceTime s g hSum hu2 chi modes).norm.pow 2)).mono hsub)
  obtain ⟨hf, hbalance⟩ := intervalIntegral_frozenMaterialRate_eq_energy
    s a b hab hI g hg hSum hu hB chi modes delta
  have hdom : ∀ᵐ τ ∂volume.restrict (Set.Ioo a b),
      (∫ x : T3, frozenMaterialRate chi modes s.coefficients delta τ x) +
        (∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) -
        (∫ x : T3, signedForcingEnvelope chi modes outputs (s.coefficients τ) delta x) ≤
      ((16 * nu / delta) * strainGradientCutoffWeight modes chi) *
        (kineticEnergy (s.coefficients τ) * kineticEnergy (fourierCurl (s.coefficients τ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hpoint,
      ae_hasDerivAt_meanEnergy s a b hab hI g hg hSum hu hB chi modes delta] with τ hτ hp hderiv
    have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
      (hu τ (hsub (Set.Ioo_subset_Icc_self hτ)))
    have h := LocalSignedAlignmentBudget.integral_materialRate_lower_bound_paid
      chi modes outputs _ hm delta nu hd hnu.le _ hderiv.1 hp
    nlinarith
  have h := LocalEnergySubinterval.integral_le_of_energy_enstrophy_majorant
    s hnu g hg hSum hu2 a b ha hab hb _
    ((16 * nu / delta) * strainGradientCutoffWeight modes chi)
    (mul_nonneg (by positivity) (strainGradientCutoffWeight_nonneg modes chi))
    ((hf.add hz).sub hR) hdom
  rw [intervalIntegral.integral_sub (hf.add hz) hR,
    intervalIntegral.integral_add hf hz, hbalance] at h
  have he : (16 * nu / delta * strainGradientCutoffWeight modes chi) * kineticEnergy u₀ ^ 2 /
      (4 * nu) = 4 * strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / delta := by
    field_simp
    ring
  rw [he] at h
  linarith

end Mettapedia.FluidDynamics.NavierStokes.LocalMeanAlignmentEstimate
