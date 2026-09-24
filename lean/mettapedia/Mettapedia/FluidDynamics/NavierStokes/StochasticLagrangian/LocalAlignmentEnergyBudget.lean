import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAESpectralDifferentiability
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMeanAlignmentEstimate

/-!
# Signed alignment energy budget for the actual local solution

The actual frozen material derivative agrees almost everywhere with the
algebraic strain/vorticity rate. Spectral differentiability, integrability
and the mean fundamental theorem of calculus are derived here, not
additional dynamical hypotheses. The unresolved signed nonlinear source
remains explicit; no cutoff-uniform or global regularity bound is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentEnergyBudget

open scoped Topology ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeLocalInfiniteVelocity PancakeFourierStrainGradient
open InfiniteConvectionEnergy LocalAlignmentForcing LocalMeanAlignmentBalance LocalSignedAlignmentBudget
open LocalFrozenAlignmentRate LocalAESpectralDifferentiability

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
  (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
  (hchir : ∀ q, chi (-q) = conj (chi q))
  (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
  (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
  (delta a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)

include hB hg hSum hu hchi hcut hchir hsub hout hs hk hab hI

theorem ae_ae_frozenMaterialRate_eq_materialRate :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      frozenMaterialRate chi modes s.coefficients delta t x =
        materialRate chi modes outputs (s.coefficients t) delta nu x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_ae_spectralDifferentiable s a b hab hI chi modes hB] with t ht hL
  exact hL.mono (fun x hx ↦ frozenMaterialRate_eq_materialRate s g hg hSum hu chi C hchi modes outputs
    hcut hchir hsub hout hs hk delta a b hab hI t ht x hx)

theorem ae_integrable_materialRate :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      Integrable (materialRate chi modes outputs (s.coefficients t) delta nu) := by
  filter_upwards [ae_hasDerivAt_meanEnergy s a b hab hI g hg hSum hu hB chi modes delta,
    ae_ae_frozenMaterialRate_eq_materialRate s hB g hg hSum hu chi C hchi modes outputs
      hcut hchir hsub hout hs hk delta a b hab hI] with t ht heq
  exact ht.1.congr heq

/-- The physical rate has an integrable spatial mean and its integral
is the endpoint difference of the actual full-vorticity energy. -/
theorem intervalIntegral_materialRate_eq_energy :
    IntervalIntegrable (fun t ↦ ∫ x : T3,
      materialRate chi modes outputs (s.coefficients t) delta nu x) volume a b ∧
      (∫ t in a..b, ∫ x : T3, materialRate chi modes outputs (s.coefficients t) delta nu x) =
        meanEnergy chi modes (s.coefficients b) delta - meanEnergy chi modes (s.coefficients a) delta := by
  obtain ⟨hF, hbalance⟩ := intervalIntegral_frozenMaterialRate_eq_energy
    s a b hab hI g hg hSum hu hB chi modes delta
  have heq : (fun t ↦ ∫ x : T3, frozenMaterialRate chi modes s.coefficients delta t x) =ᵐ[
      volume.restrict (Set.uIoc a b)]
      (fun t ↦ ∫ x : T3, materialRate chi modes outputs (s.coefficients t) delta nu x) := by
    rw [Set.uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
    exact (ae_ae_frozenMaterialRate_eq_materialRate s hB g hg hSum hu chi C hchi modes outputs
      hcut hchir hsub hout hs hk delta a b hab hI).mono (fun _ h ↦ integral_congr_ae h)
  exact ⟨hF.congr_ae heq, (intervalIntegral.integral_congr_ae_restrict heq).symm.trans hbalance⟩

/-- Full residual damping and initial-energy diffusion payment, with the
chain-rule comparison discharged for the actual local solution. -/
theorem meanEnergy_add_integral_residual_le (hnu : 0 < nu) (hd : 0 < delta) :
    meanEnergy chi modes (s.coefficients b) delta +
      (∫ t in a..b, ∫ x : T3, ‖residual chi modes (s.coefficients t) x‖ ^ 2) ≤
      meanEnergy chi modes (s.coefficients a) delta +
        4 * strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / delta +
        ∫ t in a..b, ∫ x : T3, signedForcingEnvelope chi modes outputs (s.coefficients t) delta x :=
  LocalMeanAlignmentEstimate.meanEnergy_add_integral_residual_le s hnu hB g hg hSum hu
    chi C hchi modes outputs delta hd a b hab hI
    ((ae_ae_frozenMaterialRate_eq_materialRate s hB g hg hSum hu chi C hchi modes outputs
      hcut hchir hsub hout hs hk delta a b hab hI).mono (fun _ ht ↦ ht.mono (fun _ hx ↦ hx.le)))

end Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentEnergyBudget
