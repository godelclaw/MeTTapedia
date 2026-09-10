import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpaceTimeExtension
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMeanMaterialBalance

/-!
# The full-vorticity alignment energy has a local mean balance

On a compact interior time interval of an actual local solution, the frozen
material derivative of the alignment energy is spatially integrable almost
everywhere in time. Its mean is the derivative of the mean energy, and its
time integral equals the endpoint energy difference. Only the strain is
filtered; both the transported vorticity and advecting velocity are full fields.

The constant time extension is used only to apply the periodic weak chain rule.
The final balance is for the original local solution. Identification with the
algebraic strain/vorticity rate is a separate dynamical step.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalMeanAlignmentBalance

open scoped Topology
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths
open PancakeDyadicDirectionEvolution PancakeWeakIncompressibleTransport PancakeMaterialChainRule
open PancakeCurlOutputTail PancakeInfiniteFourierDerivative
open LocalAlignmentTransport LocalSpaceTimeExtension

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def velocity (u : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (fullFourierField id u x)

theorem velocity_apply (u : FourierVelocity) (x : T3) (j : Fin 3) :
    velocity u x j = InfiniteFourierTransport.velocityComponent u j x := rfl

theorem continuous_velocity (u : FourierVelocity) : Continuous (velocity u) :=
  complexRealPartEuclideanCLM.continuous.comp (fullFourierField id u).continuous

def meanEnergy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) : ℝ := ∫ x : T3, alignmentEnergy chi modes u delta x

/-- The actual derivative along the line with the instantaneous full velocity. -/
def frozenMaterialRate (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (delta t : ℝ) (x : T3) : ℝ :=
  scalarMaterialRate (fun τ ↦ alignmentEnergy chi modes (u τ) delta) (velocity (u t)) t x

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hI hSum hu in
theorem locallyLipschitz_extendedVelocity (t : ℝ) (j : Fin 3) :
    LocallyLipschitz (fun r : X3 ↦ velocity (coefficients s a b hab t) (torusPoint r) j) :=
  InfiniteFourierTransport.locallyLipschitz_velocityComponent _
    (summable_moment s a b hab hI g hSum hu 1 (by omega) t) j

include hI hSum hu in
theorem divergence_extendedVelocity (t : ℝ) (x : T3) :
    coordinateDivergence (fun j y ↦ velocity (coefficients s a b hab t) y j) x = 0 :=
  InfiniteFourierTransport.coordinateDivergence_velocity_zero _
    (summable_moment s a b hab hI g hSum hu 2 (by omega) t)
    (s.transverse _) x

include hI hg hSum hu in
theorem ae_hasDerivAt_extendedMean (hB : 0 ≤ B) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (delta : ℝ) :
    ∀ᵐ t : ℝ, Integrable (frozenMaterialRate chi modes (coefficients s a b hab) delta t) ∧
      HasDerivAt (fun τ ↦ meanEnergy chi modes (coefficients s a b hab τ) delta)
        (∫ x : T3, frozenMaterialRate chi modes (coefficients s a b hab) delta t x) t :=
  PancakeMeanMaterialBalance.ae_hasDerivAt_mean_materialRate _ _
    (LocalSpaceTimeExtension.continuous_alignmentEnergy s a b hab hI g hSum hu chi modes delta)
    (fun _ ↦ continuous_velocity _)
    (locallyLipschitz_alignmentEnergy s a b hab hI g hg hSum hu hB chi modes delta)
    (locallyLipschitz_extendedVelocity s a b hab hI g hSum hu)
    (fun t ↦ Filter.Eventually.of_forall (divergence_extendedVelocity s a b hab hI g hSum hu t))

include hI hg hSum hu in
theorem intervalIntegral_extendedMaterialRate (hB : 0 ≤ B) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (delta : ℝ) :
    IntervalIntegrable (fun t ↦ ∫ x : T3,
      frozenMaterialRate chi modes (coefficients s a b hab) delta t x) volume a b ∧
      (∫ t in a..b, ∫ x : T3, frozenMaterialRate chi modes (coefficients s a b hab) delta t x) =
        meanEnergy chi modes (s.coefficients b) delta - meanEnergy chi modes (s.coefficients a) delta := by
  have h := PancakeMeanMaterialBalance.intervalIntegral_materialRate_eq
    (fun t ↦ alignmentEnergy chi modes (coefficients s a b hab t) delta)
    (fun t ↦ velocity (coefficients s a b hab t))
    (LocalSpaceTimeExtension.continuous_alignmentEnergy s a b hab hI g hSum hu chi modes delta)
    (fun _ ↦ continuous_velocity _)
    (locallyLipschitz_alignmentEnergy s a b hab hI g hg hSum hu hB chi modes delta)
    (locallyLipschitz_extendedVelocity s a b hab hI g hSum hu)
    (fun t ↦ Filter.Eventually.of_forall (divergence_extendedVelocity s a b hab hI g hSum hu t)) a b
  simpa only [frozenMaterialRate, meanEnergy, coefficients_eq s a b hab b ⟨hab, le_rfl⟩,
    coefficients_eq s a b hab a ⟨le_rfl, hab⟩] using h

/-- Constant extension does not alter a derivative at an interior time. -/
theorem frozenMaterialRate_extension_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (delta t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3) :
    frozenMaterialRate chi modes (coefficients s a b hab) delta t x =
      frozenMaterialRate chi modes s.coefficients delta t x := by
  unfold frozenMaterialRate scalarMaterialRate
  rw [coefficients_eq s a b hab t (Set.Ioo_subset_Icc_self ht)]
  apply Filter.EventuallyEq.deriv_eq
  have hc : Filter.Tendsto (fun h : ℝ ↦ t + h) (𝓝 0) (𝓝 t) := by
    have hc : ContinuousAt (fun h : ℝ ↦ t + h) 0 := by fun_prop
    simpa only [ContinuousAt, add_zero] using hc
  filter_upwards [hc.eventually (Icc_mem_nhds ht.1 ht.2)] with h hh
  rw [coefficients_eq s a b hab (t + h) hh]

include hab hI hg hSum hu in
/-- Spatial integrability and differentiation of the original mean hold
almost everywhere on the interior interval. -/
theorem ae_hasDerivAt_meanEnergy (hB : 0 ≤ B) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (delta : ℝ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      Integrable (frozenMaterialRate chi modes s.coefficients delta t) ∧
        HasDerivAt (fun τ ↦ meanEnergy chi modes (s.coefficients τ) delta)
          (∫ x : T3, frozenMaterialRate chi modes s.coefficients delta t x) t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (ae_hasDerivAt_extendedMean s a b hab hI g hg hSum hu hB chi modes delta)]
    with t ht hd
  have he := funext (frozenMaterialRate_extension_eq s a b hab chi modes delta t ht)
  rw [he] at hd
  refine ⟨hd.1, hd.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
  rw [coefficients_eq s a b hab τ hτ]

include hab hI hg hSum hu in
/-- A full-field mean balance, with time integrability derived rather than assumed. -/
theorem intervalIntegral_frozenMaterialRate_eq_energy (hB : 0 ≤ B) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (delta : ℝ) :
    IntervalIntegrable (fun t ↦ ∫ x : T3,
      frozenMaterialRate chi modes s.coefficients delta t x) volume a b ∧
      (∫ t in a..b, ∫ x : T3, frozenMaterialRate chi modes s.coefficients delta t x) =
        meanEnergy chi modes (s.coefficients b) delta - meanEnergy chi modes (s.coefficients a) delta := by
  obtain ⟨hInt, heq⟩ := intervalIntegral_extendedMaterialRate s a b hab hI g hg hSum hu hB chi modes delta
  have he : Set.EqOn
      (fun t ↦ ∫ x : T3, frozenMaterialRate chi modes (coefficients s a b hab) delta t x)
      (fun t ↦ ∫ x : T3, frozenMaterialRate chi modes s.coefficients delta t x) (Set.uIoo a b) := by
    intro t ht
    have ht' : t ∈ Set.Ioo a b := by simpa only [Set.uIoo_of_le hab] using ht
    exact integral_congr_ae (Filter.Eventually.of_forall
      (frozenMaterialRate_extension_eq s a b hab chi modes delta t ht'))
  exact ⟨hInt.congr_uIoo he, (intervalIntegral.integral_congr_uIoo he).symm.trans heq⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalMeanAlignmentBalance
