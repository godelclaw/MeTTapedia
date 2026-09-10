import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTracePatchEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.WeightedFourierPressurePatch

/-!
# A weighted angular pressure budget with no cone assumption

The adaptive Fourier patches are constructed from the weighted line
projector. Their pressure energy splits into a weighted scalar trace
term, the trace energy above a tilt-symbol threshold, the exact
localization commutator, and prescribed approximation errors.

No pressure modes are discarded and no cell-count factor occurs.
Controlling the tail and commutator uniformly in scale and time remains
a separate dynamical problem; this theorem does not assume those bounds.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WeightedPressureAngularBudget

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeAnisotropyDepletion
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open FourierPressureTiltEnergy FourierPressurePatchEnergy FourierPressureLocalization
open FourierPressureTraceSymbol PressureTracePatchEnergy LocalPressureCommutator

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- One family works for every finite real pressure field and every
nonnegative angular threshold. Its weighted coverage is also retained. -/
theorem exists_weighted_pressure_angular_budget
    (a : T3 → ℝ) (ha : Continuous a) (han : ∀ x, 0 ≤ a x)
    (e : T3 → R3) (he : ∀ x, ‖e x‖ = 1)
    (hP : Continuous (fun x ↦ Real.sqrt (a x) • InnerProductSpace.rankOne ℝ (e x) (e x)))
    (rho delta : ℝ) (hr : 0 < rho) (hd : 0 < delta) :
    ∃ (centers : Finset T3) (c : ↑centers → FourierCoeff (Fin 3)),
      (∀ x, |(∑ i, quadraticWeight (c i) x) - a x| ≤ delta) ∧
      ∀ (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity),
        (∀ q, -q ∈ outputs ↔ q ∈ outputs) → ∀ eta : ℝ, 0 ≤ eta →
        (∫ x : T3, a x *
          ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
            4 * eta ^ 2 * (∫ x : T3, a x * realPressureTrace chi outputs u x ^ 2) +
              4 * (∑ i, tiltTailTraceEnergy (c i) chi outputs u (e i.1) eta) +
              4 * (∑ i, tiltCommutatorEnergy (c i) chi outputs u (e i.1)) +
              (32 * rho ^ 2 + 2 * delta + 4 * eta ^ 2 * delta) * hessianEnergy chi outputs u := by
  obtain ⟨centers, c, hmass, henergy⟩ :=
    WeightedFourierPressurePatch.exists_weighted_pressure_patches a ha han e he hP rho delta hr hd
  refine ⟨centers, c, hmass, ?_⟩
  intro chi outputs u hs eta heta
  have hpatch := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    frozenPatchEnergy_le_with_tail (c i) chi outputs u (e i.1) (he i.1) eta heta)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hpatch
  have htrace := sum_tracePatchEnergy_le_weighted c chi outputs u hs a ha delta hd.le
    (fun x ↦ by have hx := (abs_le.mp (hmass x)).2; linarith only [hx])
  have hweighted := mul_le_mul_of_nonneg_left htrace (by positivity : 0 ≤ 4 * eta ^ 2)
  have h := henergy chi outputs u hs
  nlinarith only [h, hpatch, hweighted]

end Mettapedia.FluidDynamics.NavierStokes.WeightedPressureAngularBudget
