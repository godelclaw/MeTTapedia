import Mettapedia.GSLT.Dynamics.BoundaryBellman
import MettapediaNS.WholeSpaceEnstrophyContinuation

/-!
# Bellman certificates on actual whole-space fluid histories

A history edge is a smooth unforced Navier–Stokes evolution over a positive
physical-time interval. Its boundary states retain the complete velocity.
Matching edges reconstruct an actual evolution by the existing concatenation
theorem, with the same viscosity and the canonical pressure.

The cost is the time integral of the actual order-energy production. Its
identification with the endpoint energy change follows from the PDE derivative
and the fundamental theorem of calculus. At order zero, the unforced energy
inequality supplies a proved Bellman certificate. At order one, a nonnegative
finite-horizon certificate would imply the existing continuation criterion.
No such order-one certificate is constructed here.

The window state includes physical time. A certificate is required for every
admissible segment in that window, so it also bounds arbitrary prefixes, not
only a chosen partition. This is a sufficient verification interface; it is
not an identification of an NS evolution with a Schrödinger bridge optimizer.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceHistoryBridge

open Set InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceOrderEnergy WholeSpaceViscousFlow
open Mettapedia.GSLT.Dynamics.BoundaryBellman

abbrev FluidState := SmoothL2Field Space

/-- A retained, unforced physical evolution with its full endpoint data. -/
structure Segment (ν : ℝ) (source target : FluidState) where
  duration : ℝ
  positive : 0 < duration
  evolution : NSEvolution ν duration positive.le
  initial : evolution.velocity ⟨0, le_rfl, positive.le⟩ = source
  final : evolution.velocity ⟨duration, positive.le, le_rfl⟩ = target

/-- The literal PDE production, including viscous dissipation and pressure. -/
def productionPath {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT) (n : ℕ) :
    C(Icc (0 : ℝ) T, ℝ) := by
  refine ⟨fun t ↦ orderProduction n (U.velocity t) (U.derivative t), ?_⟩
  apply continuous_const.mul
  apply continuous_finsetSum
  intro w _
  have ha := (ordinaryWordPath U.velocity U.velocity_continuous w).continuous.congr
    (ordinaryWordPath_apply U.velocity U.velocity_continuous w)
  have hb := (ordinaryWordPath U.derivative U.derivative_continuous w).continuous.congr
    (ordinaryWordPath_apply U.derivative U.derivative_continuous w)
  exact ha.inner hb

/-- The cost is identified with energy change by integration of the actual
derivative, rather than being postulated as a transition label. -/
theorem production_integral {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    realIntegral T hT (productionPath U n) t =
      orderEnergy n (U.velocity t) - orderEnergy n (U.velocity ⟨0, le_rfl, hT⟩) := by
  have hi := eq_initial_add_integral T hT (productionPath U n)
    (extendPath T hT (U.orderEnergyPath n)) (U.orderEnergy_hasDerivWithinAt n) t
  have he : orderEnergy n (U.velocity t) =
      orderEnergy n (U.velocity ⟨0, le_rfl, hT⟩) +
        realIntegral T hT (productionPath U n) t := by
    simpa only [extendPath, projIcc_of_mem hT t.property,
      projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
      NSEvolution.orderEnergyPath, ContinuousMap.coe_mk, integral_apply] using hi
  linarith

namespace Segment

variable {ν : ℝ} {source middle target : FluidState}

/-- Compatible boundary witnesses glue to a solution, with no new forcing. -/
def comp (first : Segment ν source middle) (second : Segment ν middle target) :
    Segment ν source target where
  duration := first.duration + second.duration
  positive := add_pos first.positive second.positive
  evolution := first.evolution.concatenate second.evolution first.positive second.positive
    (first.final.trans second.initial.symm)
  initial := (first.evolution.concatenate_initial second.evolution first.positive
    second.positive (first.final.trans second.initial.symm)).trans first.initial
  final := (first.evolution.concatenate_right second.evolution first.positive
    second.positive (first.final.trans second.initial.symm)
    ⟨second.duration, second.positive.le, le_rfl⟩).trans second.final

/-- Signed cost in physical time, without absolute values or discounting. -/
def cost (h : Segment ν source target) (n : ℕ) : ℝ :=
  realIntegral h.duration h.positive.le (productionPath h.evolution n) h.duration

theorem cost_eq (h : Segment ν source target) (n : ℕ) :
    h.cost n = orderEnergy n target - orderEnergy n source := by
  have he := production_integral h.evolution n ⟨h.duration, h.positive.le, le_rfl⟩
  simpa only [h.initial, h.final, cost] using he

theorem cost_comp (first : Segment ν source middle) (second : Segment ν middle target)
    (n : ℕ) : (first.comp second).cost n = first.cost n + second.cost n := by
  rw [cost_eq, cost_eq, cost_eq]
  ring

theorem kinetic_cost_nonpos (hν : 0 ≤ ν) (h : Segment ν source target) : h.cost 0 ≤ 0 := by
  have he := h.evolution.orderEnergy_zero_le hν ⟨h.duration, h.positive.le, le_rfl⟩
  rw [h.initial, h.final] at he
  rw [cost_eq]
  linarith

end Segment

/-- Every positive prefix of a given evolution is an admissible history edge. -/
def initialSegment {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT)
    (t : Icc (0 : ℝ) T) (ht : 0 < (t : ℝ)) :
    Segment ν (U.velocity ⟨0, le_rfl, hT⟩) (U.velocity t) where
  duration := t
  positive := ht
  evolution := U.restrictTime t ht.le t.property.2
  initial := rfl
  final := rfl

/-- Time is retained along with the complete velocity. -/
abbrev TimedState := ℝ × FluidState

/-- A segment in a fixed physical-time window. The same endpoint velocity
must be supplied by every subsequent segment. -/
structure WindowStep (ν H : ℝ) (source target : TimedState) where
  segment : Segment ν source.2 target.2
  start_nonnegative : 0 ≤ source.1
  clock : target.1 = source.1 + segment.duration
  within : target.1 ≤ H

/-- Gluing preserves the clock and window as well as the full seam state. -/
def WindowStep.comp {ν H : ℝ} {source middle target : TimedState}
    (first : WindowStep ν H source middle) (second : WindowStep ν H middle target) :
    WindowStep ν H source target where
  segment := first.segment.comp second.segment
  start_nonnegative := first.start_nonnegative
  clock := by
    change target.1 = source.1 + (first.segment.duration + second.segment.duration)
    rw [second.clock, first.clock, add_assoc]
  within := second.within

/-- The generic boundary-witness equipment, instantiated with actual NS. -/
def window (ν H : ℝ) (n : ℕ) : CostedRelation TimedState TimedState where
  witness := WindowStep ν H
  cost h := h.segment.cost n

/-- Kinetic energy supplies a genuine certificate for the order-zero cost. -/
theorem kinetic_bounds {ν : ℝ} (hν : 0 ≤ ν) (H : ℝ) :
    (window ν H 0).Bounds (fun _ ↦ 0) (fun _ ↦ 0) := by
  intro source target h
  simpa only [window, add_zero] using h.segment.kinetic_cost_nonpos hν

/-- Its composed costs are bounded independently of the number of segments. -/
theorem kinetic_history_cost_nonpos {ν : ℝ} (hν : 0 ≤ ν) (H : ℝ) (n : ℕ)
    {source target : TimedState} (h : ((window ν H 0).iterate n).witness source target) :
    ((window ν H 0).iterate n).cost h ≤ 0 :=
  CostedRelation.cost_le_initial ((kinetic_bounds hν H).iterate n) (fun _ ↦ le_rfl) h

/-- A nonnegative reserve for the physical production bounds every time in
every evolution, including times outside a selected finite partition. -/
theorem orderEnergy_le_of_reserve {ν T H : ℝ} {hT : 0 ≤ T} {n : ℕ}
    (U : NSEvolution ν T hT) (hTH : T ≤ H) (reserve : TimedState → ℝ)
    (nonnegative : ∀ state, 0 ≤ reserve state)
    (bound : (window ν H n).Bounds reserve reserve) (t : Icc (0 : ℝ) T) :
    orderEnergy n (U.velocity t) ≤ orderEnergy n (U.velocity ⟨0, le_rfl, hT⟩) +
      reserve (0, U.velocity ⟨0, le_rfl, hT⟩) := by
  by_cases ht : (t : ℝ) = 0
  · have he : t = (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) := Subtype.ext ht
    rw [he]
    exact le_add_of_nonneg_right (nonnegative _)
  · have hpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    let h : (window ν H n).witness (0, U.velocity ⟨0, le_rfl, hT⟩)
        (t, U.velocity t) :=
      { segment := initialSegment U t hpos
        start_nonnegative := le_rfl
        clock := by simp [initialSegment]
        within := t.property.2.trans hTH }
    have hc := CostedRelation.cost_le_initial bound nonnegative h
    change (initialSegment U t hpos).cost n ≤ reserve (0, U.velocity ⟨0, le_rfl, hT⟩) at hc
    rw [Segment.cost_eq] at hc
    linarith

/-- The explicit open certificate obligation implies whole-space continuation.
The reserve may depend on the finite horizon and the viscosity. It is finite
at each full initial datum because it is real-valued. Existence of these
order-one reserves is a hypothesis, not a consequence of the ledger laws. -/
theorem hasNSEvolution_of_bellman {ν : ℝ} (hν : 0 < ν)
    (certificates : ∀ H : ℝ, ∃ reserve : TimedState → ℝ,
      (∀ state, 0 ≤ reserve state) ∧ (window ν H 1).Bounds reserve reserve)
    (A : FluidState) (hA : A.toLp ∈ solenoidalSpace) :
    ∀ T, 0 < T → HasNSEvolution ν A T := by
  apply hasNSEvolution_of_orderOne_bound hν A hA
  intro H
  obtain ⟨reserve, nonnegative, bound⟩ := certificates H
  refine ⟨orderEnergy 1 A + reserve (0, A), ?_⟩
  intro S hS hSH U hU t
  have he := orderEnergy_le_of_reserve U hSH reserve nonnegative bound t
  simpa only [hU] using he

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceHistoryBridge
