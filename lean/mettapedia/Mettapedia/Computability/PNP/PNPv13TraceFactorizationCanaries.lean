import Mettapedia.Computability.PNP.PNPv13RandomCoinTraceCapture

/-!
# PNP v13 trace-factorization canaries

This module mirrors the finite private validation lab for trace factorization.
A trace assignment is not enough: a named observer must be constant on
target-relevant trace fibers, and randomized observers require that condition
for every coin slice.
-/

namespace Mettapedia.Computability.PNP

/-- States in the finite trace-factorization canaries. -/
inductive TraceFactorizationLabState where
  | left
  | right
deriving DecidableEq, Repr

/-- Trace labels in the finite trace-factorization canaries. -/
inductive TraceFactorizationLabTrace where
  | leftTrace
  | rightTrace
  | sharedTrace
deriving DecidableEq, Repr

/-- Coin labels for the randomized trace-factorization canary. -/
inductive TraceFactorizationLabCoin where
  | coin0
  | coin1
deriving DecidableEq, Repr

/-- Positive canary surface: target-relevant states have distinct traces. -/
def traceFactorizationIdentitySurface :
    V13TraceCaptureSurface TraceFactorizationLabState
      TraceFactorizationLabTrace where
  traceOf
    | .left => .leftTrace
    | .right => .rightTrace
  targetRelevant := fun _ => True

/-- Negative canary surface: target-relevant states share one trace. -/
def traceFactorizationCollapsedSurface :
    V13TraceCaptureSurface TraceFactorizationLabState
      TraceFactorizationLabTrace where
  traceOf
    | .left => .sharedTrace
    | .right => .sharedTrace
  targetRelevant := fun _ => True

/-- Observer that separates the two target-relevant canary states. -/
def traceFactorizationSeparatingObserver :
    TraceFactorizationLabState → Bool
  | .left => false
  | .right => true

/-- Constant observer used as a guard: not every collision blocks every observer. -/
def traceFactorizationConstantObserver :
    TraceFactorizationLabState → Bool
  | _ => true

/-- Randomized observer with a separating deterministic slice at each coin. -/
def traceFactorizationRandomSeparatingObserver :
    TraceFactorizationLabState → TraceFactorizationLabCoin → Bool
  | .left, _ => false
  | .right, _ => true

/-- Positive lab canary: distinct traces support named and universal capture. -/
theorem traceFactorizationIdentitySurface_lab_positive_canary :
    traceFactorizationIdentitySurface.CapturesAllBoolObservers ∧
      traceFactorizationIdentitySurface.ObserverTraceDecodable
        traceFactorizationSeparatingObserver ∧
      traceFactorizationIdentitySurface.ObserverTraceDecodable
        traceFactorizationConstantObserver := by
  refine ⟨?_, ?_, ?_⟩
  · intro observer
    refine
      ⟨fun trace =>
        match trace with
        | .leftTrace => observer .left
        | .rightTrace => observer .right
        | .sharedTrace => false, ?_⟩
    intro state hstate
    cases state <;> rfl
  · refine
      ⟨fun trace =>
        match trace with
        | .leftTrace => false
        | .rightTrace => true
        | .sharedTrace => false, ?_⟩
    intro state hstate
    cases state <;> rfl
  · refine ⟨fun _ => true, ?_⟩
    intro state hstate
    cases state <;> rfl

/-- Negative lab canary: a same-trace separating observer cannot factor. -/
theorem traceFactorizationCollapsed_conflictingObserver_negative_canary :
    traceFactorizationCollapsedSurface.ObserverSameTraceConflict
        traceFactorizationSeparatingObserver ∧
      ¬ traceFactorizationCollapsedSurface.ObserverTraceDecodable
        traceFactorizationSeparatingObserver := by
  refine ⟨?_, ?_⟩
  · refine ⟨.left, .right, trivial, trivial, rfl, ?_⟩
    decide
  · intro hfactor
    rcases hfactor with ⟨decode, hdecode⟩
    have hleft : decode .sharedTrace = false := hdecode .left trivial
    have hright : decode .sharedTrace = true := hdecode .right trivial
    rw [hleft] at hright
    cases hright

/-- Guard canary: a constant observer factors through a collapsed trace. -/
theorem traceFactorizationCollapsed_constantObserver_guard_canary :
    traceFactorizationCollapsedSurface.ObserverTraceDecodable
        traceFactorizationConstantObserver ∧
      ¬ traceFactorizationCollapsedSurface.CapturesAllBoolObservers := by
  refine ⟨?_, ?_⟩
  · refine ⟨fun _ => true, ?_⟩
    intro state hstate
    cases state <;> rfl
  · intro hall
    exact traceFactorizationCollapsed_conflictingObserver_negative_canary.2
      (hall traceFactorizationSeparatingObserver)

/-- Negative lab canary: assigning traces is weaker than factorizing observers. -/
theorem traceFactorizationCollapsed_traceAssignment_negative_canary :
    traceFactorizationCollapsedSurface.traceOf .left = .sharedTrace ∧
      traceFactorizationCollapsedSurface.traceOf .right = .sharedTrace ∧
      ¬ traceFactorizationCollapsedSurface.ObserverTraceDecodable
        traceFactorizationSeparatingObserver := by
  exact
    ⟨rfl, rfl,
      traceFactorizationCollapsed_conflictingObserver_negative_canary.2⟩

/-- Negative lab canary: one conflicting coin slice blocks randomized capture. -/
theorem traceFactorizationCollapsed_randomCoin_negative_canary :
    traceFactorizationCollapsedSurface.RandomObserverSameTraceConflict
        traceFactorizationRandomSeparatingObserver ∧
      ¬ traceFactorizationCollapsedSurface.RandomObserverTraceDecodable
        traceFactorizationRandomSeparatingObserver := by
  refine ⟨?_, ?_⟩
  · refine ⟨.coin0, .left, .right, trivial, trivial, rfl, ?_⟩
    decide
  · intro hfactor
    rcases hfactor with ⟨decode, hdecode⟩
    have hleft : decode .sharedTrace .coin0 = false :=
      hdecode .left .coin0 trivial
    have hright : decode .sharedTrace .coin0 = true :=
      hdecode .right .coin0 trivial
    rw [hleft] at hright
    cases hright

/-- The canaries separate trace assignment from observer factorization. -/
theorem traceFactorizationCanaries_separate_traceAssignment_from_factorization :
    traceFactorizationCollapsedSurface.traceOf .left = .sharedTrace ∧
      traceFactorizationCollapsedSurface.traceOf .right = .sharedTrace ∧
      traceFactorizationCollapsedSurface.ObserverTraceDecodable
        traceFactorizationConstantObserver ∧
      ¬ traceFactorizationCollapsedSurface.ObserverTraceDecodable
        traceFactorizationSeparatingObserver := by
  exact
    ⟨rfl, rfl,
      traceFactorizationCollapsed_constantObserver_guard_canary.1,
      traceFactorizationCollapsed_conflictingObserver_negative_canary.2⟩

end Mettapedia.Computability.PNP
