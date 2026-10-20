import Mettapedia.OSLF.NativeTypes.Runtime.Interface
import Mettapedia.OSLF.NativeTypes.Decision.Machine.State

open Mettapedia.OSLF.Framework

/-!
# Retained public native-judgment sessions

Admission refusals and unresolved profile obligations are distinct states.
An admitted session retains its decoded source, pending formula work and
ordered execution observations. Resumption consumes one shared work budget.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Runtime.Description
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

inductive Session (driver : Driver) (runtime : Engine driver)
    (formula : driver.Formula) (raw : Pattern) where
  | refusedSource (reason : SourceIssue)
  | refusedFormula (source : driver.Decoded raw) (reason : Mettapedia.OSLF.NativeTypes.Decision.Admission.Refusal)
  | rejectedCube (source : driver.Decoded raw)
  | unresolvedCube (source : driver.Decoded raw)
  | running (source : driver.Decoded raw)
      (state : Mettapedia.OSLF.NativeTypes.Decision.Machine.State
        (Mettapedia.OSLF.NativeTypes.Decision.Machine.Evidence runtime.cursor)
        (Mettapedia.OSLF.NativeTypes.Decision.Machine.denotation runtime.leaves formula runtime.cursor.spatial.theory source.val))

def Session.nativeResult {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} : Session driver runtime formula raw →
    Mettapedia.OSLF.NativeTypes.Runtime.Description.Result driver formula raw
  | .refusedSource reason => .refusedSource reason
  | .refusedFormula source reason => .checked source (.refused reason)
  | .rejectedCube source => .checked source .rejectedCube
  | .unresolvedCube source => .checked source .unresolvedCube
  | .running source state => .checked source (.semantic (Outcome.map
      (Iff.of_eq (congrArg (fun predicate : GSLTTypeSynthesis.EquationPredicate driver.system =>
        predicate source.val) (Mettapedia.OSLF.NativeTypes.Decision.Machine.denotation_comparison
          runtime.leaves driver.tests runtime.leaf_meaning formula runtime.cursor.spatial.theory |>.trans
            (congrArg (fun spatial => Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.denotation driver.tests formula spatial)
              runtime.spatial_meaning)))) state.outcome))

def Session.readout {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} (session : Session driver runtime formula raw) :
    Mettapedia.OSLF.NativeTypes.Runtime.Description.Readout := session.nativeResult.readout

theorem running_readout {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} (source : driver.Decoded raw)
    (state : Mettapedia.OSLF.NativeTypes.Decision.Machine.State
      (Mettapedia.OSLF.NativeTypes.Decision.Machine.Evidence runtime.cursor)
      (Mettapedia.OSLF.NativeTypes.Decision.Machine.denotation runtime.leaves formula runtime.cursor.spatial.theory source.val)) :
    (Session.running source state).readout = .judgment
      (match state.outcome.answer with | some answer => .decided answer | none => .unknown) := by
  cases result : state.outcome <;> simp only [Session.readout, Session.nativeResult,
    Mettapedia.OSLF.NativeTypes.Runtime.Description.Result.readout, Mettapedia.OSLF.NativeTypes.Decision.Admission.Verdict.readout,
    result, Outcome.map, Outcome.answer]

def Session.spent {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} : Session driver runtime formula raw → Nat
  | .running _ state => state.spent
  | _ => 0

/-- A settled formula may have short-circuited. This is not frontier closure. -/
def Session.settled {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} : Session driver runtime formula raw → Bool
  | .running _ state => state.outcome.answer.isSome
  | _ => false

def Session.observations {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} : Session driver runtime formula raw →
    List (Mettapedia.OSLF.NativeTypes.Decision.Machine.Observation runtime.cursor)
  | .running _ state => state.observations.filterMap
      Mettapedia.OSLF.NativeTypes.Decision.Machine.Evidence.operational?
  | _ => []

def Session.spatialObservations {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} : Session driver runtime formula raw →
    List (Mettapedia.OSLF.NativeTypes.Decision.Machine.SpatialObservation runtime.cursor)
  | .running _ state => state.observations.filterMap
      Mettapedia.OSLF.NativeTypes.Decision.Machine.Evidence.separation?
  | _ => []

/-- The joint archive retains the interleaving of operational and structural work. -/
def Session.evidence {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} : Session driver runtime formula raw →
    List (Mettapedia.OSLF.NativeTypes.Decision.Machine.Evidence runtime.cursor)
  | .running _ state => state.observations
  | _ => []

def resume {driver : Driver} {runtime : Engine driver} {formula : driver.Formula} {raw : Pattern}
    (fuel : Nat) : Session driver runtime formula raw → Session driver runtime formula raw
  | .running source state => .running source (Mettapedia.OSLF.NativeTypes.Decision.Machine.resume fuel state)
  | other => other

theorem resume_add {driver : Driver} {runtime : Engine driver} {formula : driver.Formula} {raw : Pattern}
    (first more : Nat) (session : Session driver runtime formula raw) :
    resume (first + more) session = resume more (resume first session) := by
  cases session <;> simp only [resume]
  exact congrArg (Session.running _) (Mettapedia.OSLF.NativeTypes.Decision.Machine.resume_add first more _)

theorem resume_spent_le {driver : Driver} {runtime : Engine driver} {formula : driver.Formula} {raw : Pattern}
    (fuel : Nat) (session : Session driver runtime formula raw) :
    (resume fuel session).spent ≤ session.spent + fuel := by
  cases session with
  | running source state => exact Mettapedia.OSLF.NativeTypes.Decision.Machine.resume_spent_le state fuel
  | refusedSource | refusedFormula | rejectedCube | unresolvedCube =>
    simp only [resume, Session.spent, Nat.zero_add, Nat.zero_le]

theorem resume_observations_prefix {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} (fuel : Nat) (session : Session driver runtime formula raw) :
    ∃ suffix, (resume fuel session).observations = session.observations ++ suffix := by
  cases session with
  | running source state =>
    obtain ⟨suffix, extended⟩ :=
      Mettapedia.OSLF.NativeTypes.Decision.Machine.resume_observations_prefix state fuel
    exact ⟨suffix.filterMap Mettapedia.OSLF.NativeTypes.Decision.Machine.Evidence.operational?, by
      simp only [resume, Session.observations, extended, List.filterMap_append]⟩
  | refusedSource | refusedFormula | rejectedCube | unresolvedCube => exact ⟨[], rfl⟩

theorem resume_conclusive {driver : Driver} {runtime : Engine driver} {formula : driver.Formula} {raw : Pattern}
    (session : Session driver runtime formula raw) (answer : Bool)
    (read : session.readout = .judgment (.decided answer)) (fuel : Nat) :
    resume fuel session = session := by
  cases session with
  | running source state =>
    have decided : state.outcome.Decided := by
      rw [running_readout] at read
      cases result : state.outcome.answer with
      | none => rw [result] at read; cases read
      | some value => exact ⟨value, result⟩
    exact congrArg (Session.running source)
      (Mettapedia.OSLF.NativeTypes.Decision.Machine.resume_conclusive state decided fuel)
  | refusedSource | refusedFormula | rejectedCube | unresolvedCube => rfl

theorem positive {driver : Driver} {runtime : Engine driver} {formula : driver.Formula} {raw : Pattern}
    (session : Session driver runtime formula raw)
    (read : session.readout = .judgment (.decided true)) : Meaning driver formula raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.Description.positive driver formula raw session.nativeResult read

theorem negative {driver : Driver} {runtime : Engine driver} {formula : driver.Formula} {raw : Pattern}
    (session : Session driver runtime formula raw)
    (read : session.readout = .judgment (.decided false)) : ¬ Meaning driver formula raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.Description.negative driver formula raw session.nativeResult read

theorem observation_step {driver : Driver} {runtime : Engine driver} {formula : driver.Formula} {raw : Pattern}
    (session : Session driver runtime formula raw)
    (observation : Mettapedia.OSLF.NativeTypes.Decision.Machine.Observation runtime.cursor)
    (_listed : observation ∈ session.observations) :
    driver.system.Step observation.source (runtime.cursor.target observation.source observation.receipt) :=
  observation.step

theorem spatial_observation_split {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} (session : Session driver runtime formula raw)
    (observation : Mettapedia.OSLF.NativeTypes.Decision.Machine.SpatialObservation runtime.cursor)
    (_listed : observation ∈ session.spatialObservations) :
    driver.backend.spatial.theory.Split observation.index observation.source
      observation.parts.1 observation.parts.2 := by
  rw [← runtime.spatial_meaning]
  exact observation.split

theorem resume_evidence_prefix {driver : Driver} {runtime : Engine driver}
    {formula : driver.Formula} {raw : Pattern} (fuel : Nat) (session : Session driver runtime formula raw) :
    ∃ suffix, (resume fuel session).evidence = session.evidence ++ suffix := by
  cases session with
  | running source state =>
    exact Mettapedia.OSLF.NativeTypes.Decision.Machine.resume_observations_prefix state fuel
  | refusedSource | refusedFormula | rejectedCube | unresolvedCube => exact ⟨[], rfl⟩

end Mettapedia.OSLF.NativeTypes.Runtime
