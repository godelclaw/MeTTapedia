import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.GradualDependentCapability
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeInteractionObservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.StagedReflective.GSLTILInteractionTransport

/-!
# Gradual dependent interaction as a displayed native capability

An endpoint-only GSLT rewrite path remains executable independently of
whether candidate currently retains its authenticated occurrences.  The exact
native capability over that path is an `EventPath` whose erasure is the same
raw path.  This is the interaction instance of the general gradual dependent
capability architecture.

Exact paths compose and transport constructionally.  Suspended evidence does
not block raw path composition.  Stable blame is not propagated through
composition or language transport unless a separate exact-reflection theorem
is supplied: refuting a component is not, by itself, a proof that every
composite or translated interaction is impossible.

Thus `Compρ` construction, route transport, occurrence observation, and lazy
checking share one proof-relevant carrier without adding unknowns to kernel
conversion or turning an observation into an execution gate.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDependentInteraction

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.IndexedOperational.EventTransport
open Mettapedia.Languages.MeTTa.Experimental.StagedReflective
open Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability
open Mettapedia.TypeTheory.DisplayedEvidence
open Mettapedia.TypeTheory.DisplayedEvidence.Status
open Mettapedia.TypeTheory.DisplayedEvidence.ExactMap (mapSafe mapReflecting)
open Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILInteractionTransport
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteraction
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionInterpretation
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionObservation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

universe uSite uEvent

variable {theory : GSLT}
  (presentation : InteractionPresentation.{uSite, uEvent} theory)

/-! ## Raw chronological composition and exact occurrence paths -/

/-- Exact interaction evidence is an occurrence path together with the
equation identifying its endpoint-only erasure. -/
structure ExactPath {source target : theory.Term}
    (raw : theory.RewritePath source target) where
  path : EventPath presentation source target
  erase_eq : EventPath.erase presentation path = raw

/-- Authenticated occurrence paths form a displayed capability over ordinary
GSLT rewrite paths. -/
def pathFibre (source target : theory.Term) : Family where
  Raw := theory.RewritePath source target
  Exact := ExactPath presentation

/-- Exact chronological composition retains every occurrence in order. -/
def composeExact {source middle target : theory.Term}
    {firstRaw : theory.RewritePath source middle}
    {secondRaw : theory.RewritePath middle target}
    (first : ExactPath presentation firstRaw)
    (second : ExactPath presentation secondRaw) :
    ExactPath presentation (Mettapedia.GSLT.RewritePath.append firstRaw secondRaw) where
  path := EventPath.append presentation first.path second.path
  erase_eq := by
    rw [EventPath.erase_append, first.erase_eq, second.erase_eq]

/-- Chronological composition is an ordinary exact map out of the product
of its two displayed path capabilities. -/
def composeMap {source middle target : theory.Term} :
    ExactMap
      (Family.product (pathFibre presentation source middle)
        (pathFibre presentation middle target))
      (pathFibre presentation source target) where
  mapRaw := fun paths => Mettapedia.GSLT.RewritePath.append paths.1 paths.2
  mapExact := fun evidence =>
    composeExact presentation evidence.1 evidence.2

/-- Gradual interaction composition is constructional only when both
components are exact.  In every other case the raw composite remains the
index and the optional native capability is suspended. -/
def composeState {source middle target : theory.Term}
    {firstRaw : theory.RewritePath source middle}
    {secondRaw : theory.RewritePath middle target} :
    Status (Reason := List Nat) (pathFibre presentation source middle) firstRaw ->
      Status (Reason := List Nat) (pathFibre presentation middle target) secondRaw ->
      Status (Reason := List Nat) (pathFibre presentation source target)
        (Mettapedia.GSLT.RewritePath.append firstRaw secondRaw)
  | first, second =>
      mapSafe (composeMap presentation) (Status.combine first second)

theorem composeState_left_mono {source middle target : theory.Term}
    {firstRaw : theory.RewritePath source middle}
    {secondRaw : theory.RewritePath middle target}
    {refined coarse : Status (Reason := List Nat) (pathFibre presentation source middle) firstRaw}
    (precision : Status.Refines refined coarse)
    (second : Status (Reason := List Nat) (pathFibre presentation middle target) secondRaw) :
    Status.Refines (composeState presentation refined second)
      (composeState presentation coarse second) := by
  exact Status.Refines.mapSafe
    (Status.combine_left_mono precision second)

theorem composeState_right_mono {source middle target : theory.Term}
    {firstRaw : theory.RewritePath source middle}
    {secondRaw : theory.RewritePath middle target}
    (first : Status (Reason := List Nat) (pathFibre presentation source middle) firstRaw)
    {refined coarse : Status (Reason := List Nat) (pathFibre presentation middle target) secondRaw}
    (precision : Status.Refines refined coarse) :
    Status.Refines (composeState presentation first refined)
      (composeState presentation first coarse) := by
  exact Status.Refines.mapSafe
    (Status.combine_right_mono first precision)

/-- Increasing precision in either component increases, and never destroys,
the precision of gradual interaction composition. -/
theorem composeState_mono {source middle target : theory.Term}
    {firstRaw : theory.RewritePath source middle}
    {secondRaw : theory.RewritePath middle target}
    {firstRefined firstCoarse :
      Status (Reason := List Nat) (pathFibre presentation source middle) firstRaw}
    {secondRefined secondCoarse :
      Status (Reason := List Nat) (pathFibre presentation middle target) secondRaw}
    (firstPrecision : Status.Refines firstRefined firstCoarse)
    (secondPrecision : Status.Refines secondRefined secondCoarse) :
    Status.Refines
      (composeState presentation firstRefined secondRefined)
      (composeState presentation firstCoarse secondCoarse) :=
  Status.Refines.trans
    (composeState_left_mono presentation firstPrecision secondRefined)
    (composeState_right_mono presentation firstCoarse secondPrecision)

/-! ## Observation is downstream of exact capability -/

/-- Observe chronological occurrence provenance only when it is retained.
The endpoint-only raw path remains the state index in all three cases. -/
def observe {source target : theory.Term}
    {raw : theory.RewritePath source target} :
    Status (Reason := List Nat) (pathFibre presentation source target) raw ->
      Option (List (Occurrence presentation))
  | .suspended => none
  | .established evidence => some (EventPath.events presentation evidence.path)
  | .refuted _ => none

@[simp] theorem observe_compose_exact {source middle target : theory.Term}
    {firstRaw : theory.RewritePath source middle}
    {secondRaw : theory.RewritePath middle target}
    (first : ExactPath presentation firstRaw)
    (second : ExactPath presentation secondRaw) :
    observe presentation
        (composeState presentation (.established first) (.established second)) =
      some (EventPath.events presentation first.path ++
        EventPath.events presentation second.path) := by
  simp [composeState, Status.combine, mapSafe, composeMap, observe,
    composeExact, EventPath.events_append]

/-- Raw semantics is never reconstructed from optional evidence. -/
def rawOfState {source target : theory.Term}
    {raw : theory.RewritePath source target}
    (_state : Status (Reason := List Nat) (pathFibre presentation source target) raw) :
    theory.RewritePath source target :=
  raw

@[simp] theorem rawOfState_suspended {source target : theory.Term}
    (raw : theory.RewritePath source target) :
    rawOfState presentation
      (.suspended : Status (Reason := List Nat) (pathFibre presentation source target) raw) = raw :=
  rfl

/-! ## Exact language transport and safe cache transport -/

/-- Operational translation is an exact map of occurrence capabilities. -/
def transportMap
    {targetTheory : GSLT}
    (translation : OperationalTranslation theory targetTheory)
    {source target : theory.Term} :
    ExactMap (pathFibre presentation source target)
      (pathFibre (transportedPresentation translation presentation)
        (translation.mapTerm source) (translation.mapTerm target)) where
  mapRaw := mapRewritePath translation
  mapExact := fun evidence =>
    { path := transportEventPath translation presentation evidence.path
      erase_eq := by
        rw [transportEventPath_erase, evidence.erase_eq] }

/-- Positive evidence transports; stable blame is invalidated unless a route
also supplies the stronger exact-reflection capability. -/
def transportState
    {targetTheory : GSLT}
    (translation : OperationalTranslation theory targetTheory)
    {source target : theory.Term}
    {raw : theory.RewritePath source target} :
    Status (Reason := List Nat) (pathFibre presentation source target) raw ->
      Status (Reason := List Nat)
        (pathFibre (transportedPresentation translation presentation)
          (translation.mapTerm source) (translation.mapTerm target))
        (mapRewritePath translation raw) :=
  ExactMap.mapSafe (transportMap presentation translation)

@[simp] theorem transport_exact
    {targetTheory : GSLT}
    (translation : OperationalTranslation theory targetTheory)
    {source target : theory.Term}
    {raw : theory.RewritePath source target}
    (evidence : ExactPath presentation raw) :
    transportState presentation translation (.established evidence) =
      .established ((transportMap presentation translation).mapExact evidence) :=
  rfl

/-- Exact transport retains the chronological occurrence list observed by
the displayed capability, not just the existence of a semantic path. -/
@[simp] theorem observe_transport_exact
    {targetTheory : GSLT}
    (translation : OperationalTranslation theory targetTheory)
    {source target : theory.Term} {raw : theory.RewritePath source target}
    (evidence : ExactPath presentation raw) :
    observe (transportedPresentation translation presentation)
        (transportState presentation translation (.established evidence)) =
      some ((EventPath.events presentation evidence.path).map
        (mapOccurrence presentation (transportedPresentation translation presentation)
          translation.mapTerm id (transportEvent translation))) := by
  exact congrArg some (EventPath.events_map presentation _ _ _ _ evidence.path)

@[simp] theorem transport_refuted_invalidates
    {targetTheory : GSLT}
    (translation : OperationalTranslation theory targetTheory)
    {source target : theory.Term}
    {raw : theory.RewritePath source target}
    (blame : Refutation (Reason := List Nat) (pathFibre presentation source target) raw) :
    transportState presentation translation (.refuted blame) = .suspended :=
  rfl

theorem transportState_mono
    {targetTheory : GSLT}
    (translation : OperationalTranslation theory targetTheory)
    {source target : theory.Term}
    {raw : theory.RewritePath source target}
    {refined coarse : Status (Reason := List Nat) (pathFibre presentation source target) raw}
    (precision : Status.Refines refined coarse) :
    Status.Refines
      (transportState presentation translation refined)
      (transportState presentation translation coarse) :=
  precision.mapSafe

/-- Route transport commutes with exact chronological composition at the
proof-relevant occurrence-path level. -/
theorem transport_path_append
    {targetTheory : GSLT}
    (translation : OperationalTranslation theory targetTheory)
    {source middle target : theory.Term}
    {firstRaw : theory.RewritePath source middle}
    {secondRaw : theory.RewritePath middle target}
    (first : ExactPath presentation firstRaw)
    (second : ExactPath presentation secondRaw) :
    (transportEventPath translation presentation
      (composeExact presentation first second).path) =
      EventPath.append (transportedPresentation translation presentation)
        (transportEventPath translation presentation first.path)
        (transportEventPath translation presentation second.path) := by
  exact transportEventPath_append translation presentation first.path second.path

/-! ## The intrinsic `Compρ` instance -/

/-- Every intrinsic interaction computation immediately supplies exact
gradual evidence for its own endpoint-only erasure. -/
def exactStateOfComputation
    (nativePresentation : InteractionPresentation theory)
    {interpretation : EndpointInterpretation theory}
    {source target : StagedReflectiveTm 0 0}
    (execution : Computation interpretation nativePresentation source target) :
    Status (Reason := List Nat)
      (pathFibre nativePresentation execution.1.1 execution.2.1.1)
      (NativeInteractionObservation.erase execution) :=
  .established ⟨NativeInteractionObservation.path execution, rfl⟩

@[simp] theorem observe_exactStateOfComputation
    (nativePresentation : InteractionPresentation theory)
    {interpretation : EndpointInterpretation theory}
    {source target : StagedReflectiveTm 0 0}
    (execution : Computation interpretation nativePresentation source target) :
    observe nativePresentation
        (exactStateOfComputation nativePresentation execution) =
      some (NativeInteractionObservation.events execution) :=
  rfl

/-- Native `Compρ` composition therefore constructs exact gradual evidence
and exposes chronological provenance without an interior check. -/
theorem observe_composed_computation
    (nativePresentation : InteractionPresentation theory)
    (interpretation : EndpointInterpretation theory)
    {source middle target : StagedReflectiveTm 0 0}
    (first : Computation interpretation nativePresentation source middle)
    (second : Computation interpretation nativePresentation middle target) :
    observe nativePresentation
        (exactStateOfComputation nativePresentation
          (NativeInteractionObservation.compose interpretation nativePresentation
            first second)) =
      some (NativeInteractionObservation.events first ++
        NativeInteractionObservation.events second) := by
  rw [observe_exactStateOfComputation]
  exact congrArg some
    (NativeInteractionObservation.events_compose
      interpretation nativePresentation first second)

/-! ## Indexed protocol and nondeterministic controls -/

namespace Canary

/-- The dependent COMM event selected by `count`, viewed as an exact gradual
interaction state. -/
def indexedCommState (count : Nat) :=
  exactStateOfComputation rhoOccurrencePresentation
    ((interpretedRhoStep (indexedComm count)) PUnit.unit)

/-- Positive and negative protocol facts share one index: the request for one
field has one authenticated occurrence, while a two-field continuation is
uninhabited. -/
theorem one_request_exact_but_two_field_response_uninhabited :
    Option.map List.length
        (observe rhoOccurrencePresentation (indexedCommState 1)) = some 1 ∧
      ¬ ∃ response : SizedResponse 1, response.actual = 2 := by
  constructor
  · rfl
  · exact one_request_rejects_two_field_response

open Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILInteractionTransport.Canary

def leftExact : ExactPath forkPresentation
    (EventPath.erase forkPresentation leftPath) :=
  ⟨leftPath, rfl⟩

/-- A many-to-one route transports the exact occurrence rather than
collapsing it to endpoint equality. -/
theorem collapsed_fork_retains_left_occurrence :
    Option.map List.length
        (observe (transportedPresentation collapseFork forkPresentation)
          (transportState forkPresentation collapseFork (.established leftExact))) =
      some 1 := by
  rfl

/-- A refuted component is not promoted to a translated refutation merely
because a forward operational map exists. -/
theorem arbitrary_refutation_invalidates_under_collapse
    {raw : forkTheory.RewritePath ForkState.root ForkState.left}
    (blame : Refutation (Reason := List Nat)
      (pathFibre forkPresentation ForkState.root ForkState.left) raw) :
    transportState forkPresentation collapseFork (.refuted blame) =
      .suspended :=
  rfl

end Canary

#print axioms composeState_mono
#print axioms transportState_mono
#print axioms transport_path_append
#print axioms observe_composed_computation
#print axioms Canary.one_request_exact_but_two_field_response_uninhabited
#print axioms Canary.collapsed_fork_retains_left_occurrence

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDependentInteraction
