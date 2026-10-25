import Mettapedia.GSLT.Core.OperationalPathFibration
import Mettapedia.Languages.MeTTa.PrimeCandidates.StagedReflective.GSLTILTypedOperationComposition
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeInteractionFibration

/-!
# Proof-relevant interaction transport along typed GSLT-IL routes

A represented language route preserves semantic steps, but interaction paths
carry more than their endpoints.  This module constructs the proof-relevant
pushforward presentation whose events retain their source site, endpoints, and
occurrence evidence.  Transported paths erase to the ordinary GSLT path map and
preserve their exact chronological length.

Independent component events therefore transport to two authenticated orders
with one common endpoint.  This is not a target-native scheduling license:
resource separation is additional structure and is never inferred from route
representability.  Conversely, raw nondeterministic branches require no
independence certificate.  A many-to-one translation may merge their visible
targets while the pushed-forward occurrence histories remain distinct.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILInteractionTransport

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
open Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILTypedOperationComposition
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationAdmission
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationSyntax
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionFibration

open Mettapedia.GSLT.IndexedOperational.EventTransport

universe uSite uEvent

/-! ## Typed GSLT-IL programs transport interaction paths -/

/-- The proof-relevant interaction presentation induced by one intrinsically
endpoint-indexed candidate language-operation program. -/
def programTransportedPresentation
    (model : CandidateModel) {source target : Language}
    (program : Program source target)
    (presentation : InteractionPresentation (SemanticTheoryAt model source)) :
    InteractionPresentation (SemanticTheoryAt model target) :=
  transportedPresentation
    (representedProgramRoute model program).toOperationalTranslation
    presentation

/-- A typed program transports an authenticated source interaction without
rechecking it or replacing it by endpoint-only execution. -/
def transportProgramInteraction
    (model : CandidateModel) {source target : Language}
    (program : Program source target)
    (presentation : InteractionPresentation (SemanticTheoryAt model source))
    {first last : StateAt model source}
    (path : EventPath presentation first last) :
    EventPath (programTransportedPresentation model program presentation)
      ((programTranslation model program).mapTerm first)
      ((programTranslation model program).mapTerm last) :=
  transportEventPath
    (representedProgramRoute model program).toOperationalTranslation
    presentation path

/-- Erasing the transported interaction is exactly execution-path transport
along the typed program's operational interpretation. -/
theorem transportProgramInteraction_erase
    (model : CandidateModel) {source target : Language}
    (program : Program source target)
    (presentation : InteractionPresentation (SemanticTheoryAt model source))
    {first last : StateAt model source}
    (path : EventPath presentation first last) :
    EventPath.erase (programTransportedPresentation model program presentation)
        (transportProgramInteraction model program presentation path) =
      mapRewritePath (programTranslation model program)
        (EventPath.erase presentation path) := by
  exact transportEventPath_erase
    (representedProgramRoute model program).toOperationalTranslation
    presentation path

/-- The actual interpreted program maps packaged occurrences using the
same state, site and evidence maps as its history transport. -/
def transportProgramOccurrence
    (model : CandidateModel) {source target : Language}
    (program : Program source target)
    (presentation : InteractionPresentation (SemanticTheoryAt model source)) :
    Occurrence presentation →
      Occurrence (programTransportedPresentation model program presentation) :=
  mapOccurrence presentation (programTransportedPresentation model program presentation)
    (representedProgramRoute model program).toOperationalTranslation.mapTerm id
    (transportEvent (representedProgramRoute model program).toOperationalTranslation)

/-- Every chosen event valuation commutes with transport along the actual
represented program, including an undefined partial grade. -/
theorem transportProgramInteraction_grade
    (model : CandidateModel) {source target : Language}
    (program : Program source target)
    (presentation : InteractionPresentation (SemanticTheoryAt model source))
    (valuation : Valuation
      (Occurrence (programTransportedPresentation model program presentation)))
    {first last : StateAt model source}
    (path : EventPath presentation first last) :
    EventPath.grade (programTransportedPresentation model program presentation) valuation
        (transportProgramInteraction model program presentation path) =
      EventPath.grade presentation
        (valuation.pullback (transportProgramOccurrence model program presentation)) path := by
  exact EventPath.grade_map presentation _ _ _ _ valuation path

/-! ## Independent squares transport, but are not inferred -/

/-- The two chronological histories supplied by a genuinely separated
interleaving square after transport through an arbitrary operational route. -/
structure TransportedIndependentSquare
    {left right : GSLT}
    (leftPresentation : InteractionPresentation.{uSite, uEvent} left)
    (rightPresentation : InteractionPresentation.{uSite, uEvent} right)
    {target : GSLT}
    (translation : OperationalTranslation
      (GSLT.interleavingProduct left right) target)
    {leftSite : leftPresentation.Site}
    {rightSite : rightPresentation.Site}
    {leftSource leftTarget : left.Term}
    {rightSource rightTarget : right.Term}
    (leftEvent : leftPresentation.Event leftSite leftSource leftTarget)
    (rightEvent : rightPresentation.Event rightSite rightSource rightTarget) where
  leftThenRight : EventPath
    (transportedPresentation translation
      (fibredPresentation leftPresentation rightPresentation))
    (translation.mapTerm (leftSource, rightSource))
    (translation.mapTerm (leftTarget, rightTarget))
  rightThenLeft : EventPath
    (transportedPresentation translation
      (fibredPresentation leftPresentation rightPresentation))
    (translation.mapTerm (leftSource, rightSource))
    (translation.mapTerm (leftTarget, rightTarget))
  leftLength : EventPath.pathLength _ leftThenRight = 2
  rightLength : EventPath.pathLength _ rightThenLeft = 2

/-- An exact component separation square remains two authenticated histories
under route transport.  This transports established independence; it does not
derive a target resource-separation certificate. -/
def transportIndependentSquare
    {left right : GSLT}
    (leftPresentation : InteractionPresentation.{uSite, uEvent} left)
    (rightPresentation : InteractionPresentation.{uSite, uEvent} right)
    {target : GSLT}
    (translation : OperationalTranslation
      (GSLT.interleavingProduct left right) target)
    {leftSite : leftPresentation.Site}
    {rightSite : rightPresentation.Site}
    {leftSource leftTarget : left.Term}
    {rightSource rightTarget : right.Term}
    (leftEvent : leftPresentation.Event leftSite leftSource leftTarget)
    (rightEvent : rightPresentation.Event rightSite rightSource rightTarget) :
    TransportedIndependentSquare leftPresentation rightPresentation
      translation leftEvent rightEvent where
  leftThenRight := transportEventPath translation
    (fibredPresentation leftPresentation rightPresentation)
    (leftThenRightPath leftPresentation rightPresentation leftEvent rightEvent)
  rightThenLeft := transportEventPath translation
    (fibredPresentation leftPresentation rightPresentation)
    (rightThenLeftPath leftPresentation rightPresentation leftEvent rightEvent)
  leftLength := by simp
  rightLength := by simp

/-- A route reflects distinct branch targets only when its term map carries
the corresponding faithfulness capability.  Step preservation alone is not
such a reflection theorem. -/
theorem distinct_targets_of_injective_transport
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (injective : Function.Injective translation.mapTerm)
    {first second : source.Term} (different : first ≠ second) :
    translation.mapTerm first ≠ translation.mapTerm second :=
  injective.ne different

/-! ## Nondeterministic multiworld control -/

namespace Canary

inductive ForkState where
  | root
  | left
  | right
  deriving DecidableEq

def forkTheory : GSLT where
  Term := ForkState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    source = .root ∧ (target = .left ∨ target = .right)
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

inductive ForkSite where
  | chooseLeft
  | chooseRight
  deriving DecidableEq

inductive ForkEvent : ForkSite → ForkState → ForkState → Type where
  | chooseLeft : ForkEvent .chooseLeft .root .left
  | chooseRight : ForkEvent .chooseRight .root .right

def forkPresentation : InteractionPresentation forkTheory where
  Site := ForkSite
  Event := ForkEvent
  sound := by
    intro site source target event
    cases event with
    | chooseLeft => exact ⟨rfl, Or.inl rfl⟩
    | chooseRight => exact ⟨rfl, Or.inr rfl⟩

def leftPath : EventPath forkPresentation ForkState.root ForkState.left :=
  .cons ForkEvent.chooseLeft
    (.nil (presentation := forkPresentation) ForkState.left)

def rightPath : EventPath forkPresentation ForkState.root ForkState.right :=
  .cons ForkEvent.chooseRight
    (.nil (presentation := forkPresentation) ForkState.right)

/-- Raw choice supplies two branch worlds but no independence diamond. -/
theorem fork_is_nondeterministic_without_diamond :
    forkTheory.Step .root .left ∧
      forkTheory.Step .root .right ∧
      ¬ ∃ join,
        forkTheory.Step .left join ∧ forkTheory.Step .right join := by
  constructor
  · exact ⟨rfl, Or.inl rfl⟩
  constructor
  · exact ⟨rfl, Or.inr rfl⟩
  · rintro ⟨join, leftStep, _rightStep⟩
    exact ForkState.noConfusion leftStep.1

/-- A deliberately many-to-one operational translation. -/
def collapseFork : OperationalTranslation forkTheory
    Mettapedia.GSLT.Core.InteractionEvent.Canary.loopTheory where
  mapTerm := fun _ => ()
  mapEquiv := fun _ => rfl
  mapStep := fun _ => trivial

def transportedLeftPath :=
  transportEventPath collapseFork forkPresentation leftPath

def transportedRightPath :=
  transportEventPath collapseFork forkPresentation rightPath

/-- Read the retained source sites from a transported history. -/
def originSites : {first last :
    Mettapedia.GSLT.Core.InteractionEvent.Canary.loopTheory.Term} →
    EventPath (transportedPresentation collapseFork forkPresentation)
      first last → List ForkSite
  | _, _, .nil _ => []
  | _, _, .cons (site := site) _ rest => site :: originSites rest

@[simp] theorem transportedLeftPath_sites :
    originSites transportedLeftPath = [.chooseLeft] :=
  by rfl

@[simp] theorem transportedRightPath_sites :
    originSites transportedRightPath = [.chooseRight] :=
  by rfl

/-- Endpoint collapse does not collapse proof-relevant branch identity. -/
theorem collapsed_targets_retain_distinct_occurrence_worlds :
    collapseFork.mapTerm ForkState.left =
        collapseFork.mapTerm ForkState.right ∧
      transportedLeftPath ≠ transportedRightPath := by
  constructor
  · rfl
  · intro equal
    have siteEqual := congrArg originSites equal
    have impossible : [ForkSite.chooseLeft] = [ForkSite.chooseRight] :=
      transportedLeftPath_sites.symm.trans
        (siteEqual.trans transportedRightPath_sites)
    simp at impossible

end Canary

#print axioms transportProgramInteraction_erase
#print axioms transportIndependentSquare
#print axioms distinct_targets_of_injective_transport
#print axioms Canary.fork_is_nondeterministic_without_diamond
#print axioms Canary.collapsed_targets_retain_distinct_occurrence_worlds

end Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILInteractionTransport
