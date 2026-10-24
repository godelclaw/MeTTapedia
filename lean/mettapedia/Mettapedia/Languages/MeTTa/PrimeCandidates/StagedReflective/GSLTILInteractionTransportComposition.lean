import Mettapedia.GSLT.Core.OperationalPathFibration
import Mettapedia.Languages.MeTTa.PrimeCandidates.StagedReflective.GSLTILInteractionTransport

/-!
# Compositionality of proof-relevant GSLT-IL interaction transport

Transport through two represented language routes retains two nested
provenance wrappers.  Transport through their operational composite retains
one wrapper around the same source occurrence.  This module proves that these
presentations and all of their finite histories are equivalent, not merely
equal after endpoint erasure.

The equivalence is intentionally stated at the transported target.  A
non-injective route may make source events with different source endpoints
composable after translation, so an arbitrary transported target history need
not reflect to one source history.  Compositional transport nevertheless
retains exactly the same sites and occurrence evidence in its nested and
flattened forms.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILInteractionTransportComposition

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILInteractionTransport
open Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILTypedOperationComposition
open Mettapedia.Languages.MeTTa.PrimeCandidates.IndexedLanguageChange
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationAdmission
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationSyntax

open Mettapedia.GSLT.IndexedOperational.EventTransport

universe uSite uEvent

/-! ## Typed GSLT-IL programs instantiate the operational law -/

/-- The operational interpretation of authored path composition is exactly
the composite of the two interpreted translations. -/
theorem programTranslation_comp
    (model : CandidateModel)
    {first middle last : Language}
    (earlier : Program first middle) (later : Program middle last) :
    programTranslation model (Quiver.Path.comp earlier later) =
      OperationalTranslation.comp
        (programTranslation model earlier) (programTranslation model later) := by
  apply OperationalTranslation.ext
  funext state
  change
    transportTerm (diagram model)
        (gsltInterpretation.map (Quiver.Path.comp earlier later)) state =
      transportTerm (diagram model) (gsltInterpretation.map later)
        (transportTerm (diagram model) (gsltInterpretation.map earlier) state)
  have mapped :
      gsltInterpretation.map (Quiver.Path.comp earlier later) =
        CategoryTheory.CategoryStruct.comp
          (gsltInterpretation.map earlier) (gsltInterpretation.map later) :=
    gsltInterpretation.map_comp earlier later
  rw [mapped]
  exact transportTerm_comp (diagram model)
    (gsltInterpretation.map earlier) (gsltInterpretation.map later) state

/-- The path-level equivalence above is directly the interaction-transport law
for any pair of typed GSLT-IL programs. -/
def typedProgramTransportCompEquiv
    (model : CandidateModel)
    {first middle last : Language}
    (earlier : Program first middle) (later : Program middle last)
    (presentation : InteractionPresentation (SemanticTheoryAt model first))
    {source target : StateAt model last} :
    EventPath
        (transportedPresentation (programTranslation model later)
          (transportedPresentation (programTranslation model earlier)
            presentation)) source target ≃
      EventPath
        (transportedPresentation
          (OperationalTranslation.comp (programTranslation model earlier)
            (programTranslation model later)) presentation) source target :=
  transportedPathCompEquiv (programTranslation model earlier)
    (programTranslation model later) presentation

/-- Successive interaction transport is equivalent to transport along the
actual authored composite GSLT-IL program, not merely an extensionally chosen
operational map. -/
def authoredProgramTransportCompEquiv
    (model : CandidateModel)
    {first middle last : Language}
    (earlier : Program first middle) (later : Program middle last)
    (presentation : InteractionPresentation (SemanticTheoryAt model first))
    {source target : StateAt model last} :
    EventPath
        (transportedPresentation (programTranslation model later)
          (transportedPresentation (programTranslation model earlier)
            presentation)) source target ≃
      EventPath
        (programTransportedPresentation model
          (Quiver.Path.comp earlier later) presentation) source target := by
  change EventPath
      (transportedPresentation (programTranslation model later)
        (transportedPresentation (programTranslation model earlier)
          presentation)) source target ≃
    EventPath
      (transportedPresentation
        (representedProgramRoute model
          (Quiver.Path.comp earlier later)).toOperationalTranslation
        presentation) source target
  rw [representedProgramRoute_toOperationalTranslation,
    programTranslation_comp]
  exact typedProgramTransportCompEquiv model earlier later presentation

/-! ## Proof-relevant non-collapse control -/

namespace Canary

open Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILInteractionTransport.Canary

/-- Transport the two raw fork worlds first through identity and then through
the endpoint-collapsing route. -/
def twiceTransportedLeft :=
  transportEventPath collapseFork
    (transportedPresentation (OperationalTranslation.id forkTheory)
      forkPresentation)
    (transportEventPath (OperationalTranslation.id forkTheory)
      forkPresentation leftPath)

def twiceTransportedRight :=
  transportEventPath collapseFork
    (transportedPresentation (OperationalTranslation.id forkTheory)
      forkPresentation)
    (transportEventPath (OperationalTranslation.id forkTheory)
      forkPresentation rightPath)

/-- Read the twice-retained source sites without attempting endpoint
reflection through the non-injective route. -/
def twiceOriginSites :
    {source target :
      Mettapedia.GSLT.Core.InteractionEvent.Canary.loopTheory.Term} →
    EventPath
      (transportedPresentation collapseFork
        (transportedPresentation (OperationalTranslation.id forkTheory)
          forkPresentation)) source target → List ForkSite
  | _, _, .nil _ => []
  | _, _, .cons (site := site) _ rest => site :: twiceOriginSites rest

@[simp] theorem twiceTransportedLeft_sites :
    twiceOriginSites twiceTransportedLeft = [.chooseLeft] := by
  rfl

@[simp] theorem twiceTransportedRight_sites :
    twiceOriginSites twiceTransportedRight = [.chooseRight] := by
  rfl

/-- Compositional transport does not identify raw worlds merely because their
visible targets coincide after the later route. -/
theorem successive_transport_retains_distinct_raw_worlds :
    twiceTransportedLeft ≠ twiceTransportedRight := by
  intro equal
  have siteEqual := congrArg twiceOriginSites equal
  have impossible : [ForkSite.chooseLeft] = [ForkSite.chooseRight] :=
    twiceTransportedLeft_sites.symm.trans
      (siteEqual.trans twiceTransportedRight_sites)
  simp at impossible

/-- A target-only history made composable by the deliberately collapsing
translation.  Its two occurrences come from incompatible source worlds. -/
def collapsedLeftEvent :
    (transportedPresentation collapseFork forkPresentation).Event
      .chooseLeft () () :=
  .ofSource ForkEvent.chooseLeft

def collapsedRightEvent :
    (transportedPresentation collapseFork forkPresentation).Event
      .chooseRight () () :=
  .ofSource ForkEvent.chooseRight

def collapsedCrossWorldHistory :
    EventPath (transportedPresentation collapseFork forkPresentation) () () :=
  .cons collapsedLeftEvent
    (.cons collapsedRightEvent
      (.nil (presentation :=
        transportedPresentation collapseFork forkPresentation) ()))

theorem rewritePath_length_zero_of_normal
    {theory : GSLT} {source target : theory.Term}
    (normal : theory.IsNormalForm source)
    (path : theory.RewritePath source target) : path.length = 0 := by
  cases path with
  | nil => rfl
  | cons step _ => exact (normal ⟨_, step⟩).elim

theorem forkLeft_normal : forkTheory.IsNormalForm .left := by
  simp [forkTheory, GSLT.IsNormalForm, GSLT.IsRedex, GSLT.Step]

theorem forkRight_normal : forkTheory.IsNormalForm .right := by
  simp [forkTheory, GSLT.IsNormalForm, GSLT.IsRedex, GSLT.Step]

theorem forkRewritePath_length_le_one
    : {source target : ForkState} →
      (path : forkTheory.RewritePath source target) → path.length ≤ 1
  | _, _, .nil _ => by simp [GSLT.RewritePath.length]
  | _, _, .cons step rest => by
      rcases step.2 with middleIsLeft | middleIsRight
      · cases middleIsLeft
        have restLength :=
          rewritePath_length_zero_of_normal forkLeft_normal rest
        simp [GSLT.RewritePath.length, restLength]
      · cases middleIsRight
        have restLength :=
          rewritePath_length_zero_of_normal forkRight_normal rest
        simp [GSLT.RewritePath.length, restLength]

theorem forkPath_length_le_one
    {source target : ForkState}
    (path : EventPath forkPresentation source target) :
    EventPath.pathLength forkPresentation path ≤ 1 := by
  have bounded := forkRewritePath_length_le_one (EventPath.erase _ path)
  erw [EventPath.erase_length] at bounded
  exact bounded

/-- Preservation cannot be strengthened to unconditional path reflection:
the non-injective route exposes a valid two-event target history with no
single source history. -/
theorem noninjective_transport_does_not_reflect_all_histories :
    ¬ ∃ (source target : ForkState)
        (path : EventPath forkPresentation source target),
      transportEventPath collapseFork forkPresentation path =
        collapsedCrossWorldHistory := by
  rintro ⟨source, target, path, equal⟩
  have transportedLength :
      EventPath.pathLength
          (transportedPresentation collapseFork forkPresentation)
          (transportEventPath collapseFork forkPresentation path) = 2 := by
    rw [equal]
    simp [collapsedCrossWorldHistory, EventPath.pathLength]
  have sourceLength : EventPath.pathLength forkPresentation path = 2 := by
    rw [← transportEventPath_length collapseFork forkPresentation path]
    exact transportedLength
  have bounded := forkPath_length_le_one path
  omega

end Canary

#print axioms transportedEventIdentityEquiv
#print axioms transportedEventCompEquiv
#print axioms transportedPathIdentityEquiv
#print axioms transportedPathCompEquiv
#print axioms flatten_transport_twice
#print axioms mapRewritePath_comp
#print axioms flattenTransportedPath_append
#print axioms programTranslation_comp
#print axioms typedProgramTransportCompEquiv
#print axioms authoredProgramTransportCompEquiv
#print axioms Canary.successive_transport_retains_distinct_raw_worlds
#print axioms Canary.noninjective_transport_does_not_reflect_all_histories

end Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILInteractionTransportComposition
