import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Parameters
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.FutureResponses
import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.CertifiedSections

/-!
# An open contextual former from requests and complete source events

A request telescope retains index values, every rely value and the actual
dependent continuation result. The event carrier remains independent. The
former universally quantifies over requests and existentially retains an
event with the specified focus, captures and target membership.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ResponseSemantics

open _root_.CategoryTheory
open Mettapedia.TypeTheory Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics
open Classifier
open Mettapedia.GSLT.Topos

universe u
variable {D : Presheaf.CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u) (interface : Interface D.Carrier)

/-- These are semantic telescope data, not correctness or completeness fields. -/
structure Requests where
  parameters : Scope W (arity interface)
  values : Wᵒᵖ ⥤ Type u
  project : values ⟶ parameters.1
  indices : ∀ position : Fin interface.indices.length,
    values ⟶ Classifier.Carrier.presheaf operational interface.indices[position].1
  relies : ∀ position : Fin interface.relies.length,
    values ⟶ Classifier.Carrier.presheaf operational interface.relies[position].1
  target : values ⟶ Classifier.Carrier.presheaf operational interface.target

/-- The projections of an independent operational event diagram. -/
structure Observations where
  events : Wᵒᵖ ⥤ Type u
  focus : events ⟶ operational interface.focus
  indices : ∀ position : Fin interface.indices.length, events ⟶ operational interface.indices[position].1
  relies : ∀ position : Fin interface.relies.length, events ⟶ operational interface.relies[position].1
  target : events ⟶ operational interface.target

variable {operational interface}
variable (requests : Requests operational interface) (observed : Observations operational interface)

abbrev query := FunctorToTypes.prod (operational interface.focus) requests.parameters.1
abbrev inputs := FunctorToTypes.prod (operational interface.focus) requests.values
abbrev candidates := FunctorToTypes.prod (inputs requests) observed.events

def project : inputs requests ⟶ query requests where
  app _ := TypeCat.ofHom fun value => (value.1, requests.project.app _ value.2)
  naturality world future arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    change ((operational interface.focus).map arrow value.1,
      requests.project.app future (requests.values.map arrow value.2)) =
      ((operational interface.focus).map arrow value.1,
        requests.parameters.1.map arrow (requests.project.app world value.2))
    exact Prod.ext rfl (requests.project.naturality_apply arrow value.2)

def observe : candidates requests observed ⟶ inputs requests where
  app _ := TypeCat.ofHom Prod.fst
  naturality _ _ _ := rfl

/-- This specification is stated in terms of the independently supplied
source projections, without the generated classifier or interpreter. -/
def SourceResponse {world : Wᵒᵖ} (request : requests.values.obj world)
    (focus : (operational interface.focus).obj world) (event : observed.events.obj world) : Prop :=
  observed.focus.app world event = focus ∧
  (∀ position, (requests.indices position).app world request =
    .operational ((observed.indices position).app world event)) ∧
  (∀ position, (requests.relies position).app world request =
    .operational ((observed.relies position).app world event)) ∧
  Code.Member (.operational (observed.target.app world event)) (requests.target.app world request)

noncomputable def accepted : Subfunctor (candidates requests observed) where
  obj _ := fun value => SourceResponse requests observed value.1.2 value.1.1 value.2
  map arrow value := by
    rintro ⟨focused, indices, relies, target⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (observed.focus.naturality_apply arrow value.2).trans
        (congrArg ((operational interface.focus).map arrow) focused)
    · intro position
      exact ((requests.indices position).naturality_apply arrow value.1.2).trans
        ((congrArg (Code.map arrow) (indices position)).trans
          (congrArg Code.operational ((observed.indices position).naturality_apply arrow value.2).symm))
    · intro position
      exact ((requests.relies position).naturality_apply arrow value.1.2).trans
        ((congrArg (Code.map arrow) (relies position)).trans
          (congrArg Code.operational ((observed.relies position).naturality_apply arrow value.2).symm))
    · have transported := Code.member_map arrow target
      have sameTarget := requests.target.naturality_apply arrow value.1.2
      have sameValue := observed.target.naturality_apply arrow value.2
      change Code.Member (.operational ((operational interface.target).map arrow (observed.target.app _ value.2)))
        (Code.map arrow (requests.target.app _ value.1.2)) at transported
      change requests.target.app _ (requests.values.map arrow value.1.2) = Code.map arrow (requests.target.app _ value.1.2) at sameTarget
      rw [← sameValue, ← sameTarget] at transported
      exact transported

noncomputable def meaning : Subfunctor (query requests) :=
  FutureResponses.classifier (observe requests observed) (project requests) ⊤ (accepted requests observed)

/-- Every future request has an actual complete source event. -/
def SourceMeaning (world : Wᵒᵖ) (focus : (operational interface.focus).obj world)
    (parameters : requests.parameters.1.obj world) : Prop :=
  ∀ (future : Wᵒᵖ) (restriction : world ⟶ future) (request : requests.values.obj future),
    requests.project.app future request = requests.parameters.1.map restriction parameters →
    ∃ event : observed.events.obj future,
      SourceResponse requests observed request ((operational interface.focus).map restriction focus) event

theorem meaning_exact (world : Wᵒᵖ) (focus : (operational interface.focus).obj world)
    (parameters : requests.parameters.1.obj world) :
    (focus, parameters) ∈ (meaning requests observed).obj world ↔
      SourceMeaning requests observed world focus parameters := by
  rw [meaning, FutureResponses.classifier_iff_source]
  constructor
  · intro holds future restriction request over
    obtain ⟨⟨input, event⟩, response, same⟩ := holds future restriction
      ((operational interface.focus).map restriction focus, request) (Prod.ext rfl over) trivial
    change input = ((operational interface.focus).map restriction focus, request) at same
    cases same
    exact ⟨event, response⟩
  · intro holds future restriction input over _
    rcases input with ⟨actualFocus, request⟩
    change (actualFocus, requests.project.app future request) =
      ((operational interface.focus).map restriction focus,
        requests.parameters.1.map restriction parameters) at over
    have focusEq : actualFocus = (operational interface.focus).map restriction focus :=
      congrArg Prod.fst over
    have parameterEq : requests.project.app future request =
        requests.parameters.1.map restriction parameters := congrArg Prod.snd over
    obtain ⟨event, response⟩ := holds future restriction request parameterEq
    refine ⟨((actualFocus, request), event), ?_, rfl⟩
    change SourceResponse requests observed request actualFocus event
    rw [focusEq]
    exact response

/-- Reindexing an open parameter environment preserves the independent
future-response law, including all newly available rely values. -/
theorem source_restrict {world future : Wᵒᵖ} (restriction : world ⟶ future)
    (focus : (operational interface.focus).obj world)
    (parameters : requests.parameters.1.obj world)
    (holds : SourceMeaning requests observed world focus parameters) :
    SourceMeaning requests observed future
      ((operational interface.focus).map restriction focus)
      (requests.parameters.1.map restriction parameters) :=
  (meaning_exact requests observed future _ _).mp
    ((meaning requests observed).map restriction
      ((meaning_exact requests observed world focus parameters).mpr holds))

/-- Present requests recover actual source events; different events remain
separate elements of the supplied operational event carrier. -/
theorem current_response {world : Wᵒᵖ}
    (focus : (operational interface.focus).obj world)
    (parameters : requests.parameters.1.obj world)
    (holds : SourceMeaning requests observed world focus parameters)
    (request : requests.values.obj world) (over : requests.project.app world request = parameters) :
    ∃ event : observed.events.obj world, SourceResponse requests observed request focus event := by
  have response := holds world (𝟙 world) request (by simpa only [Functor.map_id_apply] using over)
  simpa only [Functor.map_id_apply] using response

/-- The output is an actual certified value in the common native model. -/
noncomputable def former :
    (Classifier.CertifiedProjection.certifiedAt operational interface.focus interface.resultSort
      requests.parameters.1).decoded.sections :=
  Classifier.CertifiedSections.classifier operational interface.focus interface.resultSort (meaning requests observed)

/-- Decoded membership of the output is the independently quantified source law. -/
theorem former_exact (world : Wᵒᵖ) (focus : (operational interface.focus).obj world)
    (parameters : requests.parameters.1.obj world) :
    Code.Member (.operational focus)
      (Classifier.CertifiedProjection.certifiedAtEquiv operational interface.focus interface.resultSort
        requests.parameters.1 ⟨world, parameters⟩
          ((former requests observed).val ⟨world, parameters⟩)).val ↔
      SourceMeaning requests observed world focus parameters :=
  (Classifier.CertifiedSections.classifier_exact operational _ _ _ world parameters focus).trans
    (meaning_exact requests observed world focus parameters)

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ResponseSemantics
