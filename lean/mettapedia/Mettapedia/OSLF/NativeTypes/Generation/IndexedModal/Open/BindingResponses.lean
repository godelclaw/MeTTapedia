import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.FutureResponses
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaInputs

/-!
# Contextual response classifiers over original binding receipts

Classifier parameters retain the independently typed local focus and every
matched capture. Requests add the ordered rely values. The source program
is deliberately existential: complete original receipt frames map to
requests after forgetting the program, while keeping its complete evidence
in the event carrier. Target conditions are natural predicates of those
events, so universal may membership sees all future substitutions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.BindingResponses

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Modal
open CurriedBindingLanguage BindingSemanticAdmission IntrinsicScopedConditionalPresheaf
open NativeBindingSchemaInputs NativeBindingLocalValues

universe u v w

/-- Ordered heterogeneous tuples use the same presheaf action at every
generated position; no slot list is supplied separately. -/
def tuple {C : Type u} [Category.{v} C] {I : Type}
    (family : I → C ⥤ Type) : C ⥤ Type where
  obj X := ∀ index, (family index).obj X
  map arrow := TypeCat.ofHom (fun values index => (family index).map arrow (values index))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro values
    funext index
    exact (family index).map_id_apply X (values index)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro values
    funext index
    exact (family index).map_comp_apply first second (values index)

variable {plan : Plan} (header : NativeModalHeaders.Header plan)

abbrev Base := IntrinsicScopedConditionalPresheaf.Base (algebra plan.snapshot.language)

def parameters : Base (plan := plan) ⥤ Type :=
  FunctorToTypes.prod
    (values (language := plan.snapshot.language)
      (NativeEventDeclarations.schema plan header.origin).focusBound
      (NativeEventDeclarations.schema plan header.origin).focusCarrier)
    (tuple fun index : Fin header.matched.length =>
      values (language := plan.snapshot.language)
        header.matched[index].slot.dependencies header.matched[index].slot.expected)

def requests : Base (plan := plan) ⥤ Type :=
  FunctorToTypes.prod (parameters header)
    (tuple fun index : Fin header.rely.length =>
      values (language := plan.snapshot.language)
        header.rely[index].slot.dependencies header.rely[index].slot.expected)

def project : requests header ⟶ parameters header where
  app _ := TypeCat.ofHom Prod.fst
  naturality := by intros; rfl

def forgetSource (sort : String) : inputs header sort ⟶ requests header where
  app _ := TypeCat.ofHom fun input => ((input.focus, input.matched), input.rely)
  naturality := by intros; rfl

noncomputable def observe
    (decoded : NativeModalHeaders.decode? plan header.origin = some header) (sort : String)
    (freeEmpty : plan.snapshot.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan)) :
    events header sort freeEmpty ready ⟶ requests header :=
  NativeBindingSchemaInputs.observe header decoded sort freeEmpty ready ≫ forgetSource header sort

variable (decoded : NativeModalHeaders.decode? plan header.origin = some header) (sort : String)
    (freeEmpty : plan.snapshot.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))

noncomputable def classifier (rely : Subfunctor (requests header))
    (post : Subfunctor (events header sort freeEmpty ready)) : Subfunctor (parameters header) :=
  FutureResponses.classifier (observe header decoded sort freeEmpty ready) (project header) rely post

/-- A source response is a complete original scoped firing whose actual
focus and completed ordered captures match the independent request. -/
def SourceResponse {X : Base (plan := plan)}
    (frame : (events header sort freeEmpty ready).obj X)
    (request : (requests header).obj X) : Prop :=
  frame.focus = request.1.1.val ∧
    (∀ index, captureValue freeEmpty frame.point header.matched[index].slot
      (matchedPresent header decoded frame index) = request.1.2 index) ∧
    (∀ index, captureValue freeEmpty frame.point header.rely[index].slot
      (relyPresent header decoded frame index) = request.2 index)

theorem observes_iff_source {X : Base (plan := plan)}
    (frame : (events header sort freeEmpty ready).obj X)
    (request : (requests header).obj X) :
    (observe header decoded sort freeEmpty ready).app X frame = request ↔
      SourceResponse header decoded sort freeEmpty ready frame request := by
  change (((observeValue header decoded freeEmpty frame).focus,
      (observeValue header decoded freeEmpty frame).matched),
        (observeValue header decoded freeEmpty frame).rely) = request ↔ _
  constructor
  · intro same
    refine ⟨congrArg (fun value => value.1.1.val) same, ?_, ?_⟩
    · intro index
      exact congrArg (fun value => value.1.2 index) same
    · intro index
      exact congrArg (fun value => value.2 index) same
  · rintro ⟨focus, matched, relies⟩
    apply Prod.ext
    · apply Prod.ext
      · exact Subtype.ext focus
      · exact funext matched
    · exact funext relies

/-- The independent source reading quantifies over future contexts and
typed requests. The witnessed source program stays inside the receipt. -/
def SourceMeaning (rely : Subfunctor (requests header))
    (post : Subfunctor (events header sort freeEmpty ready))
    (X : Base (plan := plan)) (parameter : (parameters header).obj X) : Prop :=
  ∀ (Y : Base (plan := plan)) (substitution : X ⟶ Y) (request : (requests header).obj Y),
    request.1 = (parameters header).map substitution parameter → request ∈ rely.obj Y →
    ∃ frame : (events header sort freeEmpty ready).obj Y,
      frame ∈ post.obj Y ∧ SourceResponse header decoded sort freeEmpty ready frame request

theorem classifier_iff_source (rely : Subfunctor (requests header))
    (post : Subfunctor (events header sort freeEmpty ready))
    (X : Base (plan := plan)) (parameter : (parameters header).obj X) :
    parameter ∈ (classifier header decoded sort freeEmpty ready rely post).obj X ↔
      SourceMeaning header decoded sort freeEmpty ready rely post X parameter := by
  rw [classifier, FutureResponses.classifier_iff_source]
  constructor
  · intro holds Y substitution request aligned requested
    obtain ⟨frame, good, observed⟩ := holds Y substitution request aligned requested
    exact ⟨frame, good, (observes_iff_source header decoded sort freeEmpty ready frame request).mp observed⟩
  · intro holds Y substitution request aligned requested
    obtain ⟨frame, good, source⟩ := holds Y substitution request aligned requested
    exact ⟨frame, good, (observes_iff_source header decoded sort freeEmpty ready frame request).mpr source⟩

theorem current (rely : Subfunctor (requests header))
    (post : Subfunctor (events header sort freeEmpty ready))
    {X : Base (plan := plan)} {parameter : (parameters header).obj X}
    (holds : parameter ∈ (classifier header decoded sort freeEmpty ready rely post).obj X)
    (request : (requests header).obj X) (aligned : request.1 = parameter) (requested : request ∈ rely.obj X) :
    ∃ frame : (events header sort freeEmpty ready).obj X,
      frame ∈ post.obj X ∧ SourceResponse header decoded sort freeEmpty ready frame request := by
  obtain ⟨frame, good, observed⟩ := FutureResponses.current
    (observe header decoded sort freeEmpty ready) (project header) rely post holds request aligned requested
  exact ⟨frame, good, (observes_iff_source header decoded sort freeEmpty ready frame request).mp observed⟩

/-- Context substitution includes weakening and renaming, with the original
local dependency prefix protected by each value presheaf's lifted action. -/
theorem substitution (rely : Subfunctor (requests header))
    (post : Subfunctor (events header sort freeEmpty ready))
    {X Y : Base (plan := plan)} (arrow : X ⟶ Y)
    {parameter : (parameters header).obj X}
    (holds : parameter ∈ (classifier header decoded sort freeEmpty ready rely post).obj X) :
    (parameters header).map arrow parameter ∈
      (classifier header decoded sort freeEmpty ready rely post).obj Y :=
  FutureResponses.restrict _ _ _ _ arrow holds

/-- Receipt transport retains the entire original firing payload. -/
theorem receipt_substitution {X Y : Base (plan := plan)} (arrow : X ⟶ Y)
    (frame : (events header sort freeEmpty ready).obj X) :
    NativeReceiptRechecking.read
        ((events header sort freeEmpty ready).map arrow frame).point.val.receipt =
      NativeOperationalReceiptTransport.payload
        (NativeBindingEventAction.bound X.unop.context)
        (NativeBindingEventAction.bound Y.unop.context)
        (NativeBindingRendering.assignment (NativeAuthoredEventPresheaf.morphismSub arrow))
        (NativeReceiptRechecking.read frame.point.val.receipt) :=
  NativeAuthoredEventAction.action_read (GeneralPlanEnvironment.grammar plan)
    freeEmpty ready (NativeAuthoredEventPresheaf.morphismSub arrow) frame.point.val

/-- A concrete ambient context in the original authored binding clone. -/
def world (ambient : List String) : Base (plan := plan) :=
  Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
    (algebra plan.snapshot.language).substitution.toClone ambient)

def substitutionArrow {source target : List String}
    (substitution : Sub (signature plan.snapshot.language) source target) :
    world (plan := plan) source ⟶ world (plan := plan) target := by
  apply Quiver.Hom.op
  change (position : Fin source.length) → Term (signature plan.snapshot.language) target (source.get position)
  exact fun position => substitution _ (varOfIdx (S := signature plan.snapshot.language) source position)

theorem substitutionArrow_read {source target : List String}
    (substitution : Sub (signature plan.snapshot.language) source target) :
    NativeAuthoredEventPresheaf.morphismSub (substitutionArrow substitution) = substitution := by
  funext sort position
  change BindingSubstitutionAlgebra.fromPositions source
    (fun index => substitution _ (varOfIdx (S := signature plan.snapshot.language) source index))
      sort position = _
  exact BindingSubstitutionAlgebra.fromPositions_ofEnvironment substitution position

/-- Weakening is a genuine clone arrow, not an extra action on syntax. -/
def weakeningArrow (ambient : List String) (fresh : String) :
    world (plan := plan) ambient ⟶ world (plan := plan) (fresh :: ambient) :=
  substitutionArrow (fun _ position => Term.var (.succ position))

def renamingArrow {source target : List String}
    (mapping : Ren (signature plan.snapshot.language) source target) :
    world (plan := plan) source ⟶ world (plan := plan) target :=
  substitutionArrow (fun sort position => Term.var (mapping sort position))

theorem weakening (rely : Subfunctor (requests header))
    (post : Subfunctor (events header sort freeEmpty ready))
    {ambient : List String} (fresh : String)
    {parameter : (parameters header).obj (world (plan := plan) ambient)}
    (holds : parameter ∈ (classifier header decoded sort freeEmpty ready rely post).obj
      (world (plan := plan) ambient)) :
    (parameters header).map (weakeningArrow ambient fresh) parameter ∈
      (classifier header decoded sort freeEmpty ready rely post).obj
        (world (plan := plan) (fresh :: ambient)) :=
  substitution header decoded sort freeEmpty ready rely post (weakeningArrow ambient fresh) holds

theorem underRenaming (rely : Subfunctor (requests header))
    (post : Subfunctor (events header sort freeEmpty ready))
    {source target : List String} (rename : Ren (signature plan.snapshot.language) source target)
    {parameter : (parameters header).obj (world (plan := plan) source)}
    (holds : parameter ∈ (classifier header decoded sort freeEmpty ready rely post).obj
      (world (plan := plan) source)) :
    (parameters header).map (renamingArrow rename) parameter ∈
      (classifier header decoded sort freeEmpty ready rely post).obj
        (world (plan := plan) target) :=
  substitution header decoded sort freeEmpty ready rely post (renamingArrow rename) holds

theorem focus_substitution {source target : List String}
    (substitution : Sub (signature plan.snapshot.language) source target)
    (parameter : (parameters header).obj (world (plan := plan) source)) :
    ((parameters header).map (substitutionArrow substitution) parameter).1.val =
      ContextSubstitution.substitute
        (ContextSubstitution.lift
          (NativeEventDeclarations.schema plan header.origin).focusBound.length
          (NativeBindingRendering.assignment substitution)) parameter.1.val := by
  change ContextSubstitution.substitute
    (ContextSubstitution.lift _
      (NativeBindingRendering.assignment
        (NativeAuthoredEventPresheaf.morphismSub (substitutionArrow substitution)))) _ = _
  rw [substitutionArrow_read]
  rfl

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.BindingResponses
