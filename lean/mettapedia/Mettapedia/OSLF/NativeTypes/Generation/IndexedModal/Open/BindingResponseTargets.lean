import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.BindingResponses
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingModalDiagram

/-!
# Dependent target conditions on original scoped responses

The target predicate may depend on the entire typed request, including
matched values and ordered relies. Its target value is the original
receipt's specified RHS. Pairing those natural readouts supplies the event
predicate used by the future-sensitive universal response classifier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.BindingResponses

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Modal
open CurriedBindingLanguage BindingSemanticAdmission IntrinsicScopedConditionalPresheaf
open NativeBindingSchemaInputs
open ScopedRuleMatching

variable {plan : Plan} (header : NativeModalHeaders.Header plan)
    (decoded : NativeModalHeaders.decode? plan header.origin = some header) (sort : String)
    (freeEmpty : plan.snapshot.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    (admitted : Admitted plan.snapshot.language)
    (labels : (plan.snapshot.language.terms.map (·.label)).Nodup)

noncomputable def target : events header sort freeEmpty ready ⟶
    semanticPrograms (algebra plan.snapshot.language) sort :=
  NativeBindingModalDiagram.forget header sort freeEmpty ready ≫
    NativeAuthoredEventPresheaf.target (GeneralPlanEnvironment.grammar plan) freeEmpty ready admitted labels sort

noncomputable def observedTarget : events header sort freeEmpty ready ⟶
    FunctorToTypes.prod (requests header) (semanticPrograms (algebra plan.snapshot.language) sort) where
  app X := TypeCat.ofHom fun frame =>
    ((observe header decoded sort freeEmpty ready).app X frame,
      (target header sort freeEmpty ready admitted labels).app X frame)
  naturality X Y arrow := by
    apply ConcreteCategory.hom_ext
    intro frame
    change ((observe header decoded sort freeEmpty ready).app Y
        ((events header sort freeEmpty ready).map arrow frame),
      (target header sort freeEmpty ready admitted labels).app Y
        ((events header sort freeEmpty ready).map arrow frame)) =
      ((requests header).map arrow ((observe header decoded sort freeEmpty ready).app X frame),
        (semanticPrograms (algebra plan.snapshot.language) sort).map arrow
          ((target header sort freeEmpty ready admitted labels).app X frame))
    exact Prod.ext ((observe header decoded sort freeEmpty ready).naturality_apply arrow frame)
      ((target header sort freeEmpty ready admitted labels).naturality_apply arrow frame)

noncomputable def targetPost (predicate : Subfunctor
    (FunctorToTypes.prod (requests header) (semanticPrograms (algebra plan.snapshot.language) sort))) :
    Subfunctor (events header sort freeEmpty ready) :=
  predicate.preimage (observedTarget header decoded sort freeEmpty ready admitted labels)

theorem target_read {X : Base (plan := plan)}
    (frame : (events header sort freeEmpty ready).obj X) :
    toPattern ((target header sort freeEmpty ready admitted labels).app X frame) =
      frame.point.val.receipt.target :=
  NativeAuthoredEventAction.targetTerm_read (GeneralPlanEnvironment.grammar plan)
    freeEmpty admitted labels frame.point.val

/-- The RHS belongs to the selected declaration and its actual completed
scoped assignment, rather than merely to some successor relation. -/
theorem specified_rhs {X : Base (plan := plan)}
    (frame : (events header sort freeEmpty ready).obj X) :
    reductWith? (ScopedReflectiveExecution.binderOperation
      (GeneralPlanEnvironment.environment plan).reflection
      (NativeEventDeclarations.schema plan header.origin).declaration.rule)
      (NativeEventDeclarations.schema plan header.origin).declaration.rule
      (NativeEventDeclarations.schema plan header.origin).declaration.binding.spec
      X.unop.context.length frame.point.val.receipt.completed =
        some frame.point.val.receipt.target := by
  have firing := frame.point.val.receipt.valid
  have selected := frame.point.property
  have declared := GeneralPlanEnvironment.selected_rule plan
    (List.mk_mem_zipIdx_iff_getElem?.mp (NativeEventDeclarations.schema plan header.origin).declared)
  have specified := GeneralPlanEnvironment.selected_specification plan
    (List.mk_mem_zipIdx_iff_getElem?.mp (NativeEventDeclarations.schema plan header.origin).declared)
  cases firing with
  | fire actualRule actualSpec _ _ _ _ _ reduct _ =>
      rw [selected] at actualRule actualSpec
      cases Option.some.inj (actualRule.symm.trans declared)
      cases Option.some.inj (actualSpec.symm.trans specified)
      have length : (NativeBindingEventAction.bound X.unop.context).length = X.unop.context.length :=
        List.length_map _
      rw [length] at reduct
      exact reduct

theorem targetPost_iff {X : Base (plan := plan)}
    (predicate : Subfunctor
      (FunctorToTypes.prod (requests header) (semanticPrograms (algebra plan.snapshot.language) sort)))
    (frame : (events header sort freeEmpty ready).obj X)
    (request : (requests header).obj X)
    (sourced : SourceResponse header decoded sort freeEmpty ready frame request) :
    frame ∈ (targetPost header decoded sort freeEmpty ready admitted labels predicate).obj X ↔
      (request, (target header sort freeEmpty ready admitted labels).app X frame) ∈ predicate.obj X := by
  change ((observe header decoded sort freeEmpty ready).app X frame,
    (target header sort freeEmpty ready admitted labels).app X frame) ∈ predicate.obj X ↔ _
  rw [(observes_iff_source header decoded sort freeEmpty ready frame request).mpr sourced]

theorem classifier_iff_source_target (rely : Subfunctor (requests header))
    (predicate : Subfunctor
      (FunctorToTypes.prod (requests header) (semanticPrograms (algebra plan.snapshot.language) sort)))
    (X : Base (plan := plan)) (parameter : (parameters header).obj X) :
    parameter ∈ (classifier header decoded sort freeEmpty ready rely
      (targetPost header decoded sort freeEmpty ready admitted labels predicate)).obj X ↔
    ∀ (Y : Base (plan := plan)) (arrow : X ⟶ Y) (request : (requests header).obj Y),
      request.1 = (parameters header).map arrow parameter → request ∈ rely.obj Y →
      ∃ frame : (events header sort freeEmpty ready).obj Y,
        SourceResponse header decoded sort freeEmpty ready frame request ∧
          (request, (target header sort freeEmpty ready admitted labels).app Y frame) ∈ predicate.obj Y := by
  rw [classifier_iff_source]
  constructor
  · intro holds Y arrow request aligned requested
    obtain ⟨frame, good, sourced⟩ := holds Y arrow request aligned requested
    exact ⟨frame, sourced,
      (targetPost_iff header decoded sort freeEmpty ready admitted labels predicate frame request sourced).mp good⟩
  · intro holds Y arrow request aligned requested
    obtain ⟨frame, sourced, good⟩ := holds Y arrow request aligned requested
    exact ⟨frame,
      (targetPost_iff header decoded sort freeEmpty ready admitted labels predicate frame request sourced).mpr good,
      sourced⟩

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.BindingResponses
