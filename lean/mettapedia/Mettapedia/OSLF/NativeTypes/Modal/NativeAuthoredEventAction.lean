import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingEventAction

/-!
# Selected execution receipts over the original authored binding language

Selecting operational rules changes the execution language but does not
change constructor semantics. The comparison below uses the earned original
grammar equality to type actual substitutions and targets. The original
constructor alphabet and complete operational receipt remain independent.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeAuthoredEventAction

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open NativeReceiptRechecking
open NativeBindingEventAction (bound)

variable {environment : Environment} {language : LanguageDef}

structure Point (environment : Environment) (language : LanguageDef)
    (context : List String) (sort : String) where
  source : Term (signature language) context sort
  receipt : Execution.RootAnswer environment (bound context) (.base sort) (toPattern source)

theorem point_ext {context : List String} {sort : String}
    {left right : Point environment language context sort}
    (sources : left.source = right.source) (receipts : read left.receipt = read right.receipt) :
    left = right := by
  cases left with
  | mk leftSource leftReceipt =>
      cases right with
      | mk rightSource rightReceipt =>
          dsimp only at sources receipts
          subst rightSource
          cases NativeBindingEventAction.receipt_ext receipts
          rfl

def boundAssignment (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty)
    {source target : List String} (substitution : Sub (signature language) source target) :
    TypedBoundAssignment environment.language environment.free (bound source) (bound target) where
  assignment := NativeBindingRendering.assignment substitution
  typed := by
    intro index type located
    rw [freeEmpty]
    exact GeneralLanguageTyping.type_transport grammar.symm
      ((NativeBindingRendering.typedAssignment substitution).typed located)

def action (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) {source target : List String}
    (substitution : Sub (signature language) source target) {sort : String}
    (point : Point environment language source sort) : Point environment language target sort where
  source := Binding.bind substitution point.source
  receipt := NativeBindingEventAction.castReceipt
    (NativeBindingRendering.print_substitution substitution point.source).symm
    (NativeOperationalReceiptTransport.transport ready (boundAssignment grammar freeEmpty substitution)
      (fun index => (NativeBindingRendering.assignment_images substitution index).2)
      (fun index => (NativeBindingRendering.assignment_images substitution index).1) point.receipt)

theorem action_read (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) {source target : List String}
    (substitution : Sub (signature language) source target) {sort : String}
    (point : Point environment language source sort) :
    read (action grammar freeEmpty ready substitution point).receipt =
      NativeOperationalReceiptTransport.payload (bound source) (bound target)
        (NativeBindingRendering.assignment substitution) (read point.receipt) :=
  (NativeBindingEventAction.castReceipt_read _ _).trans rfl

theorem action_identity (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) {context : List String} {sort : String}
    (point : Point environment language context sort) :
    action grammar freeEmpty ready (fun _ position => .var position) point = point := by
  apply point_ext (Binding.bind_id point.source)
  rw [action_read, NativeBindingRendering.assignment_identity]
  exact NativeOperationalReceiptTransport.payload_identity point.receipt.valid

theorem action_composition (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) {source middle target : List String}
    (first : Sub (signature language) source middle)
    (second : Sub (signature language) middle target) {sort : String}
    (point : Point environment language source sort) :
    action grammar freeEmpty ready second (action grammar freeEmpty ready first point) =
      action grammar freeEmpty ready (fun sort position => Binding.bind second (first sort position)) point := by
  apply point_ext (Binding.bind_comp first second point.source)
  rw [action_read, action_read, action_read]
  rw [NativeOperationalReceiptTransport.payload_composition (original := read point.receipt) point.receipt.valid]
  rw [NativeBindingRendering.assignment_composition]

def targetSource (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty) {context : List String} {sort : String}
    (point : Point environment language context sort) : Source language context sort := by
  have sorted : OpenPatternWellSorted environment.language environment.free (bound context)
      (.base sort) point.receipt.target := by
    cases point.receipt.valid with
    | fire _ _ _ _ _ _ _ _ typed => exact typed
  refine ⟨point.receipt.target, ?_, sorted.2.2.1, sorted.2.1⟩
  rw [freeEmpty] at sorted
  exact GeneralLanguageTyping.type_transport grammar sorted.1

noncomputable def targetTerm (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty) (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) {context : List String} {sort : String}
    (point : Point environment language context sort) : Term (signature language) context sort :=
  (sourceEquiv admitted labels context sort).symm (targetSource grammar freeEmpty point)

theorem targetTerm_read (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty) (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) {context : List String} {sort : String}
    (point : Point environment language context sort) :
    toPattern (targetTerm grammar freeEmpty admitted labels point) = point.receipt.target :=
  congrArg Subtype.val ((sourceEquiv admitted labels context sort).apply_symm_apply
    (targetSource grammar freeEmpty point))

theorem targetTerm_natural (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty) (ready : NativeOperationalProfile.Admitted environment)
    (admitted : Admitted language) (labels : (language.terms.map (·.label)).Nodup)
    {source target : List String} (substitution : Sub (signature language) source target) {sort : String}
    (point : Point environment language source sort) :
    targetTerm grammar freeEmpty admitted labels (action grammar freeEmpty ready substitution point) =
      Binding.bind substitution (targetTerm grammar freeEmpty admitted labels point) := by
  apply toPattern_injective labels
  rw [targetTerm_read, NativeBindingRendering.print_substitution, targetTerm_read]
  exact congrArg Payload.target (action_read grammar freeEmpty ready substitution point)

end Mettapedia.OSLF.NativeTypes.Modal.NativeAuthoredEventAction
