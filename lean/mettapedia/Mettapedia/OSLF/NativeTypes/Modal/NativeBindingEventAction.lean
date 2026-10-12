import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingRendering
import Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalReceiptTransport
import Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingSourceCoverage

/-!
# Complete operational events over the actual contextual program carrier

An event carries an intrinsic source and the executor's complete dependent
receipt. Reindexing uses the printed intrinsic substitution and constructs an
independent firing in the substituted source fibre. Both source and specified
target are actual authored program inhabitants; complete histories, capture
origins and declaration indices remain in the event.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingEventAction

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open NativeReceiptRechecking

abbrev bound (context : List String) := Mettapedia.GSLT.Poly.BindingLanguage.typeContext context

structure Point (environment : Environment) (context : List String) (sort : String) where
  source : Term (signature environment.language) context sort
  receipt : Execution.RootAnswer environment (bound context) (.base sort) (toPattern source)

theorem receipt_ext {environment : Environment} {context : List TypeExpr}
    {type : TypeExpr} {source : Pattern}
    {left right : Execution.RootAnswer environment context type source}
    (same : read left = read right) : left = right := by
  cases left
  cases right
  simp only [NativeReceiptRechecking.read, Payload.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

theorem point_ext {environment : Environment} {context : List String} {sort : String}
    {left right : Point environment context sort}
    (sources : left.source = right.source) (receipts : read left.receipt = read right.receipt) :
    left = right := by
  cases left with
  | mk leftSource leftReceipt =>
      cases right with
      | mk rightSource rightReceipt =>
          dsimp only at sources receipts
          subst rightSource
          cases receipt_ext receipts
          rfl

def castReceipt {environment : Environment} {context : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} (same : source = target)
    (receipt : Execution.RootAnswer environment context type source) :
    Execution.RootAnswer environment context type target := same ▸ receipt

theorem castReceipt_read {environment : Environment} {context : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} (same : source = target)
    (receipt : Execution.RootAnswer environment context type source) :
    read (castReceipt same receipt) = read receipt := by
  cases same
  rfl

def boundAssignment {environment : Environment} (freeEmpty : environment.free = FreeTypeContext.empty)
    {source target : List String} (substitution : Sub (signature environment.language) source target) :
    TypedBoundAssignment environment.language environment.free (bound source) (bound target) where
  assignment := NativeBindingRendering.assignment substitution
  typed := by
    rw [freeEmpty]
    exact (NativeBindingRendering.typedAssignment substitution).typed

def action {environment : Environment} (freeEmpty : environment.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) {source target : List String}
    (substitution : Sub (signature environment.language) source target) {sort : String}
    (point : Point environment source sort) : Point environment target sort where
  source := Binding.bind substitution point.source
  receipt := castReceipt (NativeBindingRendering.print_substitution substitution point.source).symm
    (NativeOperationalReceiptTransport.transport ready (boundAssignment freeEmpty substitution)
      (fun index => (NativeBindingRendering.assignment_images substitution index).2)
      (fun index => (NativeBindingRendering.assignment_images substitution index).1) point.receipt)

theorem action_read {environment : Environment} (freeEmpty : environment.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) {source target : List String}
    (substitution : Sub (signature environment.language) source target) {sort : String}
    (point : Point environment source sort) :
    read (action freeEmpty ready substitution point).receipt =
      NativeOperationalReceiptTransport.payload (bound source) (bound target)
        (NativeBindingRendering.assignment substitution) (read point.receipt) := by
  exact (castReceipt_read _ _).trans rfl

theorem action_identity {environment : Environment} (freeEmpty : environment.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) {context : List String} {sort : String}
    (point : Point environment context sort) :
    action freeEmpty ready (fun _ position => .var position) point = point := by
  apply point_ext (Binding.bind_id point.source)
  rw [action_read, NativeBindingRendering.assignment_identity]
  exact NativeOperationalReceiptTransport.payload_identity point.receipt.valid

theorem action_composition {environment : Environment}
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) {source middle target : List String}
    (first : Sub (signature environment.language) source middle)
    (second : Sub (signature environment.language) middle target) {sort : String}
    (point : Point environment source sort) :
    action freeEmpty ready second (action freeEmpty ready first point) =
      action freeEmpty ready (fun sort position => Binding.bind second (first sort position)) point := by
  apply point_ext (Binding.bind_comp first second point.source)
  rw [action_read, action_read, action_read]
  rw [NativeOperationalReceiptTransport.payload_composition (original := read point.receipt) point.receipt.valid]
  rw [NativeBindingRendering.assignment_composition]

theorem target_sorted {environment : Environment} {context : List String} {sort : String}
    (point : Point environment context sort) :
    OpenPatternWellSorted environment.language environment.free (bound context) (.base sort)
      point.receipt.target := by
  cases point.receipt.valid with
  | fire _ _ _ _ _ _ _ _ typed => exact typed

def targetSource {environment : Environment} (freeEmpty : environment.free = FreeTypeContext.empty)
    {context : List String} {sort : String} (point : Point environment context sort) :
    Source environment.language context sort :=
  ⟨point.receipt.target, by
    obtain ⟨typed, canonical, object⟩ := target_sorted point
    exact ⟨by simpa only [freeEmpty] using typed, object.1, canonical⟩⟩

noncomputable def targetTerm {environment : Environment}
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (admitted : Admitted environment.language)
    (labels : (environment.language.terms.map (·.label)).Nodup)
    {context : List String} {sort : String} (point : Point environment context sort) :
    Term (signature environment.language) context sort :=
  (sourceEquiv admitted labels context sort).symm (targetSource freeEmpty point)

theorem targetTerm_read {environment : Environment}
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (admitted : Admitted environment.language)
    (labels : (environment.language.terms.map (·.label)).Nodup)
    {context : List String} {sort : String} (point : Point environment context sort) :
    toPattern (targetTerm freeEmpty admitted labels point) = point.receipt.target :=
  congrArg Subtype.val ((sourceEquiv admitted labels context sort).apply_symm_apply
    (targetSource freeEmpty point))

theorem targetTerm_natural {environment : Environment}
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment)
    (admitted : Admitted environment.language)
    (labels : (environment.language.terms.map (·.label)).Nodup)
    {source target : List String} (substitution : Sub (signature environment.language) source target)
    {sort : String} (point : Point environment source sort) :
    targetTerm freeEmpty admitted labels (action freeEmpty ready substitution point) =
      Binding.bind substitution (targetTerm freeEmpty admitted labels point) := by
  apply toPattern_injective labels
  rw [targetTerm_read, NativeBindingRendering.print_substitution, targetTerm_read]
  exact congrArg Payload.target (action_read freeEmpty ready substitution point)

theorem action_rechecked {environment : Environment}
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment)
    {source target : List String} (substitution : Sub (signature environment.language) source target)
    {sort : String} (point : Point environment source sort) :
    ∃ receipt,
      recheck environment (bound target) (.base sort)
        (toPattern (Binding.bind substitution point.source))
        (read (action freeEmpty ready substitution point).receipt) = some receipt ∧
      read receipt = read (action freeEmpty ready substitution point).receipt :=
  recheck_complete ready.prerequisites.recursive
    (action freeEmpty ready substitution point).receipt.valid

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingEventAction
