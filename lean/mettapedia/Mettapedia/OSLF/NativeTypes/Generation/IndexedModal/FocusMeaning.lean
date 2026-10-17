import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.OriginLaws
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingFocusChecking
import Mettapedia.OSLF.NativeTypes.Modal.Rules

/-!
# Source semantics of indexed contextual classifiers

Index arguments contain a classifier, a contextual value and its membership
evidence. Rely arguments vary universally; the target predicate may depend
on those values and on the completed assignment. A response retains the
selected declaration's complete source receipt and the actual local focus.
The source specification below uses the independent firing judgment and
scoped instantiation, without referring to a certificate checker.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusMeaning

open Mettapedia.OSLF.MeTTaIL Syntax ScopedRuleMatching
open Mettapedia.OSLF.NativeTypes.Modal
open NativeReceiptRechecking
open NativeBindingEventAction (bound)
open Mettapedia.GSLT.LanguageDef.WellSorted

variable (installed : Joined.Installed) (index : installed.Index) (ambient : List String)

abbrev IndexPosition := Fin installed.indexed.headers[index].indices.length
abbrev RelyPosition := Fin installed.indexed.operational.modal[installed.indexed.headers[index].origin].rely.length

abbrev IndexValue (position : IndexPosition installed index) :=
  NativeBindingSchemaCaptures.SlotValue (installed.indexed.schema index)
    installed.indexed.headers[index].indices[position].slot ambient

abbrev RelyValue (position : RelyPosition installed index) :=
  NativeBindingSchemaCaptures.SlotValue (installed.indexed.schema index)
    installed.indexed.operational.modal[installed.indexed.headers[index].origin].rely[position].slot ambient

structure IndexArgument (position : IndexPosition installed index) where
  classifier : IndexValue installed index ambient position → Prop
  value : IndexValue installed index ambient position
  member : classifier value

abbrev RelyValues := (position : RelyPosition installed index) → RelyValue installed index ambient position

structure Arguments where
  indices : (position : IndexPosition installed index) → IndexArgument installed index ambient position
  rely : (position : RelyPosition installed index) → RelyValue installed index ambient position → Prop
  target : RelyValues installed index ambient → ScopedRuleMatching.Assignment → Pattern → Prop

variable {installed index ambient}

def Requested (arguments : Arguments installed index ambient)
    (values : RelyValues installed index ambient) : Prop := ∀ position, arguments.rely position (values position)

def IndexMatches (arguments : Arguments installed index ambient) (payload : Payload) : Prop :=
  ∀ position, lookup payload.completed installed.indexed.headers[index].indices[position].slot.name =
    some (arguments.indices position).value.val

def RelyMatches (values : RelyValues installed index ambient) (payload : Payload) : Prop :=
  ∀ position, lookup payload.completed
    installed.indexed.operational.modal[installed.indexed.headers[index].origin].rely[position].slot.name =
      some (values position).val

/-- A source judgment: the authored firing, its selected instance at the
focus, all ordered parameters and the substituted target specification. -/
def SourceResponse (arguments : Arguments installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (source : Pattern) (payload : Payload) : Prop :=
  Valid installed.indexed.operational.Environment (bound ambient)
      (.base (installed.programSort index)) source payload ∧
    payload.index = (installed.indexed.schema index).ordinal ∧
    (∃ rawFocus, Instantiation.FocusInstance Substitution.instantiateBVar
      (installed.indexed.schema index).declaration.rule
      (installed.indexed.schema index).declaration.binding.spec ambient.length .left payload.completed
      [] 0 (installed.indexed.schema index).declaration.rule.left
      (installed.indexed.schema index).position rawFocus ∧ rawFocus.eraseBinderMetadata = focus) ∧
    IndexMatches arguments payload ∧ RelyMatches values payload ∧
    arguments.target values payload.completed payload.target

def FocusAdmitted (installed : Joined.Installed) (index : installed.Index)
    (ambient : List String) (focus : Pattern) : Prop :=
  HasType (BindingPipeline.plan installed.indexed.operational.generated).snapshot.language
      (BindingPipeline.plan installed.indexed.operational.generated).snapshot.free
      ((installed.indexed.schema index).focusBound ++ bound ambient) focus
      (installed.indexed.schema index).focusCarrier ∧
    isObjectPattern focus = true ∧ focus.hasCanonicalBinderMetadata = true

/-- The quantifier ranges over the independently typed rely values, not
over only those requests for which execution happened to return a receipt. -/
def SourceMeaning (arguments : Arguments installed index ambient) (focus : Pattern) : Prop :=
  FocusAdmitted installed index ambient focus ∧
    ∀ values, Requested arguments values → ∃ source payload, SourceResponse arguments focus values source payload

structure Response (arguments : Arguments installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) where
  source : Pattern
  receipt : installed.Receipt index ambient source
  focus_eq : receipt.frame.focus = focus
  indices : IndexMatches arguments (read receipt.firing.answer)
  relies : RelyMatches values (read receipt.firing.answer)
  target : arguments.target values receipt.firing.answer.completed receipt.firing.answer.target

structure Family (arguments : Arguments installed index ambient) (focus : Pattern) where
  admitted : FocusAdmitted installed index ambient focus
  respond : ∀ values, Requested arguments values → Response arguments focus values

def Inhabits (arguments : Arguments installed index ambient) (focus : Pattern) : Prop :=
  Nonempty (Family arguments focus)

theorem focus_unique {plan : GeneralExecutionAdmission.Plan} {schema : Rules.Schema plan}
    {ambient : List String} {sort : String}
    (frame : NativeBindingSchemaFocus.Frame schema ambient sort) {payload : Payload}
    (same : read frame.point.val.receipt = payload) {focus : Pattern}
    (selected : ∃ rawFocus, Instantiation.FocusInstance Substitution.instantiateBVar
      schema.declaration.rule schema.declaration.binding.spec ambient.length .left payload.completed
      [] 0 schema.declaration.rule.left schema.position rawFocus ∧ rawFocus.eraseBinderMetadata = focus) :
    frame.focus = focus := by
  obtain ⟨first, firstSelected, firstErased⟩ := frame.selected
  obtain ⟨second, secondSelected, secondErased⟩ := selected
  have completed := congrArg Payload.completed same
  change frame.point.val.receipt.completed = payload.completed at completed
  rw [completed] at firstSelected
  obtain ⟨a, checkedA, valueA⟩ := NativeBindingFocusChecking.focusAt?_complete firstSelected
  obtain ⟨b, checkedB, valueB⟩ := NativeBindingFocusChecking.focusAt?_complete secondSelected
  have equal := Option.some.inj (checkedA.symm.trans checkedB)
  have raw : first = second := valueA.symm.trans ((congrArg Subtype.val equal).trans valueB)
  exact firstErased.symm.trans ((congrArg Pattern.eraseBinderMetadata raw).trans secondErased)

theorem Response.source_response {arguments : Arguments installed index ambient} {focus : Pattern}
    {values : RelyValues installed index ambient} (response : Response arguments focus values) :
    SourceResponse arguments focus values response.source (read response.receipt.firing.answer) := by
  refine ⟨response.receipt.firing.answer.valid, response.receipt.firing.selected, ?_,
    response.indices, response.relies, response.target⟩
  have selected := response.receipt.frame.selected
  have same := congrArg Payload.completed response.receipt.same
  change response.receipt.frame.point.val.receipt.completed =
    (read response.receipt.firing.answer).completed at same
  rw [same] at selected
  simpa only [response.focus_eq] using selected

/-- Every independently specified response is accepted by the existing
receipt checker and recovers the specified focus and complete payload. -/
theorem response_complete {arguments : Arguments installed index ambient} {focus source : Pattern}
    {values : RelyValues installed index ambient} {payload : Payload}
    (valid : SourceResponse arguments focus values source payload) :
    ∃ response : Response arguments focus values,
      response.source = source ∧ read response.receipt.firing.answer = payload := by
  obtain ⟨firing, selected, focused, indices, relies, target⟩ := valid
  obtain ⟨receipt, checked, same⟩ := installed.checkReceipt_complete index ambient source payload firing selected
  have payloadRead : read receipt.firing.answer = payload := receipt.same.symm.trans same
  have focused' := focus_unique receipt.frame same focused
  refine ⟨⟨source, receipt, focused', ?_, ?_, ?_⟩, rfl, payloadRead⟩
  · simpa only [payloadRead] using indices
  · simpa only [payloadRead] using relies
  · change arguments.target values (read receipt.firing.answer).completed (read receipt.firing.answer).target
    simpa only [payloadRead] using target

/-- Full family membership agrees with the source-level universal may
specification. The reverse direction constructs all checked responses. -/
theorem inhabits_iff_source (arguments : Arguments installed index ambient) (focus : Pattern) :
    Inhabits arguments focus ↔ SourceMeaning arguments focus := by
  constructor
  · rintro ⟨family⟩
    refine ⟨family.admitted, fun values requested => ?_⟩
    let response := family.respond values requested
    exact ⟨response.source, read response.receipt.firing.answer, response.source_response⟩
  · rintro ⟨admitted, all⟩
    classical
    have responses : ∀ values, Requested arguments values → Nonempty (Response arguments focus values) := by
      intro values requested
      obtain ⟨source, payload, valid⟩ := all values requested
      obtain ⟨response, _, _⟩ := response_complete valid
      exact ⟨response⟩
    exact ⟨⟨admitted, fun values requested => Classical.choice (responses values requested)⟩⟩

/-- The generated operation's semantic classifier lives at its raw focus
carrier and the extended local binder context. -/
def former (arguments : Arguments installed index ambient) :
    Rules.TypeCode (BindingPipeline.plan installed.indexed.operational.generated)
      ((installed.indexed.schema index).focusBound ++ bound ambient)
      (installed.indexed.schema index).focusCarrier (installed.indexed.interfaces index).resultSort where
  meaning := Inhabits arguments
  bounded _ inhabited := inhabited.elim fun family => family.admitted.1

theorem former_source (arguments : Arguments installed index ambient) (focus : Pattern) :
    (former arguments).meaning focus ↔ SourceMeaning arguments focus :=
  inhabits_iff_source arguments focus

theorem empty_target_no_membership (arguments : Arguments installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (requested : Requested arguments values)
    (empty : ∀ assignment target, ¬ arguments.target values assignment target) :
    ¬ Inhabits arguments focus := by
  rintro ⟨family⟩
  let response := family.respond values requested
  exact empty _ _ response.target

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusMeaning
