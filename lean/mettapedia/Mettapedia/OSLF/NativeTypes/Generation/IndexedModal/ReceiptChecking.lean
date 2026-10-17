import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Pipeline
import Mettapedia.OSLF.NativeTypes.Modal.NativeReceiptRechecking

/-!
# Source-indexed receipt checking for installed modal classifiers

Receipt payloads retain declarations, scoped assignments, match choices,
ordered histories and targets. A classifier origin additionally identifies
the selected authored focus. The original certified receipt checker is used
without replacing receipt equality by endpoint equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Pipeline.Installed

open Mettapedia.OSLF.MeTTaIL Syntax ScopedRuleMatching GeneralPremise StructuralDescent
open Mettapedia.OSLF.NativeTypes.Modal.NativeReceiptRechecking

variable (installed : Pipeline.Installed)

def schema (index : Fin installed.headers.length) :=
  SourceInterfaces.schema installed.operational installed.headers[index].origin

structure Receipt (index : Fin installed.headers.length) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) where
  answer : Execution.RootAnswer (BindingPipeline.environment installed.operational.generated) bound type source
  selected : answer.index = (installed.schema index).ordinal

def checkReceipt (index : Fin installed.headers.length) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (payload : Payload) :
    Option (Receipt installed index bound type source) :=
  match recheck (BindingPipeline.environment installed.operational.generated) bound type source payload with
  | none => none
  | some answer =>
      if selected : answer.index = (installed.schema index).ordinal then
        some ⟨answer, selected⟩
      else none

theorem checkReceipt_read {index : Fin installed.headers.length} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} {payload : Payload}
    {receipt : Receipt installed index bound type source}
    (checked : installed.checkReceipt index bound type source payload = some receipt) :
    read receipt.answer = payload := by
  unfold checkReceipt at checked
  split at checked
  · cases checked
  · rename_i answer found
    split at checked
    · cases Option.some.inj checked
      exact fromSnapshot_read found
    · cases checked

theorem checkReceipt_sound {index : Fin installed.headers.length} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} {payload : Payload}
    {receipt : Receipt installed index bound type source}
    (checked : installed.checkReceipt index bound type source payload = some receipt) :
    Valid (BindingPipeline.environment installed.operational.generated) bound type source payload ∧
      payload.index = (installed.schema index).ordinal := by
  have same := installed.checkReceipt_read checked
  refine ⟨?_, ?_⟩
  · rw [← same]
    exact receipt.answer.valid
  · exact (congrArg Payload.index same).symm.trans receipt.selected

theorem checkReceipt_complete {index : Fin installed.headers.length} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} {payload : Payload}
    (valid : Valid (BindingPipeline.environment installed.operational.generated) bound type source payload)
    (selected : payload.index = (installed.schema index).ordinal) :
    ∃ receipt, installed.checkReceipt index bound type source payload = some receipt ∧
      read receipt.answer = payload := by
  obtain ⟨answer, checked, same⟩ := recheck_complete installed.operational.structural valid
  have chosen : answer.index = (installed.schema index).ordinal :=
    (congrArg Payload.index same).trans selected
  exact ⟨⟨answer, chosen⟩, by simp only [checkReceipt, checked, dif_pos chosen], same⟩

theorem checkReceipt_exact (index : Fin installed.headers.length) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (payload : Payload) :
    (installed.checkReceipt index bound type source payload).isSome = true ↔
      Valid (BindingPipeline.environment installed.operational.generated) bound type source payload ∧
        payload.index = (installed.schema index).ordinal := by
  constructor
  · intro accepted
    cases checked : installed.checkReceipt index bound type source payload with
    | none => rw [checked] at accepted; cases accepted
    | some receipt => exact installed.checkReceipt_sound checked
  · rintro ⟨valid, selected⟩
    obtain ⟨receipt, checked, _⟩ := installed.checkReceipt_complete valid selected
    rw [checked]
    rfl

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Pipeline.Installed
