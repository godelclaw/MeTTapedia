import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.CheckedFormation

/-! # Computed modal parameters and preserved authored origins -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Joined.Installed

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Modal
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf

variable (installed : Joined.Installed)

/-- Selected execution ordinals and original authored declarations have
separate coordinates; filtering rules can change only the former. -/
structure SourceOrigin where
  family : Nat
  selectedDeclaration : Nat
  authoredDeclaration : Nat
  position : Mettapedia.OSLF.Framework.RedexPosition.Position
  indices : List String
  bound : List Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr
  deriving DecidableEq, Repr

def sourceOrigin (index : installed.Index) : SourceOrigin :=
  let header := installed.indexed.headers[index]
  let schema := installed.indexed.schema index
  ⟨header.origin.val, schema.ordinal, schema.declaration.declarationIndex,
    schema.position, header.indices.map (fun parameter => parameter.slot.name), schema.focusBound⟩

structure SourceReceipt (index : installed.Index) (ambient : List String)
    (pattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) where
  origin : SourceOrigin
  evidence : installed.Receipt index ambient pattern
  aligned : origin = installed.sourceOrigin index

def checkSourceReceipt (index : installed.Index) (ambient : List String)
    (pattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (payload : NativeReceiptRechecking.Payload) :
    Option (SourceReceipt installed index ambient pattern) :=
  (installed.checkReceipt index ambient pattern payload).map fun evidence =>
    ⟨installed.sourceOrigin index, evidence, rfl⟩

theorem checkSourceReceipt_exact (index : installed.Index) (ambient : List String)
    (pattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (payload : NativeReceiptRechecking.Payload) :
    (installed.checkSourceReceipt index ambient pattern payload).isSome = true ↔
      NativeReceiptRechecking.Valid installed.indexed.operational.Environment
        (NativeBindingEventAction.bound ambient) (.base (installed.programSort index)) pattern payload ∧
      payload.index = (installed.indexed.schema index).ordinal := by
  simpa only [checkSourceReceipt, Option.isSome_map] using installed.checkReceipt_exact index ambient pattern payload

theorem checkSourceReceipt_read {index : installed.Index} {ambient : List String}
    {pattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern} {payload : NativeReceiptRechecking.Payload}
    {receipt : SourceReceipt installed index ambient pattern}
    (checked : installed.checkSourceReceipt index ambient pattern payload = some receipt) :
    NativeReceiptRechecking.read receipt.evidence.frame.point.val.receipt = payload ∧
      receipt.origin = installed.sourceOrigin index := by
  unfold checkSourceReceipt at checked
  cases found : installed.checkReceipt index ambient pattern payload with
  | none => rw [found] at checked; cases checked
  | some evidence =>
      rw [found] at checked
      cases Option.some.inj checked
      exact ⟨installed.checkReceipt_read found, rfl⟩

theorem source_origin_exact (index : installed.Index) :
    (installed.sourceOrigin index).authoredDeclaration =
      (Occurrences.generate (NativeCubeProfile.language installed.indexed.operational))[installed.indexed.headers[index].site].declaration ∧
    (installed.sourceOrigin index).position =
      (Occurrences.generate (NativeCubeProfile.language installed.indexed.operational))[installed.indexed.headers[index].site].position ∧
    (installed.sourceOrigin index).indices =
      SortProfiles.DisplayedGraph.indexNames
        (Occurrences.generate (NativeCubeProfile.language installed.indexed.operational))[installed.indexed.headers[index].site] :=
  ⟨installed.indexed.headers[index].matching.1.symm,
    installed.indexed.headers[index].matching.2.1.symm,
    installed.indexed.headers[index].index_names⟩

theorem modal_symbol_injective : Function.Injective installed.modalSymbol := by
  intro left right equal
  exact Sum.inr.inj (Sum.inr.inj (Sum.inl.inj equal))

theorem parameter_count_from_source (index : installed.Index) :
    installed.symbols.termArity (installed.modalSymbol index) =
      installed.indexed.headers[index].indices.length +
        installed.indexed.operational.modal[installed.indexed.headers[index].origin].rely.length + 1 := by
  change arity (D := Pipeline.classifierSignature installed.indexed.operational) (installed.indexed.interfaces index) = _
  rw [arity_full, installed.indexed.interfaces_source]
  simp only [SourceInterfaces.Header.interface, List.length_ofFn]

theorem classifier_is_focus (index : installed.Index) :
    (installed.indexed.interfaces index).focus =
      installed.indexed.operational.modal[installed.indexed.headers[index].origin].focus := by
  rw [installed.indexed.interfaces_source]
  rfl

theorem continuation_is_program (index : installed.Index) :
    (installed.indexed.interfaces index).target =
      installed.indexed.operational.modal[installed.indexed.headers[index].origin].program := by
  rw [installed.indexed.interfaces_source]
  rfl

/-- A checked native interpretation retains the entire source receipt, not
only its target or its declaration number. -/
theorem receipt_payload_preserved {index : installed.Index} {ambient : List String}
    {pattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern} {payload : NativeReceiptRechecking.Payload}
    {receipt : installed.Receipt index ambient pattern}
    (checked : installed.checkReceipt index ambient pattern payload = some receipt) :
    NativeReceiptRechecking.read receipt.firing.answer = payload ∧
      NativeReceiptRechecking.read receipt.frame.point.val.receipt = payload := by
  have native := installed.checkReceipt_read checked
  exact ⟨receipt.same.symm.trans native, native⟩

theorem distinct_source_origins_remain_distinct
    {leftIndex rightIndex : installed.Index} {ambient : List String}
    {pattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {leftPayload rightPayload : NativeReceiptRechecking.Payload}
    {leftReceipt : installed.Receipt leftIndex ambient pattern}
    {rightReceipt : installed.Receipt rightIndex ambient pattern}
    (leftChecked : installed.checkReceipt leftIndex ambient pattern leftPayload = some leftReceipt)
    (rightChecked : installed.checkReceipt rightIndex ambient pattern rightPayload = some rightReceipt)
    (distinct : leftPayload.index ≠ rightPayload.index) :
    NativeReceiptRechecking.read leftReceipt.frame.point.val.receipt ≠
      NativeReceiptRechecking.read rightReceipt.frame.point.val.receipt := by
  rw [installed.checkReceipt_read leftChecked, installed.checkReceipt_read rightChecked]
  intro equal
  exact distinct (congrArg NativeReceiptRechecking.Payload.index equal)

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Joined.Installed
