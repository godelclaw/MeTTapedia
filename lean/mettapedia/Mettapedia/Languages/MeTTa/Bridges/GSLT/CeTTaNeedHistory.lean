import Mettapedia.Languages.MeTTa.OSLFCore.ByteString
import Mettapedia.Data.String.ByteString
import Mettapedia.Machines.RationalTermGraphOrder
import Mettapedia.GSLT.LanguageDef.NativeOpsCNormalization
import Mettapedia.GSLT.LanguageDef.NativeOpsCFunctionComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsCLexAccumulator
import Mettapedia.GSLT.LanguageDef.NativeOpsReferenceFieldLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsShortCircuitTarget
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetParameterFacts
import Mettapedia.Machines.BranchLocalNeed.CacheLaws
import Mettapedia.Machines.BranchLocalNeed.Representation
import Mettapedia.Machines.RationalTermGraph
import Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
import Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
import Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts
import Mathlib.Data.List.Indexes
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Original C Need-cache completion, view transport and the shared lifecycle

The ordinary C reader admits `prime_need_frame_completed` and
`prime_need_cell_view_from_frame` from their complete configuration-selected
sources. The view body preserves and reflects an independent ordered memory
copy account, including parameter-cell entry and cleanup. It retains caller
state, source occurrence metadata and borrowed pointer aliases. Copying a
reference does not acquire its payload ownership.

The completion predicate's null guard and ordered `||` branches are retained in the admitted
IR. Exact execution reads the existing cache field only on the nonnull path;
full invocation includes parameter allocation and release and preserves the
complete caller state. Its Boolean result reflects `NeedCacheLaws.Cache.Completed`,
the completion judgment of the existing branch-local Need machine.

The record adapter records current declaration order, including the derived
`named_top` accelerator, for both capture and heap-index configurations. The
completion helper is a receipt-enabled weights-runtime source. The view reader
and record adapter select the Prime draft or the weights runtime's returned-value
provenance fields explicitly; the base profile remains the default. Enum tags have an explicit word representation. Physical C
layout, enum width, memory validity and compiler correctness remain separate
representation obligations. This predicate does not prove the encompassing
cache lookup, production-identity transport, graph collector or replay engine.
The pointer and cache field supplied to the model must describe actual live
storage; a nonnull address alone is insufficient.

Complete checked history readback retains every ordered native row and its
borrowed pointers, then reconstructs the shared source history under a supplied
single-history injective naming and executable origin-content reader. Capture
arrays are read independently and compared by finite contents. Immutable
metadata continuity and historical producer guards are separate from current
producer lookup. The admitted producer guard has exact target execution and
short-circuit readback; the enclosing native iterator, lookup helper and legal
cache-transition reachability are further obligations.

The framed-binding readback and writeback adapter lives in `CeTTaFrameWriteback`;
this module consumes it to interpret contextual Need payloads. Grounded Need
capabilities are decoded with their complete identity and rights, then checked
against the explicitly supplied retained history. The checked
history joins that lookup to the common Need heap. The logical active-union view
is explicit; physical Atom layout, complete graph interpretation and authority to
retain the containing storage remain further joins.

The ordinary contextual payload adapter now reads symbol, variable and
expression fields from actual scalar cells, then reuses the checked finite
inventory and LayerReader. Complete source readout is constructed for decreasing
finite graphs with current nonzero numbered-symbol spelling coverage or exact
managed symbol bytes. Duplicate child occurrences and distinct physical keys
remain separate. Managed spelling uses the explicit-length unsigned-byte storage
view; String interpretation requires checked UTF-8. Physical grounded payloads,
native byte ABI, GC lifetime and encompassing evaluation remain further joins.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory

open Mettapedia.GSLT.LanguageDef.NativeOps
open NativeIR (Atom Instruction)
open CeTTaFrameWriteback

variable {provenance : optParam Bool false}

/-! ## Actual by-value binding predicates

The source reader admits the complete helper from `match.h`. Its execution
reads a logical record field without dereferencing or forcing its skeleton.
Enum representation and physical layout remain explicit ABI obligations.
-/

namespace BindingValuePrimitives

def interface : Interface :=
  ⟨[⟨"BindingValue", NativeFrames.bindingValueFields⟩],
    [⟨"Atom", "Atom", "atom.h"⟩], [], []⟩

def representation : NativeC.Representation := ⟨"BindingValuePrimitives", interface, []⟩

def persistentHeader : Header :=
  ⟨"binding_value_context_is_persistent", [⟨"value", .named "BindingValue"⟩], .bool⟩

def persistentSource : List Char := "static inline bool binding_value_context_is_persistent(BindingValue value) {\n    return value.kind == BINDING_VALUE_CONTEXTUAL_PERSISTENT;\n}".toList

def persistentConstants : NativeC.PrimitiveBindings :=
  [("BINDING_VALUE_CONTEXTUAL_PERSISTENT".toList, .word 2)]

def valueAtom : Atom := .temporary 1 (.named "BindingValue")

def persistentCode : List Instruction :=
  valueFieldEqualCode valueAtom "BindingValue" 2 2 2 ++ [.return (.temporary 3 .bool)]

def persistentFunction : NativeIR.Function :=
  ⟨persistentHeader, NativeC.primitiveParameterCapture persistentHeader.parameters ++
    persistentCode, 3⟩

private def persistentTokens : List NativeC.Token :=
  [.identifier "static".toList, .identifier "inline".toList,
   .identifier "bool".toList, .identifier "binding_value_context_is_persistent".toList,
   .punctuation ['('], .identifier "BindingValue".toList, .identifier "value".toList,
   .punctuation [')'], .punctuation ['{'], .identifier "return".toList,
   .identifier "value".toList, .punctuation ['.'], .identifier "kind".toList,
   .punctuation ['=', '='], .identifier "BINDING_VALUE_CONTEXTUAL_PERSISTENT".toList,
   .punctuation [';'], .punctuation ['}']]

private def persistentParsed : NativeC.CQualifiedFunction :=
  ⟨⟨"bool".toList, 0⟩, "binding_value_context_is_persistent".toList,
    [⟨⟨⟨"BindingValue".toList, 0⟩, "value".toList⟩, false⟩],
    [.return (some (.binary .eq (.field (.identifier "value".toList) "kind".toList false)
      (.identifier "BINDING_VALUE_CONTEXTUAL_PERSISTENT".toList))) ]⟩

private theorem persistent_source_lexed : NativeC.lex persistentSource = .ok persistentTokens := by
  decide +kernel

private theorem persistent_source_parsed :
    NativeC.qualifiedFunction? (2 * persistentTokens.length + 4)
      ["bool".toList, "BindingValue".toList] (NativeC.ordinaryFunctionTokens persistentTokens) =
      some (persistentParsed, []) := by
  rfl

/-- Complete textual admission, including the by-value prototype and its
ordered field layout. The parser cannot replace the record by a pointer. -/
theorem persistent_source_admitted :
    NativeC.qualifiedReadOnlyFunctionText? representation
      ["bool".toList, "BindingValue".toList] persistentHeader
      [("BindingValue".toList, "BindingValue")] [false]
      persistentConstants persistentSource = some persistentFunction := by
  rw [NativeC.qualified_readonly_text_of_parts representation
    ["bool".toList, "BindingValue".toList] persistentHeader
    [("BindingValue".toList, "BindingValue")] [false] persistentConstants
    persistentSource persistentTokens persistentParsed persistent_source_lexed persistent_source_parsed]
  rfl

def persistentBound {World : Type} (state : TargetState World) (storage : Nat)
    (value : NativeFrames.BindingValueView) : TargetFrame × TargetState World :=
  targetDeclareLocal (targetEmptyFrame storage) state "value"
    (.named "BindingValue") value.toTarget

def persistentCaptured (frame : TargetFrame) (value : NativeFrames.BindingValueView) : TargetFrame :=
  targetDeclareTemporary frame 1 value.toTarget

def persistentFrame (frame : TargetFrame) (value : NativeFrames.BindingValueView) : TargetFrame :=
  valueFieldEqualFrame frame 2 value.kind 2

private theorem persistent_body_exact {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} (value : NativeFrames.BindingValueView)
    (read : TargetAtomEval interface frame state valueAtom value.toTarget)
    (bounded : TemporaryNamesBound frame 1)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root persistentCode frame state out ↔
      out = ⟨.returned (.bool (value.kind == 2)), persistentFrame frame value, state⟩ := by
  unfold persistentCode
  rw [target_normal_prefix_then_exact
    (by simp [valueFieldEqualCode, jumpFreeCode, jumpFreeInstruction])
    (value_field_equal_code_exact read bounded (by decide : 1 < 2)
      value.kind 2 (by rfl) root)]
  exact target_return_then_exact
    (value_field_equal_frame_result interface frame state 2 value.kind 2) root [] out

private theorem persistent_capture_prefix_exact {World : Type}
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (value : NativeFrames.BindingValueView)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root persistentFunction.body
      (persistentBound state storage value).1 (persistentBound state storage value).2 out ↔
      TargetRun interface heap calls .bool root persistentCode
        (persistentCaptured (persistentBound state storage value).1 value)
        (persistentBound state storage value).2 out := by
  let bound := persistentBound state storage value
  have read : targetLocalValue bound.1 bound.2 "value" = some value.toTarget :=
    target_singleton_parameter_readback state storage
      ⟨"value", .named "BindingValue"⟩ value.toTarget
  change TargetRun _ _ _ _ root
    (.temporary 1 (.named "BindingValue") (.readLocal "value") :: persistentCode)
    bound.1 bound.2 out ↔ _
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : bound.1.temporaryNames.contains 1 = false) (.local read))]
  rfl

private theorem persistent_invocation_body_exact {World : Type}
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (value : NativeFrames.BindingValueView)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    let bound := persistentBound state storage value
    TargetRun interface heap calls .bool root persistentFunction.body bound.1 bound.2 out ↔
      out = ⟨.returned (.bool (value.kind == 2)),
        persistentFrame (persistentCaptured bound.1 value) value, bound.2⟩ := by
  let bound := persistentBound state storage value
  dsimp only
  rw [persistent_capture_prefix_exact]
  apply persistent_body_exact
  · exact declared_temporary_atom interface bound.1 bound.2 1 _ _
  · intro identity live
    have same : identity = 1 := by
      simpa [persistentCaptured, persistentBound, targetDeclareLocal, targetEmptyFrame,
        targetDeclareTemporary, List.contains_iff_mem] using live
    omega

/-- The admitted C function compares only the contextual tag. Full invocation
preserves all caller state, including the external world and existing fault. -/
theorem persistent_invocation_exact {World : Type}
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (value : NativeFrames.BindingValueView)
    (result : TargetRawResult World) :
    TargetFunctionBody interface heap calls persistentFunction [value.toTarget] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
        result = ⟨.bool (value.kind == 2), state⟩ :=
  target_singleton_readonly_function_exact interface heap calls persistentFunction
    ⟨"value", .named "BindingValue"⟩ rfl value.toTarget (.bool (value.kind == 2)) state
    (fun storage => persistentFrame (persistentCaptured (persistentBound state storage value).1 value) value)
    (fun storage _ out => persistent_invocation_body_exact heap calls state storage value
      persistentFunction.body out)
    (fun _ => rfl) (fun _ => rfl) result

/-- Checked native-record readback supplies exactly the argument consumed by
the original helper; neither nullness nor the epoch is replaced at entry. -/
theorem persistent_readback_invocation_exact {World : Type}
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (record : TargetValue) (value : NativeFrames.BindingValueView)
    (read : NativeFrames.readBindingValue? record = some value) (result : TargetRawResult World) :
    TargetFunctionBody interface heap calls persistentFunction [record] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
        result = ⟨.bool (value.kind == 2), state⟩ := by
  rw [← NativeFrames.readBindingValue?_representation read]
  exact persistent_invocation_exact heap calls state value result

/-- The enum-only helper is admitted by the explicit comparison profile.
Its source, prototype and expected IR are the checked native reader control. -/
def contextualFunction : NativeIR.Function := NativeC.EnumComparisonControls.lowered

def contextualCode : List Instruction := contextualFunction.body.tail

def kindAtom : Atom := .temporary 1 .word

def contextualBound {World : Type} (state : TargetState World) (storage : Nat)
    (kind : BitVec 64) : TargetFrame × TargetState World :=
  targetDeclareLocal (targetEmptyFrame storage) state "kind" .word (.word kind)

def contextualCaptured (frame : TargetFrame) (kind : BitVec 64) : TargetFrame :=
  targetDeclareTemporary frame 1 (.word kind)

def contextualMarker (frame : TargetFrame) (kind : BitVec 64) : TargetFrame :=
  targetDeclareTemporary (targetDeclareTemporary frame 2 (.bool (kind == 1)))
    3 (.bool (kind == 1))

def contextualFrame {World : Type} (frame : TargetFrame) (state : TargetState World)
    (kind : BitVec 64) : TargetFrame :=
  let marker := contextualMarker frame kind
  shortCircuitFrame false marker (targetDeclareTemporary marker 4 (.bool (kind == 2)))
    state 3 (kind == 1) (kind == 2)

private theorem contextual_body_exact {World : Type}
    {interface : Interface} {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} (kind : BitVec 64)
    (read : TargetAtomEval interface frame state kindAtom (.word kind))
    (bounded : TemporaryNamesBound frame 1) (hscope : TemporariesScoped frame)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root contextualCode frame state out ↔
      out = ⟨.returned (.bool ((kind == 1) || (kind == 2))),
        contextualFrame frame state kind, state⟩ := by
  let checked := targetDeclareTemporary frame 2 (.bool (kind == 1))
  let marker := contextualMarker frame kind
  let right := targetDeclareTemporary marker 4 (.bool (kind == 2))
  have first : TargetPureEval interface frame state
      (.binary (.compare .eq) kindAtom (.word 1)) (.bool (kind == 1)) :=
    .binary read (.word 1) rfl
  have checkedBound : TemporaryNamesBound checked 2 :=
    declared_temporary_bound bounded (by decide : 1 ≤ 2) (Nat.le_refl _) _
  have markerBound : TemporaryNamesBound marker 3 :=
    declared_temporary_bound checkedBound (by decide : 2 ≤ 3) (Nat.le_refl _) _
  have markerScope : TemporariesScoped marker :=
    declared_temporaries_completeNames
      (declared_temporaries_completeNames hscope 2 _) 3 _
  have condition : TargetAtomEval interface marker state (.temporary 3 .bool) (.bool (kind == 1)) :=
    declared_temporary_atom interface checked state 3 _ _
  have protection : TemporaryProtection 1 frame marker :=
    temporary_protection_trans (declare_temporary_protects frame _ (by decide : 1 < 2))
      (declare_temporary_protects checked _ (by decide : 1 < 3))
  have rightRead := (protection_atom_evaluation protection kindAtom
    (by decide : 1 ≤ 1) state state _).mp read
  have second : TargetPureEval interface marker state
      (.binary (.compare .eq) kindAtom (.word 2)) (.bool (kind == 2)) :=
    .binary rightRead (.word 2) rfl
  have rightExact : ∀ root out, TargetRun interface heap calls .bool root
      [.temporary 4 .bool (.binary (.compare .eq) kindAtom (.word 2))] marker state out ↔
      out = ⟨.normal, right, state⟩ :=
    target_run_temporary_exact (temporary_bound_fresh markerBound (by decide : 3 < 4)) second
  have resultRead : TargetAtomEval interface right state (.temporary 4 .bool) (.bool (kind == 2)) :=
    declared_temporary_atom interface marker state 4 _ _
  have live : right.temporaryNames.contains 3 = true := by
    simp [right, marker, contextualMarker, targetDeclareTemporary]
  have armExact := short_circuit_rhs_exact false markerScope condition
    (by simp [jumpFreeCode, jumpFreeInstruction] :
      jumpFreeCode [.temporary 4 .bool (.binary (.compare .eq) kindAtom (.word 2))] = true)
    (fun _ => rightExact) resultRead live rfl
  have finalRead := short_circuit_frame_read false (value := kind == 2) condition live
    (by rfl : right.nextLocal = marker.nextLocal)
  change TargetRun interface heap calls .bool root
    (.temporary 2 .bool (.binary (.compare .eq) kindAtom (.word 1)) ::
     .temporary 3 .bool (.copy (.temporary 2 .bool)) ::
     .branch (.negated (.temporary 3 .bool))
       [.temporary 4 .bool (.binary (.compare .eq) kindAtom (.word 2)),
        .assign (.temporary 3 .bool) (.temporary 4 .bool)] [] ::
     [.return (.temporary 3 .bool)]) frame state out ↔ _
  rw [target_normal_then_exact
    (target_temporary_instruction_exact (temporary_bound_fresh bounded (by decide : 1 < 2)) first)]
  rw [target_short_circuit_copy_exact (temporary_bound_fresh checkedBound (by decide : 2 < 3))
    (declared_temporary_atom interface frame state 2 _ _)]
  simp only [shortCircuitCondition, Bool.false_eq_true, if_false] at armExact
  simp only [Bool.false_eq_true, if_false] at finalRead
  exact (target_normal_then_exact armExact root [.return (.temporary 3 .bool)] out).trans
    (target_return_then_exact finalRead root [] out)

private theorem contextual_invocation_body_exact {World : Type}
    (interface : Interface) (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (kind : BitVec 64)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    let bound := contextualBound state storage kind
    TargetRun interface heap calls .bool root contextualFunction.body bound.1 bound.2 out ↔
      out = ⟨.returned (.bool ((kind == 1) || (kind == 2))),
        contextualFrame (contextualCaptured bound.1 kind) bound.2 kind, bound.2⟩ := by
  let bound := contextualBound state storage kind
  have read : targetLocalValue bound.1 bound.2 "kind" = some (.word kind) :=
    target_singleton_parameter_readback state storage ⟨"kind", .word⟩ (.word kind)
  dsimp only
  change TargetRun _ _ _ _ root (.temporary 1 .word (.readLocal "kind") :: contextualCode)
    bound.1 bound.2 out ↔ _
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : bound.1.temporaryNames.contains 1 = false) (.local read))]
  apply contextual_body_exact
  · exact declared_temporary_atom interface bound.1 bound.2 1 _ _
  · intro identity live
    have same : identity = 1 := by
      simpa [bound, contextualCaptured, contextualBound, targetDeclareLocal, targetEmptyFrame,
        targetDeclareTemporary, List.contains_iff_mem] using live
    omega
  · exact target_declared_names_complete _ _ _ (by intro _ _; rfl)

private theorem contextual_frame_extent {World : Type}
    (frame : TargetFrame) (state : TargetState World) (kind : BitVec 64) :
    (contextualFrame frame state kind).storage = frame.storage ∧
      (contextualFrame frame state kind).nextLocal = frame.nextLocal := by
  unfold contextualFrame shortCircuitFrame
  split <;> exact ⟨rfl, rfl⟩

/-- Both original comparison occurrences, including short-circuit scope, have
exact invocation behavior over any surrounding interface and service world. -/
theorem contextual_kind_invocation_exact {World : Type}
    (interface : Interface) (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (kind : BitVec 64) (result : TargetRawResult World) :
    TargetFunctionBody interface heap calls contextualFunction [.word kind] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
        result = ⟨.bool ((kind == 1) || (kind == 2)), state⟩ := by
  apply target_singleton_readonly_function_exact interface heap calls contextualFunction
    ⟨"kind", .word⟩ rfl (.word kind) (.bool ((kind == 1) || (kind == 2))) state
    (fun storage => contextualFrame (contextualCaptured (contextualBound state storage kind).1 kind)
      (contextualBound state storage kind).2 kind)
  · intro storage _ out
    exact contextual_invocation_body_exact interface heap calls state storage kind
      contextualFunction.body out
  · intro storage
    exact (contextual_frame_extent
      (contextualCaptured (contextualBound state storage kind).1 kind)
      (contextualBound state storage kind).2 kind).1.trans rfl
  · intro storage
    exact (contextual_frame_extent
      (contextualCaptured (contextualBound state storage kind).1 kind)
      (contextualBound state storage kind).2 kind).2.trans rfl

/-- The checked view uses nonzero tags for contextual coordinates. On its
admitted enum domain this is exactly the actual helper's disjunction. -/
theorem contextual_kind_agrees_with_readback (value : NativeFrames.BindingValueView)
    (valid : value.Admissible) :
    ((value.kind == 1) || (value.kind == 2)) = true ↔ value.kind ≠ 0 := by
  have range : value.kind.toNat = 0 ∨ value.kind.toNat = 1 ∨ value.kind.toNat = 2 := by
    have bounded := valid.2
    omega
  rcases range with zero | one | two
  · have same : value.kind = 0 := BitVec.eq_of_toNat_eq zero
    simp [same]
  · have same : value.kind = 1 := BitVec.eq_of_toNat_eq one
    simp [same]
  · have same : value.kind = 2 := BitVec.eq_of_toNat_eq two
    simp [same]

namespace Controls

/-- Every skeleton and epoch takes the tag's result; nullness does not erase
its context and inspecting written syntax does not call the evaluator. -/
theorem persistent_tag_cases {World : Type} (heap : TargetHeapSemantics World)
    (calls : TargetCalls World) (state : TargetState World) (storage : Nat)
    (fresh : targetFreshFrame state.memory storage) (skeleton : Option Address) (epoch : BitVec 64) :
    TargetFunctionBody interface heap calls persistentFunction
      [(⟨skeleton, epoch, 0⟩ : NativeFrames.BindingValueView).toTarget] state ⟨.bool false, state⟩ ∧
    TargetFunctionBody interface heap calls persistentFunction
      [(⟨skeleton, epoch, 1⟩ : NativeFrames.BindingValueView).toTarget] state ⟨.bool false, state⟩ ∧
    TargetFunctionBody interface heap calls persistentFunction
      [(⟨skeleton, epoch, 2⟩ : NativeFrames.BindingValueView).toTarget] state ⟨.bool true, state⟩ := by
  refine ⟨?_, ?_, ?_⟩
  all_goals apply (persistent_invocation_exact heap calls state _ _).mpr
  all_goals exact ⟨⟨storage, fresh⟩, rfl⟩

/-- Malformed records and out-of-domain enum tags cannot enter through the
checked readback route, even when a missing field might look like zero. -/
theorem incomplete_and_invalid_records_refused :
    NativeFrames.readBindingValue? (.record "BindingValue" [.reference none, .word 0]) = none ∧
    NativeFrames.readBindingValue? (.record "BindingValue" [.reference none, .word 0, .word 3]) = none := by
  decide

end Controls

end BindingValuePrimitives

/-- Logical declaration order, including fields preceding the observed cache
state. Width and physical byte offsets remain a representation boundary. -/
def frameFields (captures heapIndex : Bool) (provenance : Bool := false) : List Parameter :=
  [⟨"parent", .ref (.named "NeedFrame")⟩,
   ⟨"named_top", .ref (.named "NeedFrame")⟩,
   ⟨"owner", .ref (.named "Arena")⟩,
   ⟨"closure_owner", .ref (.named "Arena")⟩,
   ⟨"arena_bloom", .word⟩, ⟨"arena_min_id", .word⟩, ⟨"arena_max_id", .word⟩,
   ⟨"arena_range_complete", .bool⟩, ⟨"arena_bloom_complete", .bool⟩,
   ⟨"session_id", .word⟩, ⟨"serial", .word⟩, ⟨"thunk_id", .word⟩,
   ⟨"depth", .word⟩, ⟨"authority_id", .word⟩, ⟨"evaluator_id", .word⟩,
   ⟨"storage_key", .word⟩, ⟨"import_key", .word⟩,
   ⟨"source_occurrence_id", .word⟩, ⟨"source_argument_index", .word⟩,
   ⟨"cache_state", .word⟩] ++
  (if provenance then [⟨"value_role", .word⟩, ⟨"value_producer_thunk", .word⟩,
    ⟨"value_producer_update", .word⟩] else []) ++
  [⟨"origin", .ref (.named "Atom")⟩, ⟨"cached", .ref (.named "Atom")⟩] ++
  (if captures then [⟨"capture_known", .bool⟩, ⟨"capture_var_ids", .ref .word⟩,
    ⟨"capture_var_count", .word⟩] else []) ++
  (if heapIndex then [⟨"heap_index", .ref (.named "NeedHeapIndexNode")⟩,
    ⟨"lineage_index", .ref (.named "NeedHeapIndexNode")⟩] else [])

def interface (captures heapIndex : Bool) (provenance : Bool := false) : Interface :=
  ⟨[⟨"NeedFrame", frameFields captures heapIndex provenance⟩],
    [⟨"Arena", "Arena", "atom.h"⟩, ⟨"Atom", "Atom", "atom.h"⟩,
     ⟨"NeedHeapIndexNode", "PrimeNeedHeapIndexNode", "prime_need.h"⟩], [], []⟩

def representation (captures heapIndex : Bool) (provenance : Bool := false) : NativeC.Representation :=
  ⟨"NeedHistory", interface captures heapIndex provenance, []⟩

/-- C enum values are represented exactly as nonnegative words; this does
not claim that the C enum occupies eight bytes. -/
def cacheConstants : NativeC.PrimitiveBindings :=
  [("PRIME_NEED_CACHE_VALUE".toList, .word 2),
   ("PRIME_NEED_CACHE_STABLE_FAULT".toList, .word 3)]

def completionSource : List Char := "static bool prime_need_frame_completed(const PrimeNeedFrame *frame) {\n    return frame && (frame->cache_state == PRIME_NEED_CACHE_VALUE ||\n                     frame->cache_state == PRIME_NEED_CACHE_STABLE_FAULT);\n}".toList

def completionHeader : Header :=
  ⟨"prime_need_frame_completed", [⟨"frame", .ref (.named "NeedFrame")⟩], .bool⟩

def completionAliases : NativeC.RecordAliases := [("PrimeNeedFrame".toList, "NeedFrame")]

def completionTypes : NativeC.TypeNames := ["bool".toList, "PrimeNeedFrame".toList]

def frameAtom : Atom := .temporary 1 (.ref (.named "NeedFrame"))

def comparisonCode (first : Nat) (constant : BitVec 64) : List Instruction :=
  [.temporary first (.ref .word) (.fieldAddress frameAtom "NeedFrame" 19),
   .temporary (first + 1) .word (.indirectRead (.temporary first (.ref .word))),
   .temporary (first + 2) .bool
     (.binary (.compare .eq) (.temporary (first + 1) .word) (.word constant))]

def cacheTagCode : List Instruction :=
  comparisonCode 4 2 ++
    [.temporary 7 .bool (.copy (.temporary 6 .bool)),
     .branch (.negated (.temporary 7 .bool))
       (comparisonCode 8 3 ++ [.assign (.temporary 7 .bool) (.temporary 10 .bool)]) []]

def completionCode : List Instruction :=
  [.temporary 2 .bool (.binary (.compare .ne) frameAtom (.zero (.ref (.named "NeedFrame")))),
   .temporary 3 .bool (.copy (.temporary 2 .bool)),
   .branch (.value (.temporary 3 .bool))
     (cacheTagCode ++ [.assign (.temporary 3 .bool) (.temporary 7 .bool)]) [],
   .return (.temporary 3 .bool)]

def completionFunction : NativeIR.Function :=
  ⟨completionHeader, NativeC.primitiveParameterCapture completionHeader.parameters ++ completionCode, 10⟩


private def completionTokens : List NativeC.Token :=
  [.identifier "static".toList,
   .identifier "bool".toList,
   .identifier "prime_need_frame_completed".toList,
   .punctuation ['('],
   .identifier "const".toList,
   .identifier "PrimeNeedFrame".toList,
   .punctuation ['*'],
   .identifier "frame".toList,
   .punctuation [')'],
   .punctuation ['{'],
   .identifier "return".toList,
   .identifier "frame".toList,
   .punctuation ['&', '&'],
   .punctuation ['('],
   .identifier "frame".toList,
   .punctuation ['-', '>'],
   .identifier "cache_state".toList,
   .punctuation ['=', '='],
   .identifier "PRIME_NEED_CACHE_VALUE".toList,
   .punctuation ['|', '|'],
   .identifier "frame".toList,
   .punctuation ['-', '>'],
   .identifier "cache_state".toList,
   .punctuation ['=', '='],
   .identifier "PRIME_NEED_CACHE_STABLE_FAULT".toList,
   .punctuation [')'],
   .punctuation [';'],
   .punctuation ['}']]

private theorem completion_source_lexed : NativeC.lex completionSource = .ok completionTokens := by
  decide +kernel

def completionExpression : NativeC.CExpr :=
  .binary .and (.identifier "frame".toList)
    (.binary .or
      (.binary .eq (.field (.identifier "frame".toList) "cache_state".toList true)
        (.identifier "PRIME_NEED_CACHE_VALUE".toList))
      (.binary .eq (.field (.identifier "frame".toList) "cache_state".toList true)
        (.identifier "PRIME_NEED_CACHE_STABLE_FAULT".toList)))

def completionParsed : NativeC.CQualifiedFunction :=
  ⟨⟨"bool".toList, 0⟩, "prime_need_frame_completed".toList,
    [⟨⟨⟨"PrimeNeedFrame".toList, 1⟩, "frame".toList⟩, true⟩],
    [.return (some completionExpression)]⟩

theorem completion_source_parsed : NativeC.qualifiedFunction? (2 * completionTokens.length + 4)
    completionTypes (NativeC.ordinaryFunctionTokens completionTokens) = some (completionParsed, []) := by
  rfl

theorem completion_source_admitted (captures heapIndex : Bool) :
    NativeC.qualifiedReadOnlyFunctionText? (representation captures heapIndex provenance)
      completionTypes completionHeader completionAliases [true] cacheConstants completionSource =
      some completionFunction := by
  rw [NativeC.qualified_readonly_text_of_parts (representation captures heapIndex provenance) completionTypes
    completionHeader completionAliases [true] cacheConstants completionSource completionTokens
    completionParsed completion_source_lexed completion_source_parsed]
  cases provenance <;> cases captures <;> cases heapIndex <;> rfl

theorem cache_field_position (captures heapIndex : Bool) :
    NativeLowering.fieldLayout? (interface captures heapIndex provenance) "NeedFrame" "cache_state" = some 19 := by
  cases provenance <;> cases captures <;> cases heapIndex <;> rfl


private def comparisonFrame (frame : TargetFrame) (address : Address) (first : Nat)
    (tag constant : BitVec 64) : TargetFrame :=
  fieldEqualFrame frame address 19 first tag constant

private theorem comparison_frame_bound {frame : TargetFrame} {lower first : Nat}
    (bounded : TemporaryNamesBound frame lower) (fresh : lower < first)
    (address : Address) (tag constant : BitVec 64) :
    TemporaryNamesBound (comparisonFrame frame address first tag constant) (first + 2) :=
  field_equal_frame_bound bounded fresh address 19 tag constant

private theorem comparison_frame_protects {lower first : Nat} (frame : TargetFrame)
    (fresh : lower < first) (address : Address) (tag constant : BitVec 64) :
    TemporaryProtection lower frame (comparisonFrame frame address first tag constant) :=
  field_equal_frame_protects frame fresh address 19 tag constant

private theorem comparison_frame_scoped {frame : TargetFrame} (hscope : TemporariesScoped frame)
    (address : Address) (first : Nat) (tag constant : BitVec 64) :
    TemporariesScoped (comparisonFrame frame address first tag constant) :=
  field_equal_frame_scoped hscope address 19 first tag constant

private theorem comparison_execution_exact {World : Type} {captures heapIndex : Bool}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {address : Address} {lower first : Nat}
    (read : TargetAtomEval (interface captures heapIndex provenance) frame state frameAtom (.reference (some address)))
    (bounded : TemporaryNamesBound frame lower) (fresh : lower < first)
    (tag constant : BitVec 64)
    (loaded : targetRead state.memory (sourceFieldAddress address 19) = some (.word tag))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (interface captures heapIndex provenance) heap calls .bool root
      (comparisonCode first constant) frame state out ↔
      out = ⟨.normal, comparisonFrame frame address first tag constant, state⟩ :=
  field_equal_code_exact read bounded fresh tag constant loaded "NeedFrame" root out

private def cacheTagFrame {World : Type} (frame : TargetFrame) (state : TargetState World)
    (address : Address) (tag : BitVec 64) : TargetFrame :=
  let compared := comparisonFrame frame address 4 tag 2
  let marker := targetDeclareTemporary compared 7 (.bool (tag == 2))
  shortCircuitFrame false marker (comparisonFrame marker address 8 tag 3) state 7 (tag == 2) (tag == 3)

private theorem cache_tag_execution_exact {World : Type} {captures heapIndex : Bool}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {address : Address}
    (read : TargetAtomEval (interface captures heapIndex provenance) frame state frameAtom (.reference (some address)))
    (bounded : TemporaryNamesBound frame 3) (hscope : TemporariesScoped frame)
    (tag : BitVec 64)
    (loaded : targetRead state.memory (sourceFieldAddress address 19) = some (.word tag))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (interface captures heapIndex provenance) heap calls .bool root cacheTagCode frame state out ↔
      out = ⟨.normal, cacheTagFrame frame state address tag, state⟩ := by
  let compared := comparisonFrame frame address 4 tag 2
  let marker := targetDeclareTemporary compared 7 (.bool (tag == 2))
  let current := comparisonFrame marker address 8 tag 3
  have comparedBound := comparison_frame_bound bounded (show 3 < 4 by decide) address tag 2
  have comparedScope := comparison_frame_scoped hscope address 4 tag 2
  have markerBound : TemporaryNamesBound marker 7 :=
    declared_temporary_bound comparedBound (by decide : 6 ≤ 7) (Nat.le_refl _) _
  have markerScope := declared_temporaries_completeNames comparedScope 7 (.bool (tag == 2))
  have markerProtection : TemporaryProtection 3 frame marker :=
    temporary_protection_trans (comparison_frame_protects frame (show 3 < 4 by decide) address tag 2)
      (declare_temporary_protects compared _ (show 3 < 7 by decide))
  have pointerRead := (protection_atom_evaluation markerProtection frameAtom
    (by decide : 1 ≤ 3) state state _).mp read
  have condition : TargetAtomEval (interface captures heapIndex provenance) marker state
      (.temporary 7 .bool) (.bool (tag == 2)) :=
    declared_temporary_atom (interface captures heapIndex provenance) compared state 7 _ _
  have currentProtection := comparison_frame_protects marker (show 7 < 8 by decide) address tag 3
  have live : current.temporaryNames.contains 7 = true :=
    (currentProtection.names 7 (Nat.le_refl _)).trans (by simp [marker, targetDeclareTemporary])
  have resultRead : TargetAtomEval (interface captures heapIndex provenance) current state
      (.temporary 10 .bool) (.bool (tag == 3)) :=
    declared_temporary_atom (interface captures heapIndex provenance) _ state 10 _ _
  have armExact := short_circuit_rhs_exact false (heap := heap) (calls := calls)
    markerScope condition (by simp [comparisonCode, jumpFreeCode, jumpFreeInstruction])
    (fun _ => comparison_execution_exact pointerRead markerBound (by decide : 7 < 8) tag 3 loaded)
    resultRead live rfl
  simp only [shortCircuitCondition, Bool.false_eq_true, if_false] at armExact
  have firstRead : TargetAtomEval (interface captures heapIndex provenance) compared state
      (.temporary 6 .bool) (.bool (tag == 2)) :=
    declared_temporary_atom (interface captures heapIndex provenance) _ state 6 _ _
  unfold cacheTagCode
  rw [target_normal_prefix_then_exact (by simp [comparisonCode, jumpFreeCode, jumpFreeInstruction])
    (comparison_execution_exact read bounded (by decide : 3 < 4) tag 2 loaded root)]
  rw [target_short_circuit_copy_exact (temporary_bound_fresh comparedBound (by decide : 6 < 7)) firstRead]
  rw [target_normal_then_exact armExact]
  exact target_run_empty_exact root _ state out

private theorem cache_tag_frame_read {World : Type} (captures heapIndex : Bool)
    (frame : TargetFrame) (state : TargetState World) (address : Address) (tag : BitVec 64) :
    TargetAtomEval (interface captures heapIndex provenance) (cacheTagFrame frame state address tag) state
      (.temporary 7 .bool) (.bool ((tag == 2) || (tag == 3))) := by
  let compared := comparisonFrame frame address 4 tag 2
  let marker := targetDeclareTemporary compared 7 (.bool (tag == 2))
  let current := comparisonFrame marker address 8 tag 3
  have read : TargetAtomEval (interface captures heapIndex provenance) marker state
      (.temporary 7 .bool) (.bool (tag == 2)) :=
    declared_temporary_atom (interface captures heapIndex provenance) compared state 7 _ _
  have live : current.temporaryNames.contains 7 = true := by
    simp [current, comparisonFrame, fieldEqualFrame, fieldReadFrame, marker, targetDeclareTemporary]
  exact short_circuit_frame_read false read live rfl

private theorem cache_tag_frame_protects {World : Type}
    {frame : TargetFrame} (hscope : TemporariesScoped frame) (state : TargetState World)
    (address : Address) (tag : BitVec 64) :
    TemporaryProtection 3 frame (cacheTagFrame frame state address tag) := by
  let compared := comparisonFrame frame address 4 tag 2
  let marker := targetDeclareTemporary compared 7 (.bool (tag == 2))
  have comparedScope := comparison_frame_scoped hscope address 4 tag 2
  have markerScope := declared_temporaries_completeNames comparedScope 7 (.bool (tag == 2))
  have first : TemporaryProtection 3 frame marker :=
    temporary_protection_trans (comparison_frame_protects frame (show 3 < 4 by decide) address tag 2)
      (declare_temporary_protects compared _ (show 3 < 7 by decide))
  exact temporary_protection_trans first
    (short_circuit_frame_protects false markerScope
      (temporary_protection_weaken (by decide : 3 ≤ 7)
        (comparison_frame_protects marker (show 7 < 8 by decide) address tag 3))
      (by decide : 3 < 7) state (tag == 2) (tag == 3))

private theorem cache_tag_frame_extent {World : Type} (frame : TargetFrame)
    (state : TargetState World) (address : Address) (tag : BitVec 64) :
    (cacheTagFrame frame state address tag).storage = frame.storage ∧
      (cacheTagFrame frame state address tag).nextLocal = frame.nextLocal := by
  unfold cacheTagFrame shortCircuitFrame
  split <;> exact ⟨rfl, rfl⟩

private def pointerFrame (frame : TargetFrame) (pointer : Option Address) : TargetFrame :=
  targetDeclareTemporary (targetDeclareTemporary frame 2 (.bool pointer.isSome))
    3 (.bool pointer.isSome)

private def completionFrame {World : Type} (frame : TargetFrame) (state : TargetState World)
    (pointer : Option Address) (tag : BitVec 64) : TargetFrame :=
  let marker := pointerFrame frame pointer
  match pointer with
  | none => marker
  | some address => shortCircuitFrame true marker (cacheTagFrame marker state address tag)
      state 3 true ((tag == 2) || (tag == 3))

/-- Nullness is checked before the cache field is loaded. A nonnull input
requires an actual readable field, rather than merely a numeric address. -/
theorem completion_body_exact {World : Type} {captures heapIndex : Bool}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {pointer : Option Address}
    (read : TargetAtomEval (interface captures heapIndex provenance) frame state frameAtom (.reference pointer))
    (bounded : TemporaryNamesBound frame 1) (hscope : TemporariesScoped frame)
    (tag : BitVec 64)
    (loaded : ∀ address, pointer = some address →
      targetRead state.memory (sourceFieldAddress address 19) = some (.word tag))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (interface captures heapIndex provenance) heap calls .bool root completionCode frame state out ↔
      out = ⟨.returned (.bool (pointer.isSome && ((tag == 2) || (tag == 3)))),
        completionFrame frame state pointer tag, state⟩ := by
  let checked := targetDeclareTemporary frame 2 (.bool pointer.isSome)
  let marker := pointerFrame frame pointer
  have nullRead : TargetAtomEval (interface captures heapIndex provenance) frame state
      (.zero (.ref (.named "NeedFrame"))) (.reference none) :=
    .zero (.nullPointer (.named "NeedFrame"))
  have computed : TargetPureEval (interface captures heapIndex provenance) frame state
      (.binary (.compare .ne) frameAtom (.zero (.ref (.named "NeedFrame"))))
      (.bool pointer.isSome) :=
    .binary read nullRead (by cases pointer <;> rfl)
  have checkedBound : TemporaryNamesBound checked 2 :=
    declared_temporary_bound bounded (by decide : 1 ≤ 2) (Nat.le_refl _) _
  have markerBound : TemporaryNamesBound marker 3 :=
    declared_temporary_bound checkedBound (by decide : 2 ≤ 3) (Nat.le_refl _) _
  have markerScope : TemporariesScoped marker :=
    declared_temporaries_completeNames
      (declared_temporaries_completeNames hscope 2 (.bool pointer.isSome)) 3 _
  have condition : TargetAtomEval (interface captures heapIndex provenance) marker state
      (.temporary 3 .bool) (.bool pointer.isSome) :=
    declared_temporary_atom (interface captures heapIndex provenance) checked state 3 _ _
  unfold completionCode
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (temporary_bound_fresh bounded (by decide : 1 < 2)) computed)]
  rw [target_short_circuit_copy_exact (temporary_bound_fresh checkedBound (by decide : 2 < 3))
    (declared_temporary_atom (interface captures heapIndex provenance) frame state 2 _ _)]
  cases pointer with
  | none =>
      have skipped := target_short_circuit_skip_exact (heap := heap) (calls := calls)
        (result := NativeType.bool) true markerScope condition
        (cacheTagCode ++ [.assign (.temporary 3 .bool) (.temporary 7 .bool)])
      simp only [shortCircuitCondition, if_true] at skipped
      exact (target_normal_prefix_then_exact
        (by simp [cacheTagCode, comparisonCode, jumpFreeCode, jumpFreeInstruction])
        (skipped root) [.return (.temporary 3 .bool)] out).trans
        (target_return_then_exact condition root [] out)
  | some address =>
      have markerProtection : TemporaryProtection 1 frame marker :=
        temporary_protection_trans
          (declare_temporary_protects frame _ (by decide : 1 < 2))
          (declare_temporary_protects checked _ (by decide : 1 < 3))
      have pointerRead := (protection_atom_evaluation markerProtection frameAtom
        (by decide : 1 ≤ 1) state state _).mp read
      have protection := cache_tag_frame_protects markerScope state address tag
      have live : (cacheTagFrame marker state address tag).temporaryNames.contains 3 = true :=
        (protection.names 3 (Nat.le_refl _)).trans (by simp [marker, pointerFrame, targetDeclareTemporary])
      have extent := (cache_tag_frame_extent marker state address tag).2
      have armExact := short_circuit_rhs_exact true (heap := heap) (calls := calls)
        markerScope condition
        (by simp [cacheTagCode, comparisonCode, jumpFreeCode, jumpFreeInstruction])
        (fun _ => cache_tag_execution_exact pointerRead markerBound markerScope tag (loaded address rfl))
        (cache_tag_frame_read captures heapIndex marker state address tag) live extent
      have resultRead := short_circuit_frame_read true (value := (tag == 2) || (tag == 3)) condition live extent
      simp only [shortCircuitCondition, if_true] at armExact
      simp only [if_true] at resultRead
      exact (target_normal_then_exact armExact root [.return (.temporary 3 .bool)] out).trans
        (target_return_then_exact resultRead root [] out)

private theorem completion_frame_extent {World : Type} (frame : TargetFrame)
    (state : TargetState World) (pointer : Option Address) (tag : BitVec 64) :
    (completionFrame frame state pointer tag).storage = frame.storage ∧
      (completionFrame frame state pointer tag).nextLocal = frame.nextLocal := by
  cases pointer with
  | none => exact ⟨rfl, rfl⟩
  | some address => exact cache_tag_frame_extent (pointerFrame frame (some address)) state address tag

def completionBound {World : Type} (state : TargetState World) (storage : Nat)
    (pointer : Option Address) : TargetFrame × TargetState World :=
  targetDeclareLocal (targetEmptyFrame storage) state "frame"
    (.ref (.named "NeedFrame")) (.reference pointer)

private def completionCaptured (frame : TargetFrame) (pointer : Option Address) : TargetFrame :=
  targetDeclareTemporary frame 1 (.reference pointer)

private theorem completion_capture_prefix_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (pointer : Option Address)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (interface captures heapIndex provenance) heap calls .bool root completionFunction.body
      (completionBound state storage pointer).1 (completionBound state storage pointer).2 out ↔
      TargetRun (interface captures heapIndex provenance) heap calls .bool root completionCode
        (completionCaptured (completionBound state storage pointer).1 pointer)
        (completionBound state storage pointer).2 out := by
  let bound := completionBound state storage pointer
  have read : targetLocalValue bound.1 bound.2 "frame" = some (.reference pointer) :=
    target_singleton_parameter_readback state storage
      ⟨"frame", .ref (.named "NeedFrame")⟩ (.reference pointer)
  change TargetRun _ _ _ _ root
    (.temporary 1 (.ref (.named "NeedFrame")) (.readLocal "frame") :: completionCode)
    bound.1 bound.2 out ↔ _
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : bound.1.temporaryNames.contains 1 = false) (.local read))]
  rfl

private theorem completion_loaded_bound {World : Type} (state : TargetState World)
    (storage : Nat) (pointer : Option Address) (tag : BitVec 64)
    (fresh : targetFreshFrame state.memory storage)
    (loaded : ∀ address, pointer = some address →
      targetRead state.memory (sourceFieldAddress address 19) = some (.word tag)) :
    ∀ address, pointer = some address →
      targetRead (completionBound state storage pointer).2.memory (sourceFieldAddress address 19) =
        some (.word tag) := by
  intro address same
  have read := loaded address same
  have separate := targetFreshFrame_storage_ne_read fresh read
  have unchanged := targetRead_parameter_memory_other_storage state.memory storage 0
    [.reference pointer] (sourceFieldAddress address 19) (Ne.symm separate)
  exact unchanged.trans read

private theorem completion_invocation_body_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (pointer : Option Address) (tag : BitVec 64)
    (fresh : targetFreshFrame state.memory storage)
    (loaded : ∀ address, pointer = some address →
      targetRead state.memory (sourceFieldAddress address 19) = some (.word tag))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    let bound := completionBound state storage pointer
    TargetRun (interface captures heapIndex provenance) heap calls .bool root completionFunction.body bound.1 bound.2 out ↔
      out = ⟨.returned (.bool (pointer.isSome && ((tag == 2) || (tag == 3)))),
        completionFrame (completionCaptured bound.1 pointer) bound.2 pointer tag, bound.2⟩ := by
  let bound := completionBound state storage pointer
  dsimp only
  rw [completion_capture_prefix_exact]
  apply completion_body_exact
  · exact declared_temporary_atom (interface captures heapIndex provenance) bound.1 bound.2 1 _ _
  · intro identity live
    have present : identity = 1 := by
      simpa [completionCaptured, completionBound, targetDeclareLocal, targetEmptyFrame,
        targetDeclareTemporary, List.contains_iff_mem] using live
    omega
  · exact target_declared_names_complete _ _ _ (by intro _ _; rfl)
  · exact completion_loaded_bound state storage pointer tag fresh loaded

/-- Exact invocation of the admitted C predicate, including parameter-cell
allocation and release. It calls no service and preserves the entire caller
state. The null path needs no borrowed cache cell. -/
theorem completion_invocation_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (pointer : Option Address) (tag : BitVec 64)
    (loaded : ∀ address, pointer = some address →
      targetRead state.memory (sourceFieldAddress address 19) = some (.word tag))
    (result : TargetRawResult World) :
    TargetFunctionBody (interface captures heapIndex provenance) heap calls completionFunction
      [.reference pointer] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
        result = ⟨.bool (pointer.isSome && ((tag == 2) || (tag == 3))), state⟩ := by
  apply target_singleton_readonly_function_exact (interface captures heapIndex provenance)
    heap calls completionFunction ⟨"frame", .ref (.named "NeedFrame")⟩ rfl
    (.reference pointer) (.bool (pointer.isSome && ((tag == 2) || (tag == 3)))) state
    (fun storage => completionFrame
      (completionCaptured (completionBound state storage pointer).1 pointer)
      (completionBound state storage pointer).2 pointer tag)
  · intro storage fresh out
    exact completion_invocation_body_exact captures heapIndex heap calls state storage
      pointer tag fresh loaded completionFunction.body out
  · intro storage
    exact (completion_frame_extent
      (completionCaptured (completionBound state storage pointer).1 pointer)
      (completionBound state storage pointer).2 pointer tag).1.trans rfl
  · intro storage
    exact (completion_frame_extent
      (completionCaptured (completionBound state storage pointer).1 pointer)
      (completionBound state storage pointer).2 pointer tag).2.trans rfl

open Mettapedia.Machines.BranchLocalNeed

/-- Representation of the existing Need lifecycle in the C enum. -/
def cacheCode {Value Fault : Type*} : NeedReference.Cache Value Fault → BitVec 64
  | .suspended => 0
  | .evaluating _ => 1
  | .value _ => 2
  | .stableFault _ => 3

theorem cache_code_completed {Value Fault : Type*} (cache : NeedReference.Cache Value Fault) :
    ((cacheCode cache == 2) || (cacheCode cache == 3)) = true ↔ NeedCacheLaws.Cache.Completed cache := by
  cases cache with
  | suspended => constructor <;> intro h <;> cases h
  | evaluating owner => constructor <;> intro h <;> cases h
  | value value => exact ⟨fun _ => .value value, fun _ => rfl⟩
  | stableFault fault => exact ⟨fun _ => .stableFault fault, fun _ => rfl⟩

/-- The original C predicate returns true precisely for completed cells in
the independently defined Need machine, retaining all caller state. -/
theorem completion_invocation_reflects_cache {World : Type} {Value Fault : Type*}
    (captures heapIndex : Bool) (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (address : Address) (cache : NeedReference.Cache Value Fault)
    (loaded : targetRead state.memory (sourceFieldAddress address 19) = some (.word (cacheCode cache))) :
    TargetFunctionBody (interface captures heapIndex provenance) heap calls completionFunction
      [.reference (some address)] state ⟨.bool true, state⟩ ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧ NeedCacheLaws.Cache.Completed cache := by
  rw [completion_invocation_exact captures heapIndex heap calls state (some address) (cacheCode cache)
    (by intro other same; cases Option.some.inj same; exact loaded)]
  have resultEq : (⟨.bool true, state⟩ : TargetRawResult World) =
      ⟨.bool ((some address).isSome && ((cacheCode cache == 2) || (cacheCode cache == 3))), state⟩ ↔
      ((cacheCode cache == 2) || (cacheCode cache == 3)) = true := by
    constructor
    · intro same
      have equal := TargetValue.bool.inj (congrArg TargetRawResult.value same)
      simpa using equal.symm
    · intro completed
      change (⟨.bool true, state⟩ : TargetRawResult World) =
        ⟨.bool ((cacheCode cache == 2) || (cacheCode cache == 3)), state⟩
      rw [completed]
  rw [resultEq, cache_code_completed]

/-- The absent-frame branch is defined even with no readable cache storage. -/
theorem null_completion_invocation_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (result : TargetRawResult World) :
    TargetFunctionBody (interface captures heapIndex provenance) heap calls completionFunction [.reference none]
      state result ↔ (∃ storage, targetFreshFrame state.memory storage) ∧ result = ⟨.bool false, state⟩ := by
  simpa using completion_invocation_exact captures heapIndex heap calls state none 0
    (by intro _ impossible; cases impossible) result

namespace Controls

private def address : Address := ⟨11, 0, []⟩

private def state (tag : BitVec 64) : TargetState Nat :=
  ⟨⟨fun storage element =>
    if storage = 11 ∧ element = 0 then some (.record "NeedFrame"
      (List.replicate 4 (.reference none) ++ List.replicate 3 (.word 0) ++
        [.bool true, .bool true] ++ List.replicate 10 (.word 0) ++
        [.word tag, .reference none, .reference none])) else none,
    fun _ => none⟩, none, true, false, 37, AllocatorStats.targetEmpty⟩

private def noServices : TargetCalls Nat := fun _ _ _ _ _ => False

private theorem fresh (tag : BitVec 64) : targetFreshFrame (state tag).memory 12 := by
  constructor
  · rfl
  · intro position
    simp [state]

private theorem execute_tag (heap : TargetHeapSemantics Nat) (tag : BitVec 64) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference (some address)] (state tag)
      ⟨.bool ((tag == 2) || (tag == 3)), state tag⟩ := by
  apply (completion_invocation_exact false false heap noServices (state tag)
    (some address) tag (by intro other same; cases Option.some.inj same; rfl) _).mpr
  exact ⟨⟨12, fresh tag⟩, rfl⟩

theorem completed_value_accepted (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference (some address)] (state 2) ⟨.bool true, state 2⟩ := execute_tag heap 2

theorem stable_fault_accepted (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference (some address)] (state 3) ⟨.bool true, state 3⟩ := execute_tag heap 3

theorem suspended_cache_rejected (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference (some address)] (state 0) ⟨.bool false, state 0⟩ := execute_tag heap 0

theorem evaluating_cache_rejected (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference (some address)] (state 1) ⟨.bool false, state 1⟩ := execute_tag heap 1

theorem invalid_tag_rejected (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference (some address)] (state 4) ⟨.bool false, state 4⟩ := execute_tag heap 4

theorem null_retains_unrelated_storage (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference none] (state 2) ⟨.bool false, state 2⟩ :=
  (null_completion_invocation_exact false false heap noServices (state 2) _).mpr
    ⟨⟨12, fresh 2⟩, rfl⟩

end Controls

/-- The exact caller-visible field order of `PrimeNeedCellView`. -/
def viewFields (captures : Bool) (provenance : Bool := false) : List Parameter :=
  [⟨"cache_state", .word⟩] ++
  (if provenance then [⟨"value_role", .word⟩, ⟨"value_producer_thunk", .word⟩,
    ⟨"value_producer_update", .word⟩] else []) ++
  [⟨"origin", .ref (.named "Atom")⟩,
   ⟨"cached", .ref (.named "Atom")⟩, ⟨"authority_id", .word⟩,
   ⟨"evaluator_id", .word⟩, ⟨"storage_key", .word⟩, ⟨"import_key", .word⟩,
   ⟨"source_occurrence_id", .word⟩, ⟨"source_argument_index", .word⟩] ++
  (if captures then [⟨"capture_known", .bool⟩, ⟨"capture_var_ids", .ref .word⟩,
    ⟨"capture_var_count", .word⟩] else [])

def viewRepresentation (captures heapIndex : Bool) (provenance : Bool := false) : NativeC.Representation :=
  { representation captures heapIndex provenance with interface :=
      { interface captures heapIndex provenance with records :=
          [⟨"NeedFrame", frameFields captures heapIndex provenance⟩, ⟨"NeedCellView", viewFields captures provenance⟩] } }

def viewCopies (captures : Bool) (provenance : Bool := false) : List FieldCopy :=
  let offset := if provenance then 3 else 0
  [⟨19, 0, .word⟩] ++
  (if provenance then [⟨20, 1, .word⟩, ⟨21, 2, .word⟩, ⟨22, 3, .word⟩] else []) ++
  [⟨20 + offset, 1 + offset, .ref (.named "Atom")⟩,
   ⟨21 + offset, 2 + offset, .ref (.named "Atom")⟩,
   ⟨13, 3 + offset, .word⟩, ⟨14, 4 + offset, .word⟩,
   ⟨15, 5 + offset, .word⟩, ⟨16, 6 + offset, .word⟩,
   ⟨17, 7 + offset, .word⟩, ⟨18, 8 + offset, .word⟩] ++
  (if captures then [⟨22 + offset, 9 + offset, .bool⟩,
    ⟨23 + offset, 10 + offset, .ref .word⟩, ⟨24 + offset, 11 + offset, .word⟩] else [])

def viewHeader : Header :=
  ⟨"prime_need_cell_view_from_frame",
    [⟨"frame", .ref (.named "NeedFrame")⟩, ⟨"out", .ref (.named "NeedCellView")⟩], .unit⟩

def viewAliases : NativeC.RecordAliases :=
  [("PrimeNeedFrame".toList, "NeedFrame"), ("PrimeNeedCellView".toList, "NeedCellView")]

def viewTypes : NativeC.TypeNames :=
  ["void".toList, "PrimeNeedFrame".toList, "PrimeNeedCellView".toList]

private def viewPrefix : List Char :=
  ["static void prime_need_cell_view_from_frame(\n",
   "    const PrimeNeedFrame *frame, PrimeNeedCellView *out) {\n"].flatMap String.toList

/-- Configuration-selected original C body. The capture branch is the
authored conditional-compilation branch. Source lines are retained separately
so their character and token certificates compose through the ordinary reader. -/
def viewSource (captures : Bool) (provenance : Bool := false) : List Char :=
  viewPrefix ++
    (["    out->cache_state = frame->cache_state;\n"] ++
     (if provenance then
      ["    out->value_role = frame->value_role;\n",
       "    out->value_producer_thunk = frame->value_producer_thunk;\n",
       "    out->value_producer_update = frame->value_producer_update;\n"] else []) ++
     ["    out->origin = frame->origin;\n",
      "    out->cached = frame->cached;\n",
      "    out->authority_id = frame->authority_id;\n",
      "    out->evaluator_id = frame->evaluator_id;\n",
      "    out->storage_key = frame->storage_key;\n",
      "    out->import_key = frame->import_key;\n",
      "    out->source_occurrence_id = frame->source_occurrence_id;\n",
      "    out->source_argument_index = frame->source_argument_index;\n"] ++
     (if captures then
      ["    out->capture_known = frame->capture_known;\n",
       "    out->capture_var_ids = frame->capture_var_ids;\n",
       "    out->capture_var_count = frame->capture_var_count;\n"] else [])).flatMap String.toList ++ ['}']

private def viewNames (captures : Bool) (provenance : Bool := false) : List String :=
  ["cache_state"] ++
  (if provenance then ["value_role", "value_producer_thunk", "value_producer_update"] else []) ++
  ["origin", "cached", "authority_id", "evaluator_id", "storage_key",
    "import_key", "source_occurrence_id", "source_argument_index"] ++
  (if captures then ["capture_known", "capture_var_ids", "capture_var_count"] else [])

private def viewAssignment (member : String) : List Char :=
  ("    out->" ++ member ++ " = frame->" ++ member ++ ";\n").toList

private def viewPrefixTokens : List NativeC.Token :=
  [.identifier "static".toList, .identifier "void".toList,
   .identifier "prime_need_cell_view_from_frame".toList, .punctuation ['('],
   .identifier "const".toList, .identifier "PrimeNeedFrame".toList, .punctuation ['*'],
   .identifier "frame".toList, .punctuation [','], .identifier "PrimeNeedCellView".toList,
   .punctuation ['*'], .identifier "out".toList, .punctuation [')'], .punctuation ['{']]

private def viewAssignmentTokens (member : String) : List NativeC.Token :=
    [.identifier "out".toList, .punctuation ['-', '>'], .identifier member.toList,
     .punctuation ['='], .identifier "frame".toList, .punctuation ['-', '>'],
     .identifier member.toList, .punctuation [';']]

private def viewTokens (captures : Bool) (provenance : Bool := false) : List NativeC.Token :=
  viewPrefixTokens ++ (viewNames captures provenance).flatMap viewAssignmentTokens ++ [.punctuation ['}']]

def viewParsed (captures : Bool) (provenance : Bool := false) : NativeC.CQualifiedFunction :=
  ⟨⟨"void".toList, 0⟩, "prime_need_cell_view_from_frame".toList,
    [⟨⟨⟨"PrimeNeedFrame".toList, 1⟩, "frame".toList⟩, true⟩,
     ⟨⟨⟨"PrimeNeedCellView".toList, 1⟩, "out".toList⟩, false⟩],
    (viewNames captures provenance).map (fun member =>
      .assign (.field (.identifier "out".toList) member.toList true)
        (.field (.identifier "frame".toList) member.toList true))⟩

def viewCode (captures : Bool) (provenance : Bool := false) : List Instruction :=
  fieldCopiesCode (.temporary 1 (.ref (.named "NeedFrame")))
    (.temporary 2 (.ref (.named "NeedCellView"))) "NeedFrame" "NeedCellView" (viewCopies captures provenance) 3 ++
    [.return .unit]

def viewFunction (captures : Bool) (provenance : Bool := false) : NativeIR.Function :=
  ⟨viewHeader, NativeC.primitiveParameterCapture viewHeader.parameters ++ viewCode captures provenance,
    2 + 3 * (viewCopies captures provenance).length⟩

attribute [local irreducible] NativeC.LexSegmentAgreement NativeC.lex viewSource

private theorem view_prefix_lexed :
    NativeC.LexSegmentAgreement NativeC.initialPoint NativeC.initialPoint
      viewPrefix viewPrefixTokens := by
  apply (NativeC.segment_agreement_iff_empty_history _ _ _ _).mpr
  decide +kernel

private theorem view_assignments_lexed (captures : Bool) :
    (viewNames captures provenance).Forall (fun member =>
      (viewAssignment member).foldl NativeC.step (NativeC.initialPoint.state []) =
        NativeC.initialPoint.state (viewAssignmentTokens member).reverse) := by
  cases provenance <;> cases captures <;> decide +kernel

private theorem view_source_pieces (captures : Bool) :
    viewSource captures provenance = viewPrefix ++ (viewNames captures provenance).flatMap viewAssignment ++ ['}'] := by
  cases provenance <;> cases captures <;> unfold viewSource <;> rfl

private theorem view_source_lexed (captures : Bool) :
    NativeC.lex (viewSource captures provenance) = .ok (viewTokens captures provenance) := by
  let pieces := (viewNames captures provenance).map (fun member =>
    (viewAssignment member, viewAssignmentTokens member))
  have body := NativeC.lex_segments_list NativeC.initialPoint pieces (by
    intro piece member
    obtain ⟨name, present, rfl⟩ := List.mem_map.mp member
    exact (NativeC.segment_agreement_iff_empty_history _ _ _ _).mpr
      ((List.forall_iff_forall_mem.mp (view_assignments_lexed captures)) name present))
  have closing : NativeC.LexSegmentAgreement NativeC.initialPoint NativeC.initialPoint
      ['}'] [.punctuation ['}']] := by unfold NativeC.LexSegmentAgreement; intro prior; rfl
  have complete := NativeC.lex_checked_complete
    (NativeC.lex_segment_compose view_prefix_lexed (NativeC.lex_segment_compose body closing))
  rw [view_source_pieces]
  simpa only [pieces, List.flatMap_map, Function.comp_def, viewTokens,
    List.append_assoc] using complete

private theorem view_source_parsed (captures : Bool) :
    NativeC.qualifiedFunction? (2 * (viewTokens captures provenance).length + 4) viewTypes
      (NativeC.ordinaryFunctionTokens (viewTokens captures provenance)) = some (viewParsed captures provenance, []) := by
  cases provenance <;> cases captures <;> rfl

private theorem view_assignment_length (member : String) :
    (viewAssignment member).length = 21 + 2 * member.length := by
  simp only [viewAssignment, String.toList_append, List.length_append, String.length_toList]
  change 9 + member.length + 10 + member.length + 2 = 21 + 2 * member.length
  omega

private theorem view_prefix_length : viewPrefix.length = 104 := by
  decide +kernel

private theorem view_source_length (captures : Bool) :
    (viewSource captures provenance).length = (if captures then 665 else 512) + (if provenance then 165 else 0) := by
  rw [view_source_pieces]
  simp only [List.length_append, view_prefix_length, List.length_cons,
    List.length_nil, List.length_flatMap, view_assignment_length]
  cases provenance <;> cases captures <;>
    simp only [viewNames, ↓reduceIte]
  all_goals decide +kernel

private def viewParameters : List NativeC.CParameter :=
  [⟨⟨NativeC.recordName "NeedHistory" "NeedFrame", 1⟩, "frame".toList⟩,
   ⟨⟨NativeC.recordName "NeedHistory" "NeedCellView", 1⟩, "out".toList⟩]

private def viewLowered (captures : Bool) (provenance : Bool := false) : NativeIR.Function :=
  ⟨viewHeader, NativeC.primitiveParameterCapture viewHeader.parameters ++
    fieldCopiesCode (.temporary 1 (.ref (.named "NeedFrame")))
      (.temporary 2 (.ref (.named "NeedCellView"))) "NeedFrame" "NeedCellView"
      (viewCopies captures provenance) 3, 2 + 3 * (viewCopies captures provenance).length⟩

private theorem view_body_lowered (captures heapIndex : Bool) :
    NativeC.primitiveStatements? (NativeC.primitiveParameterBindings viewHeader.parameters ++ [])
      .unit ((viewSource captures provenance).length + 1) (viewParsed captures provenance).body ⟨2⟩
      (viewRepresentation captures heapIndex provenance).interface.externals
      (viewRepresentation captures heapIndex provenance) =
      some (fieldCopiesCode (.temporary 1 (.ref (.named "NeedFrame")))
        (.temporary 2 (.ref (.named "NeedCellView"))) "NeedFrame" "NeedCellView"
        (viewCopies captures provenance) 3, ⟨2 + 3 * (viewCopies captures provenance).length⟩) := by
  rw [view_source_length]
  cases provenance <;> cases captures <;> cases heapIndex
  all_goals
    simp only [viewParsed, viewNames, viewCopies, ↓reduceIte, List.append_nil,
      List.map_cons, List.map_nil, fieldCopiesCode, fieldCopyCode, List.cons_append,
      List.nil_append, List.length_cons, List.length_nil]
    repeat' (
      apply NativeC.primitive_field_copy_cons_of_parts
      case sourceBinding => rfl
      case destinationBinding => rfl
      case sourceType => rfl
      case destinationType => rfl
      case sourceField => rfl
      case destinationField => rfl)
    rfl

private theorem view_function_lowered (captures heapIndex : Bool) :
    NativeC.primitiveFunction? (viewRepresentation captures heapIndex provenance) viewHeader []
      ((viewSource captures provenance).length + 1)
      ⟨⟨"void".toList, 0⟩, (viewParsed captures provenance).name, viewParameters,
        (viewParsed captures provenance).body⟩ = some (viewLowered captures provenance) := by
  apply NativeC.primitive_function_of_parts
  · rfl
  · cases provenance <;> cases captures <;> cases heapIndex <;> rfl
  · rfl
  · exact view_body_lowered captures heapIndex

private theorem view_body_store_profile (captures heapIndex : Bool) (fuel : Nat) :
    (viewParsed captures provenance).body.all (NativeC.parameterStoreStatement
      (viewParsed captures provenance).parameters (viewRepresentation captures heapIndex provenance).interface.externals
      (fuel + 3)) = true := by
  change ((viewNames captures provenance).map (fun member =>
    NativeC.CStatement.assign (.field (.identifier "out".toList) member.toList true)
      (.field (.identifier "frame".toList) member.toList true))).all _ = true
  rw [List.all_map]
  apply List.all_eq_true.mpr
  intro member _
  exact NativeC.parameter_store_field_copy_of_permission _ _ _ _ _ _ fuel rfl

private theorem view_aliases_valid (captures heapIndex : Bool) :
    NativeC.recordAliasesValid (viewRepresentation captures heapIndex provenance) viewAliases = true := by
  cases provenance <;> cases captures <;> cases heapIndex <;> rfl

private theorem view_store_profile (captures heapIndex : Bool) :
    (!NativeC.recordAliasesValid (viewRepresentation captures heapIndex provenance) viewAliases ||
      (viewParsed captures provenance).parameters.map NativeC.CQualifiedParameter.pointeeConst != [true, false] ||
      !(viewParsed captures provenance).body.all (NativeC.parameterStoreStatement
        (viewParsed captures provenance).parameters (viewRepresentation captures heapIndex provenance).interface.externals
        ((viewSource captures provenance).length + 1))) = false := by
  have store := view_body_store_profile (provenance := provenance) captures heapIndex
    ((viewSource captures provenance).length - 2)
  have fuel : (viewSource captures provenance).length - 2 + 3 =
      (viewSource captures provenance).length + 1 := by
    rw [view_source_length]
    cases provenance <;> cases captures <;> decide
  rw [fuel] at store
  rw [store, view_aliases_valid]
  cases provenance <;> cases captures <;> rfl

private theorem view_result_type (captures heapIndex : Bool) :
    NativeC.canonicalPrototypeType? (viewRepresentation captures heapIndex provenance) viewAliases
      (viewParsed captures provenance).result = some ⟨"void".toList, 0⟩ := by
  cases provenance <;> cases captures <;> cases heapIndex <;> rfl

private theorem view_parameter_types (captures heapIndex : Bool) :
    (viewParsed captures provenance).unqualified.parameters.mapM (fun parameter => do
      let type ← NativeC.canonicalPrototypeType? (viewRepresentation captures heapIndex provenance)
        viewAliases parameter.type
      some { parameter with type := type }) = some viewParameters := by
  cases provenance <;> cases captures <;> cases heapIndex <;> rfl

theorem view_source_admitted (captures heapIndex : Bool) :
    NativeC.qualifiedParameterStoreFunctionText? (viewRepresentation captures heapIndex provenance)
      viewTypes viewHeader viewAliases [true, false] [] (viewSource captures provenance) =
      some (viewFunction captures provenance) := by
  rw [NativeC.qualified_parameter_store_text_of_parts (viewRepresentation captures heapIndex provenance)
    viewTypes viewHeader viewAliases [true, false] [] (viewSource captures provenance) (viewTokens captures provenance)
    (viewParsed captures provenance) (view_source_lexed captures) (view_source_parsed captures)]
  have checked := NativeC.qualified_parameter_store_function_of_parts
    (viewRepresentation captures heapIndex provenance) viewHeader viewAliases [true, false] []
    ((viewSource captures provenance).length + 1) (viewParsed captures provenance) ⟨"void".toList, 0⟩ viewParameters
    (viewLowered captures provenance) (view_store_profile captures heapIndex) (view_result_type captures heapIndex)
    (view_parameter_types captures heapIndex) (view_function_lowered captures heapIndex)
  simpa only [viewLowered, viewFunction, viewCode, viewHeader, ↓reduceIte,
    List.append_assoc] using checked

/-- Complete body behavior includes every authored field assignment and the
implicit void return. The independent storage account keeps actual aliases,
all intermediate reads and every write; only compiler-private cells are new. -/
theorem view_body_execution_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (source destination : Address)
    (sourceRead : TargetAtomEval (viewRepresentation captures heapIndex provenance).interface frame state
      (.temporary 1 (.ref (.named "NeedFrame"))) (.reference (some source)))
    (destinationRead : TargetAtomEval (viewRepresentation captures heapIndex provenance).interface frame state
      (.temporary 2 (.ref (.named "NeedCellView"))) (.reference (some destination)))
    (bounded : TemporaryNamesBound frame 2) (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (viewRepresentation captures heapIndex provenance).interface heap calls .unit root
      (viewCode captures provenance) frame state out ↔
      ∃ after memory,
        FieldCopiesExecution source destination (viewCopies captures provenance) 3 frame state.memory after memory ∧
        out = ⟨.returned .unit, after, { state with memory := memory }⟩ := by
  unfold viewCode
  rw [field_copies_code_then_iff "NeedFrame" "NeedCellView" (viewCopies captures provenance)
    sourceRead destinationRead (show 1 ≤ 2 by decide) (Nat.le_refl 2) bounded (show 2 < 3 by decide)]
  simp only [target_return_then_exact (TargetAtomEval.unit)]

def viewBound {World : Type} (state : TargetState World) (storage : Nat)
    (source destination : Address) : TargetFrame × TargetState World :=
  let first := targetDeclareLocal (targetEmptyFrame storage) state "frame"
    (.ref (.named "NeedFrame")) (.reference (some source))
  targetDeclareLocal first.1 first.2 "out" (.ref (.named "NeedCellView")) (.reference (some destination))

private def viewCaptured (frame : TargetFrame) (source destination : Address) : TargetFrame :=
  targetDeclareTemporary (targetDeclareTemporary frame 1 (.reference (some source)))
    2 (.reference (some destination))

private theorem view_bound_memory {World : Type} (state : TargetState World) (storage : Nat)
    (source destination : Address) :
    (viewBound state storage source destination).2 =
      { state with memory := (targetParameterMemory state.memory storage 0
        [.reference (some source), .reference (some destination)]) } := by rfl

private theorem view_parameter_readback {World : Type} (state : TargetState World) (storage : Nat)
    (source destination : Address) :
    let bound := viewBound state storage source destination
    targetLocalValue bound.1 bound.2 "frame" = some (.reference (some source)) ∧
      targetLocalValue bound.1 bound.2 "out" = some (.reference (some destination)) := by
  let first := targetDeclareLocal (targetEmptyFrame storage) state "frame"
    (.ref (.named "NeedFrame")) (.reference (some source))
  refine ⟨?_, target_declared_local_readback first.1 first.2 "out"
    (.ref (.named "NeedCellView")) (.reference (some destination))⟩
  have address : targetLocalAddress first.1 "frame" = some ⟨storage, 0, []⟩ :=
    target_declared_local_address (targetEmptyFrame storage) state "frame"
      (.ref (.named "NeedFrame")) (.reference (some source))
  exact (target_local_readback_after_other_declare first.1 first.2 "frame" "out"
    (.ref (.named "NeedCellView")) (.reference (some destination)) ⟨storage, 0, []⟩
    (by decide) address (by change (0 : Nat) ≠ 1; decide)).trans
      (target_declared_local_readback (targetEmptyFrame storage) state "frame"
        (.ref (.named "NeedFrame")) (.reference (some source)))

private theorem view_capture_prefix_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (source destination : Address)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (viewRepresentation captures heapIndex provenance).interface heap calls .unit root
      (viewFunction captures provenance).body (viewBound state storage source destination).1
      (viewBound state storage source destination).2 out ↔
      TargetRun (viewRepresentation captures heapIndex provenance).interface heap calls .unit root
        (viewCode captures provenance) (viewCaptured (viewBound state storage source destination).1 source destination)
        (viewBound state storage source destination).2 out := by
  let bound := viewBound state storage source destination
  obtain ⟨sourceRead, destinationRead⟩ := view_parameter_readback state storage source destination
  change TargetRun _ _ _ _ root
    (.temporary 1 (.ref (.named "NeedFrame")) (.readLocal "frame") ::
     .temporary 2 (.ref (.named "NeedCellView")) (.readLocal "out") :: viewCode captures provenance)
    bound.1 bound.2 out ↔ _
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : bound.1.temporaryNames.contains 1 = false) (.local sourceRead))]
  have destinationReadAfter : targetLocalValue
      (targetDeclareTemporary bound.1 1 (.reference (some source))) bound.2 "out" =
        some (.reference (some destination)) := destinationRead
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by change ([1] : List Nat).contains 2 = false; decide)
    (.local destinationReadAfter))]
  rfl

private theorem view_invocation_body_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (source destination : Address)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    let bound := viewBound state storage source destination
    TargetRun (viewRepresentation captures heapIndex provenance).interface heap calls .unit root
      (viewFunction captures provenance).body bound.1 bound.2 out ↔
      ∃ after memory,
        FieldCopiesExecution source destination (viewCopies captures provenance) 3
          (viewCaptured bound.1 source destination) bound.2.memory after memory ∧
        out = ⟨.returned .unit, after, { bound.2 with memory := memory }⟩ := by
  let bound := viewBound state storage source destination
  dsimp only
  rw [view_capture_prefix_exact]
  apply view_body_execution_exact
  · exact .temporary (by rfl) (by rfl)
  · exact .temporary (by rfl) (by rfl)
  · intro identity present
    have same : identity = 2 ∨ identity = 1 := by
      simpa [viewCaptured, viewBound, targetDeclareLocal, targetEmptyFrame,
        targetDeclareTemporary, List.contains_iff_mem] using present
    omega

/-- Whole execution of the actual view-copy function. Caller storage must be
live; references are borrowed, and copying them does not acquire their payloads.
The result preserves all caller state except the ordered field writes. -/
theorem view_invocation_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (source destination : Address)
    (sourceLive : ∃ value, targetRead state.memory source = some value)
    (destinationLive : ∃ value, targetRead state.memory destination = some value)
    (result : TargetRawResult World) :
    TargetFunctionBody (viewRepresentation captures heapIndex provenance).interface heap calls (viewFunction captures provenance)
      [.reference (some source), .reference (some destination)] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
      ∃ memory,
        targetCopyFields source destination
          ((viewCopies captures provenance).map (fun field => (field.sourceIndex, field.destinationIndex)))
          state.memory = some memory ∧
        result = ⟨.unit, { state with memory := memory }⟩ := by
  obtain ⟨sourceValue, sourceRead⟩ := sourceLive
  obtain ⟨destinationValue, destinationRead⟩ := destinationLive
  constructor
  · intro ran
    cases ran with
    | @run storage frame bound out raw fresh parameters body returned =>
      have pair : (frame, bound) = viewBound state storage source destination :=
        (Option.some.inj parameters).symm
      have frameEq : frame = (viewBound state storage source destination).1 := congrArg Prod.fst pair
      have stateEq : bound = (viewBound state storage source destination).2 := congrArg Prod.snd pair
      subst frame
      subst bound
      obtain ⟨after, memory, copied, exactOut⟩ :=
        (view_invocation_body_exact captures heapIndex heap calls state storage source destination
          (viewFunction captures provenance).body out).mp body
      have rawEq : raw = .unit := TargetFlow.returned.inj
        (returned.symm.trans (congrArg TargetBlockOutcome.flow exactOut))
      have sourceSeparate : storage ≠ source.storage :=
        targetFreshFrame_storage_ne_read fresh sourceRead
      have destinationSeparate : storage ≠ destination.storage :=
        targetFreshFrame_storage_ne_read fresh destinationRead
      have observed := field_copies_execution_memory copied
      rw [view_bound_memory, targetCopyFields_parameter_memory source destination _ state.memory
        storage 0 [.reference (some source), .reference (some destination)]
        sourceSeparate.symm destinationSeparate.symm] at observed
      obtain ⟨callerMemory, callerCopied, memoryEq⟩ := Option.map_eq_some_iff.mp observed
      have extent := field_copies_execution_frame_extent copied
      have released : targetDropLocals memory storage 0 2 = callerMemory := by
        rw [← memoryEq]
        exact target_field_copy_parameter_teardown source destination _ storage
          [.reference (some source), .reference (some destination)] fresh destinationSeparate callerCopied
      refine ⟨⟨storage, fresh⟩, callerMemory, callerCopied, ?_⟩
      rw [rawEq, exactOut]
      rw [view_bound_memory]
      exact congrArg (TargetRawResult.mk .unit)
        (target_invocation_teardown state storage 2 after memory callerMemory extent.1 extent.2 released)
  · rintro ⟨⟨storage, fresh⟩, memory, copied, rfl⟩
    let bound := viewBound state storage source destination
    have sourceSeparate : storage ≠ source.storage :=
      targetFreshFrame_storage_ne_read fresh sourceRead
    have destinationSeparate : storage ≠ destination.storage :=
      targetFreshFrame_storage_ne_read fresh destinationRead
    have parameterCopied : targetCopyFields source destination
        ((viewCopies captures provenance).map (fun field => (field.sourceIndex, field.destinationIndex))) bound.2.memory =
        some (targetParameterMemory memory storage 0
          [.reference (some source), .reference (some destination)]) := by
      rw [view_bound_memory, targetCopyFields_parameter_memory source destination _ state.memory
        storage 0 [.reference (some source), .reference (some destination)]
        sourceSeparate.symm destinationSeparate.symm, copied]
      rfl
    obtain ⟨after, account⟩ := field_copies_execution_of_memory source destination (viewCopies captures provenance)
      3 (viewCaptured bound.1 source destination) parameterCopied
    let finalMemory := targetParameterMemory memory storage 0
      [.reference (some source), .reference (some destination)]
    let out : TargetBlockOutcome World := ⟨.returned .unit, after, { bound.2 with memory := finalMemory }⟩
    have body := (view_invocation_body_exact captures heapIndex heap calls state storage source destination
      (viewFunction captures provenance).body out).mpr ⟨after, finalMemory, account, rfl⟩
    have extent := field_copies_execution_frame_extent account
    have released : targetDropLocals finalMemory storage 0 2 = memory :=
      target_field_copy_parameter_teardown source destination _ storage
        [.reference (some source), .reference (some destination)] fresh destinationSeparate copied
    have executed : TargetFunctionBody (viewRepresentation captures heapIndex provenance).interface heap calls
        (viewFunction captures provenance) [.reference (some source), .reference (some destination)] state
        ⟨.unit, (targetLeaveScope (targetEmptyFrame storage) out.frame out.state).2⟩ :=
      .run fresh (by rfl) body rfl
    have teardown : (targetLeaveScope (targetEmptyFrame storage) out.frame out.state).2 =
        { state with memory := memory } := by
      dsimp only [out]
      rw [view_bound_memory]
      exact target_invocation_teardown state storage 2 after finalMemory memory extent.1 extent.2 released
    rw [teardown] at executed
    exact executed

/-- The original C view body preserves and reflects the independent source
storage account. Native success neither omits a source assignment nor invents
a field value. Caller state and allocation ownership remain visible. -/
theorem view_invocation_correspondence {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (sourceMemory : SourceMemory) (state : TargetState World)
    (related : MemoryRelated sourceMemory state.memory) (source destination : Address)
    (sourceLive : ∃ value, targetRead state.memory source = some value)
    (destinationLive : ∃ value, targetRead state.memory destination = some value)
    (result : TargetRawResult World) :
    TargetFunctionBody (viewRepresentation captures heapIndex provenance).interface heap calls (viewFunction captures provenance)
      [.reference (some source), .reference (some destination)] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
      ∃ original memory,
        sourceCopyFields source destination
          ((viewCopies captures provenance).map (fun field => (field.sourceIndex, field.destinationIndex)))
          sourceMemory = some original ∧
        MemoryRelated original memory ∧ result = ⟨.unit, { state with memory := memory }⟩ := by
  rw [view_invocation_exact captures heapIndex heap calls state source destination sourceLive destinationLive]
  constructor
  · rintro ⟨fresh, memory, copied, resultEq⟩
    obtain ⟨original, sourceCopied, afterRelated⟩ := field_copies_backward source destination _ related copied
    exact ⟨fresh, original, memory, sourceCopied, afterRelated, resultEq⟩
  · rintro ⟨fresh, original, memory, copied, afterRelated, resultEq⟩
    obtain ⟨native, nativeCopied, nativeRelated⟩ := field_copies_forward source destination _ related copied
    have same := memory_related_target_unique nativeRelated afterRelated
    exact ⟨fresh, native, nativeCopied, by simpa only [same] using resultEq⟩

namespace ViewControls
open Mettapedia.GSLT.LanguageDef.NativeOps

def source : Address := ⟨1, 0, []⟩
def destination : Address := ⟨2, 0, []⟩
def payload : Address := ⟨8, 0, []⟩

def frameValue (captures heapIndex : Bool) (provenance : Bool := false) : TargetValue :=
  .record "NeedFrame"
    ([.reference none, .reference none, .reference none, .reference none,
      .word 0, .word 0, .word 0, .bool true, .bool true,
      .word 16, .word 19, .word 23, .word 29,
      .word 101, .word 0, .word 107, .word 109, .word 113, .word 127,
      .word 2] ++
     (if provenance then [.word 1, .word 211, .word 223] else []) ++
     [.reference (some payload), .reference (some payload)] ++
     (if captures then [.bool true, .reference none, .word 3] else []) ++
     (if heapIndex then [.reference none, .reference none] else []))

def emptyView (captures : Bool) (provenance : Bool := false) : TargetValue :=
  .record "NeedCellView"
    ([.word 0] ++
     (if provenance then [.word 0, .word 0, .word 0] else []) ++
     [.reference none, .reference none,
      .word 0, .word 0, .word 0, .word 0, .word 0, .word 0] ++
     (if captures then [.bool false, .reference none, .word 0] else []))

def memory (captures heapIndex : Bool) (provenance : Bool := false) : TargetMemory :=
  ⟨fun storage position => if position = 0 then
      if storage = 1 then some (frameValue captures heapIndex provenance)
      else if storage = 2 then some (emptyView captures provenance)
      else if storage = 8 then some (.record "Atom" [.word 211]) else none
    else none,
   fun storage => if storage = 1 ∨ storage = 2 ∨ storage = 8 then some 1 else none⟩

def state (captures heapIndex : Bool) (provenance : Bool := false) : TargetState Nat :=
  ⟨memory captures heapIndex provenance, none, true, false, 37, AllocatorStats.targetEmpty⟩

def copied (captures heapIndex : Bool) (provenance : Bool := false) : Option TargetMemory :=
  targetCopyFields source destination
    ((viewCopies captures provenance).map (fun field => (field.sourceIndex, field.destinationIndex)))
    (memory captures heapIndex provenance)

def observed (captures heapIndex : Bool) (index : Nat) (provenance : Bool := false) : Option TargetValue :=
  (copied captures heapIndex provenance).bind (fun after => targetRead after ⟨2, 0, [index]⟩)

theorem copied_cache_is_completed (captures heapIndex : Bool) :
    observed captures heapIndex 0 = some (.word 2) := by
  cases captures <;> cases heapIndex <;> rfl

theorem copied_authority_is_original (captures heapIndex : Bool) :
    observed captures heapIndex 3 = some (.word 101) := by
  cases captures <;> cases heapIndex <;> rfl

theorem copied_occurrence_is_original (captures heapIndex : Bool) :
    observed captures heapIndex 7 = some (.word 113) := by
  cases captures <;> cases heapIndex <;> rfl

theorem copied_argument_is_original (captures heapIndex : Bool) :
    observed captures heapIndex 8 = some (.word 127) := by
  cases captures <;> cases heapIndex <;> rfl

theorem copied_payload_alias_is_retained (captures heapIndex : Bool) :
    observed captures heapIndex 1 = some (.reference (some payload)) ∧
      observed captures heapIndex 2 = some (.reference (some payload)) := by
  cases captures <;> cases heapIndex <;> exact ⟨rfl, rfl⟩

theorem captures_are_copied (heapIndex : Bool) :
    observed true heapIndex 9 = some (.bool true) ∧
      observed true heapIndex 11 = some (.word 3) := by
  cases heapIndex <;> exact ⟨rfl, rfl⟩

theorem source_and_payload_remain_live (captures heapIndex : Bool) :
    (copied captures heapIndex).bind (fun after => targetRead after source) =
      some (frameValue captures heapIndex) ∧
    (copied captures heapIndex).bind (fun after => targetRead after payload) =
      some (.record "Atom" [.word 211]) := by
  cases captures <;> cases heapIndex <;> exact ⟨rfl, rfl⟩

theorem original_view_invocation_executes (captures heapIndex : Bool)
    (heap : TargetHeapSemantics Nat) (calls : TargetCalls Nat)
    (provenance : Bool := false) :
    ∃ memory,
      TargetFunctionBody (viewRepresentation captures heapIndex provenance).interface heap calls (viewFunction captures provenance)
        [.reference (some source), .reference (some destination)] (state captures heapIndex provenance)
        ⟨.unit, { state captures heapIndex provenance with memory := memory }⟩ ∧
      targetRead memory ⟨2, 0, [7 + (if provenance then 3 else 0)]⟩ = some (.word 113) ∧
      memory.owned = (state captures heapIndex provenance).memory.owned := by
  have defined : ∃ memory, copied captures heapIndex provenance = some memory := by
    cases provenance <;> cases captures <;> cases heapIndex <;> exact ⟨_, rfl⟩
  obtain ⟨after, copied⟩ := defined
  have sourceLive : ∃ value, targetRead (state captures heapIndex provenance).memory source = some value :=
    ⟨frameValue captures heapIndex provenance, rfl⟩
  have destinationLive : ∃ value, targetRead (state captures heapIndex provenance).memory destination = some value :=
    ⟨emptyView captures provenance, rfl⟩
  have fresh : targetFreshFrame (state captures heapIndex provenance).memory 3 :=
    ⟨rfl, fun position => by simp [state, memory]⟩
  refine ⟨after,
    (view_invocation_exact (provenance := provenance) captures heapIndex heap calls
      (state captures heapIndex provenance) source destination
      sourceLive destinationLive _).mpr ⟨⟨3, fresh⟩, after, copied, rfl⟩, ?_, ?_⟩
  · have observed : (ViewControls.copied captures heapIndex provenance).bind
        (fun after => targetRead after ⟨2, 0, [7 + (if provenance then 3 else 0)]⟩) =
        some (.word 113) := by
      cases provenance <;> cases captures <;> cases heapIndex <;> rfl
    rw [copied] at observed
    exact observed
  · exact target_field_copies_owned source destination _ copied

def missingSource (captures heapIndex : Bool) : TargetState Nat :=
  { (state captures heapIndex) with memory :=
      (targetStoreCell (memory captures heapIndex) 1 0 (.record "NeedFrame" [])) }

theorem nonnull_missing_field_has_no_invocation (captures heapIndex : Bool)
    (heap : TargetHeapSemantics Nat) (calls : TargetCalls Nat) (result : TargetRawResult Nat) :
    ¬ TargetFunctionBody (viewRepresentation captures heapIndex).interface heap calls (viewFunction captures)
      [.reference (some source), .reference (some destination)] (missingSource captures heapIndex) result := by
  have sourceLive : ∃ value, targetRead (missingSource captures heapIndex).memory source = some value :=
    ⟨.record "NeedFrame" [], rfl⟩
  have destinationLive : ∃ value, targetRead (missingSource captures heapIndex).memory destination = some value :=
    ⟨emptyView captures, rfl⟩
  rw [view_invocation_exact captures heapIndex heap calls (missingSource captures heapIndex)
    source destination sourceLive destinationLive]
  have missing : targetCopyFields source destination
      ((viewCopies captures).map (fun field => (field.sourceIndex, field.destinationIndex)))
      (missingSource captures heapIndex).memory = none := by
    cases captures <;> cases heapIndex <;> rfl
  simp only [missing, reduceCtorEq, false_and, exists_false, and_false, not_false_eq_true]

/-- Omitting the actual occurrence assignment leaves the caller's zero
marker. Equal payload pointers cannot disguise the missing provenance. -/
theorem omitted_occurrence_is_visible (captures heapIndex : Bool) :
    (targetCopyFields source destination
      (((viewCopies captures).filter (fun field => field.destinationIndex != 7)).map
        (fun field => (field.sourceIndex, field.destinationIndex))) (memory captures heapIndex)).bind
      (fun after => targetRead after ⟨2, 0, [7]⟩) = some (.word 0) := by
  cases captures <;> cases heapIndex <;> rfl

/-- The former position now names source-argument metadata, not the cache.
An old positional adapter therefore changes an observable read. -/
theorem former_cache_position_reads_argument (captures heapIndex : Bool) :
    targetRead (memory captures heapIndex) { source with fields := [18] } = some (.word 127) ∧
      targetRead (memory captures heapIndex) { source with fields := [19] } = some (.word 2) := by
  cases captures <;> cases heapIndex <;> exact ⟨rfl, rfl⟩

end ViewControls

/-! ## Borrowed view readback

The native view's payload addresses stay borrowed addresses. Reading this
representation does not decode Atom graphs, retain resources, or transport a
complete evaluator configuration. The source cache is the existing Need cache,
with every native authority, occurrence and capture field kept alongside it.
-/

/-- The returned-syntax role is metadata, distinct from cache completion. -/
inductive ValueRole where
  | demandResult | ready
  deriving DecidableEq, Repr

structure ValueProvenance where
  role : ValueRole
  producerThunk : BitVec 64
  producerUpdate : BitVec 64
  deriving DecidableEq, Repr

def valueRoleCode : ValueRole → BitVec 64
  | .demandResult => 0
  | .ready => 1

/-- The locally observable guards of `prime_need_snapshot_push`. The view
omits the consumer thunk and update serial; producer identity, session and
causal-world validation require additional history information. -/
def ValueProvenanceAdmissible (tag role producerThunk producerUpdate : BitVec 64) : Prop :=
  (role = 0 ∨ role = 1) ∧ (role = 1 → tag = 2) ∧
    (producerThunk = 0 ↔ producerUpdate = 0) ∧ (producerThunk ≠ 0 → tag = 2)

instance (tag role producerThunk producerUpdate : BitVec 64) :
    Decidable (ValueProvenanceAdmissible tag role producerThunk producerUpdate) := by
  unfold ValueProvenanceAdmissible
  infer_instance

/-- Metadata is retained exactly; a producer update never becomes a thunk ID. -/
def readValueProvenance? (tag role producerThunk producerUpdate : BitVec 64) :
    Option ValueProvenance :=
  if ValueProvenanceAdmissible tag role producerThunk producerUpdate then
    some ⟨if role = 0 then .demandResult else .ready, producerThunk, producerUpdate⟩
  else none

structure CellViewReadback where
  record : NeedReference.CellRecord Address Address Address
  authority : BitVec 64
  evaluator : BitVec 64
  storage : BitVec 64
  imported : BitVec 64
  occurrence : BitVec 64
  argument : BitVec 64
  captures : Option (Bool × Option Address × BitVec 64)
  valueProvenance : Option ValueProvenance := none
  deriving DecidableEq, Repr

/-- Invalid tags, missing completed payloads and inconsistent evaluator roles
are rejected rather than converted into a source cache constructor. -/
def readCacheFields? (tag evaluator : BitVec 64) (cached : Option Address) :
    Option (NeedReference.Cache Address Address) :=
  if tag = 0 then
    if evaluator = 0 ∧ cached = none then some .suspended else none
  else if tag = 1 then
    if evaluator ≠ 0 ∧ cached = none then some (.evaluating evaluator.toNat) else none
  else if tag = 2 then
    if evaluator = 0 then cached.map .value else none
  else if tag = 3 then
    if evaluator = 0 then cached.map .stableFault else none
  else none

private def readCaptureFields? (captures : Bool) : List TargetValue →
    Option (Option (Bool × Option Address × BitVec 64))
  | [] => if captures then none else some none
  | [.bool known, .reference variableIds, .word count] =>
      if captures then some (some (known, variableIds, count)) else none
  | _ => none

private def readCellViewFields? (captures : Bool) (tag : BitVec 64)
    (metadata : Option ValueProvenance) : List TargetValue → Option CellViewReadback
  | .reference (some origin) :: .reference cached ::
      .word authority :: .word evaluator :: .word storage :: .word imported ::
      .word occurrence :: .word argument :: tail => do
      if authority = 0 then none else do
        let cache ← readCacheFields? tag evaluator cached
        let captured ← readCaptureFields? captures tail
        some ⟨⟨origin, cache⟩, authority, evaluator, storage, imported,
          occurrence, argument, captured, metadata⟩
  | _ => none

/-- Read exactly the selected C view shape. The base layout records absence
of provenance; the extended layout validates and retains the role and producer
update. Named cells may have storage key zero; authority remains separate. -/
def readCellViewWithProvenance? (captures provenance : Bool) :
    TargetValue → Option CellViewReadback
  | .record "NeedCellView" (.word tag :: fields) =>
      if provenance then
        match fields with
        | .word role :: .word producerThunk :: .word producerUpdate :: rest => do
            let metadata ← readValueProvenance? tag role producerThunk producerUpdate
            readCellViewFields? captures tag (some metadata) rest
        | _ => none
      else readCellViewFields? captures tag none fields
  | _ => none

/-- The original public reader specializes the common decoder to the base
view layout, where provenance metadata is absent. -/
abbrev readCellView? (captures : Bool) : TargetValue → Option CellViewReadback :=
  readCellViewWithProvenance? captures false

/-- Successful metadata readback enforces the checked role combinations and
preserves both exact producer words, including the selected update identity. -/
theorem readValueProvenance?_sound {tag role producerThunk producerUpdate : BitVec 64}
    {metadata : ValueProvenance}
    (read : readValueProvenance? tag role producerThunk producerUpdate = some metadata) :
    ValueProvenanceAdmissible tag role producerThunk producerUpdate ∧
      valueRoleCode metadata.role = role ∧ metadata.producerThunk = producerThunk ∧
      metadata.producerUpdate = producerUpdate := by
  unfold readValueProvenance? at read
  split at read
  · next valid =>
    cases Option.some.inj read
    refine ⟨valid, ?_, rfl, rfl⟩
    by_cases demand : role = 0
    · simp [demand, valueRoleCode]
    · have ready : role = 1 := valid.1.resolve_left demand
      simp [ready, valueRoleCode]
  · simp at read

theorem readValueProvenance?_exists_iff (tag role producerThunk producerUpdate : BitVec 64) :
    (∃ metadata, readValueProvenance? tag role producerThunk producerUpdate = some metadata) ↔
      ValueProvenanceAdmissible tag role producerThunk producerUpdate := by
  constructor
  · rintro ⟨metadata, read⟩
    exact (readValueProvenance?_sound read).1
  · intro valid
    exact ⟨⟨if role = 0 then .demandResult else .ready, producerThunk, producerUpdate⟩, by
      simp [readValueProvenance?, valid]⟩

private theorem readCellViewFields?_metadata {captures : Bool} {tag : BitVec 64}
    {metadata : Option ValueProvenance} {fields : List TargetValue} {view : CellViewReadback}
    (read : readCellViewFields? captures tag metadata fields = some view) :
    view.valueProvenance = metadata := by
  unfold readCellViewFields? at read
  split at read
  · split at read
    · simp at read
    · obtain ⟨cache, _, read⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨captured, _, read⟩ := Option.bind_eq_some_iff.mp read
      cases Option.some.inj read
      rfl
  · simp at read

/-- Every successful extended view read retains the exact producer update and
role checked from its input words. This does not resolve a producer in a world. -/
theorem readCellViewWithProvenance?_metadata {captures : Bool}
    {tag role producerThunk producerUpdate : BitVec 64} {fields : List TargetValue}
    {view : CellViewReadback}
    (read : readCellViewWithProvenance? captures true
      (.record "NeedCellView" (.word tag :: .word role :: .word producerThunk ::
        .word producerUpdate :: fields)) = some view) :
    ∃ metadata, view.valueProvenance = some metadata ∧
      ValueProvenanceAdmissible tag role producerThunk producerUpdate ∧
      valueRoleCode metadata.role = role ∧ metadata.producerThunk = producerThunk ∧
      metadata.producerUpdate = producerUpdate := by
  change (readValueProvenance? tag role producerThunk producerUpdate).bind
    (fun metadata => readCellViewFields? captures tag (some metadata) fields) = some view at read
  obtain ⟨metadata, metadataRead, viewRead⟩ := Option.bind_eq_some_iff.mp read
  exact ⟨metadata, readCellViewFields?_metadata viewRead,
    readValueProvenance?_sound metadataRead⟩

theorem readCellView?_metadata_absent {captures : Bool} {tag : BitVec 64}
    {fields : List TargetValue} {view : CellViewReadback}
    (read : readCellView? captures (.record "NeedCellView" (.word tag :: fields)) = some view) :
    view.valueProvenance = none :=
  readCellViewFields?_metadata read

/-- Select an already earned ordinary payload for persistence. Explicit
suspensions keep their origin, and a completed cache without the returned-value
role is insufficient. The caller must obtain this view in the owning world;
this selector neither authenticates a capability nor runs its source. -/
def CellViewReadback.completedPayload? (view : CellViewReadback)
    (preserveDemand : Bool) (rights : BitVec 64) : Option Address :=
  if preserveDemand || decide (rights &&& (1 : BitVec 64) = 0) then none else
    match view.record.cache, view.valueProvenance with
    | .value payload, some metadata =>
        if metadata.role = .ready then some payload else none
    | _, _ => none

/-- Successful selection requires all three independent facts: a value cache,
the earned return role, and the force bit. Numerical cache completion alone
does not license this projection. -/
theorem CellViewReadback.completedPayload?_iff (view : CellViewReadback)
    (preserveDemand : Bool) (rights : BitVec 64) (payload : Address) :
    view.completedPayload? preserveDemand rights = some payload ↔
      preserveDemand = false ∧ rights &&& (1 : BitVec 64) ≠ 0 ∧
        view.record.cache = .value payload ∧
        ∃ metadata, view.valueProvenance = some metadata ∧ metadata.role = .ready := by
  cases view with
  | mk record authority evaluator storage imported occurrence argument captures provenance =>
    cases record with
    | mk origin cache =>
      cases preserveDemand <;> cases cache <;> cases provenance <;>
        simp [completedPayload?, eq_comm, and_comm]

theorem CellViewReadback.explicit_suspension_does_not_select_payload (view : CellViewReadback)
    (rights : BitVec 64) : view.completedPayload? true rights = none := by
  simp [completedPayload?]

theorem CellViewReadback.no_force_does_not_select (view : CellViewReadback)
    (preserveDemand : Bool) (rights : BitVec 64) (denied : rights &&& (1 : BitVec 64) = 0) :
    view.completedPayload? preserveDemand rights = none := by
  simp only [completedPayload?, denied, decide_true, Bool.or_true, ↓reduceIte]

theorem CellViewReadback.absent_role_does_not_select (view : CellViewReadback)
    (preserveDemand : Bool) (rights : BitVec 64)
    (absent : view.valueProvenance = none) :
    view.completedPayload? preserveDemand rights = none := by
  simp [completedPayload?, absent]

theorem CellViewReadback.demand_result_does_not_select (view : CellViewReadback)
    (preserveDemand : Bool) (rights : BitVec 64) (metadata : ValueProvenance)
    (present : view.valueProvenance = some metadata) (role : metadata.role = .demandResult) :
    view.completedPayload? preserveDemand rights = none := by
  cases cache : view.record.cache <;> simp [completedPayload?, cache, present, role]

theorem CellViewReadback.earned_payload_selected (view : CellViewReadback)
    (rights : BitVec 64) (payload : Address) (metadata : ValueProvenance)
    (allowed : rights &&& (1 : BitVec 64) ≠ 0) (cached : view.record.cache = .value payload)
    (present : view.valueProvenance = some metadata) (role : metadata.role = .ready) :
    view.completedPayload? false rights = some payload := by
  simp only [completedPayload?, allowed, decide_false, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, cached, present, role]

theorem readCacheFields_completed_iff {tag evaluator : BitVec 64}
    {cached : Option Address} {cache : NeedReference.Cache Address Address}
    (read : readCacheFields? tag evaluator cached = some cache) :
    NeedCacheLaws.Cache.Completed cache ↔ tag = 2 ∨ tag = 3 := by
  unfold readCacheFields? at read
  split at read
  · next zero =>
      split at read
      · cases Option.some.inj read
        constructor
        · intro completed; cases completed
        · intro completed; simp [zero] at completed
      · simp at read
  · next nonzero =>
      split at read
      · next evaluating =>
          split at read
          · cases Option.some.inj read
            constructor
            · intro completed; cases completed
            · intro completed; simp [evaluating] at completed
          · simp at read
      · next notEvaluating =>
          split at read
          · next value =>
              split at read
              · cases cached with
                | none => simp at read
                | some address =>
                    cases Option.some.inj read
                    exact ⟨fun _ => Or.inl value, fun _ => .value address⟩
              · simp at read
          · next notValue =>
              split at read
              · next fault =>
                  split at read
                  · cases cached with
                    | none => simp at read
                    | some address =>
                        cases Option.some.inj read
                        exact ⟨fun _ => Or.inr fault, fun _ => .stableFault address⟩
                  · simp at read
              · simp at read

/-- Source field transport and the admitted C function have the same checked
Need-view observation. The readback guard remains executable on both sides;
it does not become an assumed correspondence or payload ownership claim. -/
theorem view_invocation_readback_correspondence {World : Type}
    (captures heapIndex : Bool) (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (sourceMemory : SourceMemory) (state : TargetState World)
    (related : MemoryRelated sourceMemory state.memory) (source destination : Address)
    (sourceLive : ∃ value, targetRead state.memory source = some value)
    (destinationLive : ∃ value, targetRead state.memory destination = some value)
    (result : TargetRawResult World) (view : CellViewReadback) :
    (TargetFunctionBody (viewRepresentation captures heapIndex provenance).interface heap calls (viewFunction captures provenance)
      [.reference (some source), .reference (some destination)] state result ∧
      (targetRead result.state.memory destination).bind (readCellViewWithProvenance? captures provenance) = some view) ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
      ∃ original memory,
        sourceCopyFields source destination
          ((viewCopies captures provenance).map (fun field => (field.sourceIndex, field.destinationIndex)))
          sourceMemory = some original ∧
        MemoryRelated original memory ∧ result = ⟨.unit, { state with memory := memory }⟩ ∧
        ((sourceRead original destination).map encodeValue).bind (readCellViewWithProvenance? captures provenance) = some view := by
  rw [view_invocation_correspondence captures heapIndex heap calls sourceMemory state related
    source destination sourceLive destinationLive]
  constructor
  · rintro ⟨⟨fresh, original, memory, copied, afterRelated, resultEq⟩, read⟩
    refine ⟨fresh, original, memory, copied, afterRelated, resultEq, ?_⟩
    rw [resultEq] at read
    simpa only [memory_read_correspondence original memory afterRelated destination] using read
  · rintro ⟨fresh, original, memory, copied, afterRelated, resultEq, read⟩
    refine ⟨⟨fresh, original, memory, copied, afterRelated, resultEq⟩, ?_⟩
    rw [resultEq]
    simpa only [memory_read_correspondence original memory afterRelated destination] using read

/-! ## Complete immutable histories and producer worlds

History headers retain native session and update identity independently of
authority. A complete inventory supplies its expected depth; truncation cannot
be accepted as a smaller complete history. Source cell naming is supplied
explicitly and does not infer source allocation coordinates from native IDs.
-/

structure HistoryRow where
  session : BitVec 64
  serial : BitVec 64
  thunk : BitVec 64
  depth : BitVec 64
  cell : CellViewReadback
  deriving DecidableEq, Repr

def HistoryRow.key (row : HistoryRow) : BitVec 64 × BitVec 64 :=
  (row.session, row.thunk)

def historyFields : List Parameter :=
  [⟨"session_id", .word⟩, ⟨"serial", .word⟩, ⟨"thunk_id", .word⟩,
   ⟨"depth", .word⟩, ⟨"cell", .named "NeedCellView"⟩]

/-- The draft iterator emits the base nested shape. The extended shape models
complete frame data; the weights runtime currently exposes no history iterator. -/
def readHistoryRow? (captures provenance : Bool) : TargetValue → Option HistoryRow
  | .record "NeedHistoryView" [.word session, .word serial, .word thunk, .word depth, cell] =>
      (readCellViewWithProvenance? captures provenance cell).map
        (fun observed => ⟨session, serial, thunk, depth, observed⟩)
  | _ => none

theorem readHistoryRow?_headers {captures provenance : Bool}
    {session serial thunk depth : BitVec 64} {cell : TargetValue} {row : HistoryRow}
    (read : readHistoryRow? captures provenance
      (.record "NeedHistoryView" [.word session, .word serial, .word thunk, .word depth, cell]) =
      some row) :
    row.session = session ∧ row.serial = serial ∧ row.thunk = thunk ∧ row.depth = depth ∧
      readCellViewWithProvenance? captures provenance cell = some row.cell := by
  change (readCellViewWithProvenance? captures provenance cell).map
    (fun observed => ⟨session, serial, thunk, depth, observed⟩) = some row at read
  obtain ⟨observed, decoded, equal⟩ := Option.map_eq_some_iff.mp read
  cases equal
  exact ⟨rfl, rfl, rfl, rfl, decoded⟩

def HistoryHeadersValid (session : BitVec 64) (row : HistoryRow) : Prop :=
  row.session = session ∧ session ≠ 0 ∧ row.serial ≠ 0 ∧ row.thunk ≠ 0 ∧
    row.cell.authority ≠ 0

def checkHistoryHeaders (session : BitVec 64) (row : HistoryRow) : Bool :=
  row.session == session && session != 0 && row.serial != 0 && row.thunk != 0 &&
    row.cell.authority != 0

theorem checkHistoryHeaders_iff (session : BitVec 64) (row : HistoryRow) :
    checkHistoryHeaders session row = true ↔ HistoryHeadersValid session row := by
  simp [checkHistoryHeaders, HistoryHeadersValid, and_assoc]

def HistoryAligned (session : BitVec 64) : List HistoryRow → Prop
  | [] => True
  | row :: rest => HistoryHeadersValid session row ∧
      row.depth.toNat = (row :: rest).length ∧ HistoryAligned session rest

def checkHistoryAligned (session : BitVec 64) : List HistoryRow → Bool
  | [] => true
  | row :: rest => checkHistoryHeaders session row &&
      row.depth.toNat == (row :: rest).length && checkHistoryAligned session rest

theorem checkHistoryAligned_iff (session : BitVec 64) (rows : List HistoryRow) :
    checkHistoryAligned session rows = true ↔ HistoryAligned session rows := by
  induction rows with
  | nil => simp [checkHistoryAligned, HistoryAligned]
  | cons row rest ih =>
      simp [checkHistoryAligned, HistoryAligned, checkHistoryHeaders_iff, ih, and_assoc]

def HistoryInventoryValid (session : BitVec 64) (remaining : Nat)
    (rows : List HistoryRow) : Prop :=
  session ≠ 0 ∧ rows.length = remaining ∧ HistoryAligned session rows

def checkHistoryInventory (session : BitVec 64) (remaining : Nat)
    (rows : List HistoryRow) : Bool :=
  session != 0 && rows.length == remaining && checkHistoryAligned session rows

theorem checkHistoryInventory_iff (session : BitVec 64) (remaining : Nat)
    (rows : List HistoryRow) :
    checkHistoryInventory session remaining rows = true ↔
      HistoryInventoryValid session remaining rows := by
  simp [checkHistoryInventory, HistoryInventoryValid, checkHistoryAligned_iff, and_assoc]

/-- A qualified first occurrence, retaining all earlier and later updates. -/
def FirstHistoryMatch (rows : List HistoryRow) (key : BitVec 64 × BitVec 64)
    (row : HistoryRow) : Prop :=
  row.key = key ∧ ∃ earlierRows, (∃ suffix, rows = earlierRows ++ row :: suffix) ∧
    ∀ earlier ∈ earlierRows, earlier.key ≠ key

def latestHistory? (rows : List HistoryRow) (key : BitVec 64 × BitVec 64) :
    Option HistoryRow :=
  rows.find? (fun row => decide (row.key = key))

theorem latestHistory?_iff (rows : List HistoryRow) (key : BitVec 64 × BitVec 64)
    (row : HistoryRow) :
    latestHistory? rows key = some row ↔ FirstHistoryMatch rows key row := by
  simp [latestHistory?, FirstHistoryMatch, List.find?_eq_some_iff_append]

theorem latestHistory?_append (earlierRows suffix : List HistoryRow)
    (key : BitVec 64 × BitVec 64) :
    latestHistory? (earlierRows ++ suffix) key =
      (latestHistory? earlierRows key).or (latestHistory? suffix key) :=
  List.find?_append

theorem latestHistory?_prefix_retained {earlierRows suffix : List HistoryRow}
    {key : BitVec 64 × BitVec 64} {row : HistoryRow}
    (found : latestHistory? earlierRows key = some row) :
    latestHistory? (earlierRows ++ suffix) key = some row := by
  rw [latestHistory?_append, found]
  rfl

/-- Origin readback is executable and explicit; a borrowed pointer is not
itself a stable producer-content identity across suffix promotion. -/
def namedRecord? {Origin : Type*} (readOrigin : Address → Option Origin) (row : HistoryRow) :
    Option (NeedReference.CellRecord Origin Address Address) :=
  (readOrigin row.cell.record.origin).map (fun origin => ⟨origin, row.cell.record.cache⟩)

/-- Only the supplied naming assigns source allocation coordinates. -/
def namedHistory {Origin : Type*} (naming : (BitVec 64 × BitVec 64) → NeedReference.CellId)
    (readOrigin : Address → Option Origin) (rows : List HistoryRow) :
    Option (NeedReference.Heap.FullHistory Origin Address Address) :=
  rows.mapM (fun row => (namedRecord? readOrigin row).map (fun record => (naming row.key, record)))

theorem namedHistory_lookup {Origin : Type*}
    (naming : (BitVec 64 × BitVec 64) → NeedReference.CellId)
    (injective : Function.Injective naming) (readOrigin : Address → Option Origin)
    (rows : List HistoryRow) (records : NeedReference.Heap.FullHistory Origin Address Address)
    (decoded : namedHistory naming readOrigin rows = some records) (key : BitVec 64 × BitVec 64) :
    NeedReference.Heap.lookupFullHistory records (naming key) =
      (latestHistory? rows key).bind (namedRecord? readOrigin) := by
  induction rows generalizing records with
  | nil =>
      change some ([] : NeedReference.Heap.FullHistory Origin Address Address) = some records at decoded
      cases Option.some.inj decoded
      rfl
  | cons row rest ih =>
      rw [namedHistory, List.mapM_cons] at decoded
      change ((namedRecord? readOrigin row).map (fun record => (naming row.key, record))).bind
        (fun entry => (namedHistory naming readOrigin rest).bind
          (fun tail => some (entry :: tail))) = some records at decoded
      obtain ⟨entry, entryRead, tail, tailRead, equal⟩ := by
        simpa only [Option.bind_eq_some_iff] using decoded
      obtain ⟨record, recordRead, entryEq⟩ := Option.map_eq_some_iff.mp entryRead
      cases entryEq
      cases Option.some.inj equal
      by_cases same : row.key = key
      · simp [NeedReference.Heap.lookupFullHistory, latestHistory?, same, recordRead]
      · have distinct : naming key ≠ naming row.key := fun equal => same (injective equal).symm
        simp [NeedReference.Heap.lookupFullHistory, latestHistory?, same, distinct]
        exact ih tail tailRead

theorem readNamedHistory_lookup {Origin : Type*} [DecidableEq Origin]
    (naming : (BitVec 64 × BitVec 64) → NeedReference.CellId)
    (injective : Function.Injective naming) (readOrigin : Address → Option Origin)
    (rows : List HistoryRow) (records : NeedReference.Heap.FullHistory Origin Address Address)
    (recordsRead : namedHistory naming readOrigin rows = some records)
    (updates : List (NeedReference.HeapUpdate Origin Address Address))
    (decoded : NeedReference.Heap.readFullHistory records = some updates)
    (key : BitVec 64 × BitVec 64) :
    NeedReference.Heap.lookupSpine updates (naming key) =
      (latestHistory? rows key).bind (namedRecord? readOrigin) := by
  rw [← NeedReference.Heap.fullHistory?_lookup
    (NeedReference.Heap.fullHistory?_readFullHistory decoded)]
  exact namedHistory_lookup naming injective readOrigin rows records recordsRead key

def CacheIsValue (cache : NeedReference.Cache Address Address) : Prop :=
  ∃ value, cache = .value value

def checkCacheIsValue : NeedReference.Cache Address Address → Bool
  | .value _ => true
  | _ => false

theorem checkCacheIsValue_iff (cache : NeedReference.Cache Address Address) :
    checkCacheIsValue cache = true ↔ CacheIsValue cache := by
  cases cache <;> simp [checkCacheIsValue, CacheIsValue]

def ConsumerForwarding (consumer : HistoryRow) (metadata : ValueProvenance) : Prop :=
  CacheIsValue consumer.cell.record.cache ∧ consumer.cell.valueProvenance = some metadata ∧
    metadata.producerThunk ≠ 0 ∧ metadata.producerThunk ≠ consumer.thunk

def forwardingMetadata? (consumer : HistoryRow) : Option ValueProvenance :=
  match consumer.cell.record.cache, consumer.cell.valueProvenance with
  | .value _, some metadata =>
      if metadata.producerThunk ≠ 0 ∧ metadata.producerThunk ≠ consumer.thunk then
        some metadata else none
  | _, _ => none

theorem forwardingMetadata?_iff (consumer : HistoryRow) (metadata : ValueProvenance) :
    forwardingMetadata? consumer = some metadata ↔ ConsumerForwarding consumer metadata := by
  unfold forwardingMetadata? ConsumerForwarding
  cases cache : consumer.cell.record.cache <;>
    cases provenance : consumer.cell.valueProvenance <;>
    simp [CacheIsValue]
  constructor
  · rintro ⟨guards, rfl⟩
    exact ⟨rfl, guards⟩
  · rintro ⟨rfl, guards⟩
    exact ⟨guards, rfl⟩

def ProducerValid (rows : List HistoryRow) (consumer producer : HistoryRow) : Prop :=
  ∃ metadata, ConsumerForwarding consumer metadata ∧
    FirstHistoryMatch rows (consumer.session, metadata.producerThunk) producer ∧
    CacheIsValue producer.cell.record.cache ∧ producer.serial = metadata.producerUpdate ∧
    producer.serial.toNat < consumer.serial.toNat

def checkProducerRow? (rows : List HistoryRow) (consumer : HistoryRow) : Option HistoryRow := do
  let metadata ← forwardingMetadata? consumer
  let producer ← latestHistory? rows (consumer.session, metadata.producerThunk)
  if checkCacheIsValue producer.cell.record.cache && producer.serial == metadata.producerUpdate &&
      decide (producer.serial.toNat < consumer.serial.toNat) then some producer else none

theorem checkProducerRow?_iff (rows : List HistoryRow) (consumer producer : HistoryRow) :
    checkProducerRow? rows consumer = some producer ↔ ProducerValid rows consumer producer := by
  unfold checkProducerRow?
  change ((forwardingMetadata? consumer).bind fun metadata =>
    (latestHistory? rows (consumer.session, metadata.producerThunk)).bind fun observed =>
      if checkCacheIsValue observed.cell.record.cache &&
          observed.serial == metadata.producerUpdate &&
          decide (observed.serial.toNat < consumer.serial.toNat) then some observed else none) =
      some producer ↔ ProducerValid rows consumer producer
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨metadata, metadataRead, bound⟩
    obtain ⟨observed, producerRead, checked⟩ := Option.bind_eq_some_iff.mp bound
    split at checked
    · next valid =>
      have fields : CacheIsValue observed.cell.record.cache ∧
          observed.serial = metadata.producerUpdate ∧
          observed.serial.toNat < consumer.serial.toNat := by
        simpa [checkCacheIsValue_iff, and_assoc] using valid
      cases Option.some.inj checked
      exact ⟨metadata, (forwardingMetadata?_iff _ _).mp metadataRead,
        (latestHistory?_iff _ _ _).mp producerRead, fields⟩
    · simp at checked
  · rintro ⟨metadata, consumerValid, producerFound, value, serial, earlier⟩
    refine ⟨metadata, (forwardingMetadata?_iff _ _).mpr consumerValid, ?_⟩
    apply Option.bind_eq_some_iff.mpr
    refine ⟨producer, (latestHistory?_iff _ _ _).mpr producerFound, ?_⟩
    have valueCheck := (checkCacheIsValue_iff _).mpr value
    have earlierUpdate : metadata.producerUpdate.toNat < consumer.serial.toNat := by
      simpa only [serial] using earlier
    simp [valueCheck, serial, earlierUpdate]

def forwardedValueSource? (rows : List HistoryRow) (key : BitVec 64 × BitVec 64) :
    Option HistoryRow :=
  (latestHistory? rows key).bind (checkProducerRow? rows)

theorem forwardedValueSource?_iff (rows : List HistoryRow) (key : BitVec 64 × BitVec 64)
    (producer : HistoryRow) :
    forwardedValueSource? rows key = some producer ↔
      ∃ consumer, FirstHistoryMatch rows key consumer ∧ ProducerValid rows consumer producer := by
  simp only [forwardedValueSource?, Option.bind_eq_some_iff, latestHistory?_iff,
    checkProducerRow?_iff]

theorem ProducerValid_same_session {rows : List HistoryRow} {consumer producer : HistoryRow}
    (valid : ProducerValid rows consumer producer) : producer.session = consumer.session := by
  obtain ⟨metadata, _, found, _⟩ := valid
  exact congrArg Prod.fst found.1

theorem ProducerValid_exact_update {rows : List HistoryRow} {consumer producer : HistoryRow}
    (valid : ProducerValid rows consumer producer) :
    ∃ metadata, consumer.cell.valueProvenance = some metadata ∧
      producer.thunk = metadata.producerThunk ∧ producer.serial = metadata.producerUpdate ∧
      producer.serial.toNat < consumer.serial.toNat := by
  obtain ⟨metadata, consumerValid, found, _, serial, earlier⟩ := valid
  exact ⟨metadata, consumerValid.2.1, congrArg Prod.snd found.1, serial, earlier⟩

/-- The unchanged final guard fragment of the weights runtime's forwarded
source helper. Its surrounding lookup calls and declarations remain separate. -/
def producerGuardSource : List Char :=
  "producer.cache_state != PRIME_NEED_CACHE_VALUE ||\n        producer_update->serial != consumer.value_producer_update ||\n        producer_update->serial >= consumer_update->serial".toList

def producerGuardParsed : NativeC.CExpr :=
  .binary .or
    (.binary .or
      (.binary .ne (.field (.identifier "producer".toList) "cache_state".toList false)
        (.identifier "PRIME_NEED_CACHE_VALUE".toList))
      (.binary .ne (.field (.identifier "producer_update".toList) "serial".toList true)
        (.field (.identifier "consumer".toList) "value_producer_update".toList false)))
    (.binary .ge (.field (.identifier "producer_update".toList) "serial".toList true)
      (.field (.identifier "consumer_update".toList) "serial".toList true))

def producerGuardBindings : NativeC.PrimitiveBindings :=
  [("producer".toList, .temporary 1 (.named "NeedCellView")),
   ("consumer".toList, .temporary 2 (.named "NeedCellView")),
   ("producer_update".toList, .temporary 3 (.ref (.named "NeedFrame"))),
   ("consumer_update".toList, .temporary 4 (.ref (.named "NeedFrame")))] ++ cacheConstants

def producerGuardCode : List Instruction :=
  [.temporary 5 .word (.fieldValue (.temporary 1 (.named "NeedCellView")) "NeedCellView" 0),
   .temporary 6 .bool (.binary (.compare .ne) (.temporary 5 .word) (.word 2)),
   .temporary 7 .bool (.copy (.temporary 6 .bool)),
   .branch (.negated (.temporary 7 .bool))
     [.temporary 8 (.ref .word) (.fieldAddress (.temporary 3 (.ref (.named "NeedFrame"))) "NeedFrame" 10),
      .temporary 9 .word (.indirectRead (.temporary 8 (.ref .word))),
      .temporary 10 .word (.fieldValue (.temporary 2 (.named "NeedCellView")) "NeedCellView" 3),
      .temporary 11 .bool (.binary (.compare .ne) (.temporary 9 .word) (.temporary 10 .word)),
      .assign (.temporary 7 .bool) (.temporary 11 .bool)] [],
   .temporary 12 .bool (.copy (.temporary 7 .bool)),
   .branch (.negated (.temporary 12 .bool))
     [.temporary 13 (.ref .word) (.fieldAddress (.temporary 3 (.ref (.named "NeedFrame"))) "NeedFrame" 10),
      .temporary 14 .word (.indirectRead (.temporary 13 (.ref .word))),
      .temporary 15 (.ref .word) (.fieldAddress (.temporary 4 (.ref (.named "NeedFrame"))) "NeedFrame" 10),
      .temporary 16 .word (.indirectRead (.temporary 15 (.ref .word))),
      .temporary 17 .bool (.binary (.compare .ge) (.temporary 14 .word) (.temporary 16 .word)),
      .assign (.temporary 12 .bool) (.temporary 17 .bool)] []]

theorem producer_guard_source_parsed :
    NativeC.expressionText? [] producerGuardSource = some producerGuardParsed := by cbv

theorem producer_guard_lowered (captures heapIndex : Bool) :
    NativeC.primitiveExpression? producerGuardBindings 100 producerGuardParsed ⟨4⟩ []
      (viewRepresentation captures heapIndex true) =
      some ⟨producerGuardCode, .temporary 12 .bool, ⟨17⟩⟩ := by
  cases captures <;> cases heapIndex <;> rfl

def producerGuardRejects (tag producerSerial selectedUpdate consumerSerial : BitVec 64) : Bool :=
  tag != 2 || producerSerial != selectedUpdate || decide (producerSerial.toNat ≥ consumerSerial.toNat)

private def producerGuardFirstCode : List Instruction :=
  fieldReadCode (.temporary 3 (.ref (.named "NeedFrame"))) "NeedFrame" 10 8 .word ++
    [.temporary 10 .word (.fieldValue (.temporary 2 (.named "NeedCellView")) "NeedCellView" 3),
     .temporary 11 .bool (.binary (.compare .ne) (.temporary 9 .word) (.temporary 10 .word))]

private def producerGuardFirstFrame (frame : TargetFrame) (address : Address)
    (serial selected : BitVec 64) : TargetFrame :=
  targetDeclareTemporary
    (targetDeclareTemporary (fieldReadFrame frame address 10 8 (.word serial)) 10 (.word selected))
    11 (.bool (serial != selected))

private theorem producer_guard_first_protects (frame : TargetFrame) (address : Address)
    (serial selected : BitVec 64) :
    TemporaryProtection 7 frame (producerGuardFirstFrame frame address serial selected) :=
  temporary_protection_trans (field_read_frame_protects frame (by decide : 7 < 8) address 10 _)
    (temporary_protection_trans (declare_temporary_protects _ _ (by decide : 7 < 10))
      (declare_temporary_protects _ _ (by decide : 7 < 11)))

private theorem producer_guard_first_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {address : Address}
    {fields : List TargetValue} {serial selected : BitVec 64}
    (bounded : TemporaryNamesBound frame 7)
    (pointer : TargetAtomEval interface frame state (.temporary 3 (.ref (.named "NeedFrame")))
      (.reference (some address)))
    (consumer : TargetAtomEval interface frame state (.temporary 2 (.named "NeedCellView"))
      (.record "NeedCellView" fields))
    (field : fields[3]? = some (.word selected))
    (loaded : targetRead state.memory (sourceFieldAddress address 10) = some (.word serial))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root producerGuardFirstCode frame state out ↔
      out = ⟨.normal, producerGuardFirstFrame frame address serial selected, state⟩ := by
  let middle := fieldReadFrame frame address 10 8 (.word serial)
  let saved := targetDeclareTemporary middle 10 (.word selected)
  have middleBound := field_read_frame_bound bounded (by decide : 7 < 8) address 10 (.word serial)
  have kept := field_read_frame_protects frame (by decide : 7 < 8) address 10 (.word serial)
  have consumerRead := (protection_atom_evaluation kept (.temporary 2 (.named "NeedCellView"))
    (by decide : 2 ≤ 7) state state _).mp consumer
  have selectedEval : TargetPureEval interface middle state
      (.fieldValue (.temporary 2 (.named "NeedCellView")) "NeedCellView" 3) (.word selected) :=
    .fieldValue consumerRead field
  have serialRead : TargetAtomEval interface middle state (.temporary 9 .word) (.word serial) :=
    declared_temporary_atom interface _ state 9 _ _
  have serialSaved := (protection_atom_evaluation
    (declare_temporary_protects middle (.word selected) (by decide : 9 < 10))
    (.temporary 9 .word) (Nat.le_refl _) state state _).mp serialRead
  have selectedSaved : TargetAtomEval interface saved state (.temporary 10 .word) (.word selected) :=
    declared_temporary_atom interface middle state 10 _ _
  have compared : TargetPureEval interface saved state
      (.binary (.compare .ne) (.temporary 9 .word) (.temporary 10 .word))
      (.bool (serial != selected)) := .binary serialSaved selectedSaved rfl
  unfold producerGuardFirstCode
  rw [target_normal_prefix_then_exact
    (by simp [fieldReadCode, jumpFreeCode, jumpFreeInstruction])
    (field_read_code_exact pointer bounded (by decide : 7 < 8) loaded "NeedFrame" root)]
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (temporary_bound_fresh middleBound (by decide : 9 < 10)) selectedEval)]
  exact target_run_temporary_exact
    (temporary_bound_fresh (declared_temporary_bound middleBound
      (by decide : 9 ≤ 10) (Nat.le_refl _) (.word selected)) (by decide : 10 < 11))
    compared root out

private def producerGuardSecondCode : List Instruction :=
  fieldReadCode (.temporary 3 (.ref (.named "NeedFrame"))) "NeedFrame" 10 13 .word ++
    fieldReadCode (.temporary 4 (.ref (.named "NeedFrame"))) "NeedFrame" 10 15 .word ++
    [.temporary 17 .bool (.binary (.compare .ge) (.temporary 14 .word) (.temporary 16 .word))]

private def producerGuardSecondFrame (frame : TargetFrame) (producer consumer : Address)
    (producerSerial consumerSerial : BitVec 64) : TargetFrame :=
  targetDeclareTemporary
    (fieldReadFrame (fieldReadFrame frame producer 10 13 (.word producerSerial))
      consumer 10 15 (.word consumerSerial)) 17
    (.bool (decide (producerSerial.toNat ≥ consumerSerial.toNat)))

private theorem producer_guard_second_protects (frame : TargetFrame) (producer consumer : Address)
    (producerSerial consumerSerial : BitVec 64) :
    TemporaryProtection 12 frame (producerGuardSecondFrame frame producer consumer producerSerial consumerSerial) :=
  temporary_protection_trans (field_read_frame_protects frame (by decide : 12 < 13) producer 10 _)
    (temporary_protection_trans (field_read_frame_protects _ (by decide : 12 < 15) consumer 10 _)
      (declare_temporary_protects _ _ (by decide : 12 < 17)))

private theorem producer_guard_second_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {producer consumer : Address}
    {producerSerial consumerSerial : BitVec 64}
    (bounded : TemporaryNamesBound frame 12)
    (producerRead : TargetAtomEval interface frame state (.temporary 3 (.ref (.named "NeedFrame")))
      (.reference (some producer)))
    (consumerRead : TargetAtomEval interface frame state (.temporary 4 (.ref (.named "NeedFrame")))
      (.reference (some consumer)))
    (producerLoaded : targetRead state.memory (sourceFieldAddress producer 10) = some (.word producerSerial))
    (consumerLoaded : targetRead state.memory (sourceFieldAddress consumer 10) = some (.word consumerSerial))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root producerGuardSecondCode frame state out ↔
      out = ⟨.normal, producerGuardSecondFrame frame producer consumer producerSerial consumerSerial, state⟩ := by
  let first := fieldReadFrame frame producer 10 13 (.word producerSerial)
  let second := fieldReadFrame first consumer 10 15 (.word consumerSerial)
  have firstBound := field_read_frame_bound bounded (by decide : 12 < 13) producer 10 (.word producerSerial)
  have firstProtection := field_read_frame_protects frame (by decide : 12 < 13) producer 10 (.word producerSerial)
  have consumerPointer := (protection_atom_evaluation firstProtection
    (.temporary 4 (.ref (.named "NeedFrame"))) (by decide : 4 ≤ 12) state state _).mp consumerRead
  have secondBound := field_read_frame_bound firstBound (by decide : 14 < 15) consumer 10 (.word consumerSerial)
  have producerValue : TargetAtomEval interface first state (.temporary 14 .word) (.word producerSerial) :=
    declared_temporary_atom interface _ state 14 _ _
  have producerValueKept := (protection_atom_evaluation
    (field_read_frame_protects first (by decide : 14 < 15) consumer 10 (.word consumerSerial))
    (.temporary 14 .word) (Nat.le_refl _) state state _).mp producerValue
  have consumerValue : TargetAtomEval interface second state (.temporary 16 .word) (.word consumerSerial) :=
    declared_temporary_atom interface _ state 16 _ _
  have compared : TargetPureEval interface second state
      (.binary (.compare .ge) (.temporary 14 .word) (.temporary 16 .word))
      (.bool (decide (producerSerial.toNat ≥ consumerSerial.toNat))) :=
    .binary producerValueKept consumerValue rfl
  unfold producerGuardSecondCode
  rw [List.append_assoc, target_normal_prefix_then_exact
    (by simp [fieldReadCode, jumpFreeCode, jumpFreeInstruction])
    (field_read_code_exact producerRead bounded (by decide : 12 < 13) producerLoaded "NeedFrame" root)]
  rw [target_normal_prefix_then_exact
    (by simp [fieldReadCode, jumpFreeCode, jumpFreeInstruction])
    (field_read_code_exact consumerPointer firstBound (by decide : 14 < 15) consumerLoaded "NeedFrame" root)]
  exact target_run_temporary_exact (temporary_bound_fresh secondBound (by decide : 16 < 17)) compared root out

/-- The guard's normal post-frame closes both private right-operand scopes.
Its construction does not read memory or change the caller state. -/
def producerGuardFrame {World : Type} (frame : TargetFrame) (state : TargetState World)
    (producer consumer : Address) (tag producerSerial selectedUpdate consumerSerial : BitVec 64) : TargetFrame :=
  let compared := targetDeclareTemporary (targetDeclareTemporary frame 5 (.word tag)) 6 (.bool (tag != 2))
  let marker7 := targetDeclareTemporary compared 7 (.bool (tag != 2))
  let closed7 := shortCircuitFrame false marker7
    (producerGuardFirstFrame marker7 producer producerSerial selectedUpdate) state 7
    (tag != 2) (producerSerial != selectedUpdate)
  let marker12 := targetDeclareTemporary closed7 12 (.bool ((tag != 2) || (producerSerial != selectedUpdate)))
  shortCircuitFrame false marker12
    (producerGuardSecondFrame marker12 producer consumer producerSerial consumerSerial) state 12
    ((tag != 2) || (producerSerial != selectedUpdate))
    (decide (producerSerial.toNat ≥ consumerSerial.toNat))

theorem producer_guard_frame_read {World : Type} (captures heapIndex : Bool)
    (frame : TargetFrame) (state : TargetState World) (producer consumer : Address)
    (tag producerSerial selectedUpdate consumerSerial : BitVec 64) :
    TargetAtomEval (viewRepresentation captures heapIndex true).interface
      (producerGuardFrame frame state producer consumer tag producerSerial selectedUpdate consumerSerial)
      state (.temporary 12 .bool)
      (.bool (producerGuardRejects tag producerSerial selectedUpdate consumerSerial)) := by
  unfold producerGuardFrame
  apply short_circuit_frame_read false
  · exact declared_temporary_atom _ _ state 12 _ _
  · simp [producerGuardSecondFrame, fieldReadFrame, targetDeclareTemporary]
  · rfl

/-- Exact execution of the admitted expression fragment. The two serial reads
are required only on their selected short-circuit paths. This does not assert
that the enclosing native lookup produced the supplied records or addresses. -/
theorem producer_guard_execution_exact {World : Type} {captures heapIndex : Bool}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {producer consumer : Address}
    {producerFields consumerFields : List TargetValue}
    {tag producerSerial selectedUpdate consumerSerial : BitVec 64}
    (bounded : TemporaryNamesBound frame 4) (hscope : TemporariesScoped frame)
    (producerView : TargetAtomEval (viewRepresentation captures heapIndex true).interface frame state
      (.temporary 1 (.named "NeedCellView")) (.record "NeedCellView" (.word tag :: producerFields)))
    (consumerView : TargetAtomEval (viewRepresentation captures heapIndex true).interface frame state
      (.temporary 2 (.named "NeedCellView")) (.record "NeedCellView" consumerFields))
    (selectedField : consumerFields[3]? = some (.word selectedUpdate))
    (producerRead : TargetAtomEval (viewRepresentation captures heapIndex true).interface frame state
      (.temporary 3 (.ref (.named "NeedFrame"))) (.reference (some producer)))
    (consumerRead : TargetAtomEval (viewRepresentation captures heapIndex true).interface frame state
      (.temporary 4 (.ref (.named "NeedFrame"))) (.reference (some consumer)))
    (producerLoaded : tag = 2 →
      targetRead state.memory (sourceFieldAddress producer 10) = some (.word producerSerial))
    (consumerLoaded : tag = 2 → producerSerial = selectedUpdate →
      targetRead state.memory (sourceFieldAddress consumer 10) = some (.word consumerSerial))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (viewRepresentation captures heapIndex true).interface heap calls .bool root
      producerGuardCode frame state out ↔
      out = ⟨.normal,
        producerGuardFrame frame state producer consumer tag producerSerial selectedUpdate consumerSerial,
        state⟩ := by
  let iface := (viewRepresentation captures heapIndex true).interface
  let saved := targetDeclareTemporary frame 5 (.word tag)
  let compared := targetDeclareTemporary saved 6 (.bool (tag != 2))
  let marker7 := targetDeclareTemporary compared 7 (.bool (tag != 2))
  let current7 := producerGuardFirstFrame marker7 producer producerSerial selectedUpdate
  let closed7 := shortCircuitFrame false marker7 current7 state 7 (tag != 2) (producerSerial != selectedUpdate)
  let marker12 := targetDeclareTemporary closed7 12 (.bool ((tag != 2) || (producerSerial != selectedUpdate)))
  let current12 := producerGuardSecondFrame marker12 producer consumer producerSerial consumerSerial
  have savedBound : TemporaryNamesBound saved 5 :=
    declared_temporary_bound bounded (by decide : 4 ≤ 5) (Nat.le_refl _) _
  have comparedBound : TemporaryNamesBound compared 6 :=
    declared_temporary_bound savedBound (by decide : 5 ≤ 6) (Nat.le_refl _) _
  have comparedScope := declared_temporaries_completeNames
    (declared_temporaries_completeNames hscope 5 (.word tag)) 6 (.bool (tag != 2))
  have markerBound : TemporaryNamesBound marker7 7 :=
    declared_temporary_bound comparedBound (by decide : 6 ≤ 7) (Nat.le_refl _) _
  have markerScope := declared_temporaries_completeNames comparedScope 7 (.bool (tag != 2))
  have markerProtection : TemporaryProtection 4 frame marker7 :=
    temporary_protection_trans (declare_temporary_protects frame _ (by decide : 4 < 5))
      (temporary_protection_trans (declare_temporary_protects saved _ (by decide : 4 < 6))
        (declare_temporary_protects compared _ (by decide : 4 < 7)))
  have producer7 := (protection_atom_evaluation markerProtection
    (.temporary 3 (.ref (.named "NeedFrame"))) (by decide : 3 ≤ 4) state state _).mp producerRead
  have consumer7 := (protection_atom_evaluation markerProtection
    (.temporary 2 (.named "NeedCellView")) (by decide : 2 ≤ 4) state state _).mp consumerView
  have condition7 : TargetAtomEval iface marker7 state (.temporary 7 .bool) (.bool (tag != 2)) :=
    declared_temporary_atom iface compared state 7 _ _
  have firstProtection := producer_guard_first_protects marker7 producer producerSerial selectedUpdate
  have live7 : current7.temporaryNames.contains 7 = true :=
    (firstProtection.names 7 (Nat.le_refl _)).trans (by simp [marker7, targetDeclareTemporary])
  have result7 : TargetAtomEval iface current7 state (.temporary 11 .bool)
      (.bool (producerSerial != selectedUpdate)) := declared_temporary_atom iface _ state 11 _ _
  have arm7 := short_circuit_rhs_exact false (heap := heap) (calls := calls)
    markerScope condition7 (by simp [producerGuardFirstCode, fieldReadCode, jumpFreeCode, jumpFreeInstruction])
    (fun selected => producer_guard_first_exact markerBound producer7 consumer7 selectedField
      (producerLoaded (by simpa using selected))) result7 live7 rfl
  simp only [shortCircuitCondition, Bool.false_eq_true, if_false, producerGuardFirstCode,
    fieldReadCode, List.cons_append, List.nil_append] at arm7
  have closedBound : TemporaryNamesBound closed7 7 :=
    short_circuit_frame_bound false markerBound state 7 _ _
  have closedScope : TemporariesScoped closed7 :=
    short_circuit_frame_scoped false markerScope state 7 _ _
  have closedProtection : TemporaryProtection 4 frame closed7 :=
    temporary_protection_trans markerProtection
      (short_circuit_frame_protects false markerScope
        (temporary_protection_weaken (by decide : 4 ≤ 7) firstProtection)
        (by decide : 4 < 7) state _ _)
  have closedRead : TargetAtomEval iface closed7 state (.temporary 7 .bool)
      (.bool ((tag != 2) || (producerSerial != selectedUpdate))) :=
    short_circuit_frame_read false condition7 live7 rfl
  have marker12Bound : TemporaryNamesBound marker12 12 :=
    declared_temporary_bound closedBound (by decide : 7 ≤ 12) (Nat.le_refl _) _
  have marker12Scope := declared_temporaries_completeNames closedScope 12
    (.bool ((tag != 2) || (producerSerial != selectedUpdate)))
  have marker12Protection : TemporaryProtection 4 frame marker12 :=
    temporary_protection_trans closedProtection (declare_temporary_protects closed7 _ (by decide : 4 < 12))
  have producer12 := (protection_atom_evaluation marker12Protection
    (.temporary 3 (.ref (.named "NeedFrame"))) (by decide : 3 ≤ 4) state state _).mp producerRead
  have consumer12 := (protection_atom_evaluation marker12Protection
    (.temporary 4 (.ref (.named "NeedFrame"))) (Nat.le_refl _) state state _).mp consumerRead
  have condition12 : TargetAtomEval iface marker12 state (.temporary 12 .bool)
      (.bool ((tag != 2) || (producerSerial != selectedUpdate))) :=
    declared_temporary_atom iface closed7 state 12 _ _
  have secondProtection := producer_guard_second_protects marker12 producer consumer producerSerial consumerSerial
  have live12 : current12.temporaryNames.contains 12 = true :=
    (secondProtection.names 12 (Nat.le_refl _)).trans (by simp [marker12, targetDeclareTemporary])
  have result12 : TargetAtomEval iface current12 state (.temporary 17 .bool)
      (.bool (decide (producerSerial.toNat ≥ consumerSerial.toNat))) :=
    declared_temporary_atom iface _ state 17 _ _
  have arm12 := short_circuit_rhs_exact false (heap := heap) (calls := calls)
    marker12Scope condition12 (by simp [producerGuardSecondCode, fieldReadCode, jumpFreeCode, jumpFreeInstruction])
    (fun selected => producer_guard_second_exact marker12Bound producer12 consumer12
      (producerLoaded (by simpa using (Bool.or_eq_false_iff.mp selected).1))
      (consumerLoaded (by simpa using (Bool.or_eq_false_iff.mp selected).1)
        (by simpa using (Bool.or_eq_false_iff.mp selected).2))) result12 live12 rfl
  simp only [shortCircuitCondition, Bool.false_eq_true, if_false, producerGuardSecondCode,
    fieldReadCode, List.cons_append, List.nil_append] at arm12
  have tagEval : TargetPureEval iface frame state
      (.fieldValue (.temporary 1 (.named "NeedCellView")) "NeedCellView" 0) (.word tag) :=
    .fieldValue producerView rfl
  have tagRead : TargetAtomEval iface saved state (.temporary 5 .word) (.word tag) :=
    declared_temporary_atom iface frame state 5 _ _
  have comparisonEval : TargetPureEval iface saved state
      (.binary (.compare .ne) (.temporary 5 .word) (.word 2)) (.bool (tag != 2)) :=
    .binary tagRead (.word 2) rfl
  have comparisonRead : TargetAtomEval iface compared state (.temporary 6 .bool) (.bool (tag != 2)) :=
    declared_temporary_atom iface saved state 6 _ _
  unfold producerGuardCode
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (temporary_bound_fresh bounded (by decide : 4 < 5)) tagEval)]
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (temporary_bound_fresh savedBound (by decide : 5 < 6)) comparisonEval)]
  rw [target_short_circuit_copy_exact (temporary_bound_fresh comparedBound (by decide : 6 < 7)) comparisonRead]
  rw [target_normal_then_exact arm7]
  rw [target_short_circuit_copy_exact (temporary_bound_fresh closedBound (by decide : 7 < 12)) closedRead]
  rw [target_normal_then_exact arm12]
  exact target_run_empty_exact root _ state out

theorem producer_guard_frame_protects {World : Type} {frame : TargetFrame}
    (hscope : TemporariesScoped frame) (state : TargetState World) (producer consumer : Address)
    (tag producerSerial selectedUpdate consumerSerial : BitVec 64) :
    TemporaryProtection 4 frame
      (producerGuardFrame frame state producer consumer tag producerSerial selectedUpdate consumerSerial) := by
  let saved := targetDeclareTemporary frame 5 (.word tag)
  let compared := targetDeclareTemporary saved 6 (.bool (tag != 2))
  let marker7 := targetDeclareTemporary compared 7 (.bool (tag != 2))
  let current7 := producerGuardFirstFrame marker7 producer producerSerial selectedUpdate
  let closed7 := shortCircuitFrame false marker7 current7 state 7 (tag != 2) (producerSerial != selectedUpdate)
  let marker12 := targetDeclareTemporary closed7 12 (.bool ((tag != 2) || (producerSerial != selectedUpdate)))
  have markerScope : TemporariesScoped marker7 :=
    declared_temporaries_completeNames (declared_temporaries_completeNames
      (declared_temporaries_completeNames hscope 5 (.word tag)) 6 (.bool (tag != 2))) 7 _
  have markerProtection : TemporaryProtection 4 frame marker7 :=
    temporary_protection_trans (declare_temporary_protects frame _ (by decide : 4 < 5))
      (temporary_protection_trans (declare_temporary_protects saved _ (by decide : 4 < 6))
        (declare_temporary_protects compared _ (by decide : 4 < 7)))
  have closedProtection : TemporaryProtection 4 frame closed7 :=
    temporary_protection_trans markerProtection
      (short_circuit_frame_protects false markerScope
        (temporary_protection_weaken (by decide : 4 ≤ 7)
          (producer_guard_first_protects marker7 producer producerSerial selectedUpdate))
        (by decide : 4 < 7) state _ _)
  have closedScope : TemporariesScoped closed7 :=
    short_circuit_frame_scoped false markerScope state 7 _ _
  have marker12Scope : TemporariesScoped marker12 :=
    declared_temporaries_completeNames closedScope 12 _
  exact temporary_protection_trans
    (temporary_protection_trans closedProtection (declare_temporary_protects closed7 _ (by decide : 4 < 12)))
    (short_circuit_frame_protects false marker12Scope
      (temporary_protection_weaken (by decide : 4 ≤ 12)
        (producer_guard_second_protects marker12 producer consumer producerSerial consumerSerial))
      (by decide : 4 < 12) state _ _)

theorem producer_guard_acceptance (tag producerSerial selectedUpdate consumerSerial : BitVec 64) :
    producerGuardRejects tag producerSerial selectedUpdate consumerSerial = false ↔
      tag = 2 ∧ producerSerial = selectedUpdate ∧ producerSerial.toNat < consumerSerial.toNat := by
  simp [producerGuardRejects, Bool.or_eq_false_iff, and_assoc]

def cacheTagOf : NeedReference.Cache Address Address → BitVec 64
  | .suspended => 0
  | .evaluating _ => 1
  | .value _ => 2
  | .stableFault _ => 3

theorem cacheTagOf_value_iff (cache : NeedReference.Cache Address Address) :
    cacheTagOf cache = 2 ↔ CacheIsValue cache := by
  cases cache <;> simp [cacheTagOf, CacheIsValue]

theorem ProducerValid_guard_iff (rows : List HistoryRow) (consumer producer : HistoryRow) :
    ProducerValid rows consumer producer ↔ ∃ metadata,
      ConsumerForwarding consumer metadata ∧
      FirstHistoryMatch rows (consumer.session, metadata.producerThunk) producer ∧
      producerGuardRejects (cacheTagOf producer.cell.record.cache) producer.serial
        metadata.producerUpdate consumer.serial = false := by
  simp only [ProducerValid, producer_guard_acceptance, cacheTagOf_value_iff]

def HistoryMetadataValid (row : HistoryRow) : Prop :=
  match row.cell.valueProvenance with
  | none => True
  | some metadata =>
      ValueProvenanceAdmissible (cacheTagOf row.cell.record.cache)
        (valueRoleCode metadata.role) metadata.producerThunk metadata.producerUpdate ∧
      (metadata.producerThunk ≠ 0 → metadata.producerThunk ≠ row.thunk)

def checkHistoryMetadata (row : HistoryRow) : Bool :=
  match row.cell.valueProvenance with
  | none => true
  | some metadata =>
      (readValueProvenance? (cacheTagOf row.cell.record.cache)
        (valueRoleCode metadata.role) metadata.producerThunk metadata.producerUpdate).isSome &&
      (metadata.producerThunk == 0 || metadata.producerThunk != row.thunk)

theorem checkHistoryMetadata_iff (row : HistoryRow) :
    checkHistoryMetadata row = true ↔ HistoryMetadataValid row := by
  cases metadata : row.cell.valueProvenance with
  | none => simp [checkHistoryMetadata, HistoryMetadataValid, metadata]
  | some observed =>
      simp [checkHistoryMetadata, HistoryMetadataValid, metadata,
        Option.isSome_iff_exists, readValueProvenance?_exists_iff]
      tauto

/-- Historical forwarding is checked in the strictly older suffix available
when that consumer update was recorded, not against a later producer update. -/
def HistoryProducerRowValid (older : List HistoryRow) (row : HistoryRow) : Prop :=
  HistoryMetadataValid row ∧ ∀ metadata, row.cell.valueProvenance = some metadata →
    metadata.producerThunk ≠ 0 → ∃ producer, ProducerValid older row producer

def checkHistoryProducerRow (older : List HistoryRow) (row : HistoryRow) : Bool :=
  checkHistoryMetadata row && match row.cell.valueProvenance with
    | none => true
    | some metadata => metadata.producerThunk == 0 || (checkProducerRow? older row).isSome

theorem checkHistoryProducerRow_iff (older : List HistoryRow) (row : HistoryRow) :
    checkHistoryProducerRow older row = true ↔ HistoryProducerRowValid older row := by
  cases metadata : row.cell.valueProvenance with
  | none => simp [checkHistoryProducerRow, HistoryProducerRowValid, metadata,
      checkHistoryMetadata_iff]
  | some observed =>
      simp [checkHistoryProducerRow, HistoryProducerRowValid, metadata,
        checkHistoryMetadata_iff, Option.isSome_iff_exists, checkProducerRow?_iff]
      tauto

def HistoryProducersValid : List HistoryRow → Prop
  | [] => True
  | row :: older => HistoryProducerRowValid older row ∧ HistoryProducersValid older

def checkHistoryProducers : List HistoryRow → Bool
  | [] => true
  | row :: older => checkHistoryProducerRow older row && checkHistoryProducers older

theorem checkHistoryProducers_iff (rows : List HistoryRow) :
    checkHistoryProducers rows = true ↔ HistoryProducersValid rows := by
  induction rows with
  | nil => simp [checkHistoryProducers, HistoryProducersValid]
  | cons row older ih =>
      simp [checkHistoryProducers, HistoryProducersValid, checkHistoryProducerRow_iff, ih]

theorem HistoryProducersValid_suffix {newer older : List HistoryRow}
    (valid : HistoryProducersValid (newer ++ older)) : HistoryProducersValid older := by
  induction newer with
  | nil => exact valid
  | cons row tail ih => exact ih valid.2

/-- Fields copied unchanged by updates of one native key. Evaluator, cache,
returned role and producer metadata are deliberately outside this tuple. -/
def stableHistoryFields (row : HistoryRow) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Option (Bool × BitVec 64) :=
  (row.cell.authority, row.cell.storage, row.cell.imported, row.cell.occurrence,
    row.cell.argument, row.cell.captures.map (fun (known, _, count) => (known, count)))

def StableHistoryMetadata (left right : HistoryRow) : Prop :=
  stableHistoryFields left = stableHistoryFields right

def HistoryMetadataContinuous : List HistoryRow → Prop
  | [] => True
  | row :: older =>
      (∀ previous, FirstHistoryMatch older row.key previous → StableHistoryMetadata row previous) ∧
      HistoryMetadataContinuous older

def checkHistoryMetadataContinuous : List HistoryRow → Bool
  | [] => true
  | row :: older =>
      (match latestHistory? older row.key with
       | none => true
       | some previous => stableHistoryFields row == stableHistoryFields previous) &&
      checkHistoryMetadataContinuous older

theorem checkHistoryMetadataContinuous_iff (rows : List HistoryRow) :
    checkHistoryMetadataContinuous rows = true ↔ HistoryMetadataContinuous rows := by
  induction rows with
  | nil => simp [checkHistoryMetadataContinuous, HistoryMetadataContinuous]
  | cons row older ih =>
      cases found : latestHistory? older row.key with
      | none => simp [checkHistoryMetadataContinuous, HistoryMetadataContinuous,
          ← latestHistory?_iff, found, ih]
      | some previous => simp [checkHistoryMetadataContinuous, HistoryMetadataContinuous,
          ← latestHistory?_iff, found, ih, StableHistoryMetadata]

theorem HistoryMetadataContinuous_suffix {newer older : List HistoryRow}
    (valid : HistoryMetadataContinuous (newer ++ older)) : HistoryMetadataContinuous older := by
  induction newer with
  | nil => exact valid
  | cons row tail ih => exact ih valid.2

/-- Read the finite uint64 capture span from the existing target memory.
Zero-count spans require no dereference; nonempty missing or mistyped arrays
fail. Array addresses remain borrowed in the original rows. -/
def readCaptureContents? (memory : TargetMemory) :
    Option (Bool × Option Address × BitVec 64) → Option (Option (Bool × List (BitVec 64)))
  | none => some none
  | some (known, ids, count) =>
      if count = 0 then some (some (known, [])) else do
        let address ← ids
        let words ← (List.range count.toNat).mapM (fun offset =>
          match targetRead memory { address with element := address.element + offset } with
          | some (.word value) => some value
          | _ => none)
        some (some (known, words))

def HistoryCapturesValid (memory : TargetMemory) : List HistoryRow → Prop
  | [] => True
  | row :: older =>
      (∃ observed, readCaptureContents? memory row.cell.captures = some observed ∧
        ∀ previous, FirstHistoryMatch older row.key previous →
          readCaptureContents? memory previous.cell.captures = some observed) ∧
      HistoryCapturesValid memory older

def checkHistoryCaptures (memory : TargetMemory) : List HistoryRow → Bool
  | [] => true
  | row :: older =>
      (match readCaptureContents? memory row.cell.captures with
       | none => false
       | some observed => match latestHistory? older row.key with
           | none => true
           | some previous => readCaptureContents? memory previous.cell.captures == some observed) &&
      checkHistoryCaptures memory older

theorem checkHistoryCaptures_iff (memory : TargetMemory) (rows : List HistoryRow) :
    checkHistoryCaptures memory rows = true ↔ HistoryCapturesValid memory rows := by
  induction rows with
  | nil => simp [checkHistoryCaptures, HistoryCapturesValid]
  | cons row older ih =>
      cases contents : readCaptureContents? memory row.cell.captures with
      | none => simp [checkHistoryCaptures, HistoryCapturesValid, contents]
      | some observed =>
          cases previous : latestHistory? older row.key with
          | none => simp [checkHistoryCaptures, HistoryCapturesValid, contents,
              ← latestHistory?_iff, previous, ih]
          | some earlier => simp [checkHistoryCaptures, HistoryCapturesValid, contents,
              ← latestHistory?_iff, previous, ih]

theorem HistoryCapturesValid_suffix {memory : TargetMemory} {newer older : List HistoryRow}
    (valid : HistoryCapturesValid memory (newer ++ older)) : HistoryCapturesValid memory older := by
  induction newer with
  | nil => exact valid
  | cons row tail ih => exact ih valid.2

/-- The result retains every native row and reconstructs the existing source
spine through explicit origin-content readback. Capture arrays are read from
memory independently for each row; neither form of readback is a C ABI claim. -/
def readHistory? {Origin : Type*} [DecidableEq Origin]
    (captures provenance : Bool) (session : BitVec 64) (remaining : Nat)
    (naming : (BitVec 64 × BitVec 64) ↪ NeedReference.CellId)
    (readOrigin : Address → Option Origin) (memory : TargetMemory) (raw : List TargetValue) :
    Option (List HistoryRow × List (NeedReference.HeapUpdate Origin Address Address)) :=
  (raw.mapM (readHistoryRow? captures provenance)).bind (fun rows =>
    if checkHistoryInventory session remaining rows && checkHistoryProducers rows &&
        checkHistoryMetadataContinuous rows && checkHistoryCaptures memory rows then
      (namedHistory naming readOrigin rows).bind (fun records =>
        (NeedReference.Heap.readFullHistory records).bind (fun updates => some (rows, updates)))
    else none)

/-- Whole-history publication reflects all computed guards and both content
readbacks. Failure returns no partially published row list or source spine. -/
theorem readHistory?_iff {Origin : Type*} [DecidableEq Origin]
    (captures provenance : Bool) (session : BitVec 64) (remaining : Nat)
    (naming : (BitVec 64 × BitVec 64) ↪ NeedReference.CellId)
    (readOrigin : Address → Option Origin) (memory : TargetMemory) (raw : List TargetValue)
    (rows : List HistoryRow) (updates : List (NeedReference.HeapUpdate Origin Address Address)) :
    readHistory? captures provenance session remaining naming readOrigin memory raw = some (rows, updates) ↔
      raw.mapM (readHistoryRow? captures provenance) = some rows ∧
      HistoryInventoryValid session remaining rows ∧ HistoryProducersValid rows ∧
      HistoryMetadataContinuous rows ∧ HistoryCapturesValid memory rows ∧
      ∃ records, namedHistory naming readOrigin rows = some records ∧
        NeedReference.Heap.readFullHistory records = some updates := by
  unfold readHistory?
  change ((raw.mapM (readHistoryRow? captures provenance)).bind fun observed =>
    if checkHistoryInventory session remaining observed && checkHistoryProducers observed &&
        checkHistoryMetadataContinuous observed && checkHistoryCaptures memory observed then
      (namedHistory naming readOrigin observed).bind (fun records =>
        (NeedReference.Heap.readFullHistory records).bind (fun history => some (observed, history)))
    else none) = some (rows, updates) ↔ _
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨observed, decoded, published⟩
    split at published
    · next checked =>
      obtain ⟨records, recordsRead, published⟩ := Option.bind_eq_some_iff.mp published
      obtain ⟨history, reconstructed, equal⟩ := Option.bind_eq_some_iff.mp published
      have valid : HistoryInventoryValid session remaining observed ∧
          HistoryProducersValid observed ∧ HistoryMetadataContinuous observed ∧
          HistoryCapturesValid memory observed := by
        simpa [checkHistoryInventory_iff, checkHistoryProducers_iff,
          checkHistoryMetadataContinuous_iff, checkHistoryCaptures_iff, and_assoc] using checked
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj equal)
      exact ⟨decoded, valid.1, valid.2.1, valid.2.2.1, valid.2.2.2,
        records, recordsRead, reconstructed⟩
    · simp at published
  · rintro ⟨decoded, inventory, producers, continuous, capturesValid,
      records, recordsRead, reconstructed⟩
    refine ⟨rows, decoded, ?_⟩
    have inventoryCheck := (checkHistoryInventory_iff _ _ _).mpr inventory
    have producerCheck := (checkHistoryProducers_iff _).mpr producers
    have continuityCheck := (checkHistoryMetadataContinuous_iff _).mpr continuous
    have captureCheck := (checkHistoryCaptures_iff _ _).mpr capturesValid
    simp [inventoryCheck, producerCheck, continuityCheck, captureCheck, recordsRead, reconstructed]

theorem readHistory?_lookup {Origin : Type*} [DecidableEq Origin]
    {captures provenance : Bool} {session : BitVec 64}
    {remaining : Nat} {naming : (BitVec 64 × BitVec 64) ↪ NeedReference.CellId}
    {readOrigin : Address → Option Origin} {memory : TargetMemory}
    {raw : List TargetValue} {rows : List HistoryRow}
    {updates : List (NeedReference.HeapUpdate Origin Address Address)}
    (read : readHistory? captures provenance session remaining naming readOrigin memory raw = some (rows, updates))
    (key : BitVec 64 × BitVec 64) :
    NeedReference.Heap.lookupSpine updates (naming key) =
      (latestHistory? rows key).bind (namedRecord? readOrigin) := by
  obtain ⟨_, _, _, _, _, records, recordsRead, decoded⟩ :=
    (readHistory?_iff _ _ _ _ _ _ _ _ _ _).mp read
  exact readNamedHistory_lookup naming naming.injective readOrigin rows records recordsRead updates decoded key

theorem readHistory?_retains_rows {Origin : Type*} [DecidableEq Origin]
    {captures provenance : Bool} {session : BitVec 64}
    {remaining : Nat} {naming : (BitVec 64 × BitVec 64) ↪ NeedReference.CellId}
    {readOrigin : Address → Option Origin} {memory : TargetMemory}
    {raw : List TargetValue} {rows : List HistoryRow}
    {updates : List (NeedReference.HeapUpdate Origin Address Address)}
    (read : readHistory? captures provenance session remaining naming readOrigin memory raw = some (rows, updates)) :
    raw.mapM (readHistoryRow? captures provenance) = some rows ∧ rows.length = remaining ∧
      ∃ records, namedHistory naming readOrigin rows = some records ∧
        NeedReference.Heap.fullHistory? updates = some records := by
  obtain ⟨decoded, inventory, _, _, _, records, recordsRead, reconstructed⟩ :=
    (readHistory?_iff _ _ _ _ _ _ _ _ _ _).mp read
  exact ⟨decoded, inventory.2.1, records, recordsRead,
    NeedReference.Heap.fullHistory?_readFullHistory reconstructed⟩

/-! ## Grounded capability readback and the selected history

The native capability contains three identities and a rights mask. It does not
contain a heap or identify a producer branch. The caller therefore supplies the
retained snapshot's session and history. Admission neither switches to an ambient
world nor obtains additional rights from a completed cache entry.

`readAtom?` uses the logical active-arm representation of the C union: the ninth
Atom field is a `ground` record containing its tag, an ignored field and selected
payload. The native constructor does not initialize the unused string-length
field for this arm, and the reader does not inspect it. This is an explicit
representation boundary, not a physical ABI offset
or a proof that the native pointer is live. No expression traversal, quotation
opening, suspension forcing or cache update occurs in these readers.
-/

namespace NativeCapabilities

/-- The four fields of `CettaPrimeNeedCapability`, without an invented world. -/
structure View where
  session : BitVec 64
  thunk : BitVec 64
  authority : BitVec 64
  rights : BitVec 64
  deriving DecidableEq, Repr

/-- The native field is uint32; only the FORCE and INSPECT bits are public. -/
def RightsAdmissible (rights : BitVec 64) : Prop :=
  rights.toNat < 2 ^ 32 ∧ rights ≠ 0 ∧ rights &&& ~~~(3 : BitVec 64) = 0

instance (rights : BitVec 64) : Decidable (RightsAdmissible rights) := by
  unfold RightsAdmissible
  infer_instance

def View.Admissible (capability : View) : Prop :=
  capability.session ≠ 0 ∧ capability.thunk ≠ 0 ∧ capability.authority ≠ 0 ∧
    RightsAdmissible capability.rights

instance (capability : View) : Decidable capability.Admissible := by
  unfold View.Admissible
  infer_instance

def read? : TargetValue → Option View
  | .record "CettaPrimeNeedCapability"
      [.word session, .word thunk, .word authority, .word rights] =>
      let capability : View := ⟨session, thunk, authority, rights⟩
      if capability.Admissible then some capability else none
  | _ => none

theorem read?_fields (session thunk authority rights : BitVec 64) (capability : View) :
    read? (.record "CettaPrimeNeedCapability"
      [.word session, .word thunk, .word authority, .word rights]) = some capability ↔
      capability = ⟨session, thunk, authority, rights⟩ ∧ capability.Admissible := by
  simp only [read?]
  split <;> simp_all [eq_comm]

theorem read?_sound {record : TargetValue} {capability : View}
    (accepted : read? record = some capability) : capability.Admissible := by
  unfold read? at accepted
  split at accepted
  · dsimp only at accepted
    split at accepted <;> simp_all
  · simp at accepted

def readAt? (memory : TargetMemory) (address : Address) : Option View :=
  (targetRead memory address).bind read?

theorem readAt?_sound {memory : TargetMemory} {address : Address} {capability : View}
    (accepted : readAt? memory address = some capability) : capability.Admissible := by
  obtain ⟨record, _, decoded⟩ := Option.bind_eq_some_iff.mp accepted
  exact read?_sound decoded

/-- Observe only the tagged grounded arm. Written expressions do not acquire
capability status from their spelling or from a pointer-shaped field. -/
def readAtom? (memory : TargetMemory) (value : NativeFrames.BindingValueView) : Option View := do
  let address ← value.skeleton
  match targetRead memory (sourceFieldAddress address 0),
      targetRead memory (sourceFieldAddress address 8) with
  | some (.word 2), some (.record "ground"
      [.word 10, _, .reference (some payload)]) => readAt? memory payload
  | _, _ => none

theorem readAtom_grounded (memory : TargetMemory) (value : NativeFrames.BindingValueView)
    (address payload : Address) (ignored : TargetValue)
    (pointer : value.skeleton = some address)
    (kind : targetRead memory (sourceFieldAddress address 0) = some (.word 2))
    (arm : targetRead memory (sourceFieldAddress address 8) =
      some (.record "ground" [.word 10, ignored, .reference (some payload)])) :
    readAtom? memory value = readAt? memory payload := by
  simp [readAtom?, pointer, kind, arm]

/-- Changing a binding epoch or its storage tag cannot strengthen a grounded
capability. The capability's own retained rights remain authoritative. -/
theorem readAtom_same_skeleton (memory : TargetMemory)
    (first second : NativeFrames.BindingValueView) (same : first.skeleton = second.skeleton) :
    readAtom? memory first = readAtom? memory second := by
  simp only [readAtom?, same]

theorem readAtom?_sound {memory : TargetMemory} {value : NativeFrames.BindingValueView}
    {capability : View} (accepted : readAtom? memory value = some capability) :
    capability.Admissible := by
  obtain ⟨address, _, decoded⟩ := Option.bind_eq_some_iff.mp accepted
  split at decoded
  · exact readAt?_sound decoded
  · simp at decoded

/-- Interpret the native mask as a finite set, retaining the native bit names. -/
def rightsSet (word : BitVec 64) : Finset (Fin 64) :=
  Finset.univ.filter fun index => word.getLsbD index.val

theorem rightsSet_subset_iff (held requested : BitVec 64) :
    rightsSet requested ⊆ rightsSet held ↔ held &&& requested = requested := by
  constructor
  · intro subset
    apply BitVec.eq_of_getLsbD_eq
    intro index bound
    rw [BitVec.getLsbD_and]
    have included : requested.getLsbD index = true → held.getLsbD index = true := by
      intro present
      have member : (⟨index, bound⟩ : Fin 64) ∈ rightsSet requested := by
        simp [rightsSet, present]
      have granted := subset member
      exact (Finset.mem_filter.mp granted).2
    cases request : requested.getLsbD index with
    | false => simp
    | true => simp [included request]
  · intro same index member
    have requestedBit : requested.getLsbD index.val = true := by
      exact (Finset.mem_filter.mp member).2
    have bits := congrArg (fun word : BitVec 64 => word.getLsbD index.val) same
    simp only [BitVec.getLsbD_and, requestedBit, Bool.and_true] at bits
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, bits⟩

/-- Retain the actual newest cell row after checking the selected snapshot,
the requested rights and the row's minted authority. Cache completion is not
an authorization test. -/
def lookup? (session : BitVec 64) (rows : List HistoryRow)
    (capability : View) (required : BitVec 64) : Option HistoryRow := do
  if capability.Admissible ∧ RightsAdmissible required ∧ capability.session = session ∧
      capability.rights &&& required = required then
    let row ← latestHistory? rows (session, capability.thunk)
    if row.cell.authority = capability.authority then some row else none
  else none

def Authorized (session : BitVec 64) (rows : List HistoryRow)
    (capability : View) (required : BitVec 64) (row : HistoryRow) : Prop :=
  capability.Admissible ∧ RightsAdmissible required ∧ capability.session = session ∧
    rightsSet required ⊆ rightsSet capability.rights ∧
    FirstHistoryMatch rows (session, capability.thunk) row ∧
    row.cell.authority = capability.authority

theorem lookup?_iff (session : BitVec 64) (rows : List HistoryRow)
    (capability : View) (required : BitVec 64) (row : HistoryRow) :
    lookup? session rows capability required = some row ↔
      Authorized session rows capability required row := by
  unfold lookup? Authorized
  simp only [rightsSet_subset_iff]
  split
  · next allowed =>
    change ((latestHistory? rows (session, capability.thunk)).bind fun found =>
      if found.cell.authority = capability.authority then some found else none) = some row ↔ _
    rw [Option.bind_eq_some_iff]
    simp only [latestHistory?_iff]
    constructor
    · rintro ⟨found, selected, admitted⟩
      split at admitted
      · next authority =>
        cases Option.some.inj admitted
        exact ⟨allowed.1, allowed.2.1, allowed.2.2.1, allowed.2.2.2, selected, authority⟩
      · simp at admitted
    · rintro ⟨_, _, _, _, selected, authority⟩
      exact ⟨row, selected, by simp [authority]⟩
  · next refused =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨valid, requiredValid, same, subset, _, _⟩
    exact refused ⟨valid, requiredValid, same, subset⟩

theorem lookup?_selected_history (session : BitVec 64) (rows : List HistoryRow)
    (capability : View) (required : BitVec 64) (row : HistoryRow)
    (accepted : lookup? session rows capability required = some row) :
    latestHistory? rows (session, capability.thunk) = some row :=
  (latestHistory?_iff _ _ _).mpr ((lookup?_iff _ _ _ _ _).mp accepted).2.2.2.2.1

/-- Join the actual decoded capability to the independently reconstructed Need
heap. Its origin and cache are read from that same selected history row. -/
theorem lookup?_source_heap {Origin : Type*} [DecidableEq Origin]
    {captures provenance : Bool} {session : BitVec 64} {remaining : Nat}
    {naming : (BitVec 64 × BitVec 64) ↪ NeedReference.CellId}
    {readOrigin : Address → Option Origin} {memory : TargetMemory}
    {raw : List TargetValue} {rows : List HistoryRow}
    {updates : List (NeedReference.HeapUpdate Origin Address Address)}
    (history : readHistory? captures provenance session remaining naming readOrigin memory raw =
      some (rows, updates))
    (capability : View) (required : BitVec 64) (row : HistoryRow)
    (accepted : lookup? session rows capability required = some row) :
    NeedReference.Heap.lookupSpine updates (naming (session, capability.thunk)) =
      namedRecord? readOrigin row := by
  rw [readHistory?_lookup history,
    lookup?_selected_history session rows capability required row accepted]
  rfl

/-- Successful restriction preserves identity and returns exactly the requested
rights. Invalid or empty masks fail before any capability is published. -/
def restrict? (session : BitVec 64) (rows : List HistoryRow)
    (capability : View) (requested : BitVec 64) : Option View :=
  (lookup? session rows capability requested).map fun _ =>
    { capability with rights := requested }

theorem restrict?_iff (session : BitVec 64) (rows : List HistoryRow)
    (capability : View) (requested : BitVec 64) (restricted : View) :
    restrict? session rows capability requested = some restricted ↔
      restricted = { capability with rights := requested } ∧
        ∃ row, Authorized session rows capability requested row := by
  simp only [restrict?, Option.map_eq_some_iff, lookup?_iff]
  constructor
  · rintro ⟨row, permitted, rfl⟩
    exact ⟨rfl, row, permitted⟩
  · rintro ⟨rfl, row, permitted⟩
    exact ⟨row, permitted, rfl⟩

theorem restrict?_no_escalation {session : BitVec 64} {rows : List HistoryRow}
    {capability restricted : View} {requested : BitVec 64}
    (accepted : restrict? session rows capability requested = some restricted) :
    restricted.session = capability.session ∧ restricted.thunk = capability.thunk ∧
      restricted.authority = capability.authority ∧
      rightsSet restricted.rights ⊆ rightsSet capability.rights := by
  obtain ⟨rfl, row, permitted⟩ := (restrict?_iff _ _ _ _ _).mp accepted
  exact ⟨rfl, rfl, rfl, permitted.2.2.2.1⟩

/-- The restricted capability authorizes exactly its retained requested rights
at the same newest row. Restriction neither substitutes a cell nor restarts it. -/
theorem restrict?_lookup_same {session : BitVec 64} {rows : List HistoryRow}
    {capability : View} {requested : BitVec 64} {row : HistoryRow}
    (accepted : lookup? session rows capability requested = some row) :
    lookup? session rows { capability with rights := requested } requested = some row := by
  obtain ⟨valid, requiredValid, same, _, selected, authority⟩ :=
    (lookup?_iff _ _ _ _ _).mp accepted
  apply (lookup?_iff _ _ _ _ _).mpr
  exact ⟨⟨valid.1, valid.2.1, valid.2.2.1, requiredValid⟩, requiredValid,
    same, Finset.Subset.refl _, selected, authority⟩

/-- Repeated attenuation cannot recover any right removed at an earlier
boundary, even when the two checks consult different snapshots. -/
theorem restrict?_chain_no_escalation
    {firstSession secondSession : BitVec 64} {firstRows secondRows : List HistoryRow}
    {original middle final : View} {firstRequest secondRequest : BitVec 64}
    (first : restrict? firstSession firstRows original firstRequest = some middle)
    (second : restrict? secondSession secondRows middle secondRequest = some final) :
    rightsSet final.rights ⊆ rightsSet original.rights :=
  (restrict?_no_escalation second).2.2.2.trans (restrict?_no_escalation first).2.2.2

end NativeCapabilities

/-! ## Contextual payload graphs

The structural reader follows every raw expression field in the selected memory
snapshot. Its key retains that selection together with the complete binding
view; an equal pointer does not identify two contextual occurrences. Grounded
observation is an explicit extension point. The capability instance below reads
the actual grounded capability and does not force it. Opaque rational-graph
carriers require their own reader, including their parameter environment.

Successful admission constructs the existing ordered graph from a finite closed
inventory. Its finite observations agree with direct memory traversal at every
depth. This is a structural observation theorem: variable resolution, permission
to force a suspension, physical memory ownership and evaluation remain distinct
contracts. Symbol labels retain either a nonzero ID in the selected symbol table or exact
managed bytes. Mapping numbered IDs to current spelling remains an explicit API
contract; interpreting bytes as text is independently checked.
-/

namespace NativePayload

open Mettapedia.Machines.RationalTermGraph

/-- The world is supplied by the retained execution, not fabricated from a
capability or discarded when a child pointer is selected. -/
structure Cursor (World : Type) where
  world : World
  value : NativeFrames.BindingValueView
  deriving DecidableEq, Repr

inductive Label (Ground : Type) where
  | symbol (identifier : BitVec 64)
  | symbolBytes (bytes : List UInt8)
  | variable (identifier : BitVec 64)
  | expression
  | grounded (value : Ground)
  deriving DecidableEq, Repr

variable {World : Type} {Ground : Type}

def Cursor.child (parent : Cursor World) (value : NativeFrames.BindingValueView) : Cursor World :=
  ⟨parent.world, value⟩

/-- Managed spellings retain their explicit length, including embedded NUL.
The buffer address is read from the spelling object's represented embedded
member. Unsupported or absent bytes are not silently replaced by UTF-8 text. -/
def readSpelling? (memory : TargetMemory) (spelling : Address) : Option (List UInt8) := do
  let length ← match targetRead memory (sourceFieldAddress spelling 1) with
    | some (.word length) => some length
    | _ => none
  if length.toNat < 2 ^ 32 then
    let buffer ← match targetRead memory (sourceFieldAddress spelling 2) with
      | some (.reference (some buffer)) => some buffer
      | _ => none
    ByteViews.targetBlock memory buffer length.toNat
  else none

/-- Numbered symbols and managed spellings share the symbol kind, but have
different stored identities. Raw ID zero is not itself a spelling. -/
def readSymbol? (memory : TargetMemory) (address : Address) : Option (Label Ground) := do
  let identifier ← match targetRead memory (sourceFieldAddress address 3) with
    | some (.word identifier) => some identifier
    | _ => none
  if identifier.toNat < 2 ^ 32 then
    if identifier = 0 then
      match targetRead memory (sourceFieldAddress address 5) with
      | some (.reference none) => some (.symbolBytes [])
      | some (.reference (some spelling)) => (readSpelling? memory spelling).map Label.symbolBytes
      | _ => none
    else some (.symbol identifier)
  else none

/-- Read a single layer without resolving, evaluating or opening any child. -/
def readLayer? (memory : World → TargetMemory) (readGround : Cursor World → Option Ground)
    (cursor : Cursor World) : Option (Label Ground × List (Cursor World)) := do
  if cursor.value.Admissible then
    let address ← cursor.value.skeleton
    match targetRead (memory cursor.world) (sourceFieldAddress address 0) with
    | some (.word 0) =>
        (readSymbol? (memory cursor.world) address).map (fun symbol => (symbol, []))
    | some (.word 1) =>
        (NativeFrames.readVariableId? (memory cursor.world) cursor.value).map
          (fun identifier => (.variable identifier, []))
    | some (.word 2) => (readGround cursor).map (fun value => (.grounded value, []))
    | some (.word 3) =>
        (NativeFrames.readExpressionChildren? (memory cursor.world) cursor.value).map
          (fun children => (.expression, children.map cursor.child))
    | _ => none
  else none

theorem readLayer?_null (memory : World → TargetMemory)
    (readGround : Cursor World → Option Ground) (cursor : Cursor World)
    (null : cursor.value.skeleton = none) : readLayer? memory readGround cursor = none := by
  simp [readLayer?, null]

theorem readLayer?_expression (memory : World → TargetMemory)
    (readGround : Cursor World → Option Ground) (cursor : Cursor World)
    (valid : cursor.value.Admissible) (address : Address)
    (pointer : cursor.value.skeleton = some address)
    (kind : targetRead (memory cursor.world) (sourceFieldAddress address 0) = some (.word 3)) :
    readLayer? memory readGround cursor =
      (NativeFrames.readExpressionChildren? (memory cursor.world) cursor.value).map
        (fun children => (.expression, children.map cursor.child)) := by
  simp [readLayer?, valid, pointer, kind]

def readRow? (memory : World → TargetMemory) (readGround : Cursor World → Option Ground)
    (cursor : Cursor World) : Option (KeyedRow (Cursor World) (Label Ground)) :=
  LayerReader.readRow? (readLayer? memory readGround) cursor

theorem readRow?_sound {memory : World → TargetMemory}
    {readGround : Cursor World → Option Ground} {cursor : Cursor World}
    {row : KeyedRow (Cursor World) (Label Ground)}
    (read : readRow? memory readGround cursor = some row) :
    row.key = cursor ∧ readLayer? memory readGround cursor = some (row.label, row.children) := by
  exact LayerReader.readRow?_sound read

def readRows? (memory : World → TargetMemory) (readGround : Cursor World → Option Ground)
    (cursors : List (Cursor World)) : Option (List (KeyedRow (Cursor World) (Label Ground))) :=
  LayerReader.readRows? (readLayer? memory readGround) cursors

theorem readRows?_member {memory : World → TargetMemory}
    {readGround : Cursor World → Option Ground} {cursors : List (Cursor World)}
    {rows : List (KeyedRow (Cursor World) (Label Ground))}
    (read : readRows? memory readGround cursors = some rows)
    (row : KeyedRow (Cursor World) (Label Ground)) (member : row ∈ rows) :
    ∃ cursor ∈ cursors, readRow? memory readGround cursor = some row := by
  exact LayerReader.readRows?_member read row member

theorem readRows?_keys {memory : World → TargetMemory}
    {readGround : Cursor World → Option Ground} {cursors : List (Cursor World)}
    {rows : List (KeyedRow (Cursor World) (Label Ground))}
    (read : readRows? memory readGround cursors = some rows) :
    rows.map KeyedRow.key = cursors := by
  exact LayerReader.readRows?_keys read

def readGraph? [DecidableEq World] (memory : World → TargetMemory)
    (readGround : Cursor World → Option Ground) (cursors : List (Cursor World)) :
    Option (KeyedTable (Cursor World) (Label Ground)) :=
  LayerReader.readTable? (readLayer? memory readGround) cursors

theorem readGraph?_isSome_iff [DecidableEq World] (memory : World → TargetMemory)
    (readGround : Cursor World → Option Ground) (cursors : List (Cursor World)) :
    (readGraph? memory readGround cursors).isSome = true ↔
      ∃ rows, readRows? memory readGround cursors = some rows ∧ KeyedInventoryValid rows := by
  exact LayerReader.readTable?_isSome_iff (readLayer? memory readGround) cursors

/-- Node keys are the exact supplied inventory, with no deduplication or
replacement of contexts by pointer equality. -/
theorem readGraph?_keys [DecidableEq World] {memory : World → TargetMemory}
    {readGround : Cursor World → Option Ground} {cursors : List (Cursor World)}
    {table : KeyedTable (Cursor World) (Label Ground)}
    (read : readGraph? memory readGround cursors = some table) :
    table.rows.map KeyedRow.key = cursors := by
  exact LayerReader.readTable?_keys read

/-- This commuting layer equation is derived from the executable memory
reader and checked graph admission; it is not an assumed correspondence. -/
theorem readGraph?_layer [DecidableEq World] {memory : World → TargetMemory}
    {readGround : Cursor World → Option Ground} {cursors : List (Cursor World)}
    {table : KeyedTable (Cursor World) (Label Ground)}
    (read : readGraph? memory readGround cursors = some table) (node : table.Node) :
    readLayer? memory readGround (table.key node) =
      some (table.graph.label node, (table.graph.children node).map table.key) := by
  exact LayerReader.readTable?_layer read node

theorem readGraph?_nonnull [DecidableEq World] {memory : World → TargetMemory}
    {readGround : Cursor World → Option Ground} {cursors : List (Cursor World)}
    {table : KeyedTable (Cursor World) (Label Ground)}
    (read : readGraph? memory readGround cursors = some table) (node : table.Node) :
    (table.key node).value.skeleton ≠ none := by
  intro null
  have layer := readGraph?_layer read node
  rw [readLayer?_null memory readGround (table.key node) null] at layer
  contradiction

/-- Direct bounded memory traversal, independent of keyed lookup and finite
node construction. Even the depth boundary checks that its root can be read. -/
def observeMemory (memory : World → TargetMemory) (readGround : Cursor World → Option Ground) :
    Nat → Cursor World → Option (Observation (Label Ground)) :=
  LayerReader.observe (readLayer? memory readGround)

/-- Every finite graph observation agrees with direct reads of the native
logical memory, at arbitrary nesting and with repeated occurrences retained. -/
theorem readGraph?_observe [DecidableEq World] {memory : World → TargetMemory}
    {readGround : Cursor World → Option Ground} {cursors : List (Cursor World)}
    {table : KeyedTable (Cursor World) (Label Ground)}
    (read : readGraph? memory readGround cursors = some table) (depth : Nat) (node : table.Node) :
    observeMemory memory readGround depth (table.key node) =
      some (observe table.graph depth node) := by
  exact LayerReader.readTable?_observe read depth node

/-- The common term-graph equality is exactly equality of these finite
structural observations. It does not identify cursor keys or resource rights. -/
theorem readGraph?_bisimilar_iff [DecidableEq World] {memory : World → TargetMemory}
    {readGround : Cursor World → Option Ground} {firstCursors secondCursors : List (Cursor World)}
    {first second : KeyedTable (Cursor World) (Label Ground)}
    (firstRead : readGraph? memory readGround firstCursors = some first)
    (secondRead : readGraph? memory readGround secondCursors = some second)
    (left : first.Node) (right : second.Node) :
    Bisimilar first.graph second.graph left right ↔
      ∀ depth, observeMemory memory readGround depth (first.key left) =
        observeMemory memory readGround depth (second.key right) := by
  exact LayerReader.readTable?_bisimilar_iff firstRead secondRead left right

/-! ### Binding-resolved structural observation

This reader applies the bounded alias observation at each inspected root.
The raw reader above remains the observation of written structure. Resolving
a root keeps the caller's selected world and adopts the complete returned
binding value, so its children inherit that value's context. Neither reader
evaluates a written call or forces a grounded suspension. Failed row admission
or alias resolution prevents graph admission; this partial structural decoder
does not replace the resolver's distinct failure results or execution faults.
-/

/-- Read the actual ordinary-row inventory in the cursor's selected world,
then resolve its root through that world's admitted frame directory. -/
def resolveCursor? (memory : World → TargetMemory)
    (directory : World → NativeFrames.DirectoryReadback) (allowance : Nat)
    (cursor : Cursor World) : Option (Cursor World) := do
  let rows ← NativeFrames.OrdinaryBindings.readback? (memory cursor.world)
    (directory cursor.world).directory.bindings
  match NativeFrames.RootResolution.Query.resolve (memory cursor.world)
      (NativeFrames.RootResolution.lookup (directory cursor.world) rows)
      allowance cursor.value with
  | .resolved value => some (cursor.child value)
  | _ => none

theorem resolveCursor?_resolved (memory : World → TargetMemory)
    (directory : World → NativeFrames.DirectoryReadback) (allowance : Nat)
    (cursor : Cursor World) (rows : List NativeFrames.OrdinaryBindings.Row)
    (value : NativeFrames.BindingValueView)
    (read : NativeFrames.OrdinaryBindings.readback? (memory cursor.world)
      (directory cursor.world).directory.bindings = some rows)
    (resolved : NativeFrames.RootResolution.Query.resolve (memory cursor.world)
      (NativeFrames.RootResolution.lookup (directory cursor.world) rows)
      allowance cursor.value = .resolved value) :
    resolveCursor? memory directory allowance cursor = some (cursor.child value) := by
  simp [resolveCursor?, read, resolved]

theorem resolveCursor?_sound {memory : World → TargetMemory}
    {directory : World → NativeFrames.DirectoryReadback} {allowance : Nat}
    {cursor result : Cursor World}
    (read : resolveCursor? memory directory allowance cursor = some result) :
    ∃ rows value,
      NativeFrames.OrdinaryBindings.readback? (memory cursor.world)
        (directory cursor.world).directory.bindings = some rows ∧
      NativeFrames.RootResolution.Query.resolve (memory cursor.world)
        (NativeFrames.RootResolution.lookup (directory cursor.world) rows)
        allowance cursor.value = .resolved value ∧ result = cursor.child value := by
  obtain ⟨rows, rowsRead, resolved⟩ := Option.bind_eq_some_iff.mp read
  cases outcome : NativeFrames.RootResolution.Query.resolve (memory cursor.world)
      (NativeFrames.RootResolution.lookup (directory cursor.world) rows)
      allowance cursor.value with
  | unreadable => simp [outcome] at resolved
  | refused => simp [outcome] at resolved
  | resolved value =>
      simp only [outcome, Option.some.injEq] at resolved
      exact ⟨rows, value, rowsRead, outcome, resolved.symm⟩

theorem resolveCursor?_world {memory : World → TargetMemory}
    {directory : World → NativeFrames.DirectoryReadback} {allowance : Nat}
    {cursor result : Cursor World}
    (read : resolveCursor? memory directory allowance cursor = some result) :
    result.world = cursor.world := by
  obtain ⟨_, _, _, _, rfl⟩ := resolveCursor?_sound read
  rfl

/-- A completed retained alias query supplies exactly the root consumed by
the structural reader. Row readback comes from the same selected world. -/
theorem resolveCursor?_completed (memory : World → TargetMemory)
    (directory : World → NativeFrames.DirectoryReadback) (allowance fuel : Nat)
    (cursor : Cursor World) (rows : List NativeFrames.OrdinaryBindings.Row)
    (observation : Mettapedia.Machines.ReadOnlyQuery.Observation
      NativeFrames.RootResolution.Query.Key NativeFrames.RootResolution.Query.Reply
      NativeFrames.RootResolution.Query.Result)
    (value : NativeFrames.BindingValueView)
    (read : NativeFrames.OrdinaryBindings.readback? (memory cursor.world)
      (directory cursor.world).directory.bindings = some rows)
    (finished : Mettapedia.Machines.Cursor.ReadOnlyQuery.completed?
      (NativeFrames.RootResolution.Query.store (memory cursor.world)
        (NativeFrames.RootResolution.lookup (directory cursor.world) rows))
      (NativeFrames.RootResolution.Query.advance (memory cursor.world)
        (directory cursor.world) rows allowance fuel cursor.value).2 = some observation)
    (answer : observation.answer = .resolved value) :
    resolveCursor? memory directory allowance cursor = some (cursor.child value) := by
  apply resolveCursor?_resolved memory directory allowance cursor rows value read
  exact (NativeFrames.RootResolution.Query.completed_correct _ _ _ _ _ _ _ finished).symm.trans answer

/-- The resolved operand is inspected by the existing raw layer reader;
grounded capability decoding therefore retains its identity and rights. -/
def readResolvedLayer? (memory : World → TargetMemory)
    (directory : World → NativeFrames.DirectoryReadback) (allowance : Nat)
    (readGround : Cursor World → Option Ground) (cursor : Cursor World) :
    Option (Label Ground × List (Cursor World)) := do
  let resolved ← resolveCursor? memory directory allowance cursor
  readLayer? memory readGround resolved

theorem readResolvedLayer?_resolved (memory : World → TargetMemory)
    (directory : World → NativeFrames.DirectoryReadback) (allowance : Nat)
    (readGround : Cursor World → Option Ground) (cursor resolved : Cursor World)
    (read : resolveCursor? memory directory allowance cursor = some resolved) :
    readResolvedLayer? memory directory allowance readGround cursor =
      readLayer? memory readGround resolved := by
  simp [readResolvedLayer?, read]

/-- Admission retains the original contextual keys even when two alias roots
observe the same returned structure. Repeated child occurrences remain ordered. -/
def readResolvedGraph? [DecidableEq World] (memory : World → TargetMemory)
    (directory : World → NativeFrames.DirectoryReadback) (allowance : Nat)
    (readGround : Cursor World → Option Ground) (cursors : List (Cursor World)) :
    Option (KeyedTable (Cursor World) (Label Ground)) :=
  LayerReader.readTable? (readResolvedLayer? memory directory allowance readGround) cursors

def observeResolvedMemory (memory : World → TargetMemory)
    (directory : World → NativeFrames.DirectoryReadback) (allowance : Nat)
    (readGround : Cursor World → Option Ground) :
    Nat → Cursor World → Option (Observation (Label Ground)) :=
  LayerReader.observe (readResolvedLayer? memory directory allowance readGround)

theorem readResolvedGraph?_keys [DecidableEq World] {memory : World → TargetMemory}
    {directory : World → NativeFrames.DirectoryReadback} {allowance : Nat}
    {readGround : Cursor World → Option Ground} {cursors : List (Cursor World)}
    {table : KeyedTable (Cursor World) (Label Ground)}
    (read : readResolvedGraph? memory directory allowance readGround cursors = some table) :
    table.rows.map KeyedRow.key = cursors := by
  exact LayerReader.readTable?_keys read

theorem readResolvedGraph?_layer [DecidableEq World] {memory : World → TargetMemory}
    {directory : World → NativeFrames.DirectoryReadback} {allowance : Nat}
    {readGround : Cursor World → Option Ground} {cursors : List (Cursor World)}
    {table : KeyedTable (Cursor World) (Label Ground)}
    (read : readResolvedGraph? memory directory allowance readGround cursors = some table)
    (node : table.Node) :
    readResolvedLayer? memory directory allowance readGround (table.key node) =
      some (table.graph.label node, (table.graph.children node).map table.key) := by
  exact LayerReader.readTable?_layer read node

/-- Every finite observation agrees with direct alias-resolved memory reads.
This is structural interpretation of bindings, separate from evaluation and
the operational profile's permission to demand a child. -/
theorem readResolvedGraph?_observe [DecidableEq World] {memory : World → TargetMemory}
    {directory : World → NativeFrames.DirectoryReadback} {allowance : Nat}
    {readGround : Cursor World → Option Ground} {cursors : List (Cursor World)}
    {table : KeyedTable (Cursor World) (Label Ground)}
    (read : readResolvedGraph? memory directory allowance readGround cursors = some table)
    (depth : Nat) (node : table.Node) :
    observeResolvedMemory memory directory allowance readGround depth (table.key node) =
      some (observe table.graph depth node) := by
  exact LayerReader.readTable?_observe read depth node

theorem readResolvedGraph?_bisimilar_iff [DecidableEq World] {memory : World → TargetMemory}
    {directory : World → NativeFrames.DirectoryReadback} {allowance : Nat}
    {readGround : Cursor World → Option Ground}
    {firstCursors secondCursors : List (Cursor World)}
    {first second : KeyedTable (Cursor World) (Label Ground)}
    (firstRead : readResolvedGraph? memory directory allowance readGround firstCursors = some first)
    (secondRead : readResolvedGraph? memory directory allowance readGround secondCursors = some second)
    (left : first.Node) (right : second.Node) :
    Bisimilar first.graph second.graph left right ↔
      ∀ depth, observeResolvedMemory memory directory allowance readGround depth (first.key left) =
        observeResolvedMemory memory directory allowance readGround depth (second.key right) := by
  exact LayerReader.readTable?_bisimilar_iff firstRead secondRead left right

/-- A concrete grounded observer reuses the native capability decoder and
retains all rights. It does not consult or execute the thunk's producer. -/
def readCapability (memory : World → TargetMemory) (cursor : Cursor World) :
    Option NativeCapabilities.View :=
  NativeCapabilities.readAtom? (memory cursor.world) cursor.value

namespace Controls

private def address (storage : Nat) : Address := ⟨storage, 0, []⟩

private def atom (kind identifier symbol : BitVec 64) (payload : TargetValue) : TargetValue :=
  .record "Atom" [.word kind, .word 0, .word identifier, .word symbol, .word 0,
    .reference none, .word 0, .word 0, payload]

private def memory (world : Nat) : TargetMemory :=
  ⟨fun storage index =>
    if storage = 81 ∧ index = 0 then
      some (atom 3 0 0 (.record "expr" [.reference (some ⟨82, 4, []⟩), .word 4]))
    else if storage = 82 ∧ 4 ≤ index then
      ([some (address 85), some (address 84), some (address 85), some (address 86)][index - 4]?).map
        TargetValue.reference
    else if storage = 83 ∧ index = 0 then some (atom 0 0 9 .unit)
    else if storage = 84 ∧ index = 0 then some (atom 1 7 0 .unit)
    else if storage = 85 ∧ index = 0 then
      some (atom 2 0 0 (.record "ground" [.word 10, .unit, .reference (some (address 87))]))
    else if storage = 86 ∧ index = 0 then
      some (atom 3 0 0 (.record "expr" [.reference (some (address 88)), .word 2]))
    else if storage = 87 ∧ index = 0 then
      some (.record "CettaPrimeNeedCapability" [.word (BitVec.ofNat 64 (world + 1)),
        .word 5, .word 9, .word 2])
    else if storage = 88 then
      ([some (address 83), some (address 84)][index]?).map TargetValue.reference
    else none,
    fun _ => none⟩

private def cursor (world storage : Nat) (epoch : BitVec 64 := 19) : Cursor Nat :=
  ⟨world, ⟨some (address storage), epoch, 1⟩⟩

private def inventory : List (Cursor Nat) := [81, 85, 84, 86, 83].map (cursor 0)

theorem expression_inventory_is_admitted :
    (readGraph? memory (readCapability memory) inventory).isSome = true := by decide

theorem direct_read_retains_capabilities_variables_and_written_subtrees :
    observeMemory memory (readCapability memory) 3 (cursor 0 81) =
      some (.node .expression [
        .node (.grounded ⟨1, 5, 9, 2⟩) [],
        .node (.variable (BitVec.ofNat 64 (19 * 2 ^ 32 + 7))) [],
        .node (.grounded ⟨1, 5, 9, 2⟩) [],
        .node .expression [.node (.symbol 9) [],
          .node (.variable (BitVec.ofNat 64 (19 * 2 ^ 32 + 7))) []]]) := by rfl

theorem repeated_edges_are_not_duplicate_nodes :
    (readGraph? memory (readCapability memory) inventory).isSome = true ∧
    (readGraph? memory (readCapability memory) (cursor 0 85 :: inventory)).isSome = false ∧
    (readGraph? memory (readCapability memory) [cursor 0 81, cursor 0 85]).isSome = false := by
  decide

theorem null_node_and_invalid_context_are_refused :
    (readGraph? memory (readCapability memory) [⟨0, ⟨none, 19, 1⟩⟩]).isSome = false ∧
    (readGraph? memory (readCapability memory) [⟨0, ⟨some (address 85), 19, 3⟩⟩]).isSome = false := by
  decide

theorem pointer_equality_does_not_choose_world_or_variable_identity :
    (readGraph? memory (readCapability memory) [cursor 0 85, cursor 1 85]).isSome = true ∧
    readLayer? memory (readCapability memory) (cursor 0 85) =
      some (.grounded ⟨1, 5, 9, 2⟩, []) ∧
    readLayer? memory (readCapability memory) (cursor 1 85) =
      some (.grounded ⟨2, 5, 9, 2⟩, []) ∧
    readLayer? memory (readCapability memory) (cursor 0 84 19) ≠
      readLayer? memory (readCapability memory) (cursor 0 84 20) := by decide

private def bindingRowsMemory (rows : List NativeFrames.OrdinaryBindings.Row)
    (world : Nat) : TargetMemory :=
  ⟨fun storage index =>
    if storage = 91 ∧ index = 0 then
      some (.record "Bindings" [.reference none, .reference (some (address 92)),
        .word (BitVec.ofNat 64 rows.length), .word 0,
        .reference none, .word 0, .word 0, .byte 0,
        .record "rhs_variable_bloom" [.byte 0, .byte 0, .byte 0], .word 0, .word 0,
        .reference none, .reference none, .reference none, .word 0, .word 0, .reference none])
    else if storage = 92 then
      (rows[index]?).map fun row => .record "Binding" [.word row.identifier, .word 0,
        .reference none, .record "BindingValue" [.reference row.value.skeleton,
          .word row.value.epoch, .word row.value.kind]]
    else if storage = 89 ∧ index = 0 then some (atom 1 8 0 .unit)
    else (memory world).cells storage index,
    fun _ => none⟩

private def boundMemory := bindingRowsMemory [⟨7, ⟨some (address 85), 0, 0⟩⟩]

private def boundEpoch : BitVec 64 := NativeFrames.encode ⟨19, 1⟩

private def boundCursor (world storage : Nat) : Cursor Nat := cursor world storage boundEpoch

/-- The authored variable points to a returned materialized expression;
its child variable then belongs to the ordinary binding image. -/
private def bindingDirectory : NativeFrames.DirectoryReadback :=
  (NativeFrames.readDirectory?
    (.record "BindingsFrameDirectoryStateView" [.reference (some (address 91)),
      .reference (some (address 93)), .word 1, .word 7, .word 17]) 20
    [(.record "BindingsFrameStateView" [.reference (some (address 91)),
      .reference (some (address 93)), .record "BindingsFrameRef" [.word boundEpoch],
      .word 1, .word 1, .word 7, .word 17, .word 0, .bool false, .bool true, .bool false],
      [.record "BindingsFrameSlotStateView" [.word 7, .word (boundEpoch * 2 ^ 32 + 7), .word 9,
        .reference none, .bool true,
        .record "BindingValue" [.reference (some (address 86)), .word 0, .word 0], .word 17]])]).get
    (by decide +kernel)

private def directories (_world : Nat) : NativeFrames.DirectoryReadback := bindingDirectory

private def resolvedInventory : List (Cursor Nat) :=
  [81, 85, 84, 86, 83].map (boundCursor 0) ++
    [⟨0, ⟨some (address 83), 0, 0⟩⟩, ⟨0, ⟨some (address 84), 0, 0⟩⟩]

theorem alias_root_adopts_returned_context_and_retains_world :
    resolveCursor? boundMemory directories 1 (boundCursor 0 84) =
      some ⟨0, ⟨some (address 86), 0, 0⟩⟩ ∧
    resolveCursor? boundMemory directories 1 ⟨0, ⟨some (address 84), 0, 0⟩⟩ =
      some ⟨0, ⟨some (address 85), 0, 0⟩⟩ := by decide +kernel

theorem resolved_inventory_keeps_original_keys_and_repeated_edges :
    (readResolvedGraph? boundMemory directories 1 (readCapability boundMemory)
      resolvedInventory).isSome = true ∧
    ((readResolvedGraph? boundMemory directories 1 (readCapability boundMemory)
      resolvedInventory).map fun table => table.rows.map KeyedRow.key) = some resolvedInventory ∧
    (readResolvedGraph? boundMemory directories 1 (readCapability boundMemory)
      (boundCursor 0 84 :: resolvedInventory)).isSome = false := by decide +kernel

theorem resolved_observation_preserves_capability_rights_and_written_structure :
    observeResolvedMemory boundMemory directories 1 (readCapability boundMemory) 3 (boundCursor 0 81) =
      some (.node .expression [
        .node (.grounded ⟨1, 5, 9, 2⟩) [],
        .node .expression [.node (.symbol 9) [], .node (.grounded ⟨1, 5, 9, 2⟩) []],
        .node (.grounded ⟨1, 5, 9, 2⟩) [],
        .node .expression [.node (.symbol 9) [], .node .expression [.cut, .cut]]]) := by rfl

theorem returned_pointer_does_not_select_the_world :
    readResolvedLayer? boundMemory directories 1 (readCapability boundMemory)
      ⟨0, ⟨some (address 84), 0, 0⟩⟩ = some (.grounded ⟨1, 5, 9, 2⟩, []) ∧
    readResolvedLayer? boundMemory directories 1 (readCapability boundMemory)
      ⟨1, ⟨some (address 84), 0, 0⟩⟩ = some (.grounded ⟨2, 5, 9, 2⟩, []) := by decide +kernel

theorem raw_and_resolved_observers_are_distinct :
    readLayer? boundMemory (readCapability boundMemory) (boundCursor 0 84) =
      some (.variable (boundEpoch * 2 ^ 32 + 7), []) ∧
    readResolvedLayer? boundMemory directories 0 (readCapability boundMemory) (boundCursor 0 84) = none ∧
    readResolvedLayer? boundMemory directories 1 (readCapability boundMemory) (boundCursor 0 84) =
      some (.expression, [⟨0, ⟨some (address 83), 0, 0⟩⟩,
        ⟨0, ⟨some (address 84), 0, 0⟩⟩]) := by decide +kernel

theorem cyclic_aliases_refuse_graph_observation :
    let cyclic := bindingRowsMemory
      [⟨7, ⟨some (address 89), 0, 0⟩⟩, ⟨8, ⟨some (address 84), 0, 0⟩⟩]
    resolveCursor? cyclic directories 4 ⟨0, ⟨some (address 84), 0, 0⟩⟩ = none ∧
    (readResolvedGraph? cyclic directories 4 (readCapability cyclic)
      [⟨0, ⟨some (address 84), 0, 0⟩⟩]).isSome = false := by decide +kernel

end Controls

end NativePayload

/-- Uniform borrowed-address relabeling reuses the common Need mapping.
Its native application is injective relocation. It does not model per-frame
capture duplication or partial suffix copying with a retained prefix. -/
def borrowedHistoryMapping (mapAddress : Address → Address) :
    NeedRepresentation.Mapping Address Unit Unit Unit Address Address Unit Unit
      Address Unit Unit Unit Address Address Unit Unit :=
  ⟨mapAddress, id, id, id, mapAddress, mapAddress, id, id⟩

def mapHistoryRow (mapAddress : Address → Address) (row : HistoryRow) : HistoryRow :=
  { row with cell := { row.cell with
      record := (borrowedHistoryMapping mapAddress).mapRecord row.cell.record
      captures := row.cell.captures.map (fun (known, variableIds, count) =>
        (known, variableIds.map mapAddress, count)) } }

@[simp] theorem mapHistoryRow_key (mapAddress : Address → Address) (row : HistoryRow) :
    (mapHistoryRow mapAddress row).key = row.key := rfl

theorem latestHistory?_map (mapAddress : Address → Address) (rows : List HistoryRow)
    (key : BitVec 64 × BitVec 64) :
    latestHistory? (rows.map (mapHistoryRow mapAddress)) key =
      (latestHistory? rows key).map (mapHistoryRow mapAddress) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      by_cases same : row.key = key
      · simp [latestHistory?, same]
      · simpa only [latestHistory?, List.map_cons, List.find?_cons,
          mapHistoryRow_key, same, decide_false, cond_false] using ih

theorem checkHistoryInventory_map (mapAddress : Address → Address) (session : BitVec 64)
    (remaining : Nat) (rows : List HistoryRow) :
    checkHistoryInventory session remaining (rows.map (mapHistoryRow mapAddress)) =
      checkHistoryInventory session remaining rows := by
  have aligned : checkHistoryAligned session (rows.map (mapHistoryRow mapAddress)) =
      checkHistoryAligned session rows := by
    induction rows with
    | nil => rfl
    | cons row rest ih => simp [checkHistoryAligned, checkHistoryHeaders, mapHistoryRow, ih]
  simp [checkHistoryInventory, aligned]

private theorem forwardingMetadata?_map (mapAddress : Address → Address) (row : HistoryRow) :
    forwardingMetadata? (mapHistoryRow mapAddress row) = forwardingMetadata? row := by
  cases cache : row.cell.record.cache <;>
    cases metadata : row.cell.valueProvenance <;>
    simp [forwardingMetadata?, mapHistoryRow, borrowedHistoryMapping,
      NeedRepresentation.Mapping.mapRecord, NeedRepresentation.Mapping.mapCache, cache, metadata]

private theorem checkCacheIsValue_map (mapAddress : Address → Address)
    (cache : NeedReference.Cache Address Address) :
    checkCacheIsValue ((borrowedHistoryMapping mapAddress).mapCache cache) =
      checkCacheIsValue cache := by
  cases cache <;> rfl

theorem checkProducerRow?_map (mapAddress : Address → Address)
    (rows : List HistoryRow) (consumer : HistoryRow) :
    checkProducerRow? (rows.map (mapHistoryRow mapAddress)) (mapHistoryRow mapAddress consumer) =
      (checkProducerRow? rows consumer).map (mapHistoryRow mapAddress) := by
  unfold checkProducerRow?
  rw [forwardingMetadata?_map]
  cases metadata : forwardingMetadata? consumer with
  | none => rfl
  | some observed =>
      change ((latestHistory? (rows.map (mapHistoryRow mapAddress))
        (consumer.session, observed.producerThunk)).bind fun producer =>
          if checkCacheIsValue producer.cell.record.cache &&
            producer.serial == observed.producerUpdate &&
            decide (producer.serial.toNat < consumer.serial.toNat) then some producer else none) =
        ((latestHistory? rows (consumer.session, observed.producerThunk)).bind fun producer =>
          if checkCacheIsValue producer.cell.record.cache &&
            producer.serial == observed.producerUpdate &&
            decide (producer.serial.toNat < consumer.serial.toNat) then some producer else none).map
              (mapHistoryRow mapAddress)
      rw [latestHistory?_map]
      cases found : latestHistory? rows (consumer.session, observed.producerThunk) with
      | none => rfl
      | some producer =>
          simp only [Option.map_some, Option.bind_some]
          simp only [mapHistoryRow, NeedRepresentation.Mapping.mapRecord, checkCacheIsValue_map]
          by_cases checked : (checkCacheIsValue producer.cell.record.cache &&
            producer.serial == observed.producerUpdate &&
            decide (producer.serial.toNat < consumer.serial.toNat)) = true
          · simp [checked, mapHistoryRow]
            have fields := Bool.and_eq_true_iff.mp checked
            have first := Bool.and_eq_true_iff.mp fields.1
            refine ⟨⟨⟨first.1, (beq_iff_eq).mp first.2⟩, ?_⟩, rfl⟩
            exact decide_eq_true (of_decide_eq_true fields.2)
          · simp [checked]
            intro value serial
            cases earlier : decide (producer.serial.toNat < consumer.serial.toNat) with
            | false => exact decide_eq_false (of_decide_eq_false earlier)
            | true =>
                exfalso
                apply checked
                simpa only [Bool.and_eq_true, beq_iff_eq] using And.intro (And.intro value serial) earlier

theorem forwardedValueSource?_map (mapAddress : Address → Address) (rows : List HistoryRow)
    (key : BitVec 64 × BitVec 64) :
    forwardedValueSource? (rows.map (mapHistoryRow mapAddress)) key =
      (forwardedValueSource? rows key).map (mapHistoryRow mapAddress) := by
  unfold forwardedValueSource?
  rw [latestHistory?_map]
  cases latest : latestHistory? rows key with
  | none => rfl
  | some consumer => simp [checkProducerRow?_map]

private theorem cacheTagOf_map (mapAddress : Address → Address)
    (cache : NeedReference.Cache Address Address) :
    cacheTagOf ((borrowedHistoryMapping mapAddress).mapCache cache) = cacheTagOf cache := by
  cases cache <;> rfl

theorem checkHistoryMetadata_map (mapAddress : Address → Address) (row : HistoryRow) :
    checkHistoryMetadata (mapHistoryRow mapAddress row) = checkHistoryMetadata row := by
  unfold checkHistoryMetadata
  simp only [mapHistoryRow, NeedRepresentation.Mapping.mapRecord, cacheTagOf_map]

theorem checkHistoryProducers_map (mapAddress : Address → Address) (rows : List HistoryRow) :
    checkHistoryProducers (rows.map (mapHistoryRow mapAddress)) = checkHistoryProducers rows := by
  induction rows with
  | nil => rfl
  | cons row older ih =>
      simp only [List.map_cons, checkHistoryProducers, ih]
      unfold checkHistoryProducerRow
      rw [checkHistoryMetadata_map]
      have metadataMapped : (mapHistoryRow mapAddress row).cell.valueProvenance =
          row.cell.valueProvenance := rfl
      rw [metadataMapped]
      simp only [checkProducerRow?_map, Option.isSome_map]

theorem StableHistoryMetadata_map (mapAddress : Address → Address)
    {left right : HistoryRow} (same : StableHistoryMetadata left right) :
    StableHistoryMetadata (mapHistoryRow mapAddress left) (mapHistoryRow mapAddress right) := by
  simp only [StableHistoryMetadata, stableHistoryFields, Prod.mk.injEq] at same
  obtain ⟨authority, storage, imported, occurrence, argument, captures⟩ := same
  simp only [StableHistoryMetadata, stableHistoryFields, mapHistoryRow, Prod.mk.injEq]
  refine ⟨authority, storage, imported, occurrence, argument, ?_⟩
  simpa only [Option.map_map, Function.comp_def] using captures

theorem HistoryMetadataContinuous_map (mapAddress : Address → Address) {rows : List HistoryRow}
    (valid : HistoryMetadataContinuous rows) :
    HistoryMetadataContinuous (rows.map (mapHistoryRow mapAddress)) := by
  induction rows with
  | nil => trivial
  | cons row older ih =>
      refine ⟨?_, ih valid.2⟩
      intro previous found
      have latest := (latestHistory?_iff _ _ _).mpr found
      rw [latestHistory?_map, mapHistoryRow_key] at latest
      obtain ⟨original, originalFound, equal⟩ := Option.map_eq_some_iff.mp latest
      cases equal
      exact StableHistoryMetadata_map mapAddress
        (valid.1 original ((latestHistory?_iff _ _ _).mp originalFound))

namespace ReadbackControls

private def view (tag evaluator : BitVec 64) (cached : Option Address)
    (tail : List TargetValue := [])
    (metadata : Option (BitVec 64 × BitVec 64 × BitVec 64) := none) : TargetValue :=
  .record "NeedCellView"
    ([.word tag] ++ (match metadata with
      | none => []
      | some (role, thunk, update) => [.word role, .word thunk, .word update]) ++
     [.reference (some ViewControls.payload), .reference cached,
      .word 101, .word evaluator, .word 0, .word 109, .word 113, .word 127] ++ tail)

theorem suspended_readback :
    (readCellView? false (view 0 0 none)).map (·.record.cache) = some .suspended := rfl

theorem evaluating_readback :
    (readCellView? false (view 1 103 none)).map (·.record.cache) =
      some (.evaluating 103) := rfl

theorem completed_readback_preserves_alias_and_metadata :
    let result := readCellView? false (view 2 0 (some ViewControls.payload))
    result.map (·.record) = some ⟨ViewControls.payload, .value ViewControls.payload⟩ ∧
      result.map (·.authority) = some 101 ∧ result.map (·.storage) = some 0 ∧
      result.map (·.occurrence) = some 113 ∧ result.map (·.argument) = some 127 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem stable_fault_readback :
    (readCellView? false (view 3 0 (some ViewControls.payload))).map (·.record.cache) =
      some (.stableFault ViewControls.payload) := rfl

theorem stale_evaluator_role_rejected :
    readCellView? false (view 2 103 (some ViewControls.payload)) = none := rfl

theorem missing_completed_payload_rejected :
    readCellView? false (view 2 0 none) = none := rfl

theorem invalid_cache_tag_rejected :
    readCellView? false (view 4 0 none) = none := rfl

theorem wrong_capture_configuration_rejected :
    readCellView? true (view 0 0 none) = none ∧
      readCellView? false (view 0 0 none [.bool true, .reference none, .word 0]) = none :=
  ⟨rfl, rfl⟩

theorem capture_metadata_retained :
    (readCellView? true (view 0 0 none [.bool true, .reference none, .word 0])).map
      (·.captures) = some (some (true, none, 0)) := rfl

theorem extended_completed_metadata_retained :
    (readCellViewWithProvenance? false true
      (view 2 0 (some ViewControls.payload) [] (some (1, 211, 223)))).map
      (·.valueProvenance) = some (some ⟨.ready, 211, 223⟩) := rfl

theorem demand_role_is_distinct_from_completion :
    (readCellViewWithProvenance? false true
      (view 2 0 (some ViewControls.payload) [] (some (0, 0, 0)))).map
      (·.valueProvenance) = some (some ⟨.demandResult, 0, 0⟩) := rfl

theorem malformed_value_role_rejected :
    readCellViewWithProvenance? false true
      (view 2 0 (some ViewControls.payload) [] (some (2, 211, 223))) = none ∧
    readCellViewWithProvenance? false true
      (view 3 0 (some ViewControls.payload) [] (some (1, 0, 0))) = none := ⟨rfl, rfl⟩

theorem malformed_producer_pair_rejected :
    readCellViewWithProvenance? false true
      (view 2 0 (some ViewControls.payload) [] (some (0, 0, 223))) = none ∧
    readCellViewWithProvenance? false true
      (view 2 0 (some ViewControls.payload) [] (some (0, 211, 0))) = none ∧
    readCellViewWithProvenance? false true
      (view 3 0 (some ViewControls.payload) [] (some (0, 211, 223))) = none :=
  ⟨rfl, rfl, rfl⟩

/-- A matching payload alias and producer thunk do not identify a producer
update: changing its serial remains observable in the checked metadata. -/
theorem changed_producer_update_is_observable :
    let first := readCellViewWithProvenance? false true
      (view 2 0 (some ViewControls.payload) [] (some (1, 211, 223)))
    let second := readCellViewWithProvenance? false true
      (view 2 0 (some ViewControls.payload) [] (some (1, 211, 224)))
    first.map (·.record) = second.map (·.record) ∧
      first.map (·.valueProvenance) = some (some ⟨.ready, 211, 223⟩) ∧
      second.map (·.valueProvenance) = some (some ⟨.ready, 211, 224⟩) ∧
      first.map (·.valueProvenance) ≠ second.map (·.valueProvenance) := by
  exact ⟨rfl, rfl, rfl, by decide⟩

theorem wrong_provenance_configuration_rejected :
    readCellViewWithProvenance? false true (view 2 0 (some ViewControls.payload)) = none ∧
    readCellView? false
      (view 2 0 (some ViewControls.payload) [] (some (1, 211, 223))) = none := ⟨rfl, rfl⟩

/-- Observe the result of the actual admitted view invocation, including its
parameter-frame allocation and teardown, rather than a separately built view. -/
theorem original_invocation_readback (captures heapIndex : Bool)
    (heap : TargetHeapSemantics Nat) (calls : TargetCalls Nat) (result : TargetRawResult Nat)
    (ran : TargetFunctionBody (viewRepresentation captures heapIndex).interface heap calls
      (viewFunction captures)
      [.reference (some ViewControls.source), .reference (some ViewControls.destination)]
      (ViewControls.state captures heapIndex) result) :
    ((targetRead result.state.memory ViewControls.destination).bind (readCellView? captures)).map
      (·.record) = some ⟨ViewControls.payload, .value ViewControls.payload⟩ := by
  have sourceLive : ∃ value, targetRead (ViewControls.state captures heapIndex).memory
      ViewControls.source = some value := ⟨ViewControls.frameValue captures heapIndex, by rfl⟩
  have destinationLive : ∃ value, targetRead (ViewControls.state captures heapIndex).memory
      ViewControls.destination = some value := ⟨ViewControls.emptyView captures, by rfl⟩
  obtain ⟨_, memory, copied, resultEq⟩ :=
    (view_invocation_exact captures heapIndex heap calls (ViewControls.state captures heapIndex)
      ViewControls.source ViewControls.destination sourceLive destinationLive result).mp ran
  have observed :
      ((ViewControls.copied captures heapIndex).bind (fun after =>
        (targetRead after ViewControls.destination).bind (readCellView? captures))).map
        (·.record) = some ⟨ViewControls.payload, .value ViewControls.payload⟩ := by
    cases captures <;> cases heapIndex <;> rfl
  change ViewControls.copied captures heapIndex = some memory at copied
  rw [copied] at observed
  simpa only [resultEq, Option.bind_some] using observed

/-- The full admitted extended invocation preserves borrowed aliases and the
exact producer update through parameter entry, ordered stores and teardown. -/
theorem extended_invocation_readback (captures heapIndex : Bool)
    (heap : TargetHeapSemantics Nat) (calls : TargetCalls Nat) (result : TargetRawResult Nat)
    (ran : TargetFunctionBody (viewRepresentation captures heapIndex true).interface heap calls
      (viewFunction captures true)
      [.reference (some ViewControls.source), .reference (some ViewControls.destination)]
      (ViewControls.state captures heapIndex true) result) :
    let read := (targetRead result.state.memory ViewControls.destination).bind
      (readCellViewWithProvenance? captures true)
    read.map (·.record) = some ⟨ViewControls.payload, .value ViewControls.payload⟩ ∧
      read.map (·.valueProvenance) = some (some ⟨.ready, 211, 223⟩) ∧
      read.map (·.authority) = some 101 ∧ read.map (·.occurrence) = some 113 ∧
      read.map (·.argument) = some 127 := by
  have sourceLive : ∃ value, targetRead (ViewControls.state captures heapIndex true).memory
      ViewControls.source = some value := ⟨ViewControls.frameValue captures heapIndex true, rfl⟩
  have destinationLive : ∃ value, targetRead (ViewControls.state captures heapIndex true).memory
      ViewControls.destination = some value := ⟨ViewControls.emptyView captures true, rfl⟩
  obtain ⟨_, memory, copied, resultEq⟩ :=
    (view_invocation_exact (provenance := true) captures heapIndex heap calls
      (ViewControls.state captures heapIndex true) ViewControls.source ViewControls.destination
      sourceLive destinationLive result).mp ran
  have observed :
      let read := (ViewControls.copied captures heapIndex true).bind (fun after =>
        (targetRead after ViewControls.destination).bind (readCellViewWithProvenance? captures true))
      read.map (·.record) = some ⟨ViewControls.payload, .value ViewControls.payload⟩ ∧
        read.map (·.valueProvenance) = some (some ⟨.ready, 211, 223⟩) ∧
        read.map (·.authority) = some 101 ∧ read.map (·.occurrence) = some 113 ∧
        read.map (·.argument) = some 127 := by
    cases captures <;> cases heapIndex <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  change ViewControls.copied captures heapIndex true = some memory at copied
  rw [copied] at observed
  simpa only [resultEq, Option.bind_some] using observed

end ReadbackControls

namespace HistoryControls

private def naming : (BitVec 64 × BitVec 64) ↪ NeedReference.CellId where
  toFun key := ⟨key.1.toNat, [17, 19], key.2.toNat, 23⟩
  inj' := by
    intro left right equal
    apply Prod.ext
    · exact BitVec.eq_of_toNat_eq (congrArg NeedReference.CellId.lineage equal)
    · exact BitVec.eq_of_toNat_eq (congrArg NeedReference.CellId.slot equal)

/-- Finite opaque payload and uint64-array observations for the controls;
this fixture is not a decoder for the concrete C Atom object graph. -/
private def memory : TargetMemory :=
  ⟨fun storage position =>
    if storage = 8 ∨ storage = 9 then
      if position = 0 then some (.record "Atom" [.word 211]) else none
    else if storage = 10 then
      if position = 0 then some (.record "Atom" [.word 212]) else none
    else if storage = 19 ∨ storage = 20 then
      if position < 3 then some (.word (BitVec.ofNat 64 (position + 1))) else none
    else if storage = 21 then
      if position < 3 then some (.word (if position = 2 then 4 else BitVec.ofNat 64 (position + 1))) else none
    else none,
   fun storage => if storage = 8 ∨ storage = 9 ∨ storage = 10 then some 1
     else if storage = 19 ∨ storage = 20 ∨ storage = 21 then some 3 else none⟩

private def readOrigin (address : Address) : Option (BitVec 64) :=
  match targetRead memory address with
  | some (.record "Atom" [.word content]) => some content
  | _ => none

private def rawRow (serial thunk depth tag evaluator : BitVec 64) (cached : Option Address)
    (role producer update : BitVec 64) (session : BitVec 64 := 7)
    (origin : Address := ViewControls.payload) (authority : BitVec 64 := 101)
    (storage : BitVec 64 := 0) (imported : BitVec 64 := 109)
    (occurrence : BitVec 64 := 113) (argument : BitVec 64 := 127)
    (provenance : Bool := true) (captures : Bool := false)
    (captureKnown : Bool := true) (captureIds : Option Address := some ⟨19, 0, []⟩)
    (captureCount : BitVec 64 := 3) : TargetValue :=
  .record "NeedHistoryView" [.word session, .word serial, .word thunk, .word depth,
    .record "NeedCellView" ([.word tag] ++
      (if provenance then [.word role, .word producer, .word update] else []) ++
      [.reference (some origin), .reference cached, .word authority, .word evaluator,
       .word storage, .word imported, .word occurrence, .word argument] ++
      (if captures then [.bool captureKnown, .reference captureIds, .word captureCount] else []))]

private def older (provenance : Bool) (captures : Bool) : List TargetValue :=
  let row := fun serial thunk depth tag evaluator cached role producer update =>
    rawRow serial thunk depth tag evaluator cached role producer update
      (provenance := provenance) (captures := captures)
  [row 7 13 7 1 203 none 0 0 0,
   row 6 13 6 0 0 none 0 0 0,
   row 5 11 5 2 0 (some ViewControls.payload) 1 0 0,
   row 4 11 4 1 201 none 0 0 0,
   row 3 11 3 0 0 none 0 0 0,
   row 2 11 2 1 199 none 0 0 0,
   row 1 11 1 0 0 none 0 0 0]

private def configuredHistory (provenance captures : Bool) : List TargetValue :=
  rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5
    (provenance := provenance) (captures := captures) :: older provenance captures

private def history : List TargetValue :=
  configuredHistory true false

private def currentProducer (raw : List TargetValue) : Option HistoryRow :=
  (raw.mapM (readHistoryRow? false true)).bind (fun rows => forwardedValueSource? rows (7, 13))

theorem complete_retry_history_accepted :
    (readHistory? false true 7 8 naming readOrigin memory history).isSome = true := by decide

theorem all_history_view_profiles_accepted (provenance captures : Bool) :
    (readHistory? captures provenance 7 8 naming readOrigin memory (configuredHistory provenance captures)).isSome = true := by
  cases provenance <;> cases captures <;> decide

theorem every_update_and_retry_is_retained :
    (readHistory? false true 7 8 naming readOrigin memory history).map (fun result => result.1.length) = some 8 ∧
      (readHistory? false true 7 8 naming readOrigin memory history).map (fun result => result.2.length) = some 8 := by
  exact ⟨by decide, by decide⟩

theorem exact_current_producer_update_retained :
    (currentProducer history).map (·.key) = some (7, 11) ∧
      (currentProducer history).map (·.serial) = some 5 ∧
      (currentProducer history).map (·.cell.record.cache) =
        some (.value ViewControls.payload) := by
  exact ⟨by decide, by decide, by decide⟩

theorem truncated_inventory_rejected :
    readHistory? false true 7 8 naming readOrigin memory (history.take 7) = none ∧
      readHistory? false true 7 7 naming readOrigin memory (history.take 7) = none := by
  exact ⟨by decide, by decide⟩

theorem foreign_session_rejected :
    readHistory? false true 8 8 naming readOrigin memory history = none ∧
      currentProducer [rawRow 8 13 2 2 0 (some ViewControls.payload) 1 11 5,
        rawRow 5 11 1 2 0 (some ViewControls.payload) 1 0 0 8] = none := by
  exact ⟨by decide, by decide⟩

theorem changed_origin_rejected :
    readHistory? false true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5 7 ⟨10, 0, []⟩ :: older true false) = none :=
  by decide

theorem suffix_copy_origin_content_is_retained :
    (readHistory? false true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5 7 ⟨9, 0, []⟩ ::
        older true false)).isSome = true := by decide

theorem duplicated_capture_arrays_are_accepted :
    (readHistory? true true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5
        (captures := true) (captureIds := some ⟨20, 0, []⟩) :: older true true)).isSome = true := by
  decide

theorem distinct_capture_pointers_have_equal_contents :
    (⟨19, 0, []⟩ : Address) ≠ ⟨20, 0, []⟩ ∧
      readCaptureContents? memory (some (true, some ⟨19, 0, []⟩, 3)) =
        readCaptureContents? memory (some (true, some ⟨20, 0, []⟩, 3)) := by
  exact ⟨by decide, by decide⟩

theorem changed_capture_word_rejected :
    readHistory? true true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5
        (captures := true) (captureIds := some ⟨21, 0, []⟩) :: older true true) = none := by
  decide

theorem sibling_update_rejected :
    currentProducer [rawRow 8 13 2 2 0 (some ViewControls.payload) 1 11 5,
      rawRow 4 11 1 2 0 (some ViewControls.payload) 1 0 0] = none := by decide

theorem stale_current_update_rejected :
    currentProducer
      (rawRow 9 11 9 2 0 (some ViewControls.payload) 1 0 0 :: history) = none := by decide

/-- A later update cannot rewrite the earlier consumer's recorded world. -/
theorem historical_suffix_survives_later_update :
    (readHistory? false true 7 9 naming readOrigin memory
      (rawRow 9 11 9 2 0 (some ViewControls.payload) 1 0 0 :: history)).isSome = true := by
  decide

theorem malformed_role_rejected :
    readHistory? false true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 2 11 5 :: older true false) = none ∧
      readHistory? false true 7 8 naming readOrigin memory
        (rawRow 8 13 8 3 0 (some ViewControls.payload) 1 11 5 :: older true false) = none := by
  exact ⟨by decide, by decide⟩

theorem self_producer_rejected :
    readHistory? false true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 13 5 :: older true false) = none := by decide

theorem split_authority_rejected :
    readHistory? false true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5 (authority := 102) ::
        older true false) = none := by decide

theorem changed_storage_import_and_occurrence_rejected :
    readHistory? false true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5 (storage := 1) ::
        older true false) = none ∧
    readHistory? false true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5 (imported := 110) ::
        older true false) = none ∧
    readHistory? false true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5 (occurrence := 114) ::
        older true false) = none ∧
    readHistory? false true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5 (argument := 128) ::
        older true false) = none := by
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem changed_capture_metadata_rejected :
    readHistory? true true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5
        (captures := true) (captureKnown := false) :: older true true) = none ∧
    readHistory? true true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5
        (captures := true) (captureIds := none) :: older true true) = none ∧
    readHistory? true true 7 8 naming readOrigin memory
      (rawRow 8 13 8 2 0 (some ViewControls.payload) 1 11 5
        (captures := true) (captureCount := 4) :: older true true) = none := by
  exact ⟨by decide, by decide, by decide⟩

theorem producer_not_earlier_rejected :
    currentProducer [rawRow 8 13 2 2 0 (some ViewControls.payload) 1 11 8,
      rawRow 8 11 1 2 0 (some ViewControls.payload) 1 0 0] = none := by decide

private def guardProducer : Address := ⟨31, 0, []⟩
private def guardConsumer : Address := ⟨32, 0, []⟩

private def guardFrame (tag selected : BitVec 64) : TargetFrame :=
  ⟨47, 0, [], [1, 2, 3, 4], fun identity =>
    if identity = 1 then some (.record "NeedCellView" [.word tag])
    else if identity = 2 then some (.record "NeedCellView" [.word 2, .word 1, .word 11, .word selected])
    else if identity = 3 then some (.reference (some guardProducer))
    else if identity = 4 then some (.reference (some guardConsumer)) else none⟩

private def guardState (producerSerial consumerSerial : Option (BitVec 64)) : TargetState Nat :=
  ⟨⟨fun storage position => if position = 0 then
      if storage = 31 then producerSerial.map (fun serial =>
        .record "NeedFrame" (List.replicate 10 (.word 0) ++ [.word serial]))
      else if storage = 32 then consumerSerial.map (fun serial =>
        .record "NeedFrame" (List.replicate 10 (.word 0) ++ [.word serial])) else none
    else none,
    fun storage => if storage = 31 then producerSerial.map (fun _ => 1)
      else if storage = 32 then consumerSerial.map (fun _ => 1) else none⟩,
    none, true, false, 37, AllocatorStats.targetEmpty⟩

private theorem guard_frame_bound (tag selected : BitVec 64) :
    TemporaryNamesBound (guardFrame tag selected) 4 := by
  intro identity live
  have found : identity = 1 ∨ identity = 2 ∨ identity = 3 ∨ identity = 4 := by
    simpa [guardFrame, List.contains_iff_mem] using live
  omega

private theorem guard_frame_scoped (tag selected : BitVec 64) :
    TemporariesScoped (guardFrame tag selected) := by
  intro identity absent
  simp_all [guardFrame]

theorem admitted_guard_accepts_exact_earlier_update (captures heapIndex : Bool)
    (heap : TargetHeapSemantics Nat) (calls : TargetCalls Nat) :
    TargetRun (viewRepresentation captures heapIndex true).interface heap calls .bool producerGuardCode
      producerGuardCode (guardFrame 2 5) (guardState (some 5) (some 8))
      ⟨.normal, producerGuardFrame (guardFrame 2 5) (guardState (some 5) (some 8))
        guardProducer guardConsumer 2 5 5 8, guardState (some 5) (some 8)⟩ ∧
    TargetAtomEval (viewRepresentation captures heapIndex true).interface
      (producerGuardFrame (guardFrame 2 5) (guardState (some 5) (some 8))
        guardProducer guardConsumer 2 5 5 8) (guardState (some 5) (some 8))
      (.temporary 12 .bool) (.bool false) := by
  constructor
  · apply (producer_guard_execution_exact (guard_frame_bound 2 5) (guard_frame_scoped 2 5)
      (.temporary rfl (by decide)) (.temporary rfl (by decide)) rfl
      (.temporary rfl (by decide)) (.temporary rfl (by decide)) (fun _ => rfl)
      (fun _ _ => rfl) producerGuardCode _).mpr rfl
  · exact producer_guard_frame_read captures heapIndex _ _ _ _ 2 5 5 8

theorem admitted_guard_nonvalue_skips_missing_serials (captures heapIndex : Bool)
    (heap : TargetHeapSemantics Nat) (calls : TargetCalls Nat) :
    targetRead (guardState none none).memory (sourceFieldAddress guardProducer 10) = none ∧
    targetRead (guardState none none).memory (sourceFieldAddress guardConsumer 10) = none ∧
    TargetRun (viewRepresentation captures heapIndex true).interface heap calls .bool producerGuardCode
      producerGuardCode (guardFrame 1 5) (guardState none none)
      ⟨.normal, producerGuardFrame (guardFrame 1 5) (guardState none none)
        guardProducer guardConsumer 1 5 5 8, guardState none none⟩ ∧
    TargetAtomEval (viewRepresentation captures heapIndex true).interface
      (producerGuardFrame (guardFrame 1 5) (guardState none none) guardProducer guardConsumer 1 5 5 8)
      (guardState none none) (.temporary 12 .bool) (.bool true) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · apply (producer_guard_execution_exact (guard_frame_bound 1 5) (guard_frame_scoped 1 5)
      (.temporary rfl (by decide)) (.temporary rfl (by decide)) rfl
      (.temporary rfl (by decide)) (.temporary rfl (by decide))
      (fun wrong => False.elim (by simp at wrong))
      (fun wrong _ => False.elim (by simp at wrong)) producerGuardCode _).mpr rfl
  · exact producer_guard_frame_read captures heapIndex _ _ _ _ 1 5 5 8

theorem admitted_guard_changed_update_skips_missing_consumer (captures heapIndex : Bool)
    (heap : TargetHeapSemantics Nat) (calls : TargetCalls Nat) :
    targetRead (guardState (some 6) none).memory (sourceFieldAddress guardConsumer 10) = none ∧
    TargetRun (viewRepresentation captures heapIndex true).interface heap calls .bool producerGuardCode
      producerGuardCode (guardFrame 2 5) (guardState (some 6) none)
      ⟨.normal, producerGuardFrame (guardFrame 2 5) (guardState (some 6) none)
        guardProducer guardConsumer 2 6 5 8, guardState (some 6) none⟩ ∧
    TargetAtomEval (viewRepresentation captures heapIndex true).interface
      (producerGuardFrame (guardFrame 2 5) (guardState (some 6) none) guardProducer guardConsumer 2 6 5 8)
      (guardState (some 6) none) (.temporary 12 .bool) (.bool true) := by
  refine ⟨rfl, ?_, ?_⟩
  · apply (producer_guard_execution_exact (guard_frame_bound 2 5) (guard_frame_scoped 2 5)
      (.temporary rfl (by decide)) (.temporary rfl (by decide)) rfl
      (.temporary rfl (by decide)) (.temporary rfl (by decide)) (fun _ => rfl)
      (fun _ wrong => False.elim (by simp at wrong)) producerGuardCode _).mpr rfl
  · exact producer_guard_frame_read captures heapIndex _ _ _ _ 2 6 5 8

end HistoryControls

namespace NativeCapabilities.Controls

private def origin : Address := ⟨211, 0, []⟩
private def result : Address := ⟨212, 0, []⟩

private def row (authority serial : BitVec 64)
    (cache : NeedReference.Cache Address Address) : HistoryRow :=
  ⟨7, serial, 11, 1,
    ⟨⟨origin, cache⟩, authority, 0, 37, 41, 43, 47, none, none⟩⟩

private def capability (rights : BitVec 64) : View := ⟨7, 11, 101, rights⟩

theorem inspect_is_not_force_even_after_completion :
    lookup? 7 [row 101 3 (.value result)] (capability 2) 2 =
      some (row 101 3 (.value result)) ∧
    lookup? 7 [row 101 3 (.value result)] (capability 2) 1 = none := by decide

theorem permission_does_not_require_a_completed_cache :
    lookup? 7 [row 101 1 .suspended] (capability 3) 1 = some (row 101 1 .suspended) := by
  decide

theorem same_cell_coordinates_in_a_sibling_do_not_supply_authority :
    lookup? 7 [row 103 3 (.value result)] (capability 3) 1 = none ∧
    lookup? 7 [row 101 3 (.value result)] (capability 3) 1 =
      some (row 101 3 (.value result)) := by decide

theorem newer_mismatching_authority_does_not_fall_back :
    lookup? 7 [row 103 4 (.value result), row 101 3 (.value result)] (capability 3) 1 =
      none := by decide

theorem selected_snapshot_and_nonempty_rights_are_required :
    lookup? 8 [row 101 3 (.value result)] (capability 3) 1 = none ∧
    lookup? 7 [] (capability 3) 1 = none ∧
    lookup? 7 [row 101 3 (.value result)] (capability 3) 0 = none ∧
    lookup? 7 [row 101 3 (.value result)] (capability 3) 4 = none := by decide

theorem attenuation_retains_identity_and_cannot_restore_force :
    restrict? 7 [row 101 3 (.value result)] (capability 3) 2 = some (capability 2) ∧
    restrict? 7 [row 101 3 (.value result)] (capability 2) 1 = none ∧
    restrict? 7 [row 101 3 (.value result)] (capability 2) 3 = none := by decide

private def capRecord (rights : BitVec 64) : TargetValue :=
  .record "CettaPrimeNeedCapability" [.word 7, .word 11, .word 101, .word rights]

private def memory (kind tag rights : BitVec 64) : TargetMemory :=
  ⟨fun storage index =>
    if index ≠ 0 then none else
    if storage = 201 then some (.record "Atom"
      [.word kind, .word 0, .word 0, .word 0, .word 0, .reference none, .word 0, .word 0,
       .record "ground" [.word tag, .unit, .reference (some ⟨202, 0, []⟩)]])
    else if storage = 202 then some (capRecord rights) else none,
   fun storage => if storage = 201 ∨ storage = 202 then some 1 else none⟩

private def operand (epoch kind : BitVec 64) : NativeFrames.BindingValueView :=
  ⟨some ⟨201, 0, []⟩, epoch, kind⟩

theorem tagged_native_read_preserves_inspection_rights :
    readAtom? (memory 2 10 2) (operand 0 0) = some (capability 2) ∧
    readAtom? (memory 2 10 2) (operand (NativeFrames.encode ⟨5, 2⟩) 2) =
      some (capability 2) := by decide

theorem written_or_wrongly_tagged_data_cannot_forge_capabilities :
    readAtom? (memory 3 10 3) (operand 0 0) = none ∧
    readAtom? (memory 2 11 3) (operand 0 0) = none ∧
    readAtom? (memory 2 10 0) (operand 0 0) = none ∧
    readAtom? (memory 2 10 4) (operand 0 0) = none := by decide

/-- The capability check uses the same actual row reconstructed by the complete
history reader, retaining its pending retry history and original cached address. -/
theorem checked_history_selects_original_producer :
    (readHistory? false true 7 8 HistoryControls.naming HistoryControls.readOrigin
      HistoryControls.memory HistoryControls.history).bind
      (fun (rows, _) => (lookup? 7 rows (capability 2) 2).map
        (fun selected => (selected.key, selected.serial, selected.cell.record.cache))) =
      some ((7, 11), 5, .value ViewControls.payload) := by decide

end NativeCapabilities.Controls

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory

section PhysicalAtomLayerReadback

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps (Address TargetValue TargetMemory targetRead targetReadPath sourceFieldAddress)
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

theorem variable_layer_from_owned_memory {World Ground : Type}
    (inventory : World → Inventory) (heaps : World → Heap L)
    (readGround : NativePayload.Cursor World → Option Ground)
    (cursor : NativePayload.Cursor World) (atom : Ptr) (identifier : UInt64)
    (valid : cursor.value.Admissible)
    (pointer : cursor.value.skeleton = some (CurrentValueRead.physicalAddress atom))
    (registered : inventory cursor.world atom = some .atom) (rest : Heap L → Prop)
    (owned : (PointsTo atom (.u32 1) ∗ PointsTo (atom + 2) (.u64 identifier) ∗ rest)
      (heaps cursor.world)) :
    NativePayload.readLayer? (fun world => memory (inventory world) (heaps world))
      readGround cursor =
      (cursor.value.variableId? identifier.toBitVec).map
        (fun identity => (NativePayload.Label.variable identity, [])) := by
  have record := variable_record_owned atom identifier rest (heaps cursor.world) owned
  have tag := field_from_registered_record (inventory cursor.world) (heaps cursor.world)
    atom (variableRecord identifier) 0 registered record
  have identity := field_from_registered_record (inventory cursor.world) (heaps cursor.world)
    atom (variableRecord identifier) 2 registered record
  simp only [variableRecord, targetReadPath, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.bind_some] at tag identity
  simp [NativePayload.readLayer?, valid, pointer, tag, readVariableId?, identity]

theorem symbol_layer_from_owned_memory {World Ground : Type}
    (inventory : World → Inventory) (heaps : World → Heap L)
    (readGround : NativePayload.Cursor World → Option Ground)
    (cursor : NativePayload.Cursor World) (atom : Ptr) (identifier : UInt32)
    (spelling : Option Ptr) (nonzero : identifier ≠ 0) (valid : cursor.value.Admissible)
    (pointer : cursor.value.skeleton = some (CurrentValueRead.physicalAddress atom))
    (registered : inventory cursor.world atom = some .atom) (rest : Heap L → Prop)
    (owned : (PointsTo atom (.u32 0) ∗ PointsTo (atom + 3) (.u32 identifier) ∗
      PointsTo (atom + 5) (.ptr spelling) ∗ rest) (heaps cursor.world)) :
    NativePayload.readLayer? (fun world => memory (inventory world) (heaps world))
      readGround cursor =
      some (NativePayload.Label.symbol (BitVec.ofNat 64 identifier.toNat), []) := by
  have record := symbol_record_owned atom identifier spelling rest (heaps cursor.world) owned
  have tag := field_from_registered_record (inventory cursor.world) (heaps cursor.world)
    atom (symbolRecord identifier spelling) 0 registered record
  have number := field_from_registered_record (inventory cursor.world) (heaps cursor.world)
    atom (symbolRecord identifier spelling) 3 registered record
  simp only [symbolRecord, targetReadPath, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.bind_some] at tag number
  have bounded := identifier.toNat_lt
  have widened : (BitVec.ofNat 64 identifier.toNat).toNat = identifier.toNat := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have notZero : (BitVec.ofNat 64 identifier.toNat) ≠ 0 := by
    intro zero
    have := congrArg BitVec.toNat zero
    simp only [widened] at this
    apply nonzero
    exact UInt32.toNat_inj.mp this
  simp [NativePayload.readLayer?, NativePayload.readSymbol?, valid, pointer, tag, number,
    widened, bounded]
  intro impossible
  exact (notZero impossible).elim

theorem expression_header_from_owned_memory (inventory : Inventory) (heap : Heap L)
    (parent : BindingValueView) (atom : Ptr) (elements : Option Ptr) (count : UInt64)
    (valid : parent.Admissible)
    (pointer : parent.skeleton = some (CurrentValueRead.physicalAddress atom))
    (registered : inventory atom = some .atom) (rest : Heap L → Prop)
    (owned : (PointsTo atom (.u32 3) ∗ PointsTo (atom + 8) (.ptr elements) ∗
      PointsTo (atom + 9) (.u64 count) ∗ rest) heap) :
    expressionView? (memory inventory heap) parent =
      some (elements.map CurrentValueRead.physicalAddress, count.toBitVec) := by
  have record := expression_record_owned atom elements count rest heap owned
  have tag := field_from_registered_record inventory heap atom
    (expressionRecord elements count) 0 registered record
  have arm := field_from_registered_record inventory heap atom
    (expressionRecord elements count) 8 registered record
  simp only [expressionRecord, targetReadPath, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.bind_some] at tag arm
  simp [expressionView?, valid, pointer, tag, arm]

theorem expression_children_from_owned_memory (inventory : Inventory) (heap : Heap L)
    (parent : BindingValueView) (atom elements : Ptr) (count : UInt64)
    (pointers : Fin count.toNat → Option Ptr)
    (valid : parent.Admissible)
    (pointer : parent.skeleton = some (CurrentValueRead.physicalAddress atom))
    (registered : inventory atom = some .atom)
    (arrayRegistered : ∀ index : Fin count.toNat,
      inventory (elements + index.val) = some .pointerCell)
    (rest : Heap L → Prop)
    (owned : (PointsTo atom (.u32 3) ∗ PointsTo (atom + 8) (.ptr (some elements)) ∗
      PointsTo (atom + 9) (.u64 count) ∗
      Cells elements ((List.ofFn fun index => CVal.ptr (pointers index)).map some) ∗ rest) heap) :
    readExpressionChildren? (memory inventory heap) parent =
      some (List.ofFn fun index => parent.child
        ((pointers index).map CurrentValueRead.physicalAddress)) := by
  have header := expression_header_from_owned_memory inventory heap parent atom (some elements)
    count valid pointer registered
    (Cells elements ((List.ofFn fun index => CVal.ptr (pointers index)).map some) ∗ rest) owned
  apply (readExpressionChildren?_iff _ _ _).mpr
  refine ⟨some (CurrentValueRead.physicalAddress elements), count.toBitVec,
    (fun index => (pointers index).map CurrentValueRead.physicalAddress), header, ?_, rfl⟩
  intro index
  have cells : (Cells elements ((List.ofFn fun i => CVal.ptr (pointers i)).map some) ∗
      PointsTo atom (.u32 3) ∗ PointsTo (atom + 8) (.ptr (some elements)) ∗
      PointsTo (atom + 9) (.u64 count) ∗ rest) heap := by cmem_exact
  have observed := read_cells (p := elements)
    (cs := (List.ofFn fun i => CVal.ptr (pointers i)).map some)
    (i := index.val) (v := CVal.ptr (pointers index))
    (by simpa only [List.length_map, List.length_ofFn, UInt64.toNat_toBitVec] using index.isLt)
    (by simp) cells
  have cellRead : cell? heap (elements + index.val) = some (.ptr (pointers index)) := by
    exact congrArg Option.join observed
  apply (expressionElement?_iff _ _ _ _).mpr
  refine ⟨CurrentValueRead.physicalAddress elements, rfl, ?_⟩
  exact pointer_from_registered_read inventory heap (elements + index.val)
    (pointers index) (arrayRegistered index) cellRead

/-- The existing graph layer follows each physical pointer occurrence and
inherits both context fields and the selected world. Shared children are not
deduplicated, and no recursive heap decoder is introduced. -/
theorem expression_layer_from_owned_memory {World Ground : Type}
    (inventory : World → Inventory) (heaps : World → Heap L)
    (readGround : NativePayload.Cursor World → Option Ground)
    (cursor : NativePayload.Cursor World) (atom elements : Ptr) (count : UInt64)
    (pointers : Fin count.toNat → Option Ptr)
    (valid : cursor.value.Admissible)
    (pointer : cursor.value.skeleton = some (CurrentValueRead.physicalAddress atom))
    (registered : inventory cursor.world atom = some .atom)
    (arrayRegistered : ∀ index : Fin count.toNat,
      inventory cursor.world (elements + index.val) = some .pointerCell)
    (rest : Heap L → Prop)
    (owned : (PointsTo atom (.u32 3) ∗ PointsTo (atom + 8) (.ptr (some elements)) ∗
      PointsTo (atom + 9) (.u64 count) ∗
      Cells elements ((List.ofFn fun index => CVal.ptr (pointers index)).map some) ∗ rest)
      (heaps cursor.world)) :
    NativePayload.readLayer? (fun world => memory (inventory world) (heaps world))
      readGround cursor = some (NativePayload.Label.expression,
        List.ofFn fun index => cursor.child
          (cursor.value.child ((pointers index).map CurrentValueRead.physicalAddress))) := by
  have record := expression_record_owned atom (some elements) count
    (Cells elements ((List.ofFn fun index => CVal.ptr (pointers index)).map some) ∗ rest)
    (heaps cursor.world) owned
  have tag := field_from_registered_record (inventory cursor.world) (heaps cursor.world)
    atom (expressionRecord (some elements) count) 0 registered record
  simp only [expressionRecord, targetReadPath, List.getElem?_cons_zero, Option.bind_some] at tag
  rw [NativePayload.readLayer?_expression _ readGround cursor valid
    (CurrentValueRead.physicalAddress atom) pointer tag,
    expression_children_from_owned_memory (inventory cursor.world) (heaps cursor.world)
      cursor.value atom elements count pointers valid pointer registered arrayRegistered rest owned]
  simp only [Option.map_some, List.map_ofFn, Function.comp_def]

/-- The physical load program and the existing logical layer commute at the
reached heap. Only the retained cursor's own world is refreshed; observations
of every other world still use their previous memory. -/
theorem variable_program_layer_readback {World Ground : Type} [DecidableEq World]
    (inventory : World → Inventory) (before : World → TargetMemory)
    (readGround : NativePayload.Cursor World → Option Ground)
    (cursor : NativePayload.Cursor World) (atom : Ptr) (identifier : UInt64)
    (valid : cursor.value.Admissible)
    (pointer : cursor.value.skeleton = some (CurrentValueRead.physicalAddress atom))
    (registered : inventory cursor.world atom = some .atom) (rest : Heap L → Prop) :
    CTriple (PointsTo atom (.u32 1) ∗ PointsTo (atom + 2) (.u64 identifier) ∗ rest)
      (structuralProgram atom)
      (fun value reached => value = some (variableRecord identifier) ∧
        NativePayload.readLayer?
          (Function.update before cursor.world (memory (inventory cursor.world) reached))
          readGround cursor =
          (cursor.value.variableId? identifier.toBitVec).map
            (fun identity => (NativePayload.Label.variable identity, [])) ∧
        (PointsTo atom (.u32 1) ∗ PointsTo (atom + 2) (.u64 identifier) ∗ rest) reached) := by
  apply triple_post _ (variable_program_owned atom identifier rest)
  intro value reached result
  refine ⟨result.1, ?_, result.2⟩
  have localRead := variable_layer_from_owned_memory inventory (fun _ => reached)
    readGround cursor atom identifier valid pointer registered rest result.2
  simpa only [NativePayload.readLayer?, Function.update_self] using localRead


end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

end PhysicalAtomLayerReadback

section PhysicalAtomLiveReadback

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory
open Mettapedia.GSLT.LanguageDef.NativeOps (TargetMemory targetRead targetReadPath sourceFieldAddress)

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

theorem forwarded_layer_refuses {World Ground : Type}
    (inventory : World → Inventory) (heaps : World → Heap L)
    (readGround : NativePayload.Cursor World → Option Ground)
    (cursor : NativePayload.Cursor World) (atom : Ptr)
    (pointer : cursor.value.skeleton = some (CurrentValueRead.physicalAddress atom))
    (registered : inventory cursor.world atom = some .atom)
    (forwarded : word? (heaps cursor.world) (atom + 4) = some 4294967295) :
    NativePayload.readLayer? (fun world => liveMemory (inventory world) (heaps world))
      readGround cursor = none := by
  have refused := forwarded_is_not_admitted (inventory cursor.world) (heaps cursor.world)
    atom registered forwarded
  simp [NativePayload.readLayer?, pointer, liveMemory, targetRead, memory,
    sourceFieldAddress, CurrentValueRead.physicalAddress, refused]

/-- The admitted graph is the existing inventory checker applied to the
constructed physical memory view. World, binding context and duplicate edges
remain its original keys and child occurrences. -/
theorem physical_graph_observation {World Ground : Type} [DecidableEq World]
    (inventory : World → Inventory) (heaps : World → Heap L)
    (readGround : NativePayload.Cursor World → Option Ground)
    (cursors : List (NativePayload.Cursor World))
    (table : Mettapedia.Machines.RationalTermGraph.KeyedTable
      (NativePayload.Cursor World) (NativePayload.Label Ground))
    (read : NativePayload.readGraph?
      (fun world => liveMemory (inventory world) (heaps world)) readGround cursors = some table)
    (depth : Nat) (node : table.Node) :
    NativePayload.observeMemory (fun world => liveMemory (inventory world) (heaps world))
      readGround depth (table.key node) =
      some (Mettapedia.Machines.RationalTermGraph.observe table.graph depth node) := by
  exact NativePayload.readGraph?_observe read depth node

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

end PhysicalAtomLiveReadback

section PhysicalAtomSourceReadback

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory
open Mettapedia.Machines.RationalTermGraph
open Mettapedia.Languages.MeTTa.OSLFCore

/-- Current, world-indexed numbered-symbol API data. The native table/byte API
must supply this view; raw symbol_number is not itself a spelling decoder.
The injectivity law applies only within the selected current table. -/
structure NumberedSymbols (World : Type) where
  bytes : World → UInt32 → Option ByteArray
  unique : ∀ world first second spelling,
    bytes world first = some spelling → bytes world second = some spelling → first = second

/-- Only nonzero numbered symbols enter this source-String profile. Managed
ID-zero spellings need the explicit spelling pointer/length helper. UTF-8 is
checked without silently replacing invalid bytes or truncating at NUL. -/
def NumberedSymbols.name? {World : Type} (table : NumberedSymbols World)
    (world : World) (identifier : UInt32) : Option String := do
  if identifier = 0 then none else
    let bytes ← table.bytes world identifier
    String.fromUTF8? bytes

theorem NumberedSymbols.name?_zero {World : Type} (table : NumberedSymbols World)
    (world : World) : table.name? world 0 = none := by simp [NumberedSymbols.name?]

theorem NumberedSymbols.name?_exact {World : Type} (table : NumberedSymbols World)
    (world : World) (identifier : UInt32) (name : String)
    (decoded : table.name? world identifier = some name) :
    identifier ≠ 0 ∧ table.bytes world identifier = some name.toByteArray := by
  unfold NumberedSymbols.name? at decoded
  split at decoded
  · simp at decoded
  · next nonzero =>
    obtain ⟨bytes, stored, utf8⟩ := Option.bind_eq_some_iff.mp decoded
    have exactBytes := (Mettapedia.Data.String.ByteString.fromUTF8?_eq_some_iff bytes name).mp utf8
    exact ⟨nonzero, exactBytes ▸ stored⟩

theorem NumberedSymbols.name?_of_bytes {World : Type} (table : NumberedSymbols World)
    (world : World) (identifier : UInt32) (name : String) (nonzero : identifier ≠ 0)
    (stored : table.bytes world identifier = some name.toByteArray) :
    table.name? world identifier = some name := by
  simp [NumberedSymbols.name?, nonzero, stored,
    Mettapedia.Data.String.ByteString.fromUTF8?_encoded]

theorem NumberedSymbols.name?_injective {World : Type} (table : NumberedSymbols World)
    (world : World) (first second : UInt32) (name : String)
    (firstRead : table.name? world first = some name)
    (secondRead : table.name? world second = some name) : first = second := by
  exact table.unique world first second name.toByteArray
    (table.name?_exact world first name firstRead).2
    (table.name?_exact world second name secondRead).2

/-- Interpret an already-read finite observation, using the existing graph
traversal. This performs no heap traversal and does not expand resource-valued
grounded atoms. Leaf arity and depth exhaustion are checked explicitly. -/
def sourceObservation? {World : Type} (table : NumberedSymbols World) (world : World) :
    Observation (NativePayload.Label Empty) → Option Atom
  | .cut => none
  | .node (.symbol identifier) [] =>
      if identifier.toNat < 2 ^ 32 then
        (table.name? world (UInt32.ofNat identifier.toNat)).map Atom.symbol
      else none
  | .node (.symbolBytes bytes) [] =>
      (String.fromUTF8? ⟨bytes.toArray⟩).map Atom.symbol
  | .node (.variable identifier) [] => some (.var (sourceIdName identifier))
  | .node .expression children =>
      (sourceObservationList? table world children).map Atom.expression
  | .node (.grounded impossible) _ => nomatch impossible
  | .node _ (_ :: _) => none
where
  sourceObservationList? (table : NumberedSymbols World) (world : World) :
      List (Observation (NativePayload.Label Empty)) → Option (List Atom)
    | [] => some []
    | child :: children => do
      let atom ← sourceObservation? table world child
      let atoms ← sourceObservationList? table world children
      pure (atom :: atoms)

theorem sourceObservation_cut {World : Type} (table : NumberedSymbols World) (world : World) :
    sourceObservation? table world .cut = none := rfl

theorem sourceObservation_expression_keeps_occurrences {World : Type}
    (table : NumberedSymbols World) (world : World)
    (child : Observation (NativePayload.Label Empty)) (value : Atom)
    (read : sourceObservation? table world child = some value) :
    sourceObservation? table world (.node .expression [child, child]) =
      some (.expression [value, value]) := by
  simp [sourceObservation?, sourceObservation?.sourceObservationList?, read]

theorem sourceObservation_variable_retains_full_identity {World : Type}
    (table : NumberedSymbols World) (world : World) (first second : BitVec 64) :
    sourceObservation? table world (.node (.variable first) []) =
        sourceObservation? table world (.node (.variable second) []) ↔ first = second := by
  simp only [sourceObservation?, Option.some.injEq, Atom.var.injEq]
  exact sourceIdName_injective.eq_iff

theorem sourceObservation_numbered_symbol {World : Type}
    (table : NumberedSymbols World) (world : World) (identifier : UInt32) (name : String)
    (nonzero : identifier ≠ 0)
    (bytes : table.bytes world identifier = some name.toByteArray) :
    sourceObservation? table world
      (.node (.symbol (BitVec.ofNat 64 identifier.toNat)) []) = some (.symbol name) := by
  have narrow := identifier.toNat_lt
  have widened : (BitVec.ofNat 64 identifier.toNat).toNat = identifier.toNat := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [sourceObservation?, widened, if_pos narrow, UInt32.ofNat_toNat,
    table.name?_of_bytes world identifier name nonzero bytes, Option.map_some]

/-- Actual physical observations and their checked finite graph give the same
source readout. The named-symbol API and finite depth remain explicit; this is
not a proof of native evaluation or unification. -/
theorem physical_graph_source_readback {L : Type} [Zero L] [Add L] [SepAlgebra L]
    [CellPermission L (Option CVal)] {World : Type} [DecidableEq World]
    (table : NumberedSymbols World) (inventory : World → Inventory) (heaps : World → Heap L)
    (cursors : List (NativePayload.Cursor World))
    (graph : KeyedTable (NativePayload.Cursor World) (NativePayload.Label Empty))
    (read : NativePayload.readGraph?
      (fun world => liveMemory (inventory world) (heaps world)) (fun _ => none) cursors = some graph)
    (depth : Nat) (node : graph.Node) :
    (NativePayload.observeMemory (fun world => liveMemory (inventory world) (heaps world))
      (fun _ => none) depth (graph.key node)).bind
        (sourceObservation? table (graph.key node).world) =
      sourceObservation? table (graph.key node).world (observe graph.graph depth node) := by
  rw [NativePayload.readGraph?_observe read depth node]
  rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

end PhysicalAtomSourceReadback

section PhysicalAtomGraphFacts

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory.NativePayload

open Mettapedia.GSLT.LanguageDef.NativeOps
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames

/-- The executable reader gives nonempty child lists only to expression
nodes. Every child carries the original retained world and binding context. -/
theorem readLayer?_children_origin {World Ground : Type}
    (memory : World → TargetMemory) (readGround : Cursor World → Option Ground)
    (cursor : Cursor World) (label : Label Ground) (children : List (Cursor World))
    (read : readLayer? memory readGround cursor = some (label, children)) :
    children = [] ∨ label = .expression ∧ ∀ child ∈ children,
      child.world = cursor.world ∧ child.value.epoch = cursor.value.epoch ∧
        child.value.kind = cursor.value.kind := by
  unfold readLayer? at read
  split at read
  · next valid =>
    cases skeleton : cursor.value.skeleton with
    | none => simp [skeleton] at read
    | some address =>
      simp only [skeleton, Option.bind_eq_bind, Option.bind_some] at read
      split at read
      · obtain ⟨symbol, _, pair⟩ := Option.map_eq_some_iff.mp read
        cases pair
        exact Or.inl rfl
      · obtain ⟨identity, _, pair⟩ := Option.map_eq_some_iff.mp read
        cases pair
        exact Or.inl rfl
      · obtain ⟨grounded, _, pair⟩ := Option.map_eq_some_iff.mp read
        cases pair
        exact Or.inl rfl
      · obtain ⟨values, decoded, pair⟩ := Option.map_eq_some_iff.mp read
        cases pair
        refine Or.inr ⟨rfl, ?_⟩
        intro child member
        obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
        obtain ⟨epoch, kind⟩ := readExpressionChildren?_context decoded value present
        exact ⟨rfl, epoch, kind⟩
      · contradiction
  · contradiction

theorem readGraph?_children_world {World Ground : Type} [DecidableEq World]
    (memory : World → TargetMemory) (readGround : Cursor World → Option Ground)
    (cursors : List (Cursor World))
    (table : Mettapedia.Machines.RationalTermGraph.KeyedTable (Cursor World) (Label Ground))
    (read : readGraph? memory readGround cursors = some table)
    (node child : table.Node) (member : child ∈ table.graph.children node) :
    (table.key child).world = (table.key node).world ∧
      (table.key child).value.epoch = (table.key node).value.epoch ∧
      (table.key child).value.kind = (table.key node).value.kind := by
  have localRead := readGraph?_layer read node
  obtain absent | ⟨_, context⟩ := readLayer?_children_origin memory readGround (table.key node)
    (table.graph.label node) _ localRead
  · have impossible : table.key child ∈ ([] : List (Cursor World)) := by
      rw [← absent]
      exact List.mem_map.mpr ⟨child, member, rfl⟩
    contradiction
  · exact context (table.key child) (List.mem_map.mpr ⟨child, member, rfl⟩)

theorem readGraph?_nonexpression_arity {World Ground : Type} [DecidableEq World]
    (memory : World → TargetMemory) (readGround : Cursor World → Option Ground)
    (cursors : List (Cursor World))
    (table : Mettapedia.Machines.RationalTermGraph.KeyedTable (Cursor World) (Label Ground))
    (read : readGraph? memory readGround cursors = some table)
    (node : table.Node) (leaf : table.graph.label node ≠ .expression) :
    table.graph.children node = [] := by
  obtain absent | ⟨expression, _⟩ := readLayer?_children_origin memory readGround (table.key node)
    (table.graph.label node) _ (readGraph?_layer read node)
  · exact List.map_eq_nil_iff.mp absent
  · exact (leaf expression).elim

theorem readGraph?_leaf_arity {World Ground : Type} [DecidableEq World]
    (memory : World → TargetMemory) (readGround : Cursor World → Option Ground)
    (cursors : List (Cursor World))
    (table : Mettapedia.Machines.RationalTermGraph.KeyedTable (Cursor World) (Label Ground))
    (read : readGraph? memory readGround cursors = some table)
    (node : table.Node) (identifier : BitVec 64)
    (leaf : table.graph.label node = .symbol identifier ∨
      table.graph.label node = .variable identifier) : table.graph.children node = [] := by
  have localRead := readGraph?_layer read node
  obtain absent | ⟨expression, _⟩ := readLayer?_children_origin memory readGround (table.key node)
    (table.graph.label node) _ localRead
  · exact List.map_eq_nil_iff.mp absent
  · rcases leaf with symbol | variableLabel
    · rw [symbol] at expression
      contradiction
    · rw [variableLabel] at expression
      contradiction

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory.NativePayload

end PhysicalAtomGraphFacts

section PhysicalAtomFiniteReadback

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory
open Mettapedia.Machines.RationalTermGraph
open Mettapedia.Languages.MeTTa.OSLFCore

theorem sourceObservationList?_complete {World : Type}
    (table : NumberedSymbols World) (world : World)
    (children : List (Observation (NativePayload.Label Empty)))
    (each : ∀ child ∈ children, ∃ value, sourceObservation? table world child = some value) :
    ∃ values, sourceObservation?.sourceObservationList? table world children = some values := by
  induction children with
  | nil => exact ⟨[], rfl⟩
  | cons child children ih =>
    obtain ⟨value, first⟩ := each child (by simp)
    obtain ⟨values, rest⟩ := ih (fun item member => each item (by simp [member]))
    exact ⟨value :: values, by simp [sourceObservation?.sourceObservationList?, first, rest]⟩

/-- Local source grammar and table coverage suffice for every finite ordinary
Atom graph. The theorem constructs the source value; no logical Atom or final
readback equality is supplied by the caller. -/
theorem finite_observation_has_source_value {World Node : Type}
    (table : NumberedSymbols World) (world : Node → World)
    (graph : Mettapedia.Machines.RationalTermGraph.Graph Node (NativePayload.Label Empty))
    (context : ∀ node child, child ∈ graph.children node → world child = world node)
    (leaves : ∀ node identifier,
      graph.label node = .symbol identifier ∨ graph.label node = .variable identifier →
        graph.children node = [])
    (symbols : ∀ node identifier, graph.label node = .symbol identifier →
      identifier.toNat < 2 ^ 32 ∧ ∃ name,
        table.name? (world node) (UInt32.ofNat identifier.toNat) = some name)
    (spellings : ∀ node bytes, graph.label node = .symbolBytes bytes →
      graph.children node = [] ∧ ∃ name, String.fromUTF8? ⟨bytes.toArray⟩ = some name)
    (rank : Node → Nat) (decreasing : Order.Decreasing graph rank)
    (depth : Nat) (node : Node) (fits : rank node < depth) :
    ∃ value, sourceObservation? table (world node) (observe graph depth node) = some value := by
  induction depth generalizing node with
  | zero => omega
  | succ depth ih =>
    cases label : graph.label node with
    | symbol identifier =>
      obtain ⟨narrow, name, named⟩ := symbols node identifier label
      refine ⟨.symbol name, ?_⟩
      simp only [observe, label, leaves node identifier (Or.inl label), List.map_nil,
        sourceObservation?, if_pos narrow, named, Option.map_some]
    | symbolBytes bytes =>
      obtain ⟨empty, name, utf8⟩ := spellings node bytes label
      refine ⟨.symbol name, ?_⟩
      simp only [observe, label, empty, List.map_nil, sourceObservation?, utf8, Option.map_some]
    | «variable» identifier =>
      refine ⟨.var (sourceIdName identifier), ?_⟩
      simp [observe, label, leaves node identifier (Or.inr label), sourceObservation?]
    | grounded impossible => exact nomatch impossible
    | expression =>
      have every : ∀ observation ∈ (graph.children node).map (observe graph depth),
          ∃ value, sourceObservation? table (world node) observation = some value := by
        intro observation member
        obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
        simpa only [context node child childMember] using
          ih child (by have := decreasing node child childMember; omega)
      obtain ⟨values, decoded⟩ := sourceObservationList?_complete table (world node) _ every
      exact ⟨.expression values, by simp [observe, label, sourceObservation?, decoded]⟩

theorem finite_source_readout_stable {World Node : Type}
    (table : NumberedSymbols World) (world : World)
    (graph : Mettapedia.Machines.RationalTermGraph.Graph Node (NativePayload.Label Empty))
    (rank : Node → Nat) (decreasing : Order.Decreasing graph rank)
    (depth extra : Nat) (node : Node) (fits : rank node < depth) :
    sourceObservation? table world (observe graph (depth + extra) node) =
      sourceObservation? table world (observe graph depth node) := by
  rw [Order.observe_stable_of_decreasing graph rank decreasing depth extra node fits]

/-- Successful physical inventory admission plus local ordinary syntax and
acyclicity yields an actual complete source Atom at every sufficient depth.
Storage, numbered-symbol API and context readout are still the declared
component boundary; this does not prove the native evaluator's semantics. -/
theorem physical_source_readback_complete {L : Type} [Zero L] [Add L] [SepAlgebra L]
    [CellPermission L (Option CVal)] {World : Type} [DecidableEq World]
    (table : NumberedSymbols World) (inventory : World → Inventory) (heaps : World → Heap L)
    (cursors : List (NativePayload.Cursor World))
    (graph : KeyedTable (NativePayload.Cursor World) (NativePayload.Label Empty))
    (read : NativePayload.readGraph?
      (fun world => liveMemory (inventory world) (heaps world)) (fun _ => none) cursors = some graph)
    (node : graph.Node)
    (symbols : ∀ child identifier, graph.graph.label child = .symbol identifier →
      identifier.toNat < 2 ^ 32 ∧ ∃ name,
        table.name? (graph.key child).world (UInt32.ofNat identifier.toNat) = some name)
    (spellings : ∀ child bytes, graph.graph.label child = .symbolBytes bytes →
      ∃ name, String.fromUTF8? ⟨bytes.toArray⟩ = some name)
    (rank : graph.Node → Nat) (decreasing : Order.Decreasing graph.graph rank)
    (depth : Nat) (fits : rank node < depth) :
    ∃ value, ∀ extra,
      (NativePayload.observeMemory (fun world => liveMemory (inventory world) (heaps world))
        (fun _ => (none : Option Empty)) (depth + extra) (graph.key node)).bind
        (sourceObservation? table (graph.key node).world) = some value := by
  have context : ∀ parent child, child ∈ graph.graph.children parent →
      (graph.key child).world = (graph.key parent).world := by
    intro parent child member
    exact (NativePayload.readGraph?_children_world _ _ cursors graph read parent child member).1
  have leaves : ∀ parent identifier,
      graph.graph.label parent = .symbol identifier ∨ graph.graph.label parent = .variable identifier →
        graph.graph.children parent = [] := by
    intro parent identifier leaf
    exact NativePayload.readGraph?_leaf_arity _ _ cursors graph read parent identifier leaf
  obtain ⟨value, decoded⟩ := finite_observation_has_source_value table (fun parent => (graph.key parent).world)
    graph.graph context leaves symbols (fun child bytes label =>
      ⟨NativePayload.readGraph?_nonexpression_arity _ _ cursors graph read child
        (by rw [label]; intro impossible; cases impossible), spellings child bytes label⟩)
      rank decreasing depth node fits
  refine ⟨value, fun extra => ?_⟩
  rw [physical_graph_source_readback table inventory heaps cursors graph read,
    finite_source_readout_stable table (graph.key node).world graph.graph rank decreasing depth extra node fits]
  exact decoded

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

end PhysicalAtomFiniteReadback

section PhysicalAtomReadbackControls

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms.Controls

open Mettapedia.Machines.CMemory
open ExecutableStorage ProductiveBlocks
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory
open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.GSLT.LanguageDef.NativeOps (TargetValue)

abbrev v : Ptr := ⟨1, 0⟩
abbrev e : Ptr := ⟨2, 0⟩
abbrev children : Ptr := ⟨3, 0⟩
abbrev s : Ptr := ⟨4, 0⟩
abbrev firstManaged : Ptr := ⟨5, 0⟩
abbrev secondManaged : Ptr := ⟨7, 0⟩
def identity : UInt64 := 1311768464867721267

def atomCells (kind : UInt32) (id : UInt64) (number arena : UInt32)
    (spelling elements : Option Ptr) (count : UInt64) : List (Option CVal) :=
  [some (.u32 kind), none, some (.u64 id), some (.u32 number), some (.u32 arena),
   some (.ptr spelling), none, none, some (.ptr elements), some (.u64 count)]

def storage : Storage CVal :=
  [(1, ⟨true, atomCells 1 identity 0 0 none none 0⟩),
   (2, ⟨true, atomCells 3 0 0 0 none (some children) 3⟩),
   (3, ⟨true, [some (.ptr (some v)), some (.ptr (some v)), some (.ptr (some s))]⟩),
   (4, ⟨true, atomCells 0 0 17 0 none none 0⟩),
   (5, ⟨true, atomCells 0 0 0 0 (some ⟨6, 0⟩) none 0⟩),
   (7, ⟨true, atomCells 0 0 0 0 (some ⟨8, 0⟩) none 0⟩),
   (6, ⟨true, [some (.u64 17), some (.u32 1), some (.u8 0x41)]⟩),
   (8, ⟨true, [some (.u64 29), some (.u32 1), some (.u8 0x42)]⟩)]

def inventory : Inventory := fun pointer =>
  if pointer = v ∨ pointer = e ∨ pointer = s ∨ pointer = firstManaged ∨ pointer = secondManaged then
    some .atom
  else if pointer.block = 3 ∧ pointer.offset < 3 then some .pointerCell
  else if pointer.block = 6 ∨ pointer.block = 8 then
    if pointer.offset = 0 then some .spelling
    else if 2 ≤ pointer.offset then some .byteCell else none
  else none

def context (world : Bool) (pointer : Ptr) (epoch kind : BitVec 64 := 0) : NativePayload.Cursor Bool :=
  ⟨world, ⟨some (CurrentValueRead.physicalAddress pointer), epoch, kind⟩⟩

def observer (data : Storage CVal) :=
  NativePayload.readLayer? (fun _ : Bool => liveMemory inventory (heap data))
    (fun _ => (none : Option Empty))

def numbered (name : String) : NumberedSymbols Bool where
  bytes := fun _ identifier => if identifier = 17 then some name.toByteArray else none
  unique := by
    intro world first second bytes firstRead secondRead
    by_cases firstKey : first = 17
    · by_cases secondKey : second = 17
      · exact firstKey.trans secondKey.symm
      · simp [secondKey] at secondRead
    · simp [firstKey] at firstRead

def graphKeys : List (NativePayload.Cursor Bool) :=
  [context true e, context true v, context true s]

def sourceAt (data : Storage CVal) (pointer : Ptr) : Option Atom :=
  (NativePayload.observeMemory (fun _ : Bool => liveMemory inventory (heap data))
    (fun _ => (none : Option Empty)) 2 (context true pointer)).bind
      (sourceObservation? (numbered "lambda") true)

/-- Equal child pointers remain two positions under the same retained context. -/
theorem physical_children_repeat_and_keep_context :
    observer storage (context true e 9 1) =
      some (.expression, [context true v 9 1, context true v 9 1, context true s 9 1]) := by
  decide +kernel

theorem variable_identity_keeps_high_bits :
    observer storage (context true v) = some (.variable identity.toBitVec, []) := by
  decide +kernel

theorem contextual_identity_uses_saved_epoch :
    observer storage (context true v 9 1) = some (.variable 38654705715, []) := by
  decide +kernel

theorem actual_finite_inventory_is_admitted :
    (NativePayload.readGraph? (fun _ : Bool => liveMemory inventory (heap storage))
      (fun _ => (none : Option Empty)) graphKeys).isSome = true := by decide +kernel

theorem physical_nested_source_keeps_repeated_variable :
    sourceAt storage e = some (.expression
      [.var (sourceIdName identity.toBitVec), .var (sourceIdName identity.toBitVec), .symbol "lambda"]) := by
  decide +kernel

/-- Actual managed payloads remain distinct even though their raw symbol
numbers agree. Only the source UTF-8 interpretation produces String names. -/
theorem managed_spelling_repairs_the_zero_id_boundary :
    word? (heap storage) (firstManaged + 3) = word? (heap storage) (secondManaged + 3) ∧
    observer storage (context true firstManaged) = some (.symbolBytes [0x41], []) ∧
    observer storage (context true secondManaged) = some (.symbolBytes [0x42], []) ∧
    sourceAt storage firstManaged = some (.symbol "A") ∧
    sourceAt storage secondManaged = some (.symbol "B") := by
  decide +kernel

theorem no_raw_id_decoder_can_distinguish_two_spellings :
    ¬ ∃ decode : UInt32 → List UInt8, decode 0 = [0x41] ∧ decode 0 = [0x42] := by
  rintro ⟨decode, first, second⟩
  have impossible : ([0x41] : List UInt8) = [0x42] := first.symm.trans second
  exact (by decide : ([0x41] : List UInt8) ≠ [0x42]) impossible

def forwarded : Storage CVal :=
  put storage 4 ⟨true, atomCells 0 0 17 4294967295 (some firstManaged) none 0⟩
def dead : Storage CVal := put storage 4 ⟨false, atomCells 0 0 17 0 none none 0⟩

theorem forwarding_is_not_an_old_symbol_read :
    observer forwarded (context true s) = none := by decide +kernel

theorem dead_registration_does_not_restore_lifetime :
    observer dead (context true s) = none := by decide +kernel

theorem world_is_part_of_the_actual_node_key : context true v ≠ context false v := by decide +kernel

theorem embedded_nul_is_not_strlen :
    (numbered "a\x00b").name? true 17 = some "a\x00b" := by
  exact (numbered "a\x00b").name?_of_bytes true 17 _ (by decide) rfl

theorem invalid_grounded_bytes_remain_lossless :
    ByteString.decode (ByteString.encode [0xff, 0, 0x80]) = some [0xff, 0, 0x80] :=
  ByteString.decode_encode _

def entry (data : Storage CVal) (pointer : Ptr) : State CVal (Option TargetValue) :=
  ⟨structuralProgram pointer, data, []⟩

def endpoint (steps : Nat) (data : Storage CVal) (pointer : Ptr) : Option (Option TargetValue × Storage CVal) :=
  match (machine.run steps (entry data pointer)).2 with
  | .finished (.returned result) => some (result.answer, result.storage)
  | _ => none

theorem actual_reader_returns_without_writes :
    endpoint 10 storage v = some (some (variableRecord identity), storage) := by
  rw [endpoint, entry, structural_program_uses_selected_fields]
  rfl

theorem zero_budget_keeps_the_exact_physical_read :
    machine.run 0 (entry storage v) = ([], .exhausted (entry storage v)) := rfl

theorem reader_resumes_without_restarting_the_tag_load :
    (machine.continueRun 9 (machine.run 1 (entry storage v))).1.length = 2 := by
  rw [← machine.run_add]
  change (machine.run 10 (entry storage v)).1.length = 2
  simp only [entry, structural_program_uses_selected_fields]
  rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms.Controls

end PhysicalAtomReadbackControls

section PhysicalAtomFiniteControls

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms.Controls

open Mettapedia.Machines.CMemory ExecutableStorage
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory
open Mettapedia.Machines.RationalTermGraph
open Mettapedia.Languages.MeTTa.OSLFCore

def checkedGraph : KeyedTable (NativePayload.Cursor Bool) (NativePayload.Label Empty) :=
  (NativePayload.readGraph? (fun _ : Bool => liveMemory inventory (heap storage))
    (fun _ => (none : Option Empty)) graphKeys).get actual_finite_inventory_is_admitted

theorem checkedGraph_is_actual_read :
    NativePayload.readGraph? (fun _ : Bool => liveMemory inventory (heap storage))
      (fun _ => (none : Option Empty)) graphKeys = some checkedGraph :=
  Option.eq_some_of_isSome actual_finite_inventory_is_admitted

def graphRank (node : checkedGraph.Node) : Nat := if node.val = 0 then 1 else 0

theorem checkedGraph_rank_decreases : Order.Decreasing checkedGraph.graph graphRank := by
  unfold Order.Decreasing
  decide +kernel

theorem checkedGraph_labels :
    checkedGraph.graph.label (⟨0, by decide⟩ : checkedGraph.Node) = .expression ∧
    checkedGraph.graph.label (⟨1, by decide⟩ : checkedGraph.Node) = .variable identity.toBitVec ∧
    checkedGraph.graph.label (⟨2, by decide⟩ : checkedGraph.Node) = .symbol 17 := by
  decide +kernel

theorem checkedGraph_symbol_coverage : ∀ node identifier,
    checkedGraph.graph.label node = .symbol identifier →
      identifier.toNat < 2 ^ 32 ∧ ∃ name,
        (numbered "lambda").name? (checkedGraph.key node).world
          (UInt32.ofNat identifier.toNat) = some name := by
  intro node identifier symbol
  have bound : node.val < 3 := node.isLt
  have alternatives : node.val = 0 ∨ node.val = 1 ∨ node.val = 2 := by omega
  rcases alternatives with first | second | third
  · have same : node = (⟨0, by decide⟩ : checkedGraph.Node) := Fin.ext first
    subst node
    rw [checkedGraph_labels.1] at symbol
    contradiction
  · have same : node = (⟨1, by decide⟩ : checkedGraph.Node) := Fin.ext second
    subst node
    rw [checkedGraph_labels.2.1] at symbol
    contradiction
  · have same : node = (⟨2, by decide⟩ : checkedGraph.Node) := Fin.ext third
    subst node
    rw [checkedGraph_labels.2.2] at symbol
    cases NativePayload.Label.symbol.inj symbol
    refine ⟨by decide, "lambda", ?_⟩
    exact (numbered "lambda").name?_of_bytes _ 17 "lambda" (by decide) rfl

theorem checkedGraph_spelling_coverage : ∀ node bytes,
    checkedGraph.graph.label node = .symbolBytes bytes →
      ∃ name, String.fromUTF8? ⟨bytes.toArray⟩ = some name := by
  intro node bytes spelling
  have bound : node.val < 3 := node.isLt
  have alternatives : node.val = 0 ∨ node.val = 1 ∨ node.val = 2 := by omega
  rcases alternatives with first | second | third
  · have same : node = (⟨0, by decide⟩ : checkedGraph.Node) := Fin.ext first
    subst node
    rw [checkedGraph_labels.1] at spelling
    contradiction
  · have same : node = (⟨1, by decide⟩ : checkedGraph.Node) := Fin.ext second
    subst node
    rw [checkedGraph_labels.2.1] at spelling
    contradiction
  · have same : node = (⟨2, by decide⟩ : checkedGraph.Node) := Fin.ext third
    subst node
    rw [checkedGraph_labels.2.2] at spelling
    contradiction

/-- This positive control uses the general rank theorem, then identifies its
constructed value from the independently checked physical observation. -/
theorem all_sufficient_depths_keep_the_actual_source :
    ∀ extra,
      (NativePayload.observeMemory (fun _ : Bool => liveMemory inventory (heap storage))
        (fun _ => (none : Option Empty)) (2 + extra) (context true e)).bind
          (sourceObservation? (numbered "lambda") true) = some (.expression
            [.var (sourceIdName identity.toBitVec), .var (sourceIdName identity.toBitVec),
              .symbol "lambda"]) := by
  obtain ⟨value, stable⟩ := physical_source_readback_complete (numbered "lambda")
    (fun _ => inventory) (fun _ => heap storage) graphKeys checkedGraph
    checkedGraph_is_actual_read (⟨0, by decide⟩ : checkedGraph.Node)
    checkedGraph_symbol_coverage checkedGraph_spelling_coverage graphRank checkedGraph_rank_decreases 2 (by decide)
  have first := stable 0
  change sourceAt storage e = some value at first
  have same := Option.some.inj (first.symm.trans physical_nested_source_keeps_repeated_variable)
  subst value
  exact stable

theorem duplicate_inventory_key_is_refused :
    (NativePayload.readGraph? (fun _ : Bool => liveMemory inventory (heap storage))
      (fun _ => (none : Option Empty)) [context true e, context true v,
        context true v, context true s]).isSome = false := by decide +kernel

theorem omitted_child_node_is_refused :
    (NativePayload.readGraph? (fun _ : Bool => liveMemory inventory (heap storage))
      (fun _ => (none : Option Empty)) [context true e, context true v]).isSome = false := by
  decide +kernel

def cyclic : Storage CVal :=
  put (put storage 2 ⟨true, atomCells 3 0 0 0 none (some children) 1⟩)
    3 ⟨true, [some (.ptr (some e))]⟩

theorem cyclic_structure_is_graph_data_but_not_complete_finite_syntax :
    (NativePayload.readGraph? (fun _ : Bool => liveMemory inventory (heap cyclic))
      (fun _ => (none : Option Empty)) [context true e]).isSome = true ∧
    sourceAt cyclic e = none := by decide +kernel

def clonePointer : Ptr := ⟨9, 0⟩
def cloneStorage : Storage CVal :=
  put (put (put storage 9 ⟨true, atomCells 1 identity 0 0 none none 0⟩)
    2 ⟨true, atomCells 3 0 0 0 none (some children) 2⟩)
    3 ⟨true, [some (.ptr (some v)), some (.ptr (some clonePointer))]⟩
def cloneInventory : Inventory := fun pointer =>
  if pointer = clonePointer then some .atom else inventory pointer

theorem equal_values_keep_distinct_physical_nodes :
    ((NativePayload.readGraph? (fun _ : Bool => liveMemory cloneInventory (heap cloneStorage))
      (fun _ => (none : Option Empty))
      [context true e, context true v, context true clonePointer]).map
        (fun graph => graph.rows.map KeyedRow.key)) =
      some [context true e, context true v, context true clonePointer] ∧
    context true v ≠ context true clonePointer := by
  decide +kernel

def wrongVariableArm : Storage CVal :=
  put storage 1 ⟨true, [some (.u32 1), none, some (.u32 51), none,
    some (.u32 0), some (.ptr none), none, none, none, none]⟩

theorem narrow_value_does_not_satisfy_wide_variable_field :
    observer wrongVariableArm (context true v) = none ∧
    endpoint 10 wrongVariableArm v = none := by
  constructor
  · decide +kernel
  · rw [endpoint, entry, structural_program_uses_selected_fields]
    rfl

/-- An actual repeated self-edge cannot acquire a decreasing finite rank. -/
theorem self_edge_has_no_decreasing_rank {Node Label : Type}
    (graph : Mettapedia.Machines.RationalTermGraph.Graph Node Label)
    (node : Node) (self : node ∈ graph.children node) :
    ¬ ∃ rank, Order.Decreasing graph rank := by
  rintro ⟨rank, decreases⟩
  exact Nat.lt_irrefl (rank node) (decreases node node self)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms.Controls

end PhysicalAtomFiniteControls


section NativeManagedLayer
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory
open Mettapedia.Machines.RationalTermGraph
open Mettapedia.Languages.MeTTa.OSLFCore
open CellPermission

variable {L : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem spelling_field_from_registered (inventory : Inventory) (heap : Heap L)
    (spelling : Ptr) (count : UInt32) (index : Nat)
    (registered : inventory spelling = some .spelling)
    (read : spellingRecord? heap spelling = some (spellingRecord spelling count)) :
    targetRead (memory inventory heap)
      (sourceFieldAddress (CurrentValueRead.physicalAddress spelling) index) =
      targetReadPath [index] (spellingRecord spelling count) := by
  simp [targetRead, memory, CurrentValueRead.physicalAddress, sourceFieldAddress,
    registered, read]

/-- The physical length cell and every owned byte determine the existing
byte reader's result. The stored hash does not stand in for the contents. -/
theorem managed_spelling_from_owned (inventory : Inventory) (heap : Heap L)
    (spelling : Ptr) (count : UInt32) (bytes : List UInt8)
    (registered : inventory spelling = some .spelling)
    (eachByte : ∀ index, index < bytes.length →
      inventory ((spelling + 2) + index) = some .byteCell)
    (size : count.toNat = bytes.length)
    (headerRest byteRest : Heap L → Prop)
    (header : (PointsTo (spelling + 1) (.u32 count) ∗ headerRest) heap)
    (contents : (Cells (spelling + 2) (bytes.map (fun byte => some (CVal.u8 byte))) ∗ byteRest) heap) :
    NativePayload.readSpelling? (memory inventory heap)
      (CurrentValueRead.physicalAddress spelling) = some bytes := by
  have record := spelling_record_owned spelling count headerRest heap header
  have length := spelling_field_from_registered inventory heap spelling count 1 registered record
  have buffer := spelling_field_from_registered inventory heap spelling count 2 registered record
  simp only [spellingRecord, targetReadPath, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.bind_some] at length buffer
  have bounded := count.toNat_lt
  have widened : (BitVec.ofNat 64 count.toNat).toNat = count.toNat := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have block := byte_block_from_owned inventory heap (spelling + 2) bytes byteRest eachByte contents
  simp only [NativePayload.readSpelling?, length, buffer]
  change (if (BitVec.ofNat 64 count.toNat).toNat < 2 ^ 32 then
    ByteViews.targetBlock (memory inventory heap)
      (CurrentValueRead.physicalAddress (spelling + 2)) (BitVec.ofNat 64 count.toNat).toNat
    else none) = some bytes
  simp only [widened, if_pos bounded]
  simpa only [size] using block

/-- Actual symbol and spelling storage compose into a byte-labelled symbol.
The caller's world, epoch and contextual kind remain in the supplied cursor. -/
theorem managed_symbol_layer_from_owned {World Ground : Type}
    (inventory : World → Inventory) (heaps : World → Heap L)
    (readGround : NativePayload.Cursor World → Option Ground)
    (cursor : NativePayload.Cursor World) (atom spelling : Ptr) (count : UInt32)
    (bytes : List UInt8) (valid : cursor.value.Admissible)
    (pointer : cursor.value.skeleton = some (CurrentValueRead.physicalAddress atom))
    (atomRegistered : inventory cursor.world atom = some .atom)
    (spellingRegistered : inventory cursor.world spelling = some .spelling)
    (eachByte : ∀ index, index < bytes.length →
      inventory cursor.world ((spelling + 2) + index) = some .byteCell)
    (size : count.toNat = bytes.length)
    (atomRest headerRest byteRest : Heap L → Prop)
    (atomOwned : (PointsTo atom (.u32 0) ∗ PointsTo (atom + 3) (.u32 0) ∗
      PointsTo (atom + 5) (.ptr (some spelling)) ∗ atomRest) (heaps cursor.world))
    (header : (PointsTo (spelling + 1) (.u32 count) ∗ headerRest) (heaps cursor.world))
    (contents : (Cells (spelling + 2) (bytes.map (fun byte => some (CVal.u8 byte))) ∗ byteRest)
      (heaps cursor.world)) :
    NativePayload.readLayer? (fun world => memory (inventory world) (heaps world))
      readGround cursor = some (.symbolBytes bytes, []) := by
  have record := symbol_record_owned atom 0 (some spelling) atomRest (heaps cursor.world) atomOwned
  have tag := field_from_registered_record (inventory cursor.world) (heaps cursor.world)
    atom (symbolRecord 0 (some spelling)) 0 atomRegistered record
  have number := field_from_registered_record (inventory cursor.world) (heaps cursor.world)
    atom (symbolRecord 0 (some spelling)) 3 atomRegistered record
  have spellingField := field_from_registered_record (inventory cursor.world) (heaps cursor.world)
    atom (symbolRecord 0 (some spelling)) 5 atomRegistered record
  simp only [symbolRecord, targetReadPath, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.bind_some] at tag number spellingField
  have spelled := managed_spelling_from_owned (inventory cursor.world) (heaps cursor.world)
    spelling count bytes spellingRegistered eachByte size headerRest byteRest header contents
  simpa [NativePayload.readLayer?, NativePayload.readSymbol?, valid, pointer, tag,
    number, spellingField] using spelled

/-- The physical forwarding/header execution reaches the same byte-labelled
layer constructed from the held cells. Both callback forwarding passes remain
in the program; the whole borrowed heap and the supplied contextual cursor are
preserved. This joins selected helper operations, not the enclosing evaluator. -/
theorem managed_forwarding_layer_wp {World Ground : Type}
    (inventory : World → Inventory) (heaps : World → Heap L)
    (readGround : NativePayload.Cursor World → Option Ground)
    (cursor : NativePayload.Cursor World) (start : Option Ptr) (atom spelling : Ptr)
    (count : UInt32) (bytes : List UInt8) (hops allowance : Nat)
    (path : SymbolForward.ForwardPath (heaps cursor.world) start (some atom) hops)
    (enough : hops ≤ allowance)
    (live : Valid (heaps cursor.world) atom) (spellingLive : Valid (heaps cursor.world) spelling)
    (valid : cursor.value.Admissible)
    (pointer : cursor.value.skeleton = some (CurrentValueRead.physicalAddress atom))
    (atomRegistered : inventory cursor.world atom = some .atom)
    (spellingRegistered : inventory cursor.world spelling = some .spelling)
    (eachByte : ∀ index, index < bytes.length →
      inventory cursor.world ((spelling + 2) + index) = some .byteCell)
    (size : count.toNat = bytes.length)
    (atomRest headerRest byteRest : Heap L → Prop)
    (atomOwned : (PointsTo atom (.u32 0) ∗ PointsTo (atom + 3) (.u32 0) ∗
      PointsTo (atom + 5) (.ptr (some spelling)) ∗ atomRest) (heaps cursor.world))
    (header : (PointsTo (spelling + 1) (.u32 count) ∗ headerRest) (heaps cursor.world))
    (contents : (Cells (spelling + 2) (bytes.map (fun byte => some (CVal.u8 byte))) ∗ byteRest)
      (heaps cursor.world)) :
    (SymbolSpelling.managedAfterForward allowance start).wp act
      (fun result reached =>
        result = .finished (.next (some atom, some (some (spelling + 2), count))) ∧
        reached = heaps cursor.world ∧
        NativePayload.readLayer? (fun world => memory (inventory world) (heaps world))
          readGround cursor = some (.symbolBytes bytes, [])) (heaps cursor.world) := by
  have kind : Reads atom (.u32 0) (heaps cursor.world) := read_of_pointsTo atomOwned
  have number : Reads (atom + 3) (.u32 0) (heaps cursor.world) :=
    read_of_pointsTo (show (PointsTo (atom + 3) (.u32 0) ∗
      (PointsTo atom (.u32 0) ∗ PointsTo (atom + 5) (.ptr (some spelling)) ∗ atomRest))
        (heaps cursor.world) by cmem_exact)
  have stored : Reads (atom + 5) (.ptr (some spelling)) (heaps cursor.world) :=
    read_of_pointsTo (show (PointsTo (atom + 5) (.ptr (some spelling)) ∗
      (PointsTo atom (.u32 0) ∗ PointsTo (atom + 3) (.u32 0) ∗ atomRest))
        (heaps cursor.world) by cmem_exact)
  apply SymbolSpelling.managedAfterForward_wp (heaps cursor.world) start atom spelling count
    hops allowance path enough live spellingLive kind number stored (read_of_pointsTo header)
  exact ⟨rfl, rfl, managed_symbol_layer_from_owned inventory heaps readGround cursor atom spelling
    count bytes valid pointer atomRegistered spellingRegistered eachByte size
    atomRest headerRest byteRest atomOwned header contents⟩

theorem forwarding_terminal_is_unforwarded (heap : Heap L) (start : Option Ptr)
    (atom : Ptr) (hops : Nat)
    (path : SymbolForward.ForwardPath heap start (some atom) hops) :
    unforwarded? heap atom = true := by
  cases SymbolSpelling.terminal_path path with
  | stop _ arena _ tag ordinary =>
      apply unforwarded_of_actual_arena heap atom arena _ ordinary
      simp only [Reads] at tag
      change CellPermission.read ((heap atom.block).2 (atom.offset + 4)) =
        some (some (.u32 arena)) at tag
      simp [word?, cell?, tag]

/-- Registering a spelling does not establish its lifetime. Supplying the
current bounds for its header and bytes joins the same owned-cell proof to
the live inventory actually used by the finite graph reader. -/
theorem managed_live_layer_from_owned {World Ground : Type}
    (inventory : World → Inventory) (heaps : World → Heap L)
    (readGround : NativePayload.Cursor World → Option Ground)
    (cursor : NativePayload.Cursor World) (start : Option Ptr) (atom spelling : Ptr)
    (count : UInt32) (bytes : List UInt8) (hops : Nat)
    (path : SymbolForward.ForwardPath (heaps cursor.world) start (some atom) hops)
    (atomLive : liveAt? (heaps cursor.world) atom = true)
    (spellingLive : liveAt? (heaps cursor.world) spelling = true)
    (byteLive : ∀ index, index < bytes.length →
      liveAt? (heaps cursor.world) ((spelling + 2) + index) = true)
    (valid : cursor.value.Admissible)
    (pointer : cursor.value.skeleton = some (CurrentValueRead.physicalAddress atom))
    (atomRegistered : inventory cursor.world atom = some .atom)
    (spellingRegistered : inventory cursor.world spelling = some .spelling)
    (eachByte : ∀ index, index < bytes.length →
      inventory cursor.world ((spelling + 2) + index) = some .byteCell)
    (size : count.toNat = bytes.length)
    (atomRest headerRest byteRest : Heap L → Prop)
    (atomOwned : (PointsTo atom (.u32 0) ∗ PointsTo (atom + 3) (.u32 0) ∗
      PointsTo (atom + 5) (.ptr (some spelling)) ∗ atomRest) (heaps cursor.world))
    (header : (PointsTo (spelling + 1) (.u32 count) ∗ headerRest) (heaps cursor.world))
    (contents : (Cells (spelling + 2) (bytes.map (fun byte => some (CVal.u8 byte))) ∗ byteRest)
      (heaps cursor.world)) :
    NativePayload.readLayer? (fun world => liveMemory (inventory world) (heaps world))
      readGround cursor = some (.symbolBytes bytes, []) := by
  apply managed_symbol_layer_from_owned
    (fun world => liveInventory (inventory world) (heaps world)) heaps readGround
    cursor atom spelling count bytes valid pointer _ _ _ size
    atomRest headerRest byteRest atomOwned header contents
  · exact (liveInventory_atom_iff _ _ _).mpr
      ⟨atomLive, atomRegistered, forwarding_terminal_is_unforwarded _ _ _ _ path⟩
  · simp [liveInventory, spellingLive, spellingRegistered]
  · intro index within
    simp [liveInventory, byteLive index within, eachByte index within]

/-- Text is a checked interpretation of the exact symbol bytes. -/
theorem managed_symbol_source_exact {World : Type} (table : NumberedSymbols World)
    (world : World) (bytes : List UInt8) (name : String) :
    sourceObservation? table world (.node (.symbolBytes bytes) []) = some (.symbol name) ↔
      String.fromUTF8? ⟨bytes.toArray⟩ = some name := by
  simp [sourceObservation?]

theorem managed_symbol_keeps_byte_identity {Ground : Type} (first second : List UInt8) :
    NativePayload.Label.symbolBytes (Ground := Ground) first = .symbolBytes second ↔ first = second := by
  simp

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

end NativeManagedLayer


section NativeManagedControls
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms.ManagedControls

open Mettapedia.Machines.CMemory
open ExecutableStorage ProductiveBlocks
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory
open Mettapedia.Languages.MeTTa.OSLFCore
open _root_.Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms.Controls

/-- The stored length is independent of C-string termination. -/
def spellingData (count : UInt32) (bytes : List UInt8) : Storage CVal :=
  put storage 6 ⟨true, [some (.u64 987), some (.u32 count)] ++
    bytes.map (fun byte => some (.u8 byte))⟩

def nulBytes : List UInt8 := [0x41, 0, 0x42]
def invalidBytes : List UInt8 := [0xff, 0, 0x80]

theorem embedded_nul_is_a_byte_not_a_terminator :
    observer (spellingData 3 nulBytes) (Controls.context true firstManaged) =
      some (.symbolBytes nulBytes, []) := by decide +kernel

theorem embedded_nul_survives_checked_text :
    sourceAt (spellingData 3 nulBytes) firstManaged =
      some (.symbol (String.ofList ['A', '\x00', 'B'])) := by decide +kernel

theorem invalid_utf8_keeps_raw_identity_and_refuses_string :
    observer (spellingData 3 invalidBytes) (Controls.context true firstManaged) =
      some (.symbolBytes invalidBytes, []) ∧
    sourceAt (spellingData 3 invalidBytes) firstManaged = none := by decide +kernel

theorem explicit_length_selects_only_the_owned_prefix :
    observer (spellingData 2 nulBytes) (Controls.context true firstManaged) =
      some (.symbolBytes [0x41, 0], []) := by decide +kernel

theorem absent_byte_is_not_invented_from_length :
    observer (spellingData 4 nulBytes) (Controls.context true firstManaged) = none := by decide +kernel

theorem wrong_width_does_not_supply_an_unsigned_byte :
    observer (put storage 6 ⟨true, [some (.u64 987), some (.u32 1), some (.u32 65)]⟩)
      (Controls.context true firstManaged) = none := by decide +kernel

theorem dead_spelling_storage_is_refused :
    observer (put storage 6 ⟨false, [some (.u64 987), some (.u32 1), some (.u8 65)]⟩)
      (Controls.context true firstManaged) = none := by decide +kernel

def emptyFallback : Storage CVal :=
  put storage firstManaged.block ⟨true, atomCells 0 0 0 0 none none 0⟩

theorem null_spelling_is_the_empty_fallback :
    observer emptyFallback (Controls.context true firstManaged) = some (.symbolBytes [], []) ∧
    sourceAt emptyFallback firstManaged = some (.symbol "") := by decide +kernel

def equalSpelling : Storage CVal :=
  put storage 8 ⟨true, [some (.u64 29), some (.u32 1), some (.u8 0x41)]⟩

theorem equal_spelling_keeps_distinct_physical_nodes :
    (NativePayload.readGraph? (fun _ : Bool => liveMemory inventory (heap equalSpelling))
      (fun _ => (none : Option Empty))
      [Controls.context true firstManaged, Controls.context true secondManaged]).map
        (fun graph => graph.rows.map (fun row => (row.key, row.label))) =
      some [(Controls.context true firstManaged, .symbolBytes [0x41]),
        (Controls.context true secondManaged, .symbolBytes [0x41])] := by decide +kernel

def repeatedManaged : Storage CVal :=
  put storage children.block ⟨true,
    [some (.ptr (some firstManaged)), some (.ptr (some firstManaged)),
      some (.ptr (some secondManaged))]⟩

theorem repeated_managed_child_is_not_deduplicated :
    sourceAt repeatedManaged e = some (.expression [.symbol "A", .symbol "A", .symbol "B"]) := by
  decide +kernel

theorem symbol_read_does_not_erase_contextual_key :
    (NativePayload.readGraph? (fun _ : Bool => liveMemory inventory (heap storage))
      (fun _ => (none : Option Empty))
      [Controls.context false firstManaged 7 1, Controls.context true firstManaged 9 1]).map
        (fun graph => graph.rows.map (fun row => row.key)) =
      some [Controls.context false firstManaged 7 1, Controls.context true firstManaged 9 1] := by decide +kernel

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms.ManagedControls

end NativeManagedControls


/-! ## Physical published-table interpretation

Numbered symbol names are read from the actual table/chunk/row/byte snapshot.
UTF-8 is checked only when constructing String-valued source symbols; the
physical payload and ID-zero managed spelling path retain exact bytes.
-/
section PublishedNumberedSource
set_option maxHeartbeats 1200000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open CellPermission

variable {L : Type} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- The existing numbered-symbol API now has a concrete physical instance.
The callback field is constructed from table/chunk/header/byte reads; neither
a final ID nor a final spelling is supplied to this constructor. -/
def publishedSymbols {World : Type} (inventory : World → PhysicalAtoms.Inventory)
    (heaps : World → Heap L) (snapshots : ∀ world, PublishedTable (inventory world) (heaps world)) :
    PhysicalAtoms.NumberedSymbols World where
  bytes := fun world => physicalBytes? (inventory world) (heaps world) (snapshots world).table
  unique := fun world => (snapshots world).readout_unique

theorem name_from_physical {World : Type}
    (inventory : World → PhysicalAtoms.Inventory) (heaps : World → Heap L)
    (snapshots : ∀ world, PublishedTable (inventory world) (heaps world))
    (world : World) (entry : EntryImage) (member : entry ∈ (snapshots world).entries)
    (name : String) (utf8 : String.fromUTF8? ⟨entry.bytes.toArray⟩ = some name) :
    (publishedSymbols inventory heaps snapshots).name? world entry.identifier = some name := by
  have bytesExact := (snapshots world).entry_bytes entry member
  have utf8Exact :=
    (Mettapedia.Data.String.ByteString.fromUTF8?_eq_some_iff ⟨entry.bytes.toArray⟩ name).mp utf8
  apply PhysicalAtoms.NumberedSymbols.name?_of_bytes _ world entry.identifier name
    ((snapshots world).rows entry member).nonzero
  change physicalBytes? (inventory world) (heaps world) (snapshots world).table entry.identifier = _
  simpa only [utf8Exact] using bytesExact

theorem source_numbered_from_physical {World : Type}
    (inventory : World → PhysicalAtoms.Inventory) (heaps : World → Heap L)
    (snapshots : ∀ world, PublishedTable (inventory world) (heaps world))
    (world : World) (entry : EntryImage) (member : entry ∈ (snapshots world).entries)
    (name : String) (utf8 : String.fromUTF8? ⟨entry.bytes.toArray⟩ = some name) :
    PhysicalAtoms.sourceObservation? (publishedSymbols inventory heaps snapshots) world
      (.node (.symbol (BitVec.ofNat 64 entry.identifier.toNat)) []) =
      some (.symbol name) := by
  have bytesExact := (snapshots world).entry_bytes entry member
  have nonzero := ((snapshots world).rows entry member).nonzero
  have utf8Exact :=
    (Mettapedia.Data.String.ByteString.fromUTF8?_eq_some_iff ⟨entry.bytes.toArray⟩ name).mp utf8
  apply PhysicalAtoms.sourceObservation_numbered_symbol _ world entry.identifier name nonzero
  change physicalBytes? (inventory world) (heaps world) (snapshots world).table entry.identifier = _
  simpa only [utf8Exact] using bytesExact

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory
open Mettapedia.Languages.MeTTa.OSLFCore
open CellPermission

variable {L : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- On an owned numbered symbol the actual current-ID body reaches the
published row's identifier. That row's physical payload, not a spelling
callback, determines the existing source observation. -/
theorem current_numbered_source_wp {World : Type}
    (inventory : World → PhysicalAtoms.Inventory) (heaps : World → Heap L)
    (snapshots : ∀ world, PublishedTable (inventory world) (heaps world))
    (world : World) (entry : EntryImage) (member : entry ∈ (snapshots world).entries)
    (lookup : Current.Lookup) (atom : Ptr) (live : Valid (heaps world) atom)
    (kind : Reads atom (.u32 0) (heaps world))
    (number : Reads (atom + 3) (.u32 entry.identifier) (heaps world))
    (name : String) (utf8 : String.fromUTF8? ⟨entry.bytes.toArray⟩ = some name)
    (post : Option Atom → Heap L → Prop) (after : post (some (Atom.symbol name)) (heaps world)) :
    (do let identifier ← Current.operations lookup (some atom)
        pure (PhysicalAtoms.sourceObservation? (publishedSymbols inventory heaps snapshots) world
          (.node (.symbol (BitVec.ofNat 64 identifier.toNat)) []))).wp act post (heaps world) := by
  rw [wp_bind']
  apply Current.numbered_current_id_wp lookup (heaps world) atom entry.identifier live kind number
    ((snapshots world).rows entry member).nonzero
  rw [wp_pure, source_numbered_from_physical inventory heaps snapshots world entry member name utf8]
  exact after

/-- The parsed current-ID source body and the physical published table reach
one source name. The final C return keeps the caller's environment and the
entire heap, and the ID-zero lookup component is unreachable on this path. -/
theorem actual_current_id_body_and_source_wp {World : Type}
    (inventory : World → PhysicalAtoms.Inventory) (heaps : World → Heap L)
    (snapshots : ∀ world, PublishedTable (inventory world) (heaps world))
    (world : World) (entry : EntryImage) (member : entry ∈ (snapshots world).entries)
    (lookup : Current.Lookup) (environment : ReadExpressions.Environment) (atom : Ptr)
    (parameter : environment "atom".toList = some (.ptr (some atom)))
    (live : Valid (heaps world) atom) (kind : Reads atom (.u32 0) (heaps world))
    (number : Reads (atom + 3) (.u32 entry.identifier) (heaps world))
    (name : String) (utf8 : String.fromUTF8? ⟨entry.bytes.toArray⟩ = some name) :
    (Current.program lookup environment).wp act
      (fun result reached =>
        result = .finished (.returned environment (some (.u32 entry.identifier))) ∧
        reached = heaps world ∧
        PhysicalAtoms.sourceObservation? (publishedSymbols inventory heaps snapshots) world
          (.node (.symbol (BitVec.ofNat 64 entry.identifier.toNat)) []) = some (Atom.symbol name))
      (heaps world) := by
  apply Current.actual_numbered_body_wp lookup environment (heaps world) atom entry.identifier
    parameter live kind number ((snapshots world).rows entry member).nonzero
  exact ⟨rfl, rfl, source_numbered_from_physical inventory heaps snapshots world entry member name utf8⟩

/-- The existing physical layer and the same byte-backed table agree on the
source name. World, epoch, kind and physical identity remain in the untouched
cursor; this theorem changes no graph keys or child occurrences. -/
theorem numbered_layer_and_source_from_owned {World Ground : Type}
    (inventory : World → PhysicalAtoms.Inventory) (heaps : World → Heap L)
    (snapshots : ∀ world, PublishedTable (inventory world) (heaps world))
    (readGround : NativePayload.Cursor World → Option Ground)
    (cursor : NativePayload.Cursor World) (entry : EntryImage)
    (member : entry ∈ (snapshots cursor.world).entries)
    (atom : Ptr) (spelling : Option Ptr)
    (valid : cursor.value.Admissible)
    (pointer : cursor.value.skeleton = some (CurrentValueRead.physicalAddress atom))
    (registered : inventory cursor.world atom = some .atom)
    (live : PhysicalAtoms.liveAt? (heaps cursor.world) atom = true)
    (unforwarded : PhysicalAtoms.unforwarded? (heaps cursor.world) atom = true)
    (rest : Heap L → Prop)
    (owned : (PointsTo atom (.u32 0) ∗ PointsTo (atom + 3) (.u32 entry.identifier) ∗
      PointsTo (atom + 5) (.ptr spelling) ∗ rest) (heaps cursor.world))
    (name : String) (utf8 : String.fromUTF8? ⟨entry.bytes.toArray⟩ = some name) :
    NativePayload.readLayer? (fun world => PhysicalAtoms.liveMemory (inventory world) (heaps world))
      readGround cursor = some (.symbol (BitVec.ofNat 64 entry.identifier.toNat), []) ∧
    PhysicalAtoms.sourceObservation? (publishedSymbols inventory heaps snapshots) cursor.world
      (.node (.symbol (BitVec.ofNat 64 entry.identifier.toNat)) []) = some (Atom.symbol name) := by
  constructor
  · apply PhysicalAtoms.symbol_layer_from_owned_memory
      (fun world => PhysicalAtoms.liveInventory (inventory world) (heaps world)) heaps
      readGround cursor atom entry.identifier spelling
      ((snapshots cursor.world).rows entry member).nonzero valid pointer
      ((PhysicalAtoms.liveInventory_atom_iff _ _ _).mpr ⟨live, registered, unforwarded⟩) rest owned
  · exact source_numbered_from_physical inventory heaps snapshots cursor.world entry member name utf8

/-- Both public byte/length helpers run through the selected physical row.
This is a join with the existing byte decoder, not an assumed native String. -/
theorem actual_numbered_spelling_source_wp {World : Type}
    (inventory : World → PhysicalAtoms.Inventory) (heaps : World → Heap L)
    (snapshots : ∀ world, PublishedTable (inventory world) (heaps world))
    (world : World) (entry : EntryImage) (member : entry ∈ (snapshots world).entries)
    (empty : Ptr)
    (entryLive : Valid (heaps world)
      (entryPointer ((snapshots world).rows entry member).chunk entry.identifier))
    (bufferLive : Valid (heaps world) entry.buffer)
    (name : String) (utf8 : String.fromUTF8? ⟨entry.bytes.toArray⟩ = some name) :
    (do let pointer ← bytesOperation empty (some (snapshots world).table) entry.identifier
        let length ← lengthOperation (some (snapshots world).table) entry.identifier
        pure (pointer, length)).wp act
      (fun result reached => result = (some entry.buffer, entry.length) ∧ reached = heaps world ∧
        PhysicalAtoms.sourceObservation? (publishedSymbols inventory heaps snapshots) world
          (.node (.symbol (BitVec.ofNat 64 entry.identifier.toNat)) []) = some (Atom.symbol name))
      (heaps world) := by
  apply spelling_pair_wp (heaps world) empty (snapshots world).table entry.identifier
    ((snapshots world).rows entry member) entry.buffer entry.length entryLive bufferLive
    ((snapshots world).buffers entry member) ((snapshots world).lengths entry member)
  exact ⟨rfl, rfl, source_numbered_from_physical inventory heaps snapshots world entry member name utf8⟩

/-- An admitted finite physical graph obtains every numbered name from its
actual published byte row. Local UTF-8 checks and a decreasing rank yield a
complete stable source value; no source Atom or final readout is an input. -/
theorem finite_physical_graph_has_source_from_published_rows {World : Type} [DecidableEq World]
    (inventory : World → PhysicalAtoms.Inventory) (heaps : World → Heap L)
    (snapshots : ∀ world, PublishedTable (inventory world) (heaps world))
    (cursors : List (NativePayload.Cursor World))
    (graph : Mettapedia.Machines.RationalTermGraph.KeyedTable
      (NativePayload.Cursor World) (NativePayload.Label Empty))
    (read : NativePayload.readGraph?
      (fun world => PhysicalAtoms.liveMemory (inventory world) (heaps world))
      (fun _ => none) cursors = some graph)
    (node : graph.Node)
    (symbols : ∀ child identifier, graph.graph.label child = .symbol identifier →
      ∃ entry ∈ (snapshots (graph.key child).world).entries,
        identifier = BitVec.ofNat 64 entry.identifier.toNat ∧
        ∃ name, String.fromUTF8? ⟨entry.bytes.toArray⟩ = some name)
    (spellings : ∀ child bytes, graph.graph.label child = .symbolBytes bytes →
      ∃ name, String.fromUTF8? ⟨bytes.toArray⟩ = some name)
    (rank : graph.Node → Nat)
    (decreasing : Mettapedia.Machines.RationalTermGraph.Order.Decreasing graph.graph rank)
    (depth : Nat) (fits : rank node < depth) :
    ∃ value, ∀ extra,
      (NativePayload.observeMemory (fun world => PhysicalAtoms.liveMemory (inventory world) (heaps world))
        (fun _ => (none : Option Empty)) (depth + extra) (graph.key node)).bind
        (PhysicalAtoms.sourceObservation? (publishedSymbols inventory heaps snapshots)
          (graph.key node).world) = some value := by
  apply PhysicalAtoms.physical_source_readback_complete
    (publishedSymbols inventory heaps snapshots) inventory heaps cursors graph read node
    ?_ spellings rank decreasing depth fits
  intro child identifier label
  obtain ⟨entry, member, rfl, name, utf8⟩ := symbols child identifier label
  have bounded := entry.identifier.toNat_lt
  have widened : entry.identifier.toNat < 2 ^ 64 := by omega
  have exactId : (BitVec.ofNat 64 entry.identifier.toNat).toNat = entry.identifier.toNat := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt widened]
  refine ⟨by rw [exactId]; exact bounded, name, ?_⟩
  rw [exactId, UInt32.ofNat_toNat]
  exact name_from_physical inventory heaps snapshots (graph.key child).world entry member name utf8

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol

end PublishedNumberedSource


/-! ## Constructed managed/current-ID source readout

Published numeric lookup and managed byte labels share the existing physical
layer reader and checked UTF-8 interpretation. Contextual cursors and repeated
child occurrences remain unchanged; invalid UTF-8 remains a byte observation.
-/
section ManagedCurrentSourceReadout
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory
open Mettapedia.Languages.MeTTa.OSLFCore
open CellPermission

variable {L : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- A successful physical managed lookup and the published numeric source
view have exactly the same checked UTF-8 observation, including rejection of
invalid UTF-8. The world is retained explicitly and ID zero is excluded only
from the numeric interpretation, never from the managed byte payload. -/
theorem lookup_numeric_and_managed_observations_agree {World : Type}
    (inventory : World → PhysicalAtoms.Inventory) (heaps : World → Heap L)
    (snapshots : ∀ world, PublishedTable (inventory world) (heaps world)) (world : World)
    (capacity : UInt32) (nonzero : capacity ≠ 0)
    (entries : Fin capacity.toNat → Option (Lookup.Physical.Key × UInt32))
    (paths : DirectoryProbe.PathsOccupied entries
      (fun key => ⟨(Lookup.home key.1 capacity).toNat, Lookup.home_within key.1 capacity nonzero⟩))
    (unique : DirectoryProbe.KeysCoherent entries)
    (reads : ∀ position, Lookup.Physical.CellRead (snapshots world).table
      (UInt32.ofNat position.val) (entries position) (heaps world))
    (hash : UInt64) (query : List UInt8)
    (found : Lookup.SourceRead.inventoryID capacity nonzero entries hash query ≠ 0) :
    PhysicalAtoms.sourceObservation? (publishedSymbols inventory heaps snapshots) world
      (.node (.symbol (BitVec.ofNat 64
        (Lookup.SourceRead.inventoryID capacity nonzero entries hash query).toNat)) []) =
    PhysicalAtoms.sourceObservation? (publishedSymbols inventory heaps snapshots) world
      (.node (.symbolBytes query) []) := by
  have actual := nonzero_inventory_reads_query (inventory world) (heaps world) (snapshots world)
    capacity nonzero entries paths unique reads hash query found
  let identifier := Lookup.SourceRead.inventoryID capacity nonzero entries hash query
  have identifierNonzero : identifier ≠ 0 := found
  have exactBytes : physicalBytes? (inventory world) (heaps world) (snapshots world).table identifier =
      some ⟨query.toArray⟩ := actual
  have narrow := identifier.toNat_lt
  have widened : (BitVec.ofNat 64 identifier.toNat).toNat = identifier.toNat := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  change PhysicalAtoms.sourceObservation? (publishedSymbols inventory heaps snapshots) world
      (.node (.symbol (BitVec.ofNat 64 identifier.toNat)) []) = _
  simp only [PhysicalAtoms.sourceObservation?, widened, if_pos narrow, UInt32.ofNat_toNat,
    PhysicalAtoms.NumberedSymbols.name?, identifierNonzero, ↓reduceIte, publishedSymbols, exactBytes]
  rfl

/-- The source spelling comes from the physically compared bytes, not the
numeric identifier's printing or a callback supplied name. -/
theorem lookup_source_symbol_exact {World : Type}
    (inventory : World → PhysicalAtoms.Inventory) (heaps : World → Heap L)
    (snapshots : ∀ world, PublishedTable (inventory world) (heaps world)) (world : World)
    (capacity : UInt32) (nonzero : capacity ≠ 0)
    (entries : Fin capacity.toNat → Option (Lookup.Physical.Key × UInt32))
    (paths : DirectoryProbe.PathsOccupied entries
      (fun key => ⟨(Lookup.home key.1 capacity).toNat, Lookup.home_within key.1 capacity nonzero⟩))
    (unique : DirectoryProbe.KeysCoherent entries)
    (reads : ∀ position, Lookup.Physical.CellRead (snapshots world).table
      (UInt32.ofNat position.val) (entries position) (heaps world))
    (hash : UInt64) (query : List UInt8)
    (found : Lookup.SourceRead.inventoryID capacity nonzero entries hash query ≠ 0)
    (name : String) :
    PhysicalAtoms.sourceObservation? (publishedSymbols inventory heaps snapshots) world
      (.node (.symbol (BitVec.ofNat 64
        (Lookup.SourceRead.inventoryID capacity nonzero entries hash query).toNat)) []) =
        some (.symbol name) ↔ String.fromUTF8? ⟨query.toArray⟩ = some name := by
  rw [lookup_numeric_and_managed_observations_agree inventory heaps snapshots world
    capacity nonzero entries paths unique reads hash query found]
  exact PhysicalAtoms.managed_symbol_source_exact _ world query name

/-- The established occurrence-preserving source interpretation composes
with the numeric lookup result without collapsing repeated child positions. -/
theorem lookup_repeated_child_source {World : Type}
    (inventory : World → PhysicalAtoms.Inventory) (heaps : World → Heap L)
    (snapshots : ∀ world, PublishedTable (inventory world) (heaps world)) (world : World)
    (capacity : UInt32) (nonzero : capacity ≠ 0)
    (entries : Fin capacity.toNat → Option (Lookup.Physical.Key × UInt32))
    (paths : DirectoryProbe.PathsOccupied entries
      (fun key => ⟨(Lookup.home key.1 capacity).toNat, Lookup.home_within key.1 capacity nonzero⟩))
    (unique : DirectoryProbe.KeysCoherent entries)
    (reads : ∀ position, Lookup.Physical.CellRead (snapshots world).table
      (UInt32.ofNat position.val) (entries position) (heaps world))
    (hash : UInt64) (query : List UInt8)
    (found : Lookup.SourceRead.inventoryID capacity nonzero entries hash query ≠ 0)
    (name : String) (utf8 : String.fromUTF8? ⟨query.toArray⟩ = some name) :
    let child := Mettapedia.Machines.RationalTermGraph.Observation.node
      (NativePayload.Label.symbol (Ground := Empty) (BitVec.ofNat 64
        (Lookup.SourceRead.inventoryID capacity nonzero entries hash query).toNat)) []
    PhysicalAtoms.sourceObservation? (publishedSymbols inventory heaps snapshots) world
      (.node .expression [child, child]) = some (.expression [.symbol name, .symbol name]) := by
  apply PhysicalAtoms.sourceObservation_expression_keeps_occurrences
  exact (lookup_source_symbol_exact inventory heaps snapshots world capacity nonzero entries
    paths unique reads hash query found name).mpr utf8

/-- The existing physical layer reader keeps the caller's complete cursor and
managed bytes, while the constructed nonzero lookup gives the same source
symbol through the published numeric table. No new decoder or graph traversal
is introduced here. -/
theorem lookup_live_layer_and_source {World Ground : Type}
    (inventory : World → PhysicalAtoms.Inventory) (heaps : World → Heap L)
    (readGround : NativePayload.Cursor World → Option Ground)
    (cursor : NativePayload.Cursor World) (start : Option Ptr) (atom spelling : Ptr)
    (count : UInt32) (bytes : List UInt8) (hops : Nat)
    (path : SymbolForward.ForwardPath (heaps cursor.world) start (some atom) hops)
    (atomLive : PhysicalAtoms.liveAt? (heaps cursor.world) atom = true)
    (spellingLive : PhysicalAtoms.liveAt? (heaps cursor.world) spelling = true)
    (byteLive : ∀ index, index < bytes.length →
      PhysicalAtoms.liveAt? (heaps cursor.world) ((spelling + 2) + index) = true)
    (valid : cursor.value.Admissible)
    (pointer : cursor.value.skeleton = some (CurrentValueRead.physicalAddress atom))
    (atomRegistered : inventory cursor.world atom = some .atom)
    (spellingRegistered : inventory cursor.world spelling = some .spelling)
    (eachByte : ∀ index, index < bytes.length →
      inventory cursor.world ((spelling + 2) + index) = some .byteCell)
    (size : count.toNat = bytes.length)
    (atomRest headerRest byteRest : Heap L → Prop)
    (atomOwned : (PointsTo atom (.u32 0) ∗ PointsTo (atom + 3) (.u32 0) ∗
      PointsTo (atom + 5) (.ptr (some spelling)) ∗ atomRest) (heaps cursor.world))
    (header : (PointsTo (spelling + 1) (.u32 count) ∗ headerRest) (heaps cursor.world))
    (contents : (Cells (spelling + 2) (bytes.map (fun byte => some (CVal.u8 byte))) ∗ byteRest)
      (heaps cursor.world))
    (snapshots : ∀ world, PublishedTable (inventory world) (heaps world))
    (capacity : UInt32) (nonzero : capacity ≠ 0)
    (entries : Fin capacity.toNat → Option (Lookup.Physical.Key × UInt32))
    (paths : DirectoryProbe.PathsOccupied entries
      (fun key => ⟨(Lookup.home key.1 capacity).toNat, Lookup.home_within key.1 capacity nonzero⟩))
    (unique : DirectoryProbe.KeysCoherent entries)
    (reads : ∀ position, Lookup.Physical.CellRead (snapshots cursor.world).table
      (UInt32.ofNat position.val) (entries position) (heaps cursor.world))
    (hash : UInt64)
    (found : Lookup.SourceRead.inventoryID capacity nonzero entries hash bytes ≠ 0)
    (name : String) (utf8 : String.fromUTF8? ⟨bytes.toArray⟩ = some name) :
    NativePayload.readLayer? (fun world => PhysicalAtoms.liveMemory (inventory world) (heaps world))
      readGround cursor = some (.symbolBytes bytes, []) ∧
    PhysicalAtoms.sourceObservation? (publishedSymbols inventory heaps snapshots) cursor.world
      (.node (.symbol (BitVec.ofNat 64
        (Lookup.SourceRead.inventoryID capacity nonzero entries hash bytes).toNat)) []) =
        some (.symbol name) := by
  refine ⟨PhysicalAtoms.managed_live_layer_from_owned inventory heaps readGround cursor start atom
    spelling count bytes hops path atomLive spellingLive byteLive valid pointer atomRegistered
    spellingRegistered eachByte size atomRest headerRest byteRest atomOwned header contents, ?_⟩
  exact (lookup_source_symbol_exact inventory heaps snapshots cursor.world capacity nonzero entries
    paths unique reads hash bytes found name).mpr utf8

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup

end ManagedCurrentSourceReadout

/-! ## Current native bindings and one joint source observation

This adapter consumes the maintained native draft's represented current
frame directory and ordinary Atom graph. Directory enumeration, borrowed
lifetime, the field ABI and the current symbol API remain their existing
component contracts. It does not interpret an historical trail as current
bindings or establish the surrounding RESULT dispatcher.

The source equations and every pending operand use one ID-to-reference map
constructed from that directory. Ambient variables have explicit unframed
IDs; a missing contextual generation cannot be admitted as an ambient name.
The finite source profile checks the existing binding-cycle test. Graph
read failure, insufficient observation depth and cyclic bindings are reader
refusals, not completed language failure. No expression is evaluated here.
-/
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory.NativePayload.CurrentBindings

open Mettapedia.GSLT.LanguageDef.NativeOps
open Mettapedia.Machines.RationalTermGraph
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared MetavariableFrameStore.Snapshot
open Mettapedia.Languages.MeTTa.HE
open Spec.Type Spec.Type.RuntimeRefinement Spec.Type.Presentation
open Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback
open NativeFrames

abbrev SourceRow := RowOf Atom
abbrev NativeRow := RowOf BindingValueView
abbrev AtomGraph (World : Type) := KeyedTable (Cursor World) (Label Empty)

/-- Full native IDs are paired with their actual current generational slots.
The directory's vector order never becomes a lexical identity. -/
def names (directory : DirectoryReadback) : List (BitVec 64 × Ref) :=
  directory.frames.flatMap fun frame => List.ofFn fun index : Fin frame.slots.length =>
    (frame.slots[index.val].varId, frame.view.token.ref index.val)

theorem names_coordinate (directory : DirectoryReadback) {identifier : BitVec 64} {ref : Ref}
    (member : (identifier, ref) ∈ names directory) :
    directory.variableCoordinate? identifier = some ref := by
  obtain ⟨frame, present, member⟩ := List.mem_flatMap.mp member
  obtain ⟨index, equal⟩ := List.mem_ofFn.mp member
  cases equal
  exact directory.variableCoordinate_slot frame present index

theorem names_functional (directory : DirectoryReadback)
    {identifier : BitVec 64} {left right : Ref}
    (first : (identifier, left) ∈ names directory)
    (second : (identifier, right) ∈ names directory) : left = right :=
  Option.some.inj ((names_coordinate directory first).symm.trans
    (names_coordinate directory second))

/-- This lookup is over the earned finite inventory, not a supplied decoder. -/
def lookupName? (entries : List (BitVec 64 × Ref)) (name : String) : Option Ref :=
  (entries.find? fun entry => sourceIdName entry.1 == name).map Prod.snd

theorem lookupName?_of_mem {entries : List (BitVec 64 × Ref)}
    (coherent : ∀ id left right, (id, left) ∈ entries → (id, right) ∈ entries → left = right)
    {identifier : BitVec 64} {ref : Ref} (member : (identifier, ref) ∈ entries) :
    lookupName? entries (sourceIdName identifier) = some ref := by
  induction entries with
  | nil => simp at member
  | cons head tail ih =>
    by_cases same : head.1 = identifier
    · have refs : head.2 = ref := coherent identifier head.2 ref
        (List.mem_cons.mpr (Or.inl (Prod.ext same.symm rfl))) member
      simp [lookupName?, same, refs]
    · have rest : (identifier, ref) ∈ tail := by
        rcases List.mem_cons.mp member with equal | rest
        · exact (same (congrArg Prod.fst equal).symm).elim
        · exact rest
      have different : sourceIdName head.1 ≠ sourceIdName identifier :=
        fun equal => same (sourceIdName_injective equal)
      simpa [lookupName?, different] using ih
        (fun id left right first second => coherent id left right
          (List.mem_cons_of_mem head first) (List.mem_cons_of_mem head second)) rest

theorem lookupName?_slot (directory : DirectoryReadback) (frame : FrameReadback)
    (member : frame ∈ directory.frames) (index : Fin frame.slots.length) :
    lookupName? (names directory) (sourceIdName frame.slots[index.val].varId) =
      some (frame.view.token.ref index.val) := by
  apply lookupName?_of_mem (fun _ _ _ => names_functional directory)
  exact List.mem_flatMap.mpr ⟨frame, member, List.mem_ofFn.mpr ⟨index, rfl⟩⟩

private def coordinateNames (coordinates : Shared.Token × List (BitVec 64)) :
    List (BitVec 64 × Ref) :=
  coordinates.2.mapIdx fun index identifier => (identifier,coordinates.1.ref index)

private theorem names_coordinates (directory : DirectoryReadback) :
    names directory =
      (directory.frames.map (fun frame =>
        (frame.view.token,frame.slots.map FrameSlotView.varId))).flatMap coordinateNames := by
  simp only [names,List.flatMap_map]
  apply List.flatMap_congr
  intro frame _
  simp only [coordinateNames,List.mapIdx_eq_ofFn,List.get_eq_getElem,
    List.length_map,List.getElem_map,Fin.val_cast]

/-- Receiving a value changes no native lexical identity. Thus the same
source decoder remains valid after the directory's write clock advances. -/
theorem names_receiveDirectory {directory after : DirectoryReadback}
    {wanted : Destination} {value : BindingValueView}
    (received : receiveDirectory? directory wanted value = some after) :
    names after = names directory := by
  rw [names_coordinates,names_coordinates,
    receiveDirectory_coordinates directory after wanted value received]

/-- Only unframed IDs can be declared ambient. In particular, listing a stale
framed ID here cannot turn a missing current generation into a free variable. -/
def globals (identifiers : List (BitVec 64)) : List String :=
  (identifiers.filter fun identifier => variableEpoch identifier == 0).map sourceIdName

def sourceName (directory : DirectoryReadback) (name : String) : String :=
  match lookupName? (names directory) name with
  | some ref => CurrentStore.referenceName ref
  | none => CurrentStore.freeName name

def covered (directory : DirectoryReadback) (ambient : List (BitVec 64)) (atom : Atom) : Bool :=
  (TypeSubst.typeVars atom).all fun name =>
    (lookupName? (names directory) name).isSome || decide (name ∈ globals ambient)

def qualify? (directory : DirectoryReadback) (ambient : List (BitVec 64)) (atom : Atom) :
    Option Atom :=
  if covered directory ambient atom then some (renameTypeVars (sourceName directory) atom)
  else none

theorem qualify?_slot (directory : DirectoryReadback) (ambient : List (BitVec 64))
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length) :
    qualify? directory ambient (.var (sourceIdName frame.slots[index.val].varId)) =
      some (.var (CurrentStore.referenceName (frame.view.token.ref index.val))) := by
  simp [qualify?, covered, TypeSubst.typeVars, sourceName,
    lookupName?_slot directory frame member index, renameTypeVars]

theorem qualify?_unlisted_contextual (directory : DirectoryReadback)
    (ambient : List (BitVec 64)) (identifier : BitVec 64)
    (missing : lookupName? (names directory) (sourceIdName identifier) = none)
    (contextual : variableEpoch identifier ≠ 0) :
    qualify? directory ambient (.var (sourceIdName identifier)) = none := by
  have absent : sourceIdName identifier ∉ globals ambient := by
    intro member
    obtain ⟨actual, present, equal⟩ := List.mem_map.mp member
    have same := sourceIdName_injective equal
    subst actual
    exact contextual (beq_iff_eq.mp (List.mem_filter.mp present).2)
  simp [qualify?, covered, TypeSubst.typeVars, missing, absent]

variable {World : Type} [DecidableEq World]

/-- Reuse the existing finite graph observation and source decoder. The node
lookup checks membership; both child order and repeated uses are retained. -/
def atom? (symbols : PhysicalAtoms.NumberedSymbols World) (graph : AtomGraph World)
    (directory : DirectoryReadback) (ambient : List (BitVec 64)) (depth : Nat)
    (cursor : Cursor World) : Option Atom := do
  let node ← graph.node? cursor
  let raw ← PhysicalAtoms.sourceObservation? symbols cursor.world (observe graph.graph depth node)
  qualify? directory ambient raw

theorem atom?_key (symbols : PhysicalAtoms.NumberedSymbols World) (graph : AtomGraph World)
    (directory : DirectoryReadback) (ambient : List (BitVec 64)) (depth : Nat)
    (node : graph.Node) :
    atom? symbols graph directory ambient depth (graph.key node) =
      (PhysicalAtoms.sourceObservation? symbols (graph.key node).world
        (observe graph.graph depth node)).bind (qualify? directory ambient) := by
  unfold atom?
  rw [graph.node?_key]
  rfl

/-- Source naming depends on lexical coordinates, not a binding write clock. -/
theorem atom?_same_names {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {before after : DirectoryReadback} (equal : names after = names before)
    (ambient : List (BitVec 64)) (depth : Nat) :
    atom? symbols graph after ambient depth = atom? symbols graph before ambient depth := by
  have namesEqual : sourceName after = sourceName before := by
    funext name
    simp only [sourceName,equal]
  have qualified : qualify? after ambient = qualify? before ambient := by
    funext atom
    simp only [qualify?,covered,equal,namesEqual]
    rfl
  funext cursor
  unfold atom?
  rw [qualified]

/-- The admitted graph's readout is the actual memory observation, followed
by the checked source naming. The logical graph is not a replacement oracle. -/
theorem atom?_memory {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {memory : World → TargetMemory} {inventory : List (Cursor World)}
    (graphRead : readGraph? memory (fun _ => (none : Option Empty)) inventory = some graph)
    {directory : DirectoryReadback} {ambient : List (BitVec 64)} {depth : Nat}
    {cursor : Cursor World} {value : Atom}
    (read : atom? symbols graph directory ambient depth cursor = some value) :
    ∃ raw, (observeMemory memory (fun _ => (none : Option Empty)) depth cursor).bind
        (PhysicalAtoms.sourceObservation? symbols cursor.world) = some raw ∧
      qualify? directory ambient raw = some value := by
  obtain ⟨node, found, rest⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨raw, decoded, qualified⟩ := Option.bind_eq_some_iff.mp rest
  have key := (graph.node?_eq_some_iff cursor node).mp found
  subst cursor
  refine ⟨raw, ?_, qualified⟩
  rw [readGraph?_observe graphRead depth node]
  exact decoded

def value? (symbols : PhysicalAtoms.NumberedSymbols World) (graph : AtomGraph World)
    (directory : DirectoryReadback) (ambient : List (BitVec 64)) (depth : Nat) (world : World) :
    Option BindingValueView → Option (Option Atom)
  | none => some none
  | some payload => (atom? symbols graph directory ambient depth ⟨world, payload⟩).map some

/-- Metadata is copied from the actual current slot. Null/open slots are
retained and do not call the Atom reader. -/
def row? (symbols : PhysicalAtoms.NumberedSymbols World) (graph : AtomGraph World)
    (directory : DirectoryReadback) (ambient : List (BitVec 64)) (depth : Nat) (world : World)
    (raw : NativeRow) : Option SourceRow := do
  let value ← value? symbols graph directory ambient depth world raw.observed.value
  pure ⟨raw.reference, CurrentStore.referenceName raw.reference,
    ⟨value, raw.observed.writeVersion, raw.observed.writeClock, raw.observed.activationBoundary⟩⟩

def rows? (symbols : PhysicalAtoms.NumberedSymbols World) (graph : AtomGraph World)
    (directory : DirectoryReadback) (ambient : List (BitVec 64)) (depth : Nat) (world : World) :
    List NativeRow → Option (List SourceRow)
  | [] => some []
  | raw :: rest => do
    let row ← row? symbols graph directory ambient depth world raw
    let tail ← rows? symbols graph directory ambient depth world rest
    pure (row :: tail)

theorem row?_coordinates {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {directory : DirectoryReadback} {ambient : List (BitVec 64)} {depth : Nat} {world : World}
    {raw : NativeRow} {row : SourceRow}
    (read : row? symbols graph directory ambient depth world raw = some row) :
    row.reference = raw.reference ∧ row.name = CurrentStore.referenceName raw.reference ∧
      row.observed.writeVersion = raw.observed.writeVersion ∧
      row.observed.writeClock = raw.observed.writeClock ∧
      row.observed.activationBoundary = raw.observed.activationBoundary := by
  obtain ⟨value, _, equal⟩ := Option.bind_eq_some_iff.mp read
  have same : (⟨raw.reference, CurrentStore.referenceName raw.reference,
    ⟨value, raw.observed.writeVersion, raw.observed.writeClock,
      raw.observed.activationBoundary⟩⟩ : SourceRow) = row := Option.some.inj equal
  subst row
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem row?_value {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {directory : DirectoryReadback} {ambient : List (BitVec 64)} {depth : Nat} {world : World}
    {raw : NativeRow} {row : SourceRow}
    (read : row? symbols graph directory ambient depth world raw = some row) :
    value? symbols graph directory ambient depth world raw.observed.value =
      some row.observed.value := by
  obtain ⟨value, decoded, equal⟩ := Option.bind_eq_some_iff.mp read
  cases Option.some.inj equal
  exact decoded

theorem row?_outputAfter {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {directory : DirectoryReadback} {ambient : List (BitVec 64)} {depth : Nat} {world : World}
    {raw : NativeRow} {row : SourceRow}
    (read : row? symbols graph directory ambient depth world raw = some row) (boundary : Nat) :
    value? symbols graph directory ambient depth world (raw.observed.outputAfter boundary) =
      some (row.observed.outputAfter boundary) := by
  have version := (row?_coordinates read).2.2.1
  by_cases recent : boundary < raw.observed.writeVersion
  · simpa [SlotReadbackOf.outputAfter, version, recent] using row?_value read
  · simp [SlotReadbackOf.outputAfter, version, recent, value?]

theorem rows?_correspondence {symbols : PhysicalAtoms.NumberedSymbols World}
    {graph : AtomGraph World} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {raw : List NativeRow} {snapshot : List SourceRow}
    (read : rows? symbols graph directory ambient depth world raw = some snapshot) :
    List.Forall₂ (fun before after => row? symbols graph directory ambient depth world before =
      some after) raw snapshot := by
  induction raw generalizing snapshot with
  | nil => simp only [rows?, Option.some.injEq] at read; subst snapshot; exact .nil
  | cons head tail ih =>
    obtain ⟨first, firstRead, rest⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨remaining, tailRead, equal⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj equal
    exact .cons firstRead (ih tailRead)

theorem rows?_names {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {directory : DirectoryReadback} {ambient : List (BitVec 64)} {depth : Nat} {world : World}
    {raw : List NativeRow} {snapshot : List SourceRow}
    (read : rows? symbols graph directory ambient depth world raw = some snapshot) :
    snapshot.map RowOf.name = raw.map (fun row => CurrentStore.referenceName row.reference) := by
  have related := rows?_correspondence read
  clear read
  induction related with
  | nil => rfl
  | cons first _ ih => simp only [List.map_cons, (row?_coordinates first).2.1, ih]

/-- Every decoded source occurrence comes from a real raw slot occurrence. -/
theorem rows?_source_member {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {directory : DirectoryReadback} {ambient : List (BitVec 64)} {depth : Nat} {world : World}
    {raw : List NativeRow} {snapshot : List SourceRow}
    (read : rows? symbols graph directory ambient depth world raw = some snapshot)
    {row : SourceRow} (member : row ∈ snapshot) :
    ∃ slot ∈ raw, row? symbols graph directory ambient depth world slot = some row := by
  have related := rows?_correspondence read
  clear read
  induction related with
  | nil => simp at member
  | @cons head result tail remaining first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst row
      exact ⟨head,List.mem_cons_self,first⟩
    · obtain ⟨slot,present,decoded⟩ := ih member
      exact ⟨slot,List.mem_cons_of_mem head present,decoded⟩

theorem rows?_same_names {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {before after : DirectoryReadback} (equal : names after = names before)
    (ambient : List (BitVec 64)) (depth : Nat) (world : World) (raw : List NativeRow) :
    rows? symbols graph after ambient depth world raw =
      rows? symbols graph before ambient depth world raw := by
  have values : value? symbols graph after ambient depth world =
      value? symbols graph before ambient depth world := by
    funext payload
    cases payload <;> simp only [value?,atom?_same_names equal]
  have rowEqual : row? symbols graph after ambient depth world =
      row? symbols graph before ambient depth world := by
    funext slot
    simp only [row?,values]
  induction raw with
  | nil => rfl
  | cons head tail ih => simp only [rows?,rowEqual,ih]

/-- Decoding commutes with a real slot-value replacement, while retaining
the complete row metadata and every untouched source occurrence. -/
theorem row?_afterWrite {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {directory : DirectoryReadback} {ambient : List (BitVec 64)} {depth : Nat} {world : World}
    {raw : NativeRow} {row : SourceRow}
    (read : row? symbols graph directory ambient depth world raw = some row)
    {payload : BindingValueView} {atom : Atom}
    (decoded : atom? symbols graph directory ambient depth ⟨world,payload⟩ = some atom)
    (clock : Nat) (target : Ref) :
    row? symbols graph directory ambient depth world (raw.afterWrite clock target (some payload)) =
      some (row.afterWrite clock target (some atom)) := by
  obtain ⟨value,valueRead,finished⟩ := Option.bind_eq_some_iff.mp read
  cases Option.some.inj finished
  by_cases selected : raw.reference = target
  · simp [row?,RowOf.afterWrite,selected,value?,decoded]
  · simp [row?,RowOf.afterWrite,selected,valueRead]

theorem rows?_afterWrite {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {directory : DirectoryReadback} {ambient : List (BitVec 64)} {depth : Nat} {world : World}
    {raw : List NativeRow} {snapshot : List SourceRow}
    (read : rows? symbols graph directory ambient depth world raw = some snapshot)
    {payload : BindingValueView} {atom : Atom}
    (decoded : atom? symbols graph directory ambient depth ⟨world,payload⟩ = some atom)
    (clock : Nat) (target : Ref) :
    rows? symbols graph directory ambient depth world
        (raw.map (RowOf.afterWrite clock target (some payload))) =
      some (snapshot.map (RowOf.afterWrite clock target (some atom))) := by
  have related := rows?_correspondence read
  clear read
  induction related with
  | nil => rfl
  | cons first _ ih =>
    simp only [List.map_cons,rows?,row?_afterWrite first decoded,
      Option.bind_eq_bind,Option.bind_some,ih,pure]

/-- Read the complete admitted graph, every current slot, and the complete
pending tuple before constructing the single binding presentation. -/
def prepare? (symbols : PhysicalAtoms.NumberedSymbols World) (memory : World → TargetMemory)
    (directory : DirectoryReadback) (ambient : List (BitVec 64)) (depth : Nat) (world : World)
    (inventory : List (Cursor World)) (pending : List BindingValueView) :
    Option (List SourceRow × List Atom) := do
  let graph ← readGraph? memory (fun _ => (none : Option Empty)) inventory
  let snapshot ← rows? symbols graph directory ambient depth world (Snapshot.rows directory.toImage)
  let tuple ← pending.mapM fun payload => atom? symbols graph directory ambient depth ⟨world, payload⟩
  if Bindings.hasLoop ⟨CurrentStore.assignments snapshot, []⟩ then none
  else some (snapshot, tuple)

def readout? (symbols : PhysicalAtoms.NumberedSymbols World) (memory : World → TargetMemory)
    (directory : DirectoryReadback) (ambient : List (BitVec 64)) (depth : Nat) (world : World)
    (inventory : List (Cursor World)) (pending : List BindingValueView) : Option (List Atom) :=
  (prepare? symbols memory directory ambient depth world inventory pending).map fun (rows, tuple) =>
    tuple.map (CurrentStore.normalize (CurrentStore.assignments rows)).apply

theorem prepare?_components {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (read : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple)) :
    ∃ graph, readGraph? memory (fun _ => (none : Option Empty)) inventory = some graph ∧
      rows? symbols graph directory ambient depth world (Snapshot.rows directory.toImage) =
        some snapshot ∧
      pending.mapM (fun payload => atom? symbols graph directory ambient depth ⟨world, payload⟩) =
        some tuple ∧ Bindings.hasLoop ⟨CurrentStore.assignments snapshot, []⟩ = false := by
  obtain ⟨graph, graphRead, rest⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨rows, rowsRead, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨atoms, atomsRead, rest⟩ := Option.bind_eq_some_iff.mp rest
  split at rest
  · contradiction
  · next noLoop =>
    cases Option.some.inj rest
    exact ⟨graph, graphRead, rowsRead, atomsRead, Bool.eq_false_iff.mpr noLoop⟩

/-- A successful current-directory receipt is decoded as the same ordered
source-slot replacement. The Atom graph is unchanged; its actual decoder
also reads the new payload. The finite-reader check remains explicit. -/
theorem prepare?_receiveDirectory
    {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {memory : World → TargetMemory} {directory after : DirectoryReadback}
    {ambient : List (BitVec 64)} {depth : Nat} {world : World}
    {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (prepared : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot,tuple))
    (graphRead : readGraph? memory (fun _ => (none : Option Empty)) inventory = some graph)
    {wanted : Destination} {payload : BindingValueView} {atom : Atom}
    (received : receiveDirectory? directory wanted payload = some after)
    (decoded : atom? symbols graph directory ambient depth ⟨world,payload⟩ = some atom)
    (finite : Bindings.hasLoop ⟨CurrentStore.assignments
      (snapshot.map (RowOf.afterWrite after.directory.writeClock
        (wanted.token.ref wanted.slot) (some atom))),[]⟩ = false) :
    prepare? symbols memory after ambient depth world inventory pending =
      some (snapshot.map (RowOf.afterWrite after.directory.writeClock
        (wanted.token.ref wanted.slot) (some atom)),tuple) := by
  obtain ⟨observed,observedRead,rowsRead,tupleRead,_⟩ := prepare?_components prepared
  have sameGraph : observed = graph := Option.some.inj (observedRead.symm.trans graphRead)
  subst observed
  have namesEq := names_receiveDirectory received
  have nextRows : rows? symbols graph after ambient depth world (Snapshot.rows after.toImage) =
      some (snapshot.map (RowOf.afterWrite after.directory.writeClock
        (wanted.token.ref wanted.slot) (some atom))) := by
    rw [Snapshot.rows_write (receiveDirectory_correspondence directory after wanted payload received),
      DirectoryReadback.toImage_clock,rows?_same_names namesEq]
    exact rows?_afterWrite rowsRead decoded _ _
  have nextTuple : pending.mapM
      (fun value => atom? symbols graph after ambient depth ⟨world,value⟩) = some tuple := by
    rw [atom?_same_names namesEq]
    exact tupleRead
  simp only [prepare?,graphRead,Option.bind_eq_bind,Option.bind_some,nextRows,nextTuple,finite,
    Bool.false_eq_true,if_false]

/-- The certificate is earned by the actual successful native read, unique
current references and the existing finite normalization theorem. -/
theorem prepare?_certified {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (read : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple)) :
    ReadoutCertificate ⟨CurrentStore.assignments snapshot, []⟩
      (CurrentStore.normalize (CurrentStore.assignments snapshot)) := by
  obtain ⟨graph, _, rowsRead, _, noLoop⟩ := prepare?_components read
  apply CurrentStore.normalize_certified_of_noLoop (CurrentStore.assignments_unique ?_) noLoop
  rw [rows?_names rowsRead]
  simpa only [List.map_map, Function.comp_def] using
    (Snapshot.rows_reference_unique directory.toImage).map CurrentStore.referenceName_injective

/-- The logical store exposes aliases as equations, using the existing
constraint presentation rather than treating variable-valued slot contents
as rigid values. This projection does not rewrite the physical slots. -/
def logicalBindings (snapshot : List SourceRow) : Bindings :=
  aliasConstraints ⟨CurrentStore.assignments snapshot,[]⟩

theorem logicalBindings_agreement (snapshot : List SourceRow) :
    BindingSourceAgreement ⟨CurrentStore.assignments snapshot,[]⟩ (logicalBindings snapshot) :=
  ⟨fun model => (aliasConstraints_models _ model).symm,
    fun name => (aliasConstraints_support _ name).symm⟩

/-- The store view earns the comparison interface's shape condition even
when an actual slot contains another variable. This is not a consistency or
groundness claim. -/
theorem logicalBindings_nonvariable (snapshot : List SourceRow) :
    Spec.Match.SolutionTheory.HEAssignmentsNonVariable (logicalBindings snapshot) := by
  intro key name stored
  have shape := aliasConstraints_nonvariable ⟨CurrentStore.assignments snapshot,[]⟩
    key (.var name) stored
  cases shape

/-- The actual successful read earns the same finite table for the logical
alias presentation. No source table or desired readout is an input. -/
theorem prepare?_logical_certified {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (read : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot,tuple)) :
    ReadoutCertificate (logicalBindings snapshot)
      (CurrentStore.normalize (CurrentStore.assignments snapshot)) :=
  ReadoutCertificate.of_normal_theory (prepare?_certified read).normal
    (fun model => ((prepare?_certified read).theory model).trans
      ((logicalBindings_agreement snapshot).solutions model))

theorem readout?_prepared {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (read : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple)) :
    readout? symbols memory directory ambient depth world inventory pending =
      some (tuple.map (CurrentStore.normalize (CurrentStore.assignments snapshot)).apply) := by
  simp only [readout?, read, Option.map_some]

/-- One actual decoded packet realizes the nonvariable logical store view,
retaining every repeated and open operand under one common valuation. -/
theorem readout?_logical_observation {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple values : List Atom}
    (prepared : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot,tuple))
    (decoded : readout? symbols memory directory ambient depth world inventory pending = some values) :
    Spec.Bindings.ScopeObservation.observedTuples (logicalBindings snapshot) values =
      Spec.Bindings.ScopeObservation.observedTuples (logicalBindings snapshot) tuple := by
  have actual : values = tuple.map (CurrentStore.normalize (CurrentStore.assignments snapshot)).apply :=
    Option.some.inj (decoded.symm.trans (readout?_prepared prepared))
  rw [actual]
  exact (prepare?_logical_certified prepared).observedTuples_eq tuple

section FutureUnification

open Spec.Eval.Steps Spec.Bindings.ScopeObservation

/-- The actual decoded operand pair preserves success of the next source
unification against any equivalent certified frame. Reader refusal is not
admitted by the preparation and decoding premises. -/
theorem readout?_unify_exists_iff {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {target pattern targetRead patternRead : Atom}
    {rest restRead : List Atom} {source : Bindings} {table : TypeSubst}
    (prepared : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot,target :: pattern :: rest))
    (decoded : readout? symbols memory directory ambient depth world inventory pending =
      some (targetRead :: patternRead :: restRead))
    (agreement : BindingSourceAgreement (logicalBindings snapshot) source)
    (certified : ReadoutCertificate source table) :
    (∃ output, UnifyCandidateRel targetRead patternRead (logicalBindings snapshot) output) ↔
      ∃ output, UnifyCandidateRel (table.apply target) (table.apply pattern) source output := by
  have actual := Option.some.inj (decoded.symm.trans (readout?_prepared prepared))
  simp only [List.map_cons,List.cons.injEq] at actual
  obtain ⟨rfl,rfl,rfl⟩ := actual
  exact certified_unify_exists_iff agreement (prepare?_logical_certified prepared) certified target pattern

theorem readout?_unify_noMatch_iff {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {target pattern targetRead patternRead : Atom}
    {rest restRead : List Atom} {source : Bindings} {table : TypeSubst}
    (prepared : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot,target :: pattern :: rest))
    (decoded : readout? symbols memory directory ambient depth world inventory pending =
      some (targetRead :: patternRead :: restRead))
    (agreement : BindingSourceAgreement (logicalBindings snapshot) source)
    (certified : ReadoutCertificate source table) :
    UnifyNoMatchRel targetRead patternRead (logicalBindings snapshot) ↔
      UnifyNoMatchRel (table.apply target) (table.apply pattern) source := by
  simpa only [not_exists,UnifyNoMatchRel] using
    not_congr (readout?_unify_exists_iff prepared decoded agreement certified)

/-- Decoded native operands construct the counterpart source operation and
both reached readout certificates. The saved packet remains correlated after
the new constraint, even when its two stores choose different representatives.
This is a reader/source-operation law, not a native slot-write theorem. -/
theorem readout?_unify_transport {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {target pattern targetRead patternRead : Atom}
    {rest restRead : List Atom} {source output : Bindings} {table : TypeSubst}
    (prepared : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot,target :: pattern :: rest))
    (decoded : readout? symbols memory directory ambient depth world inventory pending =
      some (targetRead :: patternRead :: restRead))
    (agreement : BindingSourceAgreement (logicalBindings snapshot) source)
    (certified : ReadoutCertificate source table)
    (selected : UnifyCandidateRel targetRead patternRead (logicalBindings snapshot) output) :
    ∃ sourceOutput nextTable sourceNext,
      UnifyCandidateRel (table.apply target) (table.apply pattern) source sourceOutput ∧
      BindingSourceAgreement output sourceOutput ∧
      ReadoutCertificate output nextTable ∧ ReadoutCertificate sourceOutput sourceNext ∧
      restRead.map nextTable.apply = rest.map nextTable.apply ∧
      (rest.map table.apply).map sourceNext.apply = rest.map sourceNext.apply ∧
      observedTuples output (restRead.map nextTable.apply) =
        observedTuples sourceOutput ((rest.map table.apply).map sourceNext.apply) := by
  have actual := Option.some.inj (decoded.symm.trans (readout?_prepared prepared))
  simp only [List.map_cons,List.cons.injEq] at actual
  obtain ⟨rfl,rfl,rfl⟩ := actual
  obtain ⟨sourceOutput,nextTable,sourceNext,candidate,outputs,nextCertified,sourceCertified,packet⟩ :=
    selected.certifies_paired_pending agreement (prepare?_logical_certified prepared) certified
  exact ⟨sourceOutput,nextTable,sourceNext,candidate,outputs,nextCertified,sourceCertified,packet rest⟩

end FutureUnification

/-- One valuation and one presentation serve the entire ordered pending tuple.
This includes repeated variables and expressions that remain unevaluated. -/
theorem prepare?_joint_models {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (read : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple)) (valuation : String → Atom)
    (model : TypeBindingSatisfied valuation ⟨CurrentStore.assignments snapshot, []⟩) :
    (tuple.map (CurrentStore.normalize (CurrentStore.assignments snapshot)).apply).map
        (applyTypeValuation valuation) = tuple.map (applyTypeValuation valuation) := by
  rw [List.map_map]
  exact List.map_congr_left fun atom _ => (prepare?_certified read).preserves_model valuation model atom

/-- The actual reader's decoded packet has exactly the joint source
observation of its prepared operands. Repeated and open operands are read
together under the one earned binding presentation. -/
theorem readout?_joint_observation {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple values : List Atom}
    (prepared : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple))
    (decoded : readout? symbols memory directory ambient depth world inventory pending = some values) :
    Spec.Bindings.ScopeObservation.observedTuples ⟨CurrentStore.assignments snapshot, []⟩ values =
      Spec.Bindings.ScopeObservation.observedTuples ⟨CurrentStore.assignments snapshot, []⟩ tuple := by
  have actual : values = tuple.map (CurrentStore.normalize (CurrentStore.assignments snapshot)).apply :=
    Option.some.inj (decoded.symm.trans (readout?_prepared prepared))
  rw [actual]
  exact (prepare?_certified prepared).observedTuples_eq tuple

/-- The actual packet reader realizes any independently certified source
presentation of the same complete constraint theory. The two readout tables
may choose different alias representatives; all operand occurrences share
one valuation at the public boundary. -/
theorem readout?_joint_source_readout {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple values : List Atom} {source : Bindings} {table : TypeSubst}
    (prepared : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple))
    (decoded : readout? symbols memory directory ambient depth world inventory pending = some values)
    (agreement : BindingSourceAgreement ⟨CurrentStore.assignments snapshot, []⟩ source)
    (certified : ReadoutCertificate source table) :
    Spec.Bindings.ScopeObservation.observedTuples ⟨CurrentStore.assignments snapshot, []⟩ values =
      Spec.Bindings.ScopeObservation.observedTuples source (tuple.map table.apply) := by
  have same := (agreement.theoryEquivAt (TypeSubst.typeVarsList tuple)).observedTuples_eq
    tuple (fun _ member => member)
  exact (readout?_joint_observation prepared decoded).trans
    (same.trans (certified.observedTuples_eq tuple).symm)

/-- A future source merge preserves this decoded packet even when the
incoming logical store and its next readout use different representatives.
The actual merge supplies the extension law; no native mutation or evaluator
correspondence is assumed. -/
theorem readout?_joint_source_readout_after_merge
    {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple values : List Atom}
    {source extra output : Bindings} {table : TypeSubst}
    (prepared : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple))
    (decoded : readout? symbols memory directory ambient depth world inventory pending = some values)
    (agreement : BindingSourceAgreement ⟨CurrentStore.assignments snapshot, []⟩ source)
    (merged : Spec.Match.Merge.MergeRel Spec.Match.Merge.equalityGroundedSemantic source extra output)
    (certified : ReadoutCertificate output table) :
    Spec.Bindings.ScopeObservation.observedTuples output values =
      Spec.Bindings.ScopeObservation.observedTuples output (tuple.map table.apply) := by
  have actual : values = tuple.map (CurrentStore.normalize (CurrentStore.assignments snapshot)).apply :=
    Option.some.inj (decoded.symm.trans (readout?_prepared prepared))
  rw [actual]
  have preserved :
      Spec.Bindings.ScopeObservation.observedTuples output
          (tuple.map (CurrentStore.normalize (CurrentStore.assignments snapshot)).apply) =
        Spec.Bindings.ScopeObservation.observedTuples output tuple := by
    apply (prepare?_certified prepared).observedTuples_eq_after_extension
    intro model satisfied
    exact (agreement.solutions model).mpr
      (((Spec.Bindings.ScopeObservation.bindingSatisfied_append_iff model source extra).mp
        ((merged.bindingSourceAgreement.solutions model).mp satisfied)).1)
  exact preserved.trans (certified.observedTuples_eq tuple).symm

/-- An independently derived source merge consumes the earned logical alias
view. Its model extension preserves the already decoded packet jointly,
without asserting any unproved native slot-write law. -/
theorem readout?_logical_after_merge {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple values : List Atom} {extra output : Bindings} {table : TypeSubst}
    (prepared : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot,tuple))
    (decoded : readout? symbols memory directory ambient depth world inventory pending = some values)
    (merged : Spec.Match.Merge.MergeRel Spec.Match.Merge.equalityGroundedSemantic
      (logicalBindings snapshot) extra output)
    (certified : ReadoutCertificate output table) :
    Spec.Bindings.ScopeObservation.observedTuples output values =
      Spec.Bindings.ScopeObservation.observedTuples output (tuple.map table.apply) :=
  readout?_joint_source_readout_after_merge prepared decoded (logicalBindings_agreement snapshot) merged certified

/-- A later independent source merge preserves the meaning of an already
read packet. Its model-extension fact comes from that actual merge derivation;
the concrete store may choose a different finite readout afterwards. -/
theorem readout?_joint_observation_after_merge {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple values : List Atom} {extra output : Bindings}
    (prepared : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple))
    (decoded : readout? symbols memory directory ambient depth world inventory pending = some values)
    (merged : Spec.Match.Merge.MergeRel Spec.Match.Merge.equalityGroundedSemantic
      ⟨CurrentStore.assignments snapshot, []⟩ extra output) :
    Spec.Bindings.ScopeObservation.observedTuples output values =
      Spec.Bindings.ScopeObservation.observedTuples output tuple := by
  have actual : values = tuple.map (CurrentStore.normalize (CurrentStore.assignments snapshot)).apply :=
    Option.some.inj (decoded.symm.trans (readout?_prepared prepared))
  rw [actual]
  apply (prepare?_certified prepared).observedTuples_eq_after_extension
  intro model satisfied
  exact ((Spec.Bindings.ScopeObservation.bindingSatisfied_append_iff model _ _).mp
    ((merged.bindingSourceAgreement.solutions model).mp satisfied)).1

/-- Later source constraints absorb this earlier observation simultaneously.
This reuses the existing certificate law; it makes no assumption about a
native evaluator or an independent expected result for any operand. -/
theorem prepare?_pending_absorbed {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (read : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple)) {later : Bindings} {table : TypeSubst}
    (next : ReadoutCertificate later table)
    (extension : ∀ valuation, TypeBindingSatisfied valuation later →
      TypeBindingSatisfied valuation ⟨CurrentStore.assignments snapshot, []⟩) :
    (tuple.map (CurrentStore.normalize (CurrentStore.assignments snapshot)).apply).map table.apply =
      tuple.map table.apply :=
  (prepare?_certified read).pending_absorbed next extension tuple


/-- Every slot, including open slots, remains in its original occurrence.
This is exact traversal rather than a membership-only completeness premise. -/
theorem prepare?_slots {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (read : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple)) :
    ∃ graph, readGraph? memory (fun _ => (none : Option Empty)) inventory = some graph ∧
      List.Forall₂ (fun before after =>
        row? symbols graph directory ambient depth world before = some after)
        (Snapshot.rows directory.toImage) snapshot := by
  obtain ⟨graph, graphRead, rowsRead, _⟩ := prepare?_components read
  exact ⟨graph, graphRead, rows?_correspondence rowsRead⟩

theorem rows?_every_slot {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {directory : DirectoryReadback} {ambient : List (BitVec 64)} {depth : Nat} {world : World}
    {raw : List NativeRow} {snapshot : List SourceRow}
    (read : rows? symbols graph directory ambient depth world raw = some snapshot)
    {slot : NativeRow} (member : slot ∈ raw) :
    ∃ row ∈ snapshot, row? symbols graph directory ambient depth world slot = some row := by
  have related := rows?_correspondence read
  clear read
  induction related with
  | nil => simp at member
  | @cons head result tail remaining first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst slot
      exact ⟨result, List.mem_cons_self, first⟩
    · obtain ⟨row, present, decoded⟩ := ih member
      exact ⟨row, List.mem_cons_of_mem result present, decoded⟩

/-- The decoded native snapshot obeys the same independent open-slot model
law as the contextual store. No source decoder or post-write theory is
supplied as an oracle. -/
theorem rows?_open_write_models
    {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {directory : DirectoryReadback} {ambient : List (BitVec 64)} {depth : Nat} {world : World}
    {snapshot : List SourceRow}
    (rowsRead : rows? symbols graph directory ambient depth world
      (Snapshot.rows directory.toImage) = some snapshot)
    {raw : NativeRow} (read : Snapshot.readRow? directory.toImage raw.reference = some raw)
    (unbound : raw.observed.value = none) (clock : Nat) (atom : Atom) (valuation : String → Atom) :
    TypeBindingSatisfied valuation
        ⟨CurrentStore.assignments (snapshot.map (RowOf.afterWrite clock raw.reference (some atom))),[]⟩ ↔
      TypeBindingSatisfied valuation ⟨CurrentStore.assignments snapshot,[]⟩ ∧
        valuation (CurrentStore.referenceName raw.reference) = applyTypeValuation valuation atom := by
  apply CurrentStore.open_slot_write_models snapshot raw.reference
  · intro row member
    obtain ⟨slot,_,decoded⟩ := rows?_source_member rowsRead member
    exact (row?_coordinates decoded).2.1.trans
      (congrArg CurrentStore.referenceName (row?_coordinates decoded).1.symm)
  · obtain ⟨row,member,decoded⟩ := rows?_every_slot rowsRead (Snapshot.readRow?_mem_rows read)
    exact ⟨row,member,(row?_coordinates decoded).1⟩
  · intro row member selected
    obtain ⟨slot,slotMember,decoded⟩ := rows?_source_member rowsRead member
    have slotRef : slot.reference = raw.reference :=
      (row?_coordinates decoded).1.symm.trans selected
    have slotRead := Snapshot.rows_readback slotMember
    rw [slotRef] at slotRead
    have sameSlot : slot = raw := Option.some.inj (slotRead.symm.trans read)
    subst slot
    have empty := row?_value decoded
    rw [unbound] at empty
    exact (Option.some.inj empty).symm

/-- The real current-directory operation constructs the next certified
source frame. An open destination strengthens its theory by the actual
decoded equation, so every earlier correlated packet read remains usable. -/
theorem receiveDirectory_open_renewal
    {symbols : PhysicalAtoms.NumberedSymbols World} {graph : AtomGraph World}
    {memory : World → TargetMemory} {directory after : DirectoryReadback}
    {ambient : List (BitVec 64)} {depth : Nat} {world : World}
    {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (prepared : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot,tuple))
    (graphRead : readGraph? memory (fun _ => (none : Option Empty)) inventory = some graph)
    {wanted : Destination} {payload : BindingValueView} {atom : Atom}
    (received : receiveDirectory? directory wanted payload = some after)
    (decoded : atom? symbols graph directory ambient depth ⟨world,payload⟩ = some atom)
    {raw : NativeRow} (read : Snapshot.readRow? directory.toImage raw.reference = some raw)
    (selected : raw.reference = wanted.token.ref wanted.slot)
    (unbound : raw.observed.value = none)
    (finite : Bindings.hasLoop ⟨CurrentStore.assignments
      (snapshot.map (RowOf.afterWrite after.directory.writeClock
        (wanted.token.ref wanted.slot) (some atom))),[]⟩ = false) :
    let updated := snapshot.map (RowOf.afterWrite after.directory.writeClock
      (wanted.token.ref wanted.slot) (some atom))
    let beforeBindings : Bindings := ⟨CurrentStore.assignments snapshot,[]⟩
    let afterBindings : Bindings := ⟨CurrentStore.assignments updated,[]⟩
    let earlier := CurrentStore.normalize (CurrentStore.assignments snapshot)
    let later := CurrentStore.normalize (CurrentStore.assignments updated)
    ∃ _certificate : ReadoutCertificate afterBindings later,
      directoryProvider.step (base := ()) (index := ()) directory (wanted,payload) = ⟨true,after⟩ ∧
      prepare? symbols memory after ambient depth world inventory pending = some (updated,tuple) ∧
      (∀ valuation,TypeBindingSatisfied valuation afterBindings ↔
        TypeBindingSatisfied valuation beforeBindings ∧
          valuation (CurrentStore.referenceName raw.reference) = applyTypeValuation valuation atom) ∧
      (∀ value,later.apply (earlier.apply value) = later.apply value) ∧
      (∀ packet,Spec.Bindings.ScopeObservation.observedTuples afterBindings (packet.map earlier.apply) =
        Spec.Bindings.ScopeObservation.observedTuples afterBindings packet) := by
  intro updated beforeBindings afterBindings earlier later
  have next := prepare?_receiveDirectory prepared graphRead received decoded finite
  have nextCertificate := prepare?_certified next
  have beforeCertificate := prepare?_certified prepared
  obtain ⟨observed,observedRead,rowsRead,_⟩ := prepare?_components prepared
  have sameGraph : observed = graph := Option.some.inj (observedRead.symm.trans graphRead)
  subst observed
  have models : ∀ valuation,TypeBindingSatisfied valuation afterBindings ↔
      TypeBindingSatisfied valuation beforeBindings ∧
        valuation (CurrentStore.referenceName raw.reference) = applyTypeValuation valuation atom := by
    intro valuation
    simpa only [updated,afterBindings,beforeBindings,selected] using
      rows?_open_write_models rowsRead read unbound after.directory.writeClock atom valuation
  have extension : ∀ valuation,TypeBindingSatisfied valuation afterBindings →
      TypeBindingSatisfied valuation beforeBindings := fun valuation model => (models valuation).mp model |>.1
  exact ⟨nextCertificate,directoryProvider_accepted directory after wanted payload received,next,models,
    fun value => beforeCertificate.absorbs nextCertificate extension value,
    fun packet => beforeCertificate.observedTuples_eq_after_extension extension packet⟩

/-- An open current slot stays a free residual in the selected table. Its
metadata remains present; this is distinct from a failed/stale slot read. -/
theorem prepare?_open_slot {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (read : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple)) {raw : NativeRow}
    (present : Snapshot.readRow? directory.toImage raw.reference = some raw)
    (unbound : raw.observed.value = none) :
    (CurrentStore.normalize (CurrentStore.assignments snapshot)).apply
      (.var (CurrentStore.referenceName raw.reference)) =
        .var (CurrentStore.referenceName raw.reference) := by
  obtain ⟨graph, _, rowsRead, _⟩ := prepare?_components read
  obtain ⟨row, member, rowRead⟩ := rows?_every_slot rowsRead (Snapshot.readRow?_mem_rows present)
  have name := (row?_coordinates rowRead).2.1
  have empty := row?_value rowRead
  rw [unbound] at empty
  have empty : row.observed.value = none := (Option.some.inj empty).symm
  have unique : (snapshot.map RowOf.name).Nodup := by
    rw [rows?_names rowsRead]
    simpa only [List.map_map, Function.comp_def] using
      (Snapshot.rows_reference_unique directory.toImage).map CurrentStore.referenceName_injective
  rw [← name]
  exact CurrentStore.normalize_unassigned _ _ (CurrentStore.open_slot_not_assigned unique member empty)

/-- Actual activation lookup is decoded by the same graph and names. The
original lookup receipt distinguishes unknown from known-open; outer failure
remains an unreadable/stale observation. No historical trail supplies it. -/
def activation? (symbols : PhysicalAtoms.NumberedSymbols World) (graph : AtomGraph World)
    (memory : TargetMemory) (directory : DirectoryReadback) (ambient : List (BitVec 64))
    (depth : Nat) (world : World) (inventory : Activation.Inventory) (source : Address) :
    Option (Activation.Lookup × Option Atom) := do
  let observed ← Activation.readValue? directory memory inventory source
  match observed with
  | .unknown => some (Activation.Lookup.unknown, none)
  | .known value =>
    (value? symbols graph directory ambient depth world value).map
      (fun decoded => (Activation.Lookup.known value, decoded))

theorem activation?_source_slot (symbols : PhysicalAtoms.NumberedSymbols World)
    (graph : AtomGraph World) (memory : TargetMemory) (directory : DirectoryReadback)
    (ambient : List (BitVec 64)) (depth : Nat) (world : World)
    (inventory : Activation.Inventory) (source : Address) (frame : FrameReadback)
    (member : frame ∈ directory.frames) (index : Fin frame.slots.length)
    (identity : inventory.view.authority = encode frame.view.token)
    (known : frame.slots[index.val].sourceId ∈ inventory.sources)
    (kind : targetRead memory (sourceFieldAddress source 0) = some (.word 1))
    (sourceId : targetRead memory (sourceFieldAddress source 2) =
      some (.word frame.slots[index.val].sourceId))
    (row : SourceRow)
    (decoded : row? symbols graph directory ambient depth world
      ⟨frame.view.token.ref index.val, sourceIdName frame.slots[index.val].sourceId,
        ⟨frame.slots[index.val].value.payload, frame.slots[index.val].writeVersion,
          frame.view.writeClock, frame.view.boundary⟩⟩ = some row) :
    activation? symbols graph memory directory ambient depth world inventory source =
      some (.known (if inventory.view.firstWrite < frame.slots[index.val].writeVersion
        then frame.slots[index.val].value.payload else none),
        row.observed.outputAfter inventory.view.firstWrite) := by
  rw [activation?, Activation.readValue?_source_slot directory memory inventory source frame
    member index identity known kind sourceId]
  have valueRead := row?_outputAfter decoded inventory.view.firstWrite
  exact congrArg (Option.map fun value =>
    (Activation.Lookup.known (if inventory.view.firstWrite < frame.slots[index.val].writeVersion
      then frame.slots[index.val].value.payload else none), value)) valueRead

theorem activation?_unknown (symbols : PhysicalAtoms.NumberedSymbols World)
    (graph : AtomGraph World) (memory : TargetMemory) (directory : DirectoryReadback)
    (ambient : List (BitVec 64)) (depth : Nat) (world : World)
    (inventory : Activation.Inventory) (source : Address) (identifier : BitVec 64)
    (observed : readVariableId? memory ⟨some source, 0, 0⟩ = some identifier)
    (unknown : identifier ∉ inventory.sources) :
    activation? symbols graph memory directory ambient depth world inventory source =
      some (.unknown, none) := by
  unfold activation?
  rw [Activation.readValue?_unknown directory memory inventory source identifier observed unknown]
  rfl

/-- Successful whole preparation supplies the activation's decoded current
row. Only the actual source fields, current slot and activation authority
remain inputs; no separate payload readback hypothesis is required. -/
theorem prepare?_activation_slot {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (read : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple)) (activation : Activation.Inventory) (source : Address)
    (frame : FrameReadback) (member : frame ∈ directory.frames) (index : Fin frame.slots.length)
    (identity : activation.view.authority = encode frame.view.token)
    (known : frame.slots[index.val].sourceId ∈ activation.sources)
    (kind : targetRead (memory world) (sourceFieldAddress source 0) = some (.word 1))
    (sourceId : targetRead (memory world) (sourceFieldAddress source 2) =
      some (.word frame.slots[index.val].sourceId)) :
    ∃ graph row,
      readGraph? memory (fun _ => (none : Option Empty)) inventory = some graph ∧
      row ∈ snapshot ∧ row.reference = frame.view.token.ref index.val ∧
      row.name = CurrentStore.referenceName (frame.view.token.ref index.val) ∧
      activation? symbols graph (memory world) directory ambient depth world activation source =
        some (.known (if activation.view.firstWrite < frame.slots[index.val].writeVersion
          then frame.slots[index.val].value.payload else none),
          row.observed.outputAfter activation.view.firstWrite) := by
  obtain ⟨graph, graphRead, rowsRead, _⟩ := prepare?_components read
  have present := directory.toImage_frameAt frame.view.token.handle
    (directory.frame_agrees frame member).2
  rw [directory.select_frame frame member, Option.map_some] at present
  have slotRead := directory.toImage_readSlot frame member index.val
  rw [frame.toEntry_readSlot index] at slotRead
  let raw : NativeRow :=
    ⟨frame.view.token.ref index.val, sourceIdName frame.slots[index.val].sourceId,
      ⟨frame.slots[index.val].value.payload, frame.slots[index.val].writeVersion,
        frame.view.writeClock, frame.view.boundary⟩⟩
  have rawRead : Snapshot.readRow? directory.toImage raw.reference = some raw := by
    simp only [raw, Snapshot.readRow?, Token.ref, present]
    have named : frame.toEntry.frame[index.val]? =
        some (sourceIdName frame.slots[index.val].sourceId) := by
      simp [FrameReadback.toEntry, index.isLt]
    rw [named]
    simpa only [Token.ref, Option.map_some] using
      congrArg (Option.map (fun observed =>
        (⟨frame.view.token.ref index.val, sourceIdName frame.slots[index.val].sourceId,
          observed⟩ : NativeRow))) slotRead
  obtain ⟨row, rowMember, rowRead⟩ := rows?_every_slot rowsRead
    (Snapshot.readRow?_mem_rows rawRead)
  have coordinates := row?_coordinates rowRead
  refine ⟨graph, row, graphRead, rowMember, coordinates.1, coordinates.2.1, ?_⟩
  exact activation?_source_slot symbols graph (memory world) directory ambient depth world
    activation source frame member index identity known kind sourceId row rowRead


/-- A bound slot earns its actual payload read and its equation in the one
selected presentation. Neither that readout nor a model is an input. -/
theorem prepare?_bound_slot {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (read : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple)) {raw : NativeRow}
    (present : Snapshot.readRow? directory.toImage raw.reference = some raw)
    {payload : BindingValueView} (stored : raw.observed.value = some payload) :
    ∃ graph value,
      readGraph? memory (fun _ => (none : Option Empty)) inventory = some graph ∧
      atom? symbols graph directory ambient depth ⟨world, payload⟩ = some value ∧
      (CurrentStore.normalize (CurrentStore.assignments snapshot)).apply
          (.var (CurrentStore.referenceName raw.reference)) =
        (CurrentStore.normalize (CurrentStore.assignments snapshot)).apply value := by
  obtain ⟨graph, graphRead, rowsRead, _⟩ := prepare?_components read
  obtain ⟨row, member, rowRead⟩ := rows?_every_slot rowsRead (Snapshot.readRow?_mem_rows present)
  have decoded := row?_value rowRead
  rw [stored] at decoded
  obtain ⟨value, valueRead, same⟩ := Option.map_eq_some_iff.mp decoded
  have name := (row?_coordinates rowRead).2.1
  have cert := prepare?_certified read
  have model := (cert.theory _).mp (Theory.normal_presentedValuation_satisfied cert.normal)
  have equation := model.1 row.name value
    (CurrentStore.mem_assignments.mpr ⟨row, member, rfl, same.symm⟩)
  refine ⟨graph, value, graphRead, valueRead, ?_⟩
  simpa only [Theory.presentedValuation, Theory.applyTypeValuation_presented_eq_apply,
    name] using equation

private theorem tuple_correspondence {symbols : PhysicalAtoms.NumberedSymbols World}
    {graph : AtomGraph World} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {pending : List BindingValueView} {tuple : List Atom}
    (read : pending.mapM (fun payload => atom? symbols graph directory ambient depth
      ⟨world, payload⟩) = some tuple) :
    List.Forall₂ (fun payload value => atom? symbols graph directory ambient depth
      ⟨world, payload⟩ = some value) pending tuple := by
  induction pending generalizing tuple with
  | nil => simp only [List.mapM_nil, pure] at read; cases Option.some.inj read; exact .nil
  | cons head tail ih =>
    rw [List.mapM_cons] at read
    obtain ⟨first, firstRead, rest⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨remaining, tailRead, equal⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj equal
    exact .cons firstRead (ih tailRead)

/-- Exact order and multiplicity of the complete native pending tuple, with
actual memory observations at its retained world. -/
theorem prepare?_tuple_memory {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {pending : List BindingValueView}
    {snapshot : List SourceRow} {tuple : List Atom}
    (read : prepare? symbols memory directory ambient depth world inventory pending =
      some (snapshot, tuple)) :
    List.Forall₂ (fun payload value => ∃ raw,
      (observeMemory memory (fun _ => (none : Option Empty)) depth ⟨world, payload⟩).bind
        (PhysicalAtoms.sourceObservation? symbols world) = some raw ∧
      qualify? directory ambient raw = some value) pending tuple := by
  obtain ⟨graph, graphRead, _, tupleRead, _⟩ := prepare?_components read
  exact (tuple_correspondence tupleRead).imp fun _ _ decoded => atom?_memory graphRead decoded

namespace Controls

private def token : Token := ⟨1, 1⟩
private def x : BitVec 64 := BitVec.ofNat 64 ((encode token).toNat * 2 ^ 32 + 1)
private def y : BitVec 64 := BitVec.ofNat 64 ((encode token).toNat * 2 ^ 32 + 2)
private def address (storage : Nat) : Address := ⟨storage, 0, []⟩
private def payload (storage : Nat) : BindingValueView := ⟨some (address storage), 0, 0⟩
private def aliasPayload : BindingValueView := ⟨some (address 8), encode token, 1⟩
private def openValue : BindingValueView := ⟨none, 0, 0⟩
private def view : FrameStateView :=
  ⟨address 20, address 21, token, 2, 2, 0, 2, 0, false, true, true⟩
private def second (mode : Fin 3) : BindingValueView :=
  if mode.val = 0 then openValue else if mode.val = 1 then payload 4 else payload 1
private def frame (mode : Fin 3) : FrameReadback where
  view := view
  slots := [⟨1, x, 0, none, true, aliasPayload, 1⟩, ⟨2, y, 0, none, true, second mode, 2⟩]
  admitted := by fin_cases mode <;> decide
private def directory (mode : Fin 3) : DirectoryReadback where
  directory := ⟨address 20, some (address 21), 1, 0, 2⟩
  capacity := 2
  frames := [frame mode]
  admitted := by fin_cases mode <;> decide
private def symbols : PhysicalAtoms.NumberedSymbols Unit where
  bytes := fun _ _ => none
  unique := by intros; contradiction
private def stale : BitVec 64 := BitVec.ofNat 64 ((encode ⟨1, 2⟩).toNat * 2 ^ 32 + 1)
private def memory : Unit → TargetMemory := fun _ =>
  ⟨fun storage index =>
    if storage = 10 then
      if index < 2 then some (.reference (some (address 1))) else none
    else if index = 0 then
      if storage = 1 then some (.record "Atom" [.word 1, .word 0, .word x])
      else if storage = 2 then some (.record "Atom" [.word 1, .word 0, .word y])
      else if storage = 3 then some (.record "Atom"
        [.word 3, .word 0, .word 0, .word 0, .word 0, .reference none, .word 0, .word 0,
          .record "expr" [.reference (some (address 10)), .word 2]])
      else if storage = 4 then some (.record "Atom"
        [.word 0, .word 0, .word 0, .word 0, .word 0, .reference none])
      else if storage = 5 then some (.record "Atom" [.word 1, .word 0, .word 99])
      else if storage = 6 then some (.record "Atom" [.word 1, .word 0, .word stale])
      else if storage = 7 then some (.record "Atom" [.word 1, .word 0, .word 1])
      else if storage = 8 then some (.record "Atom" [.word 1, .word 0, .word 2])
      else none
    else none, fun _ => none⟩
private def cursor (storage : Nat) : Cursor Unit := ⟨(), payload storage⟩
private def inventory : List (Cursor Unit) := [cursor 1, cursor 2, cursor 3, cursor 4, cursor 5, cursor 6, ⟨(), aliasPayload⟩]
private def graphRows : List (KeyedRow (Cursor Unit) (Label Empty)) :=
  [⟨cursor 1, .variable x, []⟩, ⟨cursor 2, .variable y, []⟩,
    ⟨cursor 3, .expression, [cursor 1, cursor 1]⟩, ⟨cursor 4, .symbolBytes [], []⟩,
    ⟨cursor 5, .variable 99, []⟩, ⟨cursor 6, .variable stale, []⟩,
    ⟨⟨(), aliasPayload⟩, .variable y, []⟩]
private def graph : AtomGraph Unit := ⟨graphRows, by decide⟩
private theorem graph_rows : readRows? memory (fun _ => (none : Option Empty)) inventory =
    some graphRows := by decide
private theorem graph_read : readGraph? memory (fun _ => (none : Option Empty)) inventory =
    some graph := by
  change (readRows? memory (fun _ => (none : Option Empty)) inventory).bind decodeKeyedTable? = _
  rw [graph_rows]
  change decodeKeyedTable? graphRows = some graph
  exact dif_pos graph.valid
private def sx : String := CurrentStore.referenceName (token.ref 0)
private def sy : String := CurrentStore.referenceName (token.ref 1)
private def snapshot (mode : Fin 3) : List SourceRow :=
  [⟨token.ref 0, sx, ⟨some (.var sy), 1, 2, none⟩⟩,
    ⟨token.ref 1, sy, ⟨if mode.val = 0 then none else
      if mode.val = 1 then some (.symbol "") else some (.var sx), 2, 2, none⟩⟩]
private theorem x_read (mode : Fin 3) (ambient : List (BitVec 64) := []) : atom? symbols graph (directory mode) ambient 2 ⟨(), payload 1⟩ =
    some (.var sx) := by
  change atom? symbols graph (directory mode) ambient 2 (graph.key ⟨0, by decide⟩) = _
  rw [atom?_key]
  change (some (Atom.var (sourceIdName x))).bind (qualify? (directory mode) ambient) = _
  exact qualify?_slot (directory mode) ambient (frame mode) (by simp [directory]) ⟨0, by simp [frame]⟩
private theorem y_read (mode : Fin 3) (ambient : List (BitVec 64) := []) : atom? symbols graph (directory mode) ambient 2 ⟨(), payload 2⟩ =
    some (.var sy) := by
  change atom? symbols graph (directory mode) ambient 2 (graph.key ⟨1, by decide⟩) = _
  rw [atom?_key]
  change (some (Atom.var (sourceIdName y))).bind (qualify? (directory mode) ambient) = _
  exact qualify?_slot (directory mode) ambient (frame mode) (by simp [directory]) ⟨1, by simp [frame]⟩
private theorem alias_read (mode : Fin 3) (ambient : List (BitVec 64) := []) :
    atom? symbols graph (directory mode) ambient 2 ⟨(), aliasPayload⟩ = some (.var sy) := by
  change atom? symbols graph (directory mode) ambient 2 (graph.key ⟨6, by decide⟩) = _
  rw [atom?_key]
  change (some (Atom.var (sourceIdName y))).bind (qualify? (directory mode) ambient) = _
  exact qualify?_slot (directory mode) ambient (frame mode) (by simp [directory]) ⟨1, by simp [frame]⟩
private theorem empty_symbol_read (mode : Fin 3) (ambient : List (BitVec 64) := []) :
    atom? symbols graph (directory mode) ambient 2 ⟨(), payload 4⟩ = some (.symbol "") := by
  change atom? symbols graph (directory mode) ambient 2 (graph.key ⟨3, by decide⟩) = _
  rw [atom?_key]
  change qualify? (directory mode) ambient (.symbol "") = _
  simp [qualify?, covered, TypeSubst.typeVars, renameTypeVars]

private theorem repeated_read (mode : Fin 3) (ambient : List (BitVec 64) := []) :
    atom? symbols graph (directory mode) ambient 2 ⟨(), payload 3⟩ =
      some (.expression [.var sx, .var sx]) := by
  change atom? symbols graph (directory mode) ambient 2 (graph.key ⟨2, by decide⟩) = _
  rw [atom?_key]
  change qualify? (directory mode) ambient
    (.expression [.var (sourceIdName x), .var (sourceIdName x)]) = _
  have named := lookupName?_slot (directory mode) (frame mode)
    (by simp [directory]) ⟨0, by simp [frame]⟩
  change lookupName? (names (directory mode)) (sourceIdName x) = some (token.ref 0) at named
  simp [qualify?, covered, TypeSubst.typeVars, TypeSubst.typeVarsList,
    sourceName, named, renameTypeVars, sx]

private def nativeSnapshot (mode : Fin 3) : List NativeRow :=
  [⟨token.ref 0, sourceIdName 1, ⟨some aliasPayload, 1, 2, none⟩⟩,
    ⟨token.ref 1, sourceIdName 2,
      ⟨if mode.val = 0 then none else some (second mode), 2, 2, none⟩⟩]

private theorem native_snapshot (mode : Fin 3) :
    Snapshot.rows (directory mode).toImage = nativeSnapshot mode := by
  fin_cases mode <;> rfl

private theorem snapshot_read (mode : Fin 3) (ambient : List (BitVec 64) := []) :
    rows? symbols graph (directory mode) ambient 2 () (Snapshot.rows (directory mode).toImage) =
      some (snapshot mode) := by
  rw [native_snapshot]
  fin_cases mode <;>
    simp [nativeSnapshot, snapshot, rows?, row?, value?, second,
      x_read, alias_read, empty_symbol_read, sx, sy]

theorem alias_pending_tuple_is_prepared :
    prepare? symbols memory (directory 0) [] 2 () inventory [payload 3, payload 1] =
      some (snapshot 0, [.expression [.var sx, .var sx], .var sx]) := by
  simp only [prepare?, graph_read, Option.bind_eq_bind, Option.bind_some, snapshot_read,
    List.mapM_cons, List.mapM_nil, repeated_read, x_read, pure]
  decide

theorem actual_nonempty_alias_has_one_certificate :
    ReadoutCertificate ⟨CurrentStore.assignments (snapshot 0), []⟩
      (CurrentStore.normalize (CurrentStore.assignments (snapshot 0))) :=
  prepare?_certified alias_pending_tuple_is_prepared

theorem repeated_open_residuals_stay_correlated :
    readout? symbols memory (directory 0) [] 2 () inventory [payload 3, payload 1] =
      some [.expression [.var sy, .var sy], .var sy] := by
  rw [readout?_prepared alias_pending_tuple_is_prepared]
  simp [CurrentStore.assignments, CurrentStore.normalize, CurrentStore.normalizeFrom,
    snapshot, TypeSubst.bind, TypeSubst.apply, TypeSubst.lookup, TypeSubst.erase,
    TypeSubst.applyAssignment, sx, sy,
    CurrentStore.referenceName, token, Token.ref]

/-- The actual memory read supplies a different constraint record with the
earned nonvariable shape, certificate and complete repeated-operand readout. -/
theorem actual_reader_has_logical_binding_view :
    Spec.Match.SolutionTheory.HEAssignmentsNonVariable (logicalBindings (snapshot 0)) ∧
    ReadoutCertificate (logicalBindings (snapshot 0))
      (CurrentStore.normalize (CurrentStore.assignments (snapshot 0))) ∧
    logicalBindings (snapshot 0) ≠ ⟨CurrentStore.assignments (snapshot 0),[]⟩ ∧
    Spec.Bindings.ScopeObservation.observedTuples (logicalBindings (snapshot 0))
        [.expression [.var sy,.var sy],.var sy] =
      Spec.Bindings.ScopeObservation.observedTuples (logicalBindings (snapshot 0))
        [.expression [.var sx,.var sx],.var sx] := by
  refine ⟨logicalBindings_nonvariable _,prepare?_logical_certified alias_pending_tuple_is_prepared,?_,
    readout?_logical_observation alias_pending_tuple_is_prepared repeated_open_residuals_stay_correlated⟩
  intro same
  have assignments := congrArg Bindings.assignments same
  change [] = [(sx,Atom.var sy)] at assignments
  cases assignments

/-- A nonvariable constraint-record shape does not close an open alias or
select a ground value. Two distinct future valuations still satisfy it. -/
theorem actual_logical_alias_view_remains_open :
    TypeBindingSatisfied (fun _ => .symbol "A") (logicalBindings (snapshot 0)) ∧
    TypeBindingSatisfied (fun _ => .symbol "B") (logicalBindings (snapshot 0)) ∧
    (Atom.symbol "A" ≠ .symbol "B") := by
  refine ⟨?_,?_,by decide +kernel⟩
  · apply ((logicalBindings_agreement (snapshot 0)).solutions _).mp
    simp [TypeBindingSatisfied,CurrentStore.assignments,snapshot,applyTypeValuation]
  · apply ((logicalBindings_agreement (snapshot 0)).solutions _).mp
    simp [TypeBindingSatisfied,CurrentStore.assignments,snapshot,applyTypeValuation]

private def independentAlias : Bindings := ⟨[], [(sy, sx)]⟩
private def independentAliasTable : TypeSubst := [(sy, .var sx)]

private theorem independentAlias_agreement :
    BindingSourceAgreement ⟨CurrentStore.assignments (snapshot 0), []⟩ independentAlias := by
  constructor
  · intro model
    simp [TypeBindingSatisfied, CurrentStore.assignments, snapshot, independentAlias,
      applyTypeValuation, eq_comm]
  · intro name
    simp [Spec.Bindings.ScopeObservation.specBindingVars, CurrentStore.assignments, snapshot,
      independentAlias, TypeSubst.typeVars, or_comm]

/-- The source alias edge is deliberately oriented oppositely to the actual
slot assignment. Its finite readout is earned by its independent equation fold. -/
theorem independent_alias_readout_certificate :
    ReadoutCertificate independentAlias independentAliasTable := by
  apply ReadoutCertificate.of_fold
  change EquationListPresentationRel [(.var sy, .var sx)] [] independentAliasTable
  apply EquationListPresentationRel.cons _ (.nil _)
  apply AppliedTypePresentationMatchRel.ordinary
    (TypeSubst.apply_empty (.var sy)) (TypeSubst.apply_empty (.var sx))
  simpa [independentAliasTable, TypeSubst.bind, TypeSubst.apply, TypeSubst.lookup,
    TypeSubst.erase] using
    (AppliedReducedTypeMatchRel.bindLeft (substitution := []) (name := sy)
      (right := .var sx) (by decide +kernel))

/-- The actual memory reader's repeated open residuals agree jointly with
the independent source readout, although their literal representatives differ. -/
theorem actual_reader_has_independent_joint_readout :
    Spec.Bindings.ScopeObservation.observedTuples
        ⟨CurrentStore.assignments (snapshot 0), []⟩
        [.expression [.var sy, .var sy], .var sy] =
      Spec.Bindings.ScopeObservation.observedTuples independentAlias
        ([.expression [.var sx, .var sx], .var sx].map independentAliasTable.apply) :=
  readout?_joint_source_readout alias_pending_tuple_is_prepared
    repeated_open_residuals_stay_correlated independentAlias_agreement
    independent_alias_readout_certificate

/-- Requiring the actual reader to choose the independent source table's
literal open name is false. This is reader execution, not a list-only control. -/
theorem actual_reader_does_not_choose_source_representative :
    readout? symbols memory (directory 0) [] 2 () inventory [payload 3, payload 1] ≠
      some ([Atom.expression [.var sx, .var sx], .var sx].map independentAliasTable.apply) := by
  rw [repeated_open_residuals_stay_correlated]
  have different : sx ≠ sy := by decide +kernel
  have fixed :
      ([Atom.expression [.var sx, .var sx], .var sx].map independentAliasTable.apply) =
        [.expression [.var sx, .var sx], .var sx] := by
    simp [independentAliasTable, TypeSubst.apply, TypeSubst.lookup, different]
  rw [fixed]
  decide +kernel

/-- The actual memory-reader packet is used as the next source operation's
operands. Both output certificates and the independent counterpart operation
are earned, while the saved repeated packet keeps its joint observation. -/
theorem actual_reader_next_source_unification :
    readout? symbols memory (directory 0) [] 2 () inventory
        [payload 1,payload 4,payload 3,payload 1] =
      some [.var sy,.symbol "",.expression [.var sy,.var sy],.var sy] ∧
    ∃ output sourceOutput nextTable sourceNext,
      Spec.Eval.Steps.UnifyCandidateRel (.var sy) (.symbol "") (logicalBindings (snapshot 0)) output ∧
      Spec.Eval.Steps.UnifyCandidateRel (independentAliasTable.apply (.var sx))
        (independentAliasTable.apply (.symbol "")) independentAlias sourceOutput ∧
      BindingSourceAgreement output sourceOutput ∧
      ReadoutCertificate output nextTable ∧ ReadoutCertificate sourceOutput sourceNext ∧
      Spec.Bindings.ScopeObservation.observedTuples output
          ([Atom.expression [.var sy,.var sy],.var sy].map nextTable.apply) =
        Spec.Bindings.ScopeObservation.observedTuples sourceOutput
          (([Atom.expression [.var sx,.var sx],.var sx].map independentAliasTable.apply).map sourceNext.apply) := by
  have prepared : prepare? symbols memory (directory 0) [] 2 () inventory
      [payload 1,payload 4,payload 3,payload 1] =
      some (snapshot 0,[.var sx,.symbol "",.expression [.var sx,.var sx],.var sx]) := by
    simp only [prepare?,graph_read,Option.bind_eq_bind,Option.bind_some,snapshot_read,
      List.mapM_cons,List.mapM_nil,x_read,empty_symbol_read,repeated_read,pure]
    decide
  have decoded : readout? symbols memory (directory 0) [] 2 () inventory
      [payload 1,payload 4,payload 3,payload 1] =
      some [.var sy,.symbol "",.expression [.var sy,.var sy],.var sy] := by
    rw [readout?_prepared prepared]
    simp [CurrentStore.assignments,CurrentStore.normalize,CurrentStore.normalizeFrom,
      snapshot,TypeSubst.bind,TypeSubst.apply,TypeSubst.lookup,TypeSubst.erase,
      TypeSubst.applyAssignment,sx,sy,CurrentStore.referenceName,token,Token.ref]
  obtain ⟨output,selected⟩ := (Spec.Eval.Steps.unifyCandidate_exists_iff_equation_model
    (.var sy) (.symbol "") (logicalBindings (snapshot 0))).mpr
      ⟨fun _ => .symbol "",(logicalBindings_agreement (snapshot 0)).solutions _ |>.mp
        (by simp [TypeBindingSatisfied,CurrentStore.assignments,snapshot,applyTypeValuation]),
        by simp [applyTypeValuation]⟩
  obtain ⟨sourceOutput,nextTable,sourceNext,candidate,agreement,nextCertified,sourceCertified,packet⟩ :=
    readout?_unify_transport prepared decoded
      ((logicalBindings_agreement (snapshot 0)).symm.trans independentAlias_agreement)
      independent_alias_readout_certificate selected
  exact ⟨decoded,output,sourceOutput,nextTable,sourceNext,selected,candidate,agreement,
    nextCertified,sourceCertified,packet.2.2⟩

private def receiptDestination (mode : Fin 3) : Destination :=
  destination (frame mode) ⟨1,by simp [frame]⟩

private def openReceived : DirectoryReadback :=
  (receiveDirectory? (directory 0) (receiptDestination 0) (payload 4)).get (by decide +kernel)

private theorem open_received :
    receiveDirectory? (directory 0) (receiptDestination 0) (payload 4) = some openReceived :=
  (Option.some_get _).symm

private def openRaw : NativeRow :=
  (Snapshot.readRow? (directory 0).toImage (token.ref 1)).get (by decide +kernel)

private def openUpdated : List SourceRow :=
  (snapshot 0).map (RowOf.afterWrite openReceived.directory.writeClock (token.ref 1) (some (.symbol "")))

/-- The actual directory receipt writes the open alias target. The decoder
retains the earlier repeated packet, earns the new certificate, and reads
both old occurrences through the same new ground value. -/
theorem actual_open_receipt_retains_the_saved_packet :
    ∃ _certificate : ReadoutCertificate ⟨CurrentStore.assignments openUpdated,[]⟩
        (CurrentStore.normalize (CurrentStore.assignments openUpdated)),
      directoryProvider.step (base := ()) (index := ()) (directory 0)
        (receiptDestination 0,payload 4) = ⟨true,openReceived⟩ ∧
      prepare? symbols memory openReceived [] 2 () inventory [payload 3,payload 1] =
        some (openUpdated,[.expression [.var sx,.var sx],.var sx]) ∧
      (∀ value,(CurrentStore.normalize (CurrentStore.assignments openUpdated)).apply
        ((CurrentStore.normalize (CurrentStore.assignments (snapshot 0))).apply value) =
        (CurrentStore.normalize (CurrentStore.assignments openUpdated)).apply value) ∧
      readout? symbols memory openReceived [] 2 () inventory [payload 3,payload 1] =
        some [.expression [.symbol "",.symbol ""],.symbol ""] ∧
      openReceived.directory.writeClock = 3 := by
  have renewed := receiveDirectory_open_renewal alias_pending_tuple_is_prepared graph_read
    open_received (empty_symbol_read 0) (raw := openRaw)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨certificate,accepted,prepared,_,absorbs,_⟩ := renewed
  refine ⟨certificate,accepted,prepared,absorbs,?_,by decide +kernel⟩
  have target : (receiptDestination 0).token.ref (receiptDestination 0).slot = token.ref 1 := rfl
  simp only [target] at prepared
  rw [readout?_prepared prepared]
  simp [CurrentStore.assignments,CurrentStore.normalize,CurrentStore.normalizeFrom,
    snapshot,RowOf.afterWrite,TypeSubst.bind,TypeSubst.apply,TypeSubst.lookup,TypeSubst.erase,
    TypeSubst.applyAssignment,sx,sy,CurrentStore.referenceName,token,Token.ref]

private def overwritten : DirectoryReadback :=
  (receiveDirectory? (directory 1) (receiptDestination 1) (payload 5)).get (by decide +kernel)

private def free99 : String := CurrentStore.freeName (sourceIdName 99)

private def overwrittenRows : List SourceRow :=
  (snapshot 1).map (RowOf.afterWrite overwritten.directory.writeClock (token.ref 1) (some (.var free99)))

private theorem overwritten_prepared :
    prepare? symbols memory overwritten [99] 2 () inventory [payload 3,payload 1] =
      some (overwrittenRows,[.expression [.var sx,.var sx],.var sx]) := by
  have before : prepare? symbols memory (directory 1) [99] 2 () inventory [payload 3,payload 1] =
      some (snapshot 1,[.expression [.var sx,.var sx],.var sx]) := by
    simp only [prepare?,graph_read,Option.bind_eq_bind,Option.bind_some,snapshot_read,
      List.mapM_cons,List.mapM_nil,repeated_read,x_read,pure]
    decide
  have decoded : atom? symbols graph (directory 1) [99] 2 ⟨(),payload 5⟩ = some (.var free99) := by
    change atom? symbols graph (directory 1) [99] 2 (graph.key ⟨4,by decide⟩) = _
    rw [atom?_key]
    change qualify? (directory 1) [99] (.var (sourceIdName 99)) = _
    have admitted : covered (directory 1) [99] (.var (sourceIdName 99)) = true := by decide +kernel
    have absent : lookupName? (names (directory 1)) (sourceIdName 99) = none := by decide +kernel
    unfold qualify?
    rw [admitted,if_pos rfl]
    simp only [renameTypeVars,sourceName,absent,free99]
  have received : receiveDirectory? (directory 1) (receiptDestination 1) (payload 5) =
      some overwritten := (Option.some_get _).symm
  exact prepare?_receiveDirectory before graph_read received decoded (by decide +kernel)

/-- Overwriting a bound target is a real successful receipt and remains
readable, but its new constraints do not preserve the old source theory. -/
theorem actual_bound_overwrite_does_not_strengthen_the_old_frame :
    prepare? symbols memory overwritten [99] 2 () inventory [payload 3,payload 1] =
      some (overwrittenRows,[.expression [.var sx,.var sx],.var sx]) ∧
    readout? symbols memory overwritten [99] 2 () inventory [payload 3,payload 1] =
      some [.expression [.var free99,.var free99],.var free99] ∧
    ¬(∀ valuation,TypeBindingSatisfied valuation ⟨CurrentStore.assignments overwrittenRows,[]⟩ →
      TypeBindingSatisfied valuation ⟨CurrentStore.assignments (snapshot 1),[]⟩) := by
  refine ⟨overwritten_prepared,?_,?_⟩
  · rw [readout?_prepared overwritten_prepared]
    have different : sx ≠ sy := by decide +kernel
    have outsideX : free99 ≠ sx :=
      (CurrentStore.referenceName_ne_freeName (token.ref 0) (sourceIdName 99)).symm
    simp [overwrittenRows,CurrentStore.assignments,CurrentStore.normalize,CurrentStore.normalizeFrom,
      snapshot,RowOf.afterWrite,TypeSubst.bind,TypeSubst.apply,TypeSubst.lookup,TypeSubst.erase,
      TypeSubst.applyAssignment,token,Token.ref,different,outsideX]
  ·
    intro strengthens
    have current : TypeBindingSatisfied (fun _ => .symbol "Z")
        ⟨CurrentStore.assignments overwrittenRows,[]⟩ := by
      refine ⟨?_,by simp⟩
      intro key term stored
      simp [overwrittenRows,CurrentStore.assignments,snapshot,RowOf.afterWrite,
        token,Token.ref] at stored
      rcases stored with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [applyTypeValuation]
    have old := strengthens _ current
    have impossible := old.1 sy (.symbol "") (by simp [CurrentStore.assignments,snapshot])
    simp [applyTypeValuation] at impossible

theorem ground_assignment_reaches_both_uses :
    readout? symbols memory (directory 1) [] 2 () inventory [payload 3, payload 1] =
      some [.expression [.symbol "", .symbol ""], .symbol ""] := by
  have prepared : prepare? symbols memory (directory 1) [] 2 () inventory [payload 3, payload 1] =
      some (snapshot 1, [.expression [.var sx, .var sx], .var sx]) := by
    simp only [prepare?, graph_read, Option.bind_eq_bind, Option.bind_some, snapshot_read,
      List.mapM_cons, List.mapM_nil, repeated_read, x_read, pure]
    decide
  rw [readout?_prepared prepared]
  simp [CurrentStore.assignments, CurrentStore.normalize, CurrentStore.normalizeFrom,
    snapshot, TypeSubst.bind, TypeSubst.apply, TypeSubst.lookup, TypeSubst.erase,
    TypeSubst.applyAssignment, sx, sy,
    CurrentStore.referenceName, token, Token.ref]

theorem cyclic_snapshot_is_reader_refusal :
    prepare? symbols memory (directory 2) [] 2 () inventory [] = none := by
  simp only [prepare?, graph_read, Option.bind_eq_bind, Option.bind_some, snapshot_read,
    List.mapM_nil, pure]
  decide

theorem missing_graph_node_is_not_open :
    atom? symbols graph (directory 0) [] 2 ⟨(), payload 77⟩ = none := by
  have missing : graph.node? ⟨(), payload 77⟩ = none := by decide
  unfold atom?
  rw [missing]
  rfl

theorem zero_depth_is_not_successful_empty_readout :
    atom? symbols graph (directory 0) [] 0 (cursor 1) = none := by
  change atom? symbols graph (directory 0) [] 0 (graph.key ⟨0, by decide⟩) = _
  rw [atom?_key]
  rfl

theorem stale_id_cannot_be_declared_ambient :
    qualify? (directory 0) [stale] (.var (sourceIdName stale)) = none := by
  apply qualify?_unlisted_contextual
  · decide
  · decide

theorem undeclared_ambient_is_refused :
    qualify? (directory 0) [] (.var (sourceIdName 99)) = none := by decide

theorem declared_ambient_retains_its_identity :
    qualify? (directory 0) [99] (.var (sourceIdName 99)) =
      some (.var (CurrentStore.freeName (sourceIdName 99))) := by
  have missing : lookupName? (names (directory 0)) (sourceIdName 99#64) = none := by decide
  have ambient : sourceIdName 99#64 ∈ globals [99#64] := by decide
  simp [qualify?, covered, sourceName, missing, ambient, TypeSubst.typeVars, renameTypeVars]

end Controls

#print axioms prepare?_certified
#print axioms prepare?_bound_slot
#print axioms prepare?_tuple_memory
#print axioms prepare?_joint_models
#print axioms prepare?_pending_absorbed
#print axioms activation?_source_slot
#print axioms prepare?_activation_slot

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory.NativePayload.CurrentBindings

/-! ## Entered ordinary-return readback from the current binding store

This downstream instance supplies the Atom and binding readers of the existing
native frame adapter. Its binding region has an authoritative borrowed frame
directory and no additional flat or equality rows. Borrowed inventory validity,
the native layout interpretation and the space API remain explicit boundaries.
The saved post-argument call is read structurally, never substituted again.

An entered CALLER frame is the starting point. These laws do not select the
ordinary branch of RESULT dispatch, execute CALLER's binding fold, or establish
its transition to BIND. In particular, an inert symbol may take another native
dispatch branch before reaching this point.
-/
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory.NativePayload.CurrentReturn

open Mettapedia.GSLT.LanguageDef.NativeOps
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared MetavariableFrameStore.Snapshot
open Mettapedia.Languages.MeTTa.HE
open Spec.Type Spec.Type.RuntimeRefinement Spec.Type.Presentation
open Spec.Type.Presentation.BindingTheory Spec.Eval
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback
open NativeFrames CurrentBindings
open CeTTaRuntimeContracts NativeCallFrame NativeCallFrame.Copy

variable {World : Type} [DecidableEq World]

/-- An Atom pointer at the materialized C interface carries no deferred
context. Contextual BindingValue payloads inside the store retain their tags
and epochs in the existing graph reader. -/
def pointerValue (pointer : Ptr) : BindingValueView :=
  ⟨some (CurrentValueRead.physicalAddress pointer), 0, 0⟩

abbrev snapshotBindings (snapshot : List SourceRow) : Bindings :=
  ⟨CurrentStore.assignments snapshot, []⟩

/-- This admits a complete frame-only binding image. A nonempty omitted flat
row, a different directory or Prime state causes refusal, not an empty source
environment. Native metadata remains in the retained physical storage. -/
def imageBindings? (directory : DirectoryReadback) (snapshot : List SourceRow)
    (image : BindingImage) : Option Bindings :=
  if image.sharedRows = [] ∧ image.exclusiveRows = [] ∧ image.constraintRows = [] ∧
      image.prime = none ∧
      image.frameIndex.map CurrentValueRead.physicalAddress = directory.directory.directory then
    some (snapshotBindings snapshot)
  else none

def atomPayloads (symbols : PhysicalAtoms.NumberedSymbols World) (graph : AtomGraph World)
    (directory : DirectoryReadback) (ambient : List (BitVec 64)) (depth : Nat) (world : World)
    (spaces : Ptr → Option Space) : PayloadReadback where
  atom := fun address => atom? symbols graph directory ambient depth ⟨world, pointerValue address⟩
  space := spaces
  bindings := fun _ => none

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def payloads (symbols : PhysicalAtoms.NumberedSymbols World) (graph : AtomGraph World)
    (directory : DirectoryReadback) (ambient : List (BitVec 64)) (depth : Nat) (world : World)
    (spaces : Ptr → Option Space) (snapshot : List SourceRow)
    (entryExtent constraintExtent : Nat) (heap : Heap L) : PayloadReadback :=
  payloadsFromBindingImage entryExtent constraintExtent heap
    (atomPayloads symbols graph directory ambient depth world spaces)
    (imageBindings? directory snapshot)

theorem payloads_binding_owned (symbols : PhysicalAtoms.NumberedSymbols World)
    (graph : AtomGraph World) (directory : DirectoryReadback) (ambient : List (BitVec 64))
    (depth : Nat) (world : World) (spaces : Ptr → Option Space) (snapshot : List SourceRow)
    (entryExtent constraintExtent : Nat) (heap : Heap L) (address : Ptr)
    (descriptor : BindingDescriptor) (rest : Heap L → Prop)
    (owned : (BindingCells address descriptor ∗ rest) heap)
    (flat : descriptor.length = 0) (shared : descriptor.sharedLength = 0)
    (equalities : descriptor.equalityLength = 0) (he : descriptor.prime = none)
    (directoryPointer : descriptor.frameIndex.map CurrentValueRead.physicalAddress =
      directory.directory.directory) :
    (payloads symbols graph directory ambient depth world spaces snapshot
      entryExtent constraintExtent heap).bindings address = some (snapshotBindings snapshot) := by
  have fields := owned_binding_descriptor address descriptor rest heap owned
  simp [payloads, payloadsFromBindingImage, bindingImage?, fields, imageOfDescriptor?,
    flat, shared, equalities, segmentReadback?, imageBindings?, he, directoryPointer]

/-- Structural observations of the four actual pointers. The same graph and
current-name map also read the remaining pending tuple. -/
theorem prepared_operands {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)}
    {original demand variantOnly materialized : Ptr} {pending : List BindingValueView}
    {snapshot : List SourceRow} {call expected raw value : Atom} {remaining : List Atom}
    (prepared : prepare? symbols memory directory ambient depth world inventory
      (pointerValue original :: pointerValue demand :: pointerValue variantOnly ::
        pointerValue materialized :: pending) =
      some (snapshot, call :: expected :: raw :: value :: remaining)) :
    ∃ graph, readGraph? memory (fun _ => (none : Option Empty)) inventory = some graph ∧
      rows? symbols graph directory ambient depth world (Snapshot.rows directory.toImage) =
        some snapshot ∧
      atom? symbols graph directory ambient depth ⟨world, pointerValue original⟩ = some call ∧
      atom? symbols graph directory ambient depth ⟨world, pointerValue demand⟩ = some expected ∧
      atom? symbols graph directory ambient depth ⟨world, pointerValue variantOnly⟩ = some raw ∧
      atom? symbols graph directory ambient depth ⟨world, pointerValue materialized⟩ = some value ∧
      pending.mapM (fun payload => atom? symbols graph directory ambient depth ⟨world, payload⟩) =
        some remaining := by
  obtain ⟨graph, graphRead, rowsRead, tupleRead, _⟩ := prepare?_components prepared
  have uncons : ∀ (head : BindingValueView) (tail : List BindingValueView)
      (first : Atom) (rest : List Atom),
      (head :: tail).mapM (fun payload => atom? symbols graph directory ambient depth
        ⟨world, payload⟩) = some (first :: rest) →
      atom? symbols graph directory ambient depth ⟨world, head⟩ = some first ∧
        tail.mapM (fun payload => atom? symbols graph directory ambient depth
          ⟨world, payload⟩) = some rest := by
    intro head tail first rest read
    rw [List.mapM_cons] at read
    obtain ⟨value, headRead, read⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨values, tailRead, equal⟩ := Option.bind_eq_some_iff.mp read
    have equal := List.cons.inj (Option.some.inj equal)
    cases equal.1
    cases equal.2
    exact ⟨headRead, tailRead⟩
  obtain ⟨firstRead, rest⟩ := uncons _ _ _ _ tupleRead
  obtain ⟨secondRead, rest⟩ := uncons _ _ _ _ rest
  obtain ⟨thirdRead, rest⟩ := uncons _ _ _ _ rest
  obtain ⟨fourthRead, rest⟩ := uncons _ _ _ _ rest
  exact ⟨graph, graphRead, rowsRead, firstRead, secondRead, thirdRead, fourthRead, rest⟩

def observedInvocation (caller : NativeCaller) (parent : PushArguments)
    (prepared : PreparedOutcome) (space : Space) (target : Ptr)
    (snapshot : List SourceRow) (call expected raw value : Atom) :
    CallReturnControl.Invocation NativeCaller :=
  ⟨caller, space, call, expected, prepared.row, snapshotBindings snapshot,
    value, raw, pointerIdentity target, pointerIdentity prepared.relay,
    parent.fuel.toInt, parent.preserve, .raw⟩

theorem invocation_from_prepared_operands (symbols : PhysicalAtoms.NumberedSymbols World)
    (graph : AtomGraph World) (directory : DirectoryReadback) (ambient : List (BitVec 64))
    (depth : Nat) (world : World) (spaces : Ptr → Option Space) (snapshot : List SourceRow)
    (entryExtent constraintExtent : Nat) (heap : Heap L)
    (caller : NativeCaller) (parent : PushArguments) (prepared : PreparedOutcome)
    (original demand spaceAddress target : Ptr) (space : Space)
    (call expected raw value : Atom)
    (kind : parent.kind = 7) (callPointer : parent.atom = some original)
    (demandPointer : parent.demand = some demand) (spacePointer : parent.space = some spaceAddress)
    (targetPointer : parent.target = some target) (spaceRead : spaces spaceAddress = some space)
    (callRead : atom? symbols graph directory ambient depth ⟨world, pointerValue original⟩ = some call)
    (demandRead : atom? symbols graph directory ambient depth ⟨world, pointerValue demand⟩ = some expected)
    (rawRead : atom? symbols graph directory ambient depth ⟨world, pointerValue prepared.variantOnly⟩ = some raw)
    (valueRead : atom? symbols graph directory ambient depth ⟨world, pointerValue prepared.materialized⟩ = some value)
    (descriptor : BindingDescriptor) (rest : Heap L → Prop)
    (owned : (BindingCells prepared.environment descriptor ∗ rest) heap)
    (flat : descriptor.length = 0) (shared : descriptor.sharedLength = 0)
    (equalities : descriptor.equalityLength = 0) (he : descriptor.prime = none)
    (directoryPointer : descriptor.frameIndex.map CurrentValueRead.physicalAddress =
      directory.directory.directory) :
    invocationOfFields? (payloads symbols graph directory ambient depth world spaces snapshot
      entryExtent constraintExtent heap) caller parent prepared =
      some (observedInvocation caller parent prepared space target snapshot call expected raw value) := by
  have bindingsRead := payloads_binding_owned symbols graph directory ambient depth world spaces snapshot
    entryExtent constraintExtent heap prepared.environment descriptor rest owned
    flat shared equalities he directoryPointer
  simp only [invocationOfFields?, kind, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    spacePointer, callPointer, targetPointer, demandReadback, demandPointer, bindingsRead]
  simp [payloads, payloadsFromBindingImage, atomPayloads, callRead, demandRead, rawRead,
    valueRead, spaceRead, observedInvocation]

theorem entered_current_return_readback {ReturnWorld Failure : Type}
    (symbols : PhysicalAtoms.NumberedSymbols World) (memory : World → TargetMemory)
    (directory : DirectoryReadback) (ambient : List (BitVec 64)) (depth : Nat) (world : World)
    (inventory : List (Cursor World)) (pending : List BindingValueView)
    (snapshot : List SourceRow) (call expected raw value : Atom) (remaining : List Atom)
    (spaces : Ptr → Option Space) (space : Space)
    (offset : FrameOffsets) (frameEnvironmentOffset outcomeEnvironmentOffset : Nat)
    (entryExtent constraintExtent : Nat) (storage : ExecutableStorage.Storage CVal)
    (stack child : Ptr) (caller : NativeCaller) (prepared : PreparedOutcome)
    (parent : PushArguments) (original demand spaceAddress target : Ptr)
    (descriptor : BindingDescriptor) (rest : Heap (Excl (Option CVal)) → Prop)
    (preparedRead : prepare? symbols memory directory ambient depth world inventory
      (pointerValue original :: pointerValue demand :: pointerValue prepared.variantOnly ::
        pointerValue prepared.materialized :: pending) =
      some (snapshot, call :: expected :: raw :: value :: remaining))
    (kind : parent.kind = 7) (callPointer : parent.atom = some original)
    (demandPointer : parent.demand = some demand) (spacePointer : parent.space = some spaceAddress)
    (targetPointer : parent.target = some target) (spaceRead : spaces spaceAddress = some space)
    (flat : descriptor.length = 0) (shared : descriptor.sharedLength = 0)
    (equalities : descriptor.equalityLength = 0) (he : descriptor.prime = none)
    (directoryPointer : descriptor.frameIndex.map CurrentValueRead.physicalAddress =
      directory.directory.directory)
    (borrowedFrom : directory.directory.bindings = CurrentValueRead.physicalAddress prepared.environment)
    (environment : prepared.environment = prepared.seed + outcomeEnvironmentOffset)
    (owned : (FrameCells offset caller.frame parent ∗
      FrameCells offset child
        (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
          outcomeEnvironmentOffset).scalar ∗
      StackCells stack (child :: caller.frame :: caller.parents) ∗
      BindingCells prepared.environment descriptor ∗
      BindingCells (child + frameEnvironmentOffset) descriptor.retainedFork ∗ rest)
      (ExecutableStorage.heap storage))
    (distinct : (child :: caller.frame :: caller.parents).Nodup) :
    let invocation := observedInvocation caller parent prepared space target snapshot call expected raw value
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    ∃ graph, readGraph? memory (fun _ => (none : Option Empty)) inventory = some graph ∧
      directory.directory.bindings = CurrentValueRead.physicalAddress prepared.environment ∧
      retainedFrameReadback? (World := ReturnWorld) (Failure := Failure) offset frameEnvironmentOffset
        (payloads symbols graph directory ambient depth world spaces snapshot entryExtent constraintExtent
          (ExecutableStorage.heap storage)) storage stack child caller prepared =
        some (CallReturnControl.active
          ⟨invocation, raw, expected, snapshotBindings snapshot, pointerIdentity prepared.relay⟩
          (stack, child, storage)) ∧
      ReadoutCertificate (snapshotBindings snapshot) table ∧
      readout? symbols memory directory ambient depth world inventory
        (pointerValue original :: pointerValue demand :: pointerValue prepared.variantOnly ::
          pointerValue prepared.materialized :: pending) =
        some ((call :: expected :: raw :: value :: remaining).map table.apply) ∧
      ∀ (published : List (Nat × ResultPair)) (dispatch : Spec.Eval.GroundedDispatch)
        (live : List Atom) (typing : EvalTypeService) (protectedScope : List String)
        (result : FrameResult),
        value ≠ Atom.notReducible → ¬IsEmptyOrErrorRel value →
        CallReturnControl.project? .ordinaryTail (CallReturnControl.start invocation published) =
          some (CallReturnControl.requested invocation published) ∧
        (EvalAtomRawRel space dispatch live value expected
            (BindingFrame.selected (snapshotBindings snapshot) table (prepare?_certified preparedRead))
            result (typing := typing) (protectedScope := protectedScope) ↔
          CallReturnRel space dispatch live call expected value
            (BindingFrame.selected (snapshotBindings snapshot) table (prepare?_certified preparedRead))
            result (typing := typing) (protectedScope := protectedScope)) := by
  dsimp only
  obtain ⟨graph, graphRead, _, callRead, demandRead, rawRead, valueRead, _⟩ :=
    prepared_operands preparedRead
  let base := atomPayloads symbols graph directory ambient depth world spaces
  let decode := imageBindings? directory snapshot
  let readers := payloads symbols graph directory ambient depth world spaces snapshot
    entryExtent constraintExtent (ExecutableStorage.heap storage)
  let invocation := observedInvocation caller parent prepared space target snapshot call expected raw value
  have sourceOwned : (BindingCells prepared.environment descriptor ∗
      FrameCells offset caller.frame parent ∗
      FrameCells offset child
        (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
          outcomeEnvironmentOffset).scalar ∗
      StackCells stack (child :: caller.frame :: caller.parents) ∗
      BindingCells (child + frameEnvironmentOffset) descriptor.retainedFork ∗ rest)
      (ExecutableStorage.heap storage) := by cmem_exact
  have decoded := invocation_from_prepared_operands symbols graph directory ambient depth world spaces
    snapshot entryExtent constraintExtent (ExecutableStorage.heap storage) caller parent prepared
    original demand spaceAddress target space call expected raw value kind callPointer demandPointer
    spacePointer targetPointer spaceRead callRead demandRead rawRead valueRead descriptor _ sourceOwned
    flat shared equalities he directoryPointer
  have copied : readers.bindings (child + frameEnvironmentOffset) = readers.bindings prepared.environment := by
    apply owned_retained_copy_readback entryExtent constraintExtent (ExecutableStorage.heap storage)
      base decode prepared.environment (child + frameEnvironmentOffset) descriptor
      (by simp [flat, shared]) he
      (FrameCells offset caller.frame parent ∗
        FrameCells offset child
          (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
            outcomeEnvironmentOffset).scalar ∗
        StackCells stack (child :: caller.frame :: caller.parents) ∗ rest)
    cmem_exact
  have retained := retained_readback_of_owned_native_entry (World := ReturnWorld) (Failure := Failure)
    offset frameEnvironmentOffset outcomeEnvironmentOffset readers storage stack child caller prepared
    parent invocation (BindingCells prepared.environment descriptor ∗
      BindingCells (child + frameEnvironmentOffset) descriptor.retainedFork ∗ rest)
    owned decoded environment copied distinct
  refine ⟨graph, graphRead, borrowedFrom, retained, prepare?_certified preparedRead,
    readout?_prepared preparedRead, ?_⟩
  intro published dispatch live typing protectedScope result notRefusal notStopped
  refine ⟨(CallReturnControl.ordinary_source_square invocation published dispatch live typing
    (.selected _ (prepare?_certified preparedRead)) rfl notRefusal notStopped result).1, ?_⟩
  exact (CallReturnRel.evaluate_iff notRefusal notStopped).symm

/-- A successful finite read of an actual variable layer uses the directory's
full generational identity. The observed source variable is not a supplied
decoder result. -/
theorem prepared_variable_identity {symbols : PhysicalAtoms.NumberedSymbols World}
    {memory : World → TargetMemory} {directory : DirectoryReadback} {ambient : List (BitVec 64)}
    {depth : Nat} {world : World} {inventory : List (Cursor World)} {graph : AtomGraph World}
    (graphRead : readGraph? memory (fun _ => (none : Option Empty)) inventory = some graph)
    (frame : FrameReadback) (member : frame ∈ directory.frames) (index : Fin frame.slots.length)
    (pointer : Ptr) (raw : Atom)
    (layer : readLayer? memory (fun _ => (none : Option Empty)) ⟨world, pointerValue pointer⟩ =
      some (.variable frame.slots[index.val].varId, []))
    (observed : atom? symbols graph directory ambient depth ⟨world, pointerValue pointer⟩ = some raw) :
    raw = .var (CurrentStore.referenceName (frame.view.token.ref index.val)) := by
  obtain ⟨source, memoryRead, qualified⟩ := atom?_memory graphRead observed
  cases depth with
  | zero => simp [observeMemory, Mettapedia.Machines.RationalTermGraph.LayerReader.observe,
      layer, PhysicalAtoms.sourceObservation?] at memoryRead
  | succ depth =>
    simp only [observeMemory, Mettapedia.Machines.RationalTermGraph.LayerReader.observe, layer,
      List.mapM_nil, pure, Option.map_some, Option.bind_some,
      PhysicalAtoms.sourceObservation?, Option.some.injEq] at memoryRead
    subst source
    exact (Option.some.inj ((qualify?_slot directory ambient frame member index).symm.trans qualified)).symm

/-- The freshly written slot and the actual materialized pointer earn a
selected-frame substitution. Open payloads use the same certified readout as
the remaining packet; they need not already be normal. This does not execute
the native CALLER variable step. -/
theorem prepared_current_slot_materialization
    {symbols : PhysicalAtoms.NumberedSymbols World} {memory : World → TargetMemory}
    {directory : DirectoryReadback} {ambient : List (BitVec 64)} {depth : Nat} {world : World}
    {inventory : List (Cursor World)} {original demand variantOnly materialized : Ptr}
    {pending : List BindingValueView} {snapshot : List SourceRow}
    {call expected raw value : Atom} {remaining : List Atom}
    (prepared : prepare? symbols memory directory ambient depth world inventory
      (pointerValue original :: pointerValue demand :: pointerValue variantOnly ::
        pointerValue materialized :: pending) =
      some (snapshot, call :: expected :: raw :: value :: remaining))
    (activation : Activation.Inventory) (source : Address)
    (frame : FrameReadback) (member : frame ∈ directory.frames) (index : Fin frame.slots.length)
    (identity : activation.view.authority = encode frame.view.token)
    (known : frame.slots[index.val].sourceId ∈ activation.sources)
    (kind : targetRead (memory world) (sourceFieldAddress source 0) = some (.word 1))
    (sourceId : targetRead (memory world) (sourceFieldAddress source 2) =
      some (.word frame.slots[index.val].sourceId))
    (fresh : activation.view.firstWrite < frame.slots[index.val].writeVersion)
    (stored : frame.slots[index.val].value.payload = some (pointerValue materialized))
    (layer : readLayer? memory (fun _ => (none : Option Empty)) ⟨world, pointerValue variantOnly⟩ =
      some (.variable frame.slots[index.val].varId, [])) :
    (BindingFrame.selected (snapshotBindings snapshot)
      (CurrentStore.normalize (CurrentStore.assignments snapshot)) (prepare?_certified prepared)).Materialization
        raw ((CurrentStore.normalize (CurrentStore.assignments snapshot)).apply value) ∧
      ∃ graph, readGraph? memory (fun _ => (none : Option Empty)) inventory = some graph ∧
        activation? symbols graph (memory world) directory ambient depth world activation source =
          some (.known (some (pointerValue materialized)), some value) := by
  obtain ⟨graph, graphRead, _, _, _, rawRead, valueRead, _⟩ := prepared_operands prepared
  obtain ⟨graph', row, graphRead', rowMember, _, rowName, activationRead⟩ :=
    prepare?_activation_slot prepared activation source frame member index identity known kind sourceId
  have sameGraph := Option.some.inj (graphRead.symm.trans graphRead')
  subst graph'
  have nativeRead := Activation.readValue?_source_slot directory (memory world) activation source frame
    member index identity known kind sourceId
  have decoded : activation? symbols graph (memory world) directory ambient depth world activation source =
      some (.known (some (pointerValue materialized)), some value) := by
    simp [activation?, nativeRead, fresh, stored, value?, valueRead]
  have output : row.observed.outputAfter activation.view.firstWrite = some value := by
    have equal := Option.some.inj (activationRead.symm.trans decoded)
    exact congrArg Prod.snd equal
  have rowValue : row.observed.value = some value := by
    unfold SlotReadbackOf.outputAfter at output
    split at output
    · exact output
    · contradiction
  have certified := prepare?_certified prepared
  have model := (certified.theory _).mp (Theory.normal_presentedValuation_satisfied certified.normal)
  have equation := model.1 row.name value
    (CurrentStore.mem_assignments.mpr ⟨row, rowMember, rfl, rowValue⟩)
  have rawIdentity := prepared_variable_identity graphRead frame member index variantOnly raw layer rawRead
  refine ⟨?_, graph, graphRead, decoded⟩
  rw [BindingFrame.materialization_selected, rawIdentity]
  simpa only [Theory.presentedValuation, Theory.applyTypeValuation_presented_eq_apply,
    rowName] using equation.symm

namespace Controls

private def ptr (block : Nat) : Ptr := ⟨block, 0⟩
private def address (block : Nat) : Address := CurrentValueRead.physicalAddress (ptr block)
private def token : Token := ⟨1, 1⟩
private def variableId : BitVec 64 := BitVec.ofNat 64 ((encode token).toNat * 2 ^ 32 + 1)
private def frame : FrameReadback where
  view := ⟨address 32, address 21, token, 1, 1, 0, 1, 0, false, true, true⟩
  slots := [⟨1, variableId, 0, none, true, pointerValue (ptr 2), 1⟩]
  admitted := by decide
private def directory : DirectoryReadback where
  directory := ⟨address 32, some (address 21), 1, 0, 1⟩
  capacity := 2
  frames := [frame]
  admitted := by decide
private def symbols : PhysicalAtoms.NumberedSymbols Unit where
  bytes := fun _ _ => none
  unique := by intros; contradiction
private def memory : Unit → TargetMemory := fun _ =>
  ⟨fun storage index =>
    if storage = 12 then
      if index < 2 then some (.reference (some (address 1))) else none
    else if index = 0 then
      if storage = 1 then some (.record "Atom" [.word 1, .word 0, .word variableId])
      else if storage = 2 then some (.record "Atom"
        [.word 0, .word 0, .word 0, .word 0, .word 0, .reference none])
      else if storage = 3 then some (.record "Atom"
        [.word 3, .word 0, .word 0, .word 0, .word 0, .reference none, .word 0, .word 0,
          .record "expr" [.reference (some (address 12)), .word 2]])
      else if storage = 4 then some (.record "Atom" [.word 1, .word 0, .word 1])
      else none
    else none, fun _ => none⟩
private def cursor (block : Nat) : NativePayload.Cursor Unit := ⟨(), pointerValue (ptr block)⟩
private def inventory : List (NativePayload.Cursor Unit) := [cursor 1, cursor 2, cursor 3]
private def graphRows : List (Mettapedia.Machines.RationalTermGraph.KeyedRow
    (NativePayload.Cursor Unit) (Label Empty)) :=
  [⟨cursor 1, .variable variableId, []⟩, ⟨cursor 2, .symbolBytes [], []⟩,
    ⟨cursor 3, .expression, [cursor 1, cursor 1]⟩]
private def graph : AtomGraph Unit := ⟨graphRows, by decide⟩
private theorem graph_read : readGraph? memory (fun _ => (none : Option Empty)) inventory =
    some graph := by
  have rows : readRows? memory (fun _ => (none : Option Empty)) inventory = some graphRows := by decide
  change (readRows? memory (fun _ => (none : Option Empty)) inventory).bind
    Mettapedia.Machines.RationalTermGraph.decodeKeyedTable? = _
  rw [rows]
  change Mettapedia.Machines.RationalTermGraph.decodeKeyedTable? graphRows = some graph
  exact dif_pos graph.valid
private def name : String := CurrentStore.referenceName (token.ref 0)
private def savedCall : Atom := .expression [.var name, .var name]
private def snapshot : List SourceRow := [⟨token.ref 0, name, ⟨some (.symbol ""), 1, 1, none⟩⟩]
private theorem variable_read : atom? symbols graph directory [] 2 (cursor 1) = some (.var name) := by
  change atom? symbols graph directory [] 2 (graph.key ⟨0, by decide⟩) = _
  rw [atom?_key]
  change qualify? directory [] (.var (sourceIdName variableId)) = _
  exact qualify?_slot directory [] frame (by simp [directory]) ⟨0, by decide⟩
private theorem symbol_read : atom? symbols graph directory [] 2 (cursor 2) = some (.symbol "") := by
  change atom? symbols graph directory [] 2 (graph.key ⟨1, by decide⟩) = _
  rw [atom?_key]
  change qualify? directory [] (.symbol "") = _
  simp [qualify?, covered, TypeSubst.typeVars, renameTypeVars]
private theorem call_read : atom? symbols graph directory [] 2 (cursor 3) = some savedCall := by
  change atom? symbols graph directory [] 2 (graph.key ⟨2, by decide⟩) = _
  rw [atom?_key]
  change qualify? directory []
    (.expression [.var (sourceIdName variableId), .var (sourceIdName variableId)]) = _
  have named := lookupName?_slot directory frame (by simp [directory]) ⟨0, by decide⟩
  change lookupName? (names directory) (sourceIdName variableId) = some (token.ref 0) at named
  simp [qualify?, covered, TypeSubst.typeVars, TypeSubst.typeVarsList,
    sourceName, named, renameTypeVars, savedCall, name]
private theorem rows_read : rows? symbols graph directory [] 2 ()
    (Snapshot.rows directory.toImage) = some snapshot := by
  change rows? symbols graph directory [] 2 ()
    [⟨token.ref 0, sourceIdName 1, ⟨some (pointerValue (ptr 2)), 1, 1, none⟩⟩] = _
  have read := symbol_read
  change atom? symbols graph directory [] 2 ⟨(), pointerValue (ptr 2)⟩ = some (.symbol "") at read
  simp [rows?, row?, value?, read, snapshot, name]

theorem nonempty_entered_operands_are_prepared :
    prepare? symbols memory directory [] 2 () inventory
      [pointerValue (ptr 3), pointerValue (ptr 2), pointerValue (ptr 1), pointerValue (ptr 2)] =
      some (snapshot, [savedCall, .symbol "", .var name, .symbol ""]) := by
  have call := call_read
  have symbol := symbol_read
  have variableRead := variable_read
  dsimp only [cursor] at call symbol variableRead
  simp only [prepare?, graph_read, Option.bind_eq_bind, Option.bind_some, rows_read,
    List.mapM_cons, List.mapM_nil, call, symbol, variableRead, pure]
  decide

private def activation (boundary : Nat) (small : boundary < 2 ^ 64) : Activation.Inventory where
  view := ⟨none, none, encode token, 1, 1, true, encode token, 1, 0, boundary⟩
  sources := [1]
  admitted := by
    constructor
    · dsimp only [Activation.View.Admissible]
      exact ⟨by decide, by decide, by decide, by decide, by decide, small⟩
    · refine ⟨rfl, by simp, ?_, ?_⟩
      · intro source member
        have equal : source = (1 : BitVec 64) := by simpa using member
        subst source
        decide
      · intro _ index
        simp

theorem current_variable_earns_ground_materialization :
    (BindingFrame.selected (snapshotBindings snapshot)
      (CurrentStore.normalize (CurrentStore.assignments snapshot))
      (prepare?_certified nonempty_entered_operands_are_prepared)).Materialization
      (.var name) (.symbol "") ∧
    ∃ observed, readGraph? memory (fun _ => (none : Option Empty)) inventory = some observed ∧
      activation? symbols observed (memory ()) directory [] 2 () (activation 0 (by decide)) (address 4) =
        some (.known (some (pointerValue (ptr 2))), some (.symbol "")) := by
  simpa only [TypeSubst.apply] using prepared_current_slot_materialization nonempty_entered_operands_are_prepared
    (activation 0 (by decide)) (address 4) frame (by simp [directory]) ⟨0, by decide⟩
    rfl (by decide) rfl rfl (by decide) rfl (by decide)

private def offsets : FrameOffsets := ⟨1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15⟩
private def parent : PushArguments :=
  ⟨7, some (ptr 40), none, some (ptr 3), some (ptr 2), 17, some (ptr 41), true⟩
private def prepared : PreparedOutcome := ⟨ptr 32, ptr 32, ptr 2, ptr 1, ptr 42, 5⟩
private def caller : NativeCaller := ⟨ptr 30, [ptr 33]⟩
private def descriptor : BindingDescriptor :=
  { BindingDescriptor.initial with frameIndex := some (ptr 21) }
private def frameCells (next : Option Ptr) (phase : UInt32) (arguments : PushArguments) : List (Option CVal) :=
  [some (.ptr next), some (.u32 arguments.kind), some (.u32 phase), some (.ptr arguments.space),
    some (.ptr arguments.arena), some (.ptr arguments.atom), some (.ptr arguments.demand),
    some (.i32 arguments.fuel), some (.ptr arguments.target), some (.bool arguments.preserve)]
private def storage : ExecutableStorage.Storage CVal :=
  [(29, ⟨true, [some (.ptr (some (ptr 31))), some (.u64 3)]⟩),
    (30, ⟨true, frameCells (some (ptr 33)) 1 parent⟩),
    (31, ⟨true, frameCells (some (ptr 30)) 0
      (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay 0).scalar ++
        List.replicate 10 none ++ descriptor.retainedFork.cells.map some⟩),
    (32, ⟨true, descriptor.cells.map some⟩), (33, ⟨true, [some (.ptr none)]⟩)]
private def spaces (address : Ptr) : Option Space := if address = ptr 40 then some ⟨[]⟩ else none
private def readers : PayloadReadback := payloads symbols graph directory [] 2 () spaces snapshot
  1 1 (ExecutableStorage.heap storage)
private def invocation := observedInvocation caller parent prepared ⟨[]⟩ (ptr 41)
  snapshot savedCall (.symbol "") (.var name) (.symbol "")

private theorem parent_fields : frameArguments? offsets (ExecutableStorage.heap storage) caller.frame =
    some parent := rfl
private theorem child_fields : frameArguments? offsets (ExecutableStorage.heap storage) (ptr 31) =
    some (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay 0).scalar := rfl
private theorem source_image : bindingImage? 1 1 (ExecutableStorage.heap storage) (ptr 32) =
    imageOfDescriptor? 1 1 (ExecutableStorage.heap storage) descriptor := rfl
private theorem child_image : bindingImage? 1 1 (ExecutableStorage.heap storage) (ptr 31 + 20) =
    imageOfDescriptor? 1 1 (ExecutableStorage.heap storage) descriptor.retainedFork := rfl
private theorem source_bindings : readers.bindings (ptr 32) = some (snapshotBindings snapshot) := by
  simp only [readers, payloads, payloadsFromBindingImage, bind]
  rw [source_image]
  rfl
private theorem child_bindings : readers.bindings (ptr 31 + 20) = some (snapshotBindings snapshot) := by
  simp only [readers, payloads, payloadsFromBindingImage, bind]
  rw [child_image]
  rfl
private theorem decoded_invocation : invocationOfFields? readers caller parent prepared = some invocation := by
  have call : readers.atom (ptr 3) = some savedCall := call_read
  have symbol : readers.atom (ptr 2) = some (.symbol "") := symbol_read
  have variableRead : readers.atom (ptr 1) = some (.var name) := variable_read
  have space : readers.space (ptr 40) = some (Space.mk []) := rfl
  simp only [invocationOfFields?, parent, prepared, demandReadback, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, bind, Option.bind_some, space, call, symbol, variableRead,
    source_bindings]
  rfl

/-- This fixture starts at the entered child. It does not claim that the
ordinary dispatcher chooses this branch for an inert ground symbol. -/
theorem entered_return_keeps_the_actual_request_and_storage :
    retainedFrameReadback? (World := Unit) (Failure := Unit) offsets 20 readers storage
      (ptr 29) (ptr 31) caller prepared =
      some (CallReturnControl.active
        ⟨invocation, .var name, .symbol "", snapshotBindings snapshot, pointerIdentity (ptr 42)⟩
        (ptr 29, ptr 31, storage)) := by
  have request := callback_request_from_native_parent readers caller parent prepared invocation
    0 decoded_invocation rfl
  have copied : readers.bindings (ptr 31 + 20) = readers.bindings prepared.environment := by
    exact child_bindings.trans source_bindings.symm
  have loaded : nativeChildRequest? offsets 20 readers (ExecutableStorage.heap storage)
      caller prepared (ptr 31) = some
        ⟨invocation, .var name, .symbol "", snapshotBindings snapshot, pointerIdentity (ptr 42)⟩ := by
    simp only [nativeChildRequest?, invocationReadback?, parent_fields, bind, Option.bind_some,
      decoded_invocation, child_fields, callbackArguments, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte]
    simpa [requestOfCaller?, callbackArguments, copied, prepared, ptr_add_zero,
      invocation, observedInvocation] using request
  have top : pointerCell (ExecutableStorage.heap storage) (ptr 29) = some (some (ptr 31)) := rfl
  simp only [retainedFrameReadback?, top, bind, Option.bind_some, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, loaded, pure]

theorem saved_call_is_not_substituted_again : invocation.original = savedCall ∧
    invocation.original ≠ (CurrentStore.normalize (CurrentStore.assignments snapshot)).apply savedCall := by
  constructor
  · rfl
  · simp [invocation, observedInvocation, savedCall, snapshot, CurrentStore.assignments,
      CurrentStore.normalize, CurrentStore.normalizeFrom, TypeSubst.bind, TypeSubst.apply,
      TypeSubst.lookup, TypeSubst.erase, TypeSubst.applyAssignment, name]

/-- No new activation output does not mean that the current environment is
empty: its older binding still materializes the current variable. -/
theorem old_write_is_not_an_empty_current_environment :
    activation? symbols graph (memory ()) directory [] 2 () (activation 1 (by decide)) (address 4) =
      some (.known none, none) ∧
    (BindingFrame.selected (snapshotBindings snapshot)
      (CurrentStore.normalize (CurrentStore.assignments snapshot))
      (prepare?_certified nonempty_entered_operands_are_prepared)).Materialization
      (.var name) (.symbol "") := by
  constructor
  · have read := Activation.readValue?_source_slot directory (memory ()) (activation 1 (by decide))
      (address 4) frame (by simp [directory]) ⟨0, by decide⟩ rfl (by decide) rfl rfl
    unfold activation?
    rw [read]
    rfl
  · exact current_variable_earns_ground_materialization.1

theorem extra_flat_rows_are_refused (image : BindingImage) (cell : CVal) :
    imageBindings? directory snapshot { image with exclusiveRows := [cell] } = none := by
  simp [imageBindings?]

end Controls

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory.NativePayload.CurrentReturn
