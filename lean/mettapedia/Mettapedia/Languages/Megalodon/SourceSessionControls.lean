import Mettapedia.Languages.Megalodon.NativeIntegration

/-! # Complete source-row checking of a polymorphic predicate identity -/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceSessionControls
open MathdataKernel ProofJudgment BorrowedProofCursor SourceCursor
open Mettapedia.Logic.DerivationGraph.BorrowedCursor

private def applied : Tm := .app (.db 1) (.db 0)
private def implication : Tm := .imp applied applied
private def predicateType : Tp := .arr (.var 0) .prop
private def schemaBody : Tm := .all predicateType (.all (.var 0) implication)
private def schema : Tm := .typeAll schemaBody
private def nodes : Array SourceNode := #[
  ⟨⟨⟨1, [.var 0, predicateType], [applied]⟩, applied⟩, .hyp 0, [], 0⟩,
  ⟨⟨⟨1, [.var 0, predicateType], []⟩, implication⟩, .proofLam applied, [0], 1⟩,
  ⟨⟨⟨1, [predicateType], []⟩, .all (.var 0) implication⟩, .termLam, [1], 2⟩,
  ⟨⟨⟨1, [], []⟩, schemaBody⟩, .termLam, [2], 3⟩,
  ⟨⟨⟨0, [], []⟩, schema⟩, .typeLam, [3], 4⟩,
  ⟨⟨⟨0, [], []⟩, Tm.typeInstantiate (.base 0) schemaBody⟩, .typeApp (.base 0) schemaBody, [4], 5⟩]
private def read (address : Nat) : Option NativeSyntaxWire.Wire := (nodes[address]?).map NativeCursorWire.encodeNode
private theorem safeEnvironment : SourceAdmission.EnvironmentSafe {} :=
  SourceAdmission.environmentCheck_sound (by decide)
private def initial := SourceCursor.begin {} safeEnvironment 1 read
private def first := SourceCursor.resume initial 8 3 [0, 1, 2, 3, 4, 5]
private def second := SourceCursor.resume first.session 8 3 first.native.pending

theorem partial_batch_keeps_suffix :
    first.native.status = .paused ∧ first.native.pending = [3, 4, 5] := by
  simp [first, initial, SourceCursor.resume, SourceCursor.begin, NativeSession.resume, NativeSession.begin,
    ObservedCursor.walk, ObservedCursor.observeStep, RuleObservation.observe, SourceCursor.source,
    SourceCursor.decode, read, nodes, applied, implication, predicateType, schemaBody, schema,
    start, indexAt, premiseValues, SourceCursor.NodeSafe, SourceCursor.JudgmentSafe,
    SourceCursor.WitnessSafe, SourceScopeInvariant.ContextSafe, SourceScopeInvariant.Scoped,
    SourceScopeInvariant.Protected, inferTerm, MathdataKernel.normalize, deltaNormalize,
    Tm.normalize, Tm.normalizeOne, Context.proofBinder, Context.termBinder, Tp.plainWellFormed]

theorem resumed_schema_and_instance_finish :
    second.native.status = .finished ∧ second.native.pending = [] ∧
      rootAt second.native.session.state 4 = some ⟨⟨0, [], []⟩, schema⟩ ∧
      rootAt second.native.session.state 5 = some ⟨⟨0, [], []⟩, Tm.typeInstantiate (.base 0) schemaBody⟩ := by
  simp [second, first, initial, SourceCursor.resume, SourceCursor.begin, SourceCursor.Resumed.session,
    NativeSession.resume, NativeSession.begin, ObservedCursor.walk, ObservedCursor.observeStep,
    RuleObservation.observe, SourceCursor.source, SourceCursor.decode, read, nodes, applied,
    implication, predicateType, schemaBody, schema, start, indexAt, premiseValues, rootAt,
    SourceCursor.NodeSafe, SourceCursor.JudgmentSafe, SourceCursor.WitnessSafe,
    SourceScopeInvariant.ContextSafe, SourceScopeInvariant.Scoped, SourceScopeInvariant.Protected,
    inferTerm, MathdataKernel.normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Tm.typeInstantiate, Tm.typeInstantiateAt, Tp.instantiateAt, Tp.shift,
    Context.proofBinder, Context.termBinder, Context.typeBinder, Tp.plainWellFormed]

theorem source_polymorphic_schema_publishes :
    (SourceCursor.finish second 4 8 schema).isAccepted = true := by
  apply (SourceCursor.finish_accepts_iff _ _ _ _).mpr
  refine ⟨by decide, resumed_schema_and_instance_finish.1, resumed_schema_and_instance_finish.2.1,
    ⟨⟨0, [], []⟩, schema⟩, resumed_schema_and_instance_finish.2.2.1, rfl, by decide, ?_⟩
  simp [MathdataKernel.normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, schema, schemaBody,
    implication, applied]

theorem source_concrete_instance_publishes :
    (SourceCursor.finish second 5 8 (Tm.typeInstantiate (.base 0) schemaBody)).isAccepted = true := by
  apply (SourceCursor.finish_accepts_iff _ _ _ _).mpr
  refine ⟨by decide, resumed_schema_and_instance_finish.1, resumed_schema_and_instance_finish.2.1,
    ⟨⟨0, [], []⟩, Tm.typeInstantiate (.base 0) schemaBody⟩, resumed_schema_and_instance_finish.2.2.2,
    rfl, by decide, ?_⟩
  simp [MathdataKernel.normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, schemaBody, implication,
    applied, predicateType, Tm.typeInstantiate, Tm.typeInstantiateAt, Tp.instantiateAt, Tp.shift]

theorem unfinished_source_batch_refuses_publication :
    SourceCursor.finish first 2 8 schema = .unfinished .paused := by
  simp [SourceCursor.finish, show SourceScopeInvariant.Protected schema by decide,
    NativeSession.finish, partial_batch_keeps_suffix.1]

theorem altered_hypothesis_is_not_a_proof :
    let bad : SourceNode := ⟨⟨⟨1, [.var 0, predicateType], [applied]⟩, .imp applied applied⟩, .hyp 0, [], 0⟩
    ObservedCursor.observeStep {} 8
      (source 1 (fun _ => some (NativeCursorWire.encodeNode bad)))
      (start (source 1 (fun _ => some (NativeCursorWire.encodeNode bad)))) 0 = .refused := by decide

end Mettapedia.Languages.Megalodon.SourceSessionControls
