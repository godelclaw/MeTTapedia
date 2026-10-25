import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveIndexedContainerBundleRealization
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedContainerTraversal

/-!
# Selected formed List and Vector bundles through the PeTTa position visitor

The existing scoped-term and Pattern codecs retain the actual source element
and its pointwise witness application. The executable list of packets is
proved equal to the observation of every position of the selected semantic
bundle. The selected object's formation and computation evidence remain in
their source calculus. A syntax decoder does not check a typing judgment.

The concrete formed provider is the existing two-element reflexivity bundle.
This does not interpret arbitrary open guest Vector terms as semantic values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.FormationSensitiveBundleTraversal

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open PeTTa.Bridges

namespace ScopedTerm

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec

abbrev scalars := Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec.binaryScalars

abbrev headCodec :=
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec.WithScalars.towerHeadCodec scalars

def encode {n : Nat} (term : Tower.Tm n) : CettaWire.Term :=
  InferenceCettaWire.encodePattern
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec.WithScalars.encodeTm scalars headCodec term)

def decode (n : Nat) (wire : CettaWire.Term) : Option (Tower.Tm n) := do
  let pattern ← InferenceCettaWire.decodePattern wire
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec.WithScalars.decodeTm? scalars headCodec n pattern

@[simp] theorem decode_encode {n : Nat} (term : Tower.Tm n) :
    decode n (encode term) = some term := by
  simp [decode, encode, InferenceCettaWire.decodePattern_encodePattern]

theorem encode_injective (n : Nat) : Function.Injective (encode (n := n)) := by
  intro first second same
  have decoded := congrArg (decode n) same
  simpa using decoded

end ScopedTerm

open NativeVectorAll.CanonicalAdequacy
open FormationSensitiveIndexedContainerBundleRealization
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedContainerTraversal

def entry {n : Nat} (element witness : Tower.Tm n) : CettaWire.Term :=
  .application "InductionPosition" [ScopedTerm.encode element, ScopedTerm.encode witness]

def decodeEntry (n : Nat) : CettaWire.Term → Option (Tower.Tm n × Tower.Tm n)
  | .application "InductionPosition" [element, witness] => do
      return (← ScopedTerm.decode n element, ← ScopedTerm.decode n witness)
  | _ => none

@[simp] theorem decodeEntry_entry {n : Nat} (element witness : Tower.Tm n) :
    decodeEntry n (entry element witness) = some (element, witness) := by
  simp [decodeEntry, entry]

theorem entry_injective {n : Nat} {first second firstWitness secondWitness : Tower.Tm n}
    (same : entry first firstWitness = entry second secondWitness) :
    first = second ∧ firstWitness = secondWitness := by
  have decoded := congrArg (decodeEntry n) same
  simpa using decoded

theorem result_entry_distinguishes_witness {n : Nat} (element : Tower.Tm n)
    {first second : Tower.Tm n} (different : first ≠ second) :
    entry element first ≠ entry element second := by
  intro same
  exact different (entry_injective same).2

/-- Executable observations are computed directly from the same source
elements and pointwise witness term, without inverting a semantic equivalence. -/
def entries {n : Nat} (witness : Tower.Tm n) (values : List (Tower.Tm n)) : List CettaWire.Term :=
  values.map fun element => entry element (.app witness element)

noncomputable def selectedEntries
    {n : Nat} {Head : Type} {rules : Rules Head} {arity : Nat} {context : Ctx Head arity}
    {witness : Tower.Tm n} {values : List (Tower.Tm n)}
    (selected : SelectedObjectBundle (IndexedContainer.vectorInductionBundle (Witness witness))
      (semanticValue values) rules context) : List CettaWire.Term :=
  List.ofFn fun position : Fin values.length =>
    entry (values.get position) (selected.positionWitness position).1

/-- The executable packet list observes the actual selected bundle at every
source position. It does not construct an unrelated bundle with the same size. -/
theorem selectedEntries_eq_entries
    {n : Nat} {Head : Type} {rules : Rules Head} {arity : Nat} {context : Ctx Head arity}
    {witness : Tower.Tm n} {values : List (Tower.Tm n)}
    (selected : SelectedObjectBundle (IndexedContainer.vectorInductionBundle (Witness witness))
      (semanticValue values) rules context) : selectedEntries selected = entries witness values := by
  have atPosition (position : Fin values.length) :
      (selected.positionWitness position).1 = .app witness (values.get position) :=
    (selected.positionWitness position).2
  unfold selectedEntries
  simp only [atPosition]
  exact (List.ofFn_comp' values.get (fun element => entry element (.app witness element))).trans
    (congrArg (List.map (fun element => entry element (.app witness element))) (List.ofFn_get values))

def call {n : Nat} (witness : Tower.Tm n) (values : List (Tower.Tm n)) : Atom :=
  ContainerValues.wireCall (CettaWire.encodeList id (entries witness values))

def result (observations : List CettaWire.Term) : Atom :=
  listAtom (observations.map fun observation =>
    visit (MeTTaIL.CettaWireAtom.encode observation))

theorem entries_return {n : Nat} (witness : Tower.Tm n) (values : List (Tower.Tm n))
    (state : Effects.State) :
    Eval.PureReturns library.runtime [] state (call witness values) state (result (entries witness values)) := by
  simpa only [call, result, ContainerValues.wireCall, ContainerValues.encoded_list,
    IndexedContainerTraversal.call, List.map_map, Function.comp_def, id_eq] using
    returns state ((entries witness values).map MeTTaIL.CettaWireAtom.encode)

theorem result_injective : Function.Injective result := by
  intro first second same
  have wireSame : first.map MeTTaIL.CettaWireAtom.encode = second.map MeTTaIL.CettaWireAtom.encode :=
    output_injective (by simpa only [result, List.map_map, Function.comp_def] using same)
  exact (List.map_injective_iff.mpr (fun left right eq =>
    MeTTaIL.CettaWireAtom.encode_injective left right eq)) wireSame

theorem entries_completed_iff {n : Nat} (witness : Tower.Tm n) (values : List (Tower.Tm n))
    (before after : Effects.State) (answers input output : List Atom) :
    (∃ fuel, Eval.run library.runtime fuel
      { state := before, control := .evaluate [] (call witness values) } =
        .complete after answers input output) ↔
      after = before ∧ answers = [result (entries witness values)] ∧ input = [] ∧ output = [] :=
  Eval.path_completed_iff library.runtime _ before _ [] [] (entries_return witness values before)
    after answers input output

theorem selected_entries_return
    {n : Nat} {Head : Type} {rules : Rules Head} {arity : Nat} {context : Ctx Head arity}
    {witness : Tower.Tm n} {values : List (Tower.Tm n)}
    (selected : SelectedObjectBundle (IndexedContainer.vectorInductionBundle (Witness witness))
      (semanticValue values) rules context) (state : Effects.State) :
    Eval.PureReturns library.runtime [] state (call witness values) state (result (selectedEntries selected)) := by
  rw [selectedEntries_eq_entries]
  exact entries_return witness values state

namespace Canonical

open NativeVectorAll.Controls.CanonicalAdequacyControls

def observations : List CettaWire.Term := entries reflexiveWitness canonicalValues

theorem selected_observations : selectedEntries VectorInstance.realization = observations :=
  selectedEntries_eq_entries VectorInstance.realization

theorem formed : FormationSensitive.Judgment NativeVectorAll.rules .nil
    VectorInstance.realization.objectTerm VectorInstance.realization.objectType :=
  VectorInstance.realization.formed

theorem returns (state : Effects.State) : Eval.PureReturns library.runtime [] state
    (call reflexiveWitness canonicalValues) state (result observations) :=
  entries_return reflexiveWitness canonicalValues state

theorem retains_two_positions : observations.length = 2 := by decide +kernel

theorem refuses_reordered_positions : result observations ≠ result observations.reverse := by
  intro same
  have orders := result_injective same
  have sourceSame := (entry_injective (List.cons.inj orders).1).1
  exact (by decide +kernel : canonicalValues[0] ≠ canonicalValues[1]) sourceSame

theorem refuses_changed_witness :
    entry canonicalValues[0] (.app reflexiveWitness canonicalValues[0]) ≠
      entry canonicalValues[0] (.app reflexiveWitness canonicalValues[1]) := by
  apply result_entry_distinguishes_witness
  intro same
  exact (by decide +kernel : canonicalValues[0] ≠ canonicalValues[1])
    (Tm.app.inj same).2

theorem refuses_wrong_scope : ScopedTerm.decode 0
    (ScopedTerm.encode (.var (0 : Fin 1))) = none := by
  decide +kernel

end Canonical

namespace ListProvider

open NativeIndexedFamilies IntrinsicCanonicalSemantics
open FormationSensitiveRegisteredListGuestLift
open FormationSensitiveNativeList (Typing)

variable {n : Nat} {context : Tower.Ctx n}
variable {source target relation : Tower.Tm n}

def entry (sourceTerm : TypedTerm context source)
    (lifted : ElementLift target relation sourceTerm) : CettaWire.Term :=
  .application "RelatorPosition" [ScopedTerm.encode sourceTerm.term,
    ScopedTerm.encode lifted.1.term, ScopedTerm.encode lifted.2.term]

/-- This decoder recovers syntax at the declared scope. Source formation
and relation typing are supplied by the selected provider, not by decoding. -/
def decodeEntry (arity : Nat) : CettaWire.Term → Option (Tower.Tm arity × Tower.Tm arity × Tower.Tm arity)
  | .application "RelatorPosition" [sourceTerm, targetTerm, evidence] => do
      return (← ScopedTerm.decode arity sourceTerm, ← ScopedTerm.decode arity targetTerm,
        ← ScopedTerm.decode arity evidence)
  | _ => none

@[simp] theorem decodeEntry_entry (sourceTerm : TypedTerm context source)
    (lifted : ElementLift target relation sourceTerm) :
    decodeEntry n (entry sourceTerm lifted) = some (sourceTerm.term, lifted.1.term, lifted.2.term) := by
  simp [decodeEntry, entry]

abbrev Frame := Σ sourceTerm : TypedTerm context source, ElementLift target relation sourceTerm

def encodeFrame (frame : Frame (context := context) (source := source) (target := target) (relation := relation)) :
    CettaWire.Term := entry frame.1 frame.2

theorem encodeFrame_injective : Function.Injective
    (encodeFrame (context := context) (source := source) (target := target) (relation := relation)) := by
  rintro ⟨firstSource, firstTarget, firstEvidence⟩ ⟨secondSource, secondTarget, secondEvidence⟩ same
  have decoded := congrArg (decodeEntry n) same
  change decodeEntry n (entry firstSource ⟨firstTarget, firstEvidence⟩) =
    decodeEntry n (entry secondSource ⟨secondTarget, secondEvidence⟩) at decoded
  simp only [decodeEntry_entry, Option.some.injEq, Prod.mk.injEq] at decoded
  have sourceSame : firstSource = secondSource := TypedTerm.ext decoded.1
  subst secondSource
  have targetSame : firstTarget = secondTarget := TypedTerm.ext decoded.2.1
  subst secondTarget
  have evidenceSame : firstEvidence = secondEvidence := TypedRelationEvidence.ext decoded.2.2
  subst secondEvidence
  rfl

def entries (sourceList : CanonicalList context source)
    (lifted : CanonicalLift target relation sourceList) : List CettaWire.Term :=
  List.ofFn fun position : Fin sourceList.length => entry (sourceList.get position)
    (canonicalLiftPositionEquiv target relation sourceList lifted position)

theorem selected_position
    {sourceList : CanonicalList context source}
    (lifted : QualifiedLift target relation sourceList)
    (formedContext : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (sourceTyping : Typing context source (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (rename wk target) (sortTm Intrinsic.motiveLevel))))
    (position : Fin sourceList.length) :
    (ListInstance.realization lifted formedContext sourceTyping targetTyping relationTyping).positionWitness position =
      canonicalLiftPositionEquiv target relation sourceList
        ⟨lifted.targetList, lifted.evidence⟩ position := by
  change canonicalLiftRegisteredPositionEquiv target relation sourceList
    ⟨lifted.targetList, lifted.evidence⟩ position = _
  rw [canonicalLiftRegisteredPositionEquiv_eq]
  rfl

noncomputable def selectedEntries
    {sourceList : CanonicalList context source}
    (lifted : QualifiedLift target relation sourceList)
    (formedContext : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (sourceTyping : Typing context source (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (rename wk target) (sortTm Intrinsic.motiveLevel)))) : List CettaWire.Term :=
  List.ofFn fun position : Fin sourceList.length => entry (sourceList.get position)
    ((ListInstance.realization lifted formedContext sourceTyping targetTyping relationTyping).positionWitness position)

/-- Both the target term and the retained relation-evidence term agree with
the actual formed provider at each source occurrence. -/
theorem selectedEntries_eq_entries
    {sourceList : CanonicalList context source}
    (lifted : QualifiedLift target relation sourceList)
    (formedContext : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (sourceTyping : Typing context source (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (rename wk target) (sortTm Intrinsic.motiveLevel)))) :
    selectedEntries lifted formedContext sourceTyping targetTyping relationTyping =
      entries sourceList ⟨lifted.targetList, lifted.evidence⟩ := by
  unfold selectedEntries entries
  congr 1
  funext position
  rw [selected_position]

def call (sourceList : CanonicalList context source)
    (lifted : CanonicalLift target relation sourceList) : Atom :=
  ContainerValues.wireCall (CettaWire.encodeList id (entries sourceList lifted))

theorem entries_return (sourceList : CanonicalList context source)
    (lifted : CanonicalLift target relation sourceList) (state : Effects.State) :
    Eval.PureReturns library.runtime [] state (call sourceList lifted) state (result (entries sourceList lifted)) := by
  simpa only [call, result, ContainerValues.wireCall, ContainerValues.encoded_list,
    IndexedContainerTraversal.call, List.map_map, Function.comp_def, id_eq] using
    IndexedContainerTraversal.returns state ((entries sourceList lifted).map MeTTaIL.CettaWireAtom.encode)

theorem entries_completed_iff (sourceList : CanonicalList context source)
    (lifted : CanonicalLift target relation sourceList) (before after : Effects.State)
    (answers input output : List Atom) :
    (∃ fuel, Eval.run library.runtime fuel
      { state := before, control := .evaluate [] (call sourceList lifted) } =
        .complete after answers input output) ↔
      after = before ∧ answers = [result (entries sourceList lifted)] ∧ input = [] ∧ output = [] :=
  Eval.path_completed_iff library.runtime _ before _ [] [] (entries_return sourceList lifted before)
    after answers input output

theorem selected_entries_return
    {sourceList : CanonicalList context source}
    (lifted : QualifiedLift target relation sourceList)
    (formedContext : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (sourceTyping : Typing context source (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (rename wk target) (sortTm Intrinsic.motiveLevel)))) (state : Effects.State) :
    Eval.PureReturns library.runtime [] state
      (call sourceList ⟨lifted.targetList, lifted.evidence⟩) state
      (result (selectedEntries lifted formedContext sourceTyping targetTyping relationTyping)) := by
  rw [selectedEntries_eq_entries]
  exact entries_return sourceList ⟨lifted.targetList, lifted.evidence⟩ state

namespace Controls

def contextA : Tower.Ctx 1 := .snoc .nil (sortTm Intrinsic.elementLevel)
def relationType : Tower.Tm 1 := .pi (.var 0) (.pi (.var 1) (sortTm Intrinsic.motiveLevel))
def contextR : Tower.Ctx 2 := .snoc contextA relationType
def contextX : Tower.Ctx 3 := .snoc contextR (.var 1)
def contextY : Tower.Ctx 4 := .snoc contextX (.var 2)
def contextE : Tower.Ctx 5 := .snoc contextY (.app (.app (.var 2) (.var 1)) (.var 0))
def sourceContext : Tower.Ctx 6 := .snoc contextE (.app (.app (.var 3) (.var 2)) (.var 1))

def sourceType : Tower.Tm 6 := .var 5
def relationTerm : Tower.Tm 6 := .var 4

def sourceHead : TypedTerm sourceContext sourceType := ⟨.var 3, .var 3⟩
def targetHead : TypedTerm sourceContext sourceType := ⟨.var 2, .var 2⟩
def firstEvidence : TypedRelationEvidence relationTerm sourceHead targetHead := ⟨.var 1, .var 1⟩
def secondEvidence : TypedRelationEvidence relationTerm sourceHead targetHead := ⟨.var 0, .var 0⟩

def sourceList : CanonicalList sourceContext sourceType := [sourceHead, sourceHead]
def targetList : CanonicalList sourceContext sourceType := [targetHead, targetHead]
def evidence : CanonicalMapRel relationTerm sourceList targetList :=
  .cons firstEvidence (.cons secondEvidence .nil)
def swappedEvidence : CanonicalMapRel relationTerm sourceList targetList :=
  .cons secondEvidence (.cons firstEvidence .nil)

theorem evidence_typed : FormationSensitiveNativeList.EvidenceTyping evidence :=
  .cons (.var 3) (.var 2) (.var 1) (.cons (.var 3) (.var 2) (.var 0) .nil)

theorem swapped_evidence_typed : FormationSensitiveNativeList.EvidenceTyping swappedEvidence :=
  .cons (.var 3) (.var 2) (.var 0) (.cons (.var 3) (.var 2) (.var 1) .nil)

def qualified : QualifiedLift sourceType relationTerm sourceList where
  targetList := targetList
  evidence := evidence
  sourceLeaves := evidence_typed.sourceList
  evidenceLeaves := evidence_typed

def swappedQualified : QualifiedLift sourceType relationTerm sourceList where
  targetList := targetList
  evidence := swappedEvidence
  sourceLeaves := swapped_evidence_typed.sourceList
  evidenceLeaves := swapped_evidence_typed

def relationLevel : Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat :=
  .max Intrinsic.elementLevel (.max Intrinsic.elementLevel (.succ Intrinsic.motiveLevel))

theorem relationType_formed : Typing contextA relationType (sortTm relationLevel) := by
  apply FormationSensitive.Typing.piForm (u := .sort Intrinsic.elementLevel)
    (v := .sort (.max Intrinsic.elementLevel (.succ Intrinsic.motiveLevel)))
  · exact .var 0
  · exact .sort Intrinsic.elementLevel
  · apply FormationSensitive.Typing.piForm (u := .sort Intrinsic.elementLevel)
      (v := .sort (.succ Intrinsic.motiveLevel))
    · exact .var 1
    · exact .sort Intrinsic.elementLevel
    · exact .headType (.sort Intrinsic.motiveLevel)
    · exact .sort (.succ Intrinsic.motiveLevel)
    · exact .sorts _ _
  · exact .sort _
  · exact .sorts _ _

theorem context_formed : FormationSensitive.ContextFormation IntrinsicRelator.rules sourceContext := by
  have a : FormationSensitive.ContextFormation IntrinsicRelator.rules contextA :=
    .snoc .nil (.headType (.sort Intrinsic.elementLevel)) (.sort (.succ Intrinsic.elementLevel))
  have r : FormationSensitive.ContextFormation IntrinsicRelator.rules contextR :=
    .snoc a relationType_formed (.sort relationLevel)
  have x : FormationSensitive.ContextFormation IntrinsicRelator.rules contextX :=
    .snoc r (.var 1) (.sort Intrinsic.elementLevel)
  have y : FormationSensitive.ContextFormation IntrinsicRelator.rules contextY :=
    .snoc x (.var 2) (.sort Intrinsic.elementLevel)
  have relationY : Typing contextY (.var 2)
      (.pi (.var 3) (.pi (.var 4) (sortTm Intrinsic.motiveLevel))) := .var 2
  have appliedY : Typing contextY (.app (.var 2) (.var 1))
      (.pi (.var 3) (sortTm Intrinsic.motiveLevel)) :=
    .appElim relationY (.var 1)
  have first : Typing contextY (.app (.app (.var 2) (.var 1)) (.var 0)) (sortTm Intrinsic.motiveLevel) :=
    .appElim appliedY (.var 0)
  have e : FormationSensitive.ContextFormation IntrinsicRelator.rules contextE :=
    .snoc y first (.sort Intrinsic.motiveLevel)
  have relationE : Typing contextE (.var 3)
      (.pi (.var 4) (.pi (.var 5) (sortTm Intrinsic.motiveLevel))) := .var 3
  have appliedE : Typing contextE (.app (.var 3) (.var 2))
      (.pi (.var 4) (sortTm Intrinsic.motiveLevel)) :=
    .appElim relationE (.var 2)
  have second : Typing contextE (.app (.app (.var 3) (.var 2)) (.var 1)) (sortTm Intrinsic.motiveLevel) :=
    .appElim appliedE (.var 1)
  exact .snoc e second (.sort Intrinsic.motiveLevel)

theorem source_formed : Typing sourceContext sourceType (sortTm Intrinsic.elementLevel) := .var 5

theorem relation_formed : Typing sourceContext relationTerm
    (.pi sourceType (.pi (rename wk sourceType) (sortTm Intrinsic.motiveLevel))) := .var 4

def observations : List CettaWire.Term := entries sourceList ⟨targetList, evidence⟩

theorem selected_observations :
    selectedEntries qualified context_formed source_formed source_formed relation_formed = observations :=
  selectedEntries_eq_entries qualified context_formed source_formed source_formed relation_formed

theorem formed : FormationSensitive.Judgment IntrinsicRelator.rules sourceContext
    (ListInstance.realization qualified context_formed source_formed source_formed relation_formed).objectTerm
    (ListInstance.realization qualified context_formed source_formed source_formed relation_formed).objectType :=
  (ListInstance.realization qualified context_formed source_formed source_formed relation_formed).formed

theorem swapped_formed : FormationSensitive.Judgment IntrinsicRelator.rules sourceContext
    (ListInstance.realization swappedQualified context_formed source_formed source_formed relation_formed).objectTerm
    (ListInstance.realization swappedQualified context_formed source_formed source_formed relation_formed).objectType :=
  (ListInstance.realization swappedQualified context_formed source_formed source_formed relation_formed).formed

theorem same_values_different_evidence :
    observations ≠ entries sourceList ⟨targetList, swappedEvidence⟩ := by decide +kernel

theorem same_values_different_output :
    result observations ≠ result (entries sourceList ⟨targetList, swappedEvidence⟩) := by
  intro same
  exact same_values_different_evidence (result_injective same)

end Controls

end ListProvider

structure ExecutionControl where
  label : String
  expression : Atom
  expected : Atom
  semantics : ∀ state, Eval.PureReturns library.runtime [] state expression state expected

def executionControls : List ExecutionControl :=
  [⟨"vector", call NativeVectorAll.Controls.CanonicalAdequacyControls.reflexiveWitness
      NativeVectorAll.Controls.CanonicalAdequacyControls.canonicalValues,
    result Canonical.observations, Canonical.returns⟩,
   ⟨"list-proof-order", ListProvider.call ListProvider.Controls.sourceList
      ⟨ListProvider.Controls.targetList, ListProvider.Controls.evidence⟩,
    result ListProvider.Controls.observations,
    ListProvider.entries_return _ _⟩,
   ⟨"list-proof-swap", ListProvider.call ListProvider.Controls.sourceList
      ⟨ListProvider.Controls.targetList, ListProvider.Controls.swappedEvidence⟩,
    result (ListProvider.entries ListProvider.Controls.sourceList
      ⟨ListProvider.Controls.targetList, ListProvider.Controls.swappedEvidence⟩),
    ListProvider.entries_return _ _⟩]

def modelChecks : Bool := executionControls.all fun control =>
  match Eval.evaluate library.runtime 30000 Effects.empty control.expression with
  | .complete _ answers [] [] => answers == [control.expected]
  | _ => false

#print axioms ScopedTerm.decode_encode
#print axioms entry_injective
#print axioms selectedEntries_eq_entries
#print axioms selected_entries_return
#print axioms result_injective
#print axioms entries_completed_iff
#print axioms Canonical.selected_observations
#print axioms Canonical.formed
#print axioms Canonical.returns
#print axioms Canonical.refuses_reordered_positions
#print axioms Canonical.refuses_changed_witness
#print axioms ListProvider.selected_position
#print axioms ListProvider.selectedEntries_eq_entries
#print axioms ListProvider.selected_entries_return
#print axioms ListProvider.decodeEntry_entry
#print axioms ListProvider.encodeFrame_injective
#print axioms ListProvider.entries_completed_iff
#print axioms ListProvider.Controls.context_formed
#print axioms ListProvider.Controls.formed
#print axioms ListProvider.Controls.swapped_formed
#print axioms ListProvider.Controls.selected_observations
#print axioms ListProvider.Controls.same_values_different_evidence

end Mettapedia.Languages.MeTTa.Bridges.GSLT.FormationSensitiveBundleTraversal
