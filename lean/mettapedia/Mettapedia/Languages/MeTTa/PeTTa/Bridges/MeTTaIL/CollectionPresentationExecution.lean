import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentationProofs

/-!
# Native reconstruction of ordinary collection presentations

The source replays retained decisions using the established allocator and
canonical comparison. The original allocation history stays with its answer.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RecursiveCollectionPresentation
open CanonicalBags CanonicalCompare CollectionSelection
open InferenceCettaWire (encodePattern encodeCollectionType encodeRest encodeBinder)
open RecursiveCollectionExecution (eventTerm)
open CollectionSelectionExecution (decisionTerm pairTerm booleanTerm)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_presentation.metta"
    sha256 "b20a814bc1b9baa86a6778e8fdff9c459ff27d272743bd48c5ddf25993bdba91"

def library : BridgeKit.Library :=
  RetainedMatchingWire.interpretedLibrary

set_option maxRecDepth 100000 in
theorem checked : library.check = true := RetainedMatchingWire.interpreted_checked

section ProofMetadata

private local instance presentationEquationEq : DecidableEq SpaceSemantics.Equation := by
  intro left right
  apply decidable_of_iff (left.head = right.head ∧ left.arguments = right.arguments ∧ left.body = right.body)
  constructor
  · rintro ⟨head, arguments, body⟩
    cases left
    cases right
    cases head
    cases arguments
    cases body
    rfl
  · intro same
    cases same
    exact ⟨rfl, rfl, rfl⟩

/-- Direct outward calls derived from the actual family bodies. -/
def presentationProofInheritedHeads : List String := ["gslt:automata:append", "gslt:automata:length", "gslt:recursive-collection:arrange", "gslt:collection:replay",  "gslt:complete:take", "gslt:complete:drop"]

theorem presentationProofInheritedHeads_derived :
    ((source.program.equations.flatMap (fun row => CompleteExecution.sourceLiteralHeads row.body)).filter
      (fun head => head.startsWith "gslt:" && !(source.program.equations.map (·.head)).contains head)).eraseDups =
        presentationProofInheritedHeads := by decide +kernel

private def presentationMetadataBase : SpaceSemantics.Program where
  equations := [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[1]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program.equations[12]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program.equations[26]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[5]'(by decide +kernel)).program.equations[5]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[10]'(by decide +kernel)).program.equations[0]'(by decide +kernel)]
  declarations := [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[1]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program.declarations[12]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program.declarations[26]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[5]'(by decide +kernel)).program.declarations[5]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[10]'(by decide +kernel)).program.declarations[0]'(by decide +kernel)]

/-- Bounded source metadata; all operational conclusions retain the shared runtime. -/
def presentationProofLibrary : Library := ⟨presentationMetadataBase, source.program, ["gslt:collection-presentation:"]⟩

def presentationProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || presentationProofLibrary.owns head || presentationProofInheritedHeads.contains head

theorem presentationProof_checked : presentationProofLibrary.check = true := by decide +kernel

theorem presentationProof_agreement :
    ProgramAgreementOn presentationProofHeads presentationProofLibrary.runtime library.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

#print axioms presentationProofInheritedHeads_derived
#print axioms presentationProof_checked
#print axioms presentationProof_agreement

end ProofMetadata

def presentationTerm {α : Type} (element : α → Term)
    (result : α × List EquationalScopedReceipts.Event) : Term :=
  .application "RecursivePresentation" [element result.1, encodeList eventTerm result.2]

syntax "presentation_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| presentation_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in presentationProof_checked using presentationProof_agreement; metta_eval [$facts,*] with presentationProof_checked in presentationProof_agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        CompleteExecution.pattern_symbol_unmatched, presentationTerm, eventTerm,
        encodeList, encodeOption, InferenceCettaWire.encodeList, InferenceCettaWire.encodePatterns_eq_encodeList, $extra,*]))

@[metta_head "gslt:automata:append"]
theorem append_returns {α : Type} (element : α → Term) (state : Effects.State) (left right : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)])
      state (encoded (encodeList element (left ++ right))) := by
  exact RecursiveCollectionExecution.append_returns element state left right

@[metta_head "gslt:automata:length"]
theorem length_returns {α : Type} (element : α → Term) (state : Effects.State) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:length" [encoded (encodeList element items)]) state (number items.length) := by
  exact RecursiveCollectionExecution.length_returns element state items

@[metta_head "gslt:recursive-collection:arrange"]
theorem arrange_returns (state : Effects.State) (table : List String) (ordered : NameOrdered table)
    (kind : CollType) (items : List Pattern) (covered : ∀ item ∈ items, Covered table item) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:arrange" [encoded (encodeList Term.string table),
        encoded (encodeCollectionType kind), encoded (encodeList encodePattern items)])
      state (encoded (encodeList encodePattern (arrange kind items))) := by
  exact RecursiveCollectionExecution.arrange_returns state table ordered kind items covered

@[metta_head "gslt:collection:replay"]
theorem replay_returns (state : Effects.State) (idempotent : Bool) (items : List Pattern)
    (decisions : List Decision) :
    PureReturns library.runtime [] state
      (apply "gslt:collection:replay" [encoded (booleanTerm idempotent),
        encoded (encodeList encodePattern items), encoded (encodeList decisionTerm decisions)])
      state (encoded (encodeOption (pairTerm encodePattern) (replay idempotent items decisions))) := by
  exact CollectionSelectionExecution.replay_returns encodePattern state idempotent decisions items

@[metta_head "gslt:complete:take"]
theorem take_returns (state : Effects.State) (count : Nat) (items : List Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:complete:take" [number count, encoded (encodeList encodePattern items)])
      state (encoded (encodeList encodePattern (items.take count))) := by
  induction count generalizing items with
  | zero =>
    metta_call_in CompleteExecution.completeProof_checked using CompleteExecution.completeProof_agreement
    metta_eval with CompleteExecution.completeProof_checked in CompleteExecution.completeProof_agreement
      unfolding [encodeList, List.take, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | succ count ih =>
    metta_call_in CompleteExecution.completeProof_checked using CompleteExecution.completeProof_agreement
    cases items with
    | nil =>
      metta_eval with CompleteExecution.completeProof_checked in CompleteExecution.completeProof_agreement
        unfolding [encodeList, List.take, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
          CettaWireAtom.encode, CettaWireAtom.encodeMany]
    | cons head rest =>
      have later := ih rest
      metta_eval [later] with CompleteExecution.completeProof_checked
        in CompleteExecution.completeProof_agreement unfolding
        [encodeList, List.take, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
          CettaWireAtom.encode, CettaWireAtom.encodeMany]

@[metta_head "gslt:complete:drop"]
theorem drop_returns (state : Effects.State) (count : Nat) (items : List Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:complete:drop" [number count, encoded (encodeList encodePattern items)])
      state (encoded (encodeList encodePattern (items.drop count))) := by
  have mapped (values : List Pattern) : encoded (encodeList encodePattern values) =
      CompleteExecution.terms (values.map encodePattern) := by
    simp only [CompleteExecution.terms, CettaWire.encodeList_map, Function.id_comp]
  rw [mapped, mapped, List.map_drop]
  exact CompleteExecution.drop_returns state count (items.map encodePattern)

@[metta_head "gslt:collection-presentation:wrap"]
theorem wrap_app_returns (state : Effects.State) (label : String) (items : List Pattern)
    (remaining : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state (apply "gslt:collection-presentation:wrap"
      [encoded (.application "PresentationApp" [.string label]),
        encoded (encodeOption (presentationTerm (encodeList encodePattern)) (some (items, remaining)))])
      state (encoded (encodeOption (presentationTerm encodePattern) (some (.apply label items, remaining)))) := by
  presentation_eval unfolding [encodePattern]

@[metta_head "gslt:collection-presentation:wrap"]
theorem wrap_lambda_returns (state : Effects.State) (display : Option String) (body : Pattern)
    (remaining : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state (apply "gslt:collection-presentation:wrap"
      [encoded (.application "PresentationLam" [encodeBinder display]),
        encoded (encodeOption (presentationTerm encodePattern) (some (body, remaining)))])
      state (encoded (encodeOption (presentationTerm encodePattern) (some (.lambda display body, remaining)))) := by
  presentation_eval unfolding [encodePattern]

@[metta_head "gslt:collection-presentation:wrap"]
theorem wrap_multiLambda_returns (state : Effects.State) (arity : Nat) (display : List String) (body : Pattern)
    (remaining : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state (apply "gslt:collection-presentation:wrap"
      [encoded (.application "PresentationMultiLam" [.natural arity, encodeList Term.string display]),
        encoded (encodeOption (presentationTerm encodePattern) (some (body, remaining)))])
      state (encoded (encodeOption (presentationTerm encodePattern)
        (some (.multiLambda arity display body, remaining)))) := by
  presentation_eval unfolding [encodePattern]

@[metta_head "gslt:collection-presentation:wrap"]
theorem wrap_subst_returns (state : Effects.State) (body replacement : Pattern)
    (remaining : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state (apply "gslt:collection-presentation:wrap"
      [encoded (.application "PresentationSubst" [encodePattern body]),
        encoded (encodeOption (presentationTerm encodePattern) (some (replacement, remaining)))])
      state (encoded (encodeOption (presentationTerm encodePattern)
        (some (.subst body replacement, remaining)))) := by
  presentation_eval unfolding [encodePattern]

@[metta_head "gslt:collection-presentation:wrap"]
theorem wrap_cons_returns (state : Effects.State) (head : Pattern) (tail : List Pattern)
    (remaining : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state (apply "gslt:collection-presentation:wrap"
      [encoded (.application "PresentationCons" [encodePattern head]),
        encoded (encodeOption (presentationTerm (encodeList encodePattern)) (some (tail, remaining)))])
      state (encoded (encodeOption (presentationTerm (encodeList encodePattern))
        (some (head :: tail, remaining)))) := by presentation_eval

@[metta_head "gslt:collection-presentation:wrap"]
theorem wrap_collection_returns (state : Effects.State) (kind : CollType) (items residual : List Pattern)
    (remaining : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state (apply "gslt:collection-presentation:wrap"
      [encoded (.application "PresentationCollection" [encodeCollectionType kind, encodeList encodePattern residual]),
        encoded (encodeOption (presentationTerm (encodeList encodePattern)) (some (items, remaining)))])
      state (encoded (encodeOption (presentationTerm encodePattern)
        (some (.collection kind (items ++ residual) none, remaining)))) := by
  presentation_eval [append_returns encodePattern state items residual] unfolding [encodePattern, encodeRest]

#print axioms append_returns
#print axioms length_returns
#print axioms arrange_returns
#print axioms replay_returns
#print axioms take_returns
#print axioms drop_returns
#print axioms wrap_app_returns
#print axioms wrap_lambda_returns
#print axioms wrap_multiLambda_returns
#print axioms wrap_subst_returns
#print axioms wrap_cons_returns
#print axioms wrap_collection_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution
