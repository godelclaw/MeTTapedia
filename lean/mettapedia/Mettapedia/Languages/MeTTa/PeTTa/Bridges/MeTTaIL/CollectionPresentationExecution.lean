import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentationProofs

/-!
# Native reconstruction of ordinary collection presentations

The source replays retained decisions using the established allocator and
canonical comparison. The original allocation history stays with its answer.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

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
  ⟨RecursiveCollectionExecution.library.runtime, source.program, ["gslt:collection-presentation:"]⟩

set_option maxRecDepth 100000 in
theorem checked : library.check = true := by decide +kernel

def presentationTerm {α : Type} (element : α → Term)
    (result : α × List EquationalScopedReceipts.Event) : Term :=
  .application "RecursivePresentation" [element result.1, encodeList eventTerm result.2]

syntax "presentation_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| presentation_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
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
  metta_lift checked ["left", "right"] (RecursiveCollectionExecution.append_returns element state left right)

@[metta_head "gslt:automata:length"]
theorem length_returns {α : Type} (element : α → Term) (state : Effects.State) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:length" [encoded (encodeList element items)]) state (number items.length) := by
  metta_lift checked ["items"] (RecursiveCollectionExecution.length_returns element state items)

@[metta_head "gslt:recursive-collection:arrange"]
theorem arrange_returns (state : Effects.State) (table : List String) (ordered : NameOrdered table)
    (kind : CollType) (items : List Pattern) (covered : ∀ item ∈ items, Covered table item) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:arrange" [encoded (encodeList Term.string table),
        encoded (encodeCollectionType kind), encoded (encodeList encodePattern items)])
      state (encoded (encodeList encodePattern (arrange kind items))) := by
  metta_lift checked ["names", "kind", "items"]
    (RecursiveCollectionExecution.arrange_returns state table ordered kind items covered)

@[metta_head "gslt:collection:replay"]
theorem replay_returns (state : Effects.State) (idempotent : Bool) (items : List Pattern)
    (decisions : List Decision) :
    PureReturns library.runtime [] state
      (apply "gslt:collection:replay" [encoded (booleanTerm idempotent),
        encoded (encodeList encodePattern items), encoded (encodeList decisionTerm decisions)])
      state (encoded (encodeOption (pairTerm encodePattern) (replay idempotent items decisions))) := by
  metta_lift checked ["idempotent", "items", "decisions"]
    (recursive_from_logged% ["idempotent", "items", "decisions"]
      (by metta_lift CollectionLoggedSearchExecution.checked ["idempotent", "items", "decisions"]
        (by metta_lift ScopedCollectionExecution.checked ["idempotent", "items", "decisions"]
          (CollectionSelectionExecution.replay_returns encodePattern state idempotent decisions items))))

syntax "presentation_from_complete% " "[" str,* "] " term:max : term
macro_rules
  | `(presentation_from_complete% [$names,*] $fact) =>
      `(by metta_lift checked [$names,*]
        (by metta_lift RecursiveCollectionExecution.checked [$names,*]
          (by metta_lift CompleteExecution.collection_base_checked [$names,*]
            (by metta_lift CompleteExecution.canonical_checked [$names,*]
              (by metta_lift CompleteExecution.laws_checked [$names,*] $fact)))))

@[metta_head "gslt:complete:take"]
theorem take_returns (state : Effects.State) (count : Nat) (items : List Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:complete:take" [number count, encoded (encodeList encodePattern items)])
      state (encoded (encodeList encodePattern (items.take count))) := by
  exact presentation_from_complete% ["count", "items"]
    (CompleteExecution.take_list_returns encodePattern state count items)

@[metta_head "gslt:complete:drop"]
theorem drop_returns (state : Effects.State) (count : Nat) (items : List Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:complete:drop" [number count, encoded (encodeList encodePattern items)])
      state (encoded (encodeList encodePattern (items.drop count))) := by
  exact presentation_from_complete% ["count", "items"]
    (CompleteExecution.drop_list_returns encodePattern state count items)

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

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution
