import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ScopedSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Sizes
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedRuleInstantiationExecution
import Mettapedia.OSLF.MeTTaIL.QuoteDropLaws
import Mettapedia.OSLF.MeTTaIL.CanonicalCompare

/-!
# The quote-drop normal form in the complete machine's runtime

`gslt:rule:scope-reflective-normalize` computes the quote-drop normal form of a reflective
presentation (`ScopedReflectiveBinderOperationExecution.normalize_returns`). Its code uses only the
normal-form family, binding forms, case analysis, string equality and the pattern constructors, and
the scoped library agrees with the reflection fragment on all of them, so the fact holds in the scoped
library and, raised, in the complete machine (`complete_normalize_returns`).

The normal form removes a quote with the drop below it and nothing else, so it keeps every name in a
name table (`covered_normal`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Effects (State)
open Eval
open BridgeKit WireKit

/-- The heads the quote-drop normal form's code uses. -/
def normalizeHeads (head : String) : Bool :=
  head ∈ ["gslt:rule:scope-reflective-normalize", "gslt:rule:scope-reflective-normalize-list",
    "gslt:rule:scope-reflective-normalize-finish", "let", "let*", "case", "if", "==", "PApp", "PLam",
    "PMultiLam", "PSubst", "PCollection", "Var", "FVar", "LCons", "LNil"]

set_option maxRecDepth 100000 in
theorem normalize_closed : ProgramClosed normalizeHeads ScopedReflectiveBinderOperationExecution.runtime :=
  closed_of_all _ _ (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem normalize_agreement :
    ProgramAgreementOn normalizeHeads ScopedReflectiveBinderOperationExecution.runtime scopedLibrary.runtime :=
  agreement_trans (programAgreementOn_of_retained_rows _ _ _ (by rfl) (by rfl))
    (scoped_runtime_agreement _)

set_option maxRecDepth 100000 in
/-- `gslt:rule:scope-reflective-normalize` computes the quote-drop normal form, in the scoped library. -/
theorem scoped_normalize_returns (state : State) (declaration : ReflectivePresentationDecl) (pattern : Pattern) :
    PureReturns scopedLibrary.runtime [] state
      (apply "gslt:rule:scope-reflective-normalize"
        [encoded (.string declaration.quoteConstructor), encoded (.string declaration.dropConstructor),
          patternValue pattern]) state
      (patternValue (ReflectiveSubstitution.normalizeReflective declaration pattern)) :=
  transport_call normalize_closed normalize_agreement (by decide) (by decide) (by decide +kernel) (by decide)
    ["quote", "drop", "pattern"] (by decide) rfl (by decide +kernel)
    (ScopedReflectiveBinderOperationExecution.normalize_returns state declaration pattern)

/-- `gslt:rule:scope-reflective-normalize` computes the quote-drop normal form, in the complete
machine's runtime. -/
theorem complete_normalize_returns (state : State) (declaration : ReflectivePresentationDecl) (pattern : Pattern) :
    PureReturns runtime [] state
      (apply "gslt:rule:scope-reflective-normalize"
        [encoded (.string declaration.quoteConstructor), encoded (.string declaration.dropConstructor),
          patternValue pattern]) state
      (patternValue (ReflectiveSubstitution.normalizeReflective declaration pattern)) := by
  metta_raise ["quote", "drop", "pattern"] (scoped_normalize_returns state declaration pattern)

/-! ## Name tables -/

theorem names_finish (declaration : ReflectivePresentationDecl) (label : String) (arguments : List Pattern)
    (name : String) :
    name ∈ CanonicalCompare.names (ReflectiveSubstitution.finishNormalizeReflectiveApply declaration label arguments) →
      name ∈ CanonicalCompare.names (.apply label arguments) := by
  intro member
  unfold ReflectiveSubstitution.finishNormalizeReflectiveApply at member
  split at member
  · split at member
    · split at member
      · simp [CanonicalCompare.names, CanonicalCompare.namesList, member]
      · exact member
    · exact member
  · exact member

/-- **The quote-drop normal form adds no name.** -/
theorem names_normal (declaration : ReflectivePresentationDecl) (pattern : Pattern) (name : String) :
    name ∈ CanonicalCompare.names (QuoteDrop.normal declaration pattern) → name ∈ CanonicalCompare.names pattern := by
  induction pattern using Pattern.inductionOn generalizing name with
  | hbvar index => simp [QuoteDrop.normal_bvar]
  | hfvar other => simp [QuoteDrop.normal_fvar]
  | happly label arguments ih =>
    intro member
    rw [QuoteDrop.normal_apply] at member
    have inside := names_finish declaration label _ name member
    simp only [CanonicalCompare.names, List.mem_cons, CanonicalCompare.mem_namesList, List.mem_map] at inside ⊢
    rcases inside with same | ⟨_, ⟨argument, argumentIn, rfl⟩, named⟩
    · exact .inl same
    · exact .inr ⟨argument, argumentIn, ih argument argumentIn name named⟩
  | hlambda binder body ih =>
    intro member
    rw [QuoteDrop.normal_lambda] at member
    simp only [CanonicalCompare.names, List.mem_append] at member ⊢
    exact member.imp id (ih name)
  | hmultiLambda arity binders body ih =>
    intro member
    rw [QuoteDrop.normal_multiLambda] at member
    simp only [CanonicalCompare.names, List.mem_append] at member ⊢
    exact member.imp id (ih name)
  | hsubst body replacement bodyIH replacementIH =>
    intro member
    rw [QuoteDrop.normal_subst] at member
    simp only [CanonicalCompare.names, List.mem_append] at member ⊢
    exact member.imp (bodyIH name) (replacementIH name)
  | hcollection kind elements rest ih =>
    intro member
    rw [QuoteDrop.normal_collection] at member
    simp only [CanonicalCompare.names, List.mem_append, CanonicalCompare.mem_namesList, List.mem_map] at member ⊢
    rcases member with ⟨_, ⟨element, elementIn, rfl⟩, named⟩ | inRest
    · exact .inl ⟨element, elementIn, ih element elementIn name named⟩
    · exact .inr inRest

/-- **The quote-drop normal form keeps a name table's coverage.** -/
theorem covered_normal {table : List String} (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (covered : CanonicalCompare.Covered table pattern) :
    CanonicalCompare.Covered table (ReflectiveSubstitution.normalizeReflective declaration pattern) :=
  fun name member => covered name (names_normal declaration pattern name member)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
