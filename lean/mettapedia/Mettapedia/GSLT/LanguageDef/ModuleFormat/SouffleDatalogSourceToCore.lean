import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogScalars
import Mettapedia.GSLT.Parsing.GrammarArgumentLayout
import Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter

/-! Source-derivation constructor reification into the composed Datalog Core.
The exact source row chooses each constructor. Lexical leaves use the checked
scalar realization; terminal recognition and source spans stay in the retained
derivation. This embeds syntax, including layout and literal spelling. The
semantic ProgramData projection and execution join are separate operations. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceToCore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Parsing
open LanguageDefScalarSyntax PresentationExprSemantics
open Mettapedia.GSLT.Parsing.GrammarArgumentLayout

theorem source_parameter_order (row : Fin SourceViews.grammar.terms.length) :
    parameters? (SourceViews.grammar.terms.get row)
      (SourceViews.grammar.terms.get row).syntaxPattern =
        some (SourceViews.grammar.terms.get row).params := by
  fin_cases row <;> decide +kernel

theorem source_not_bare (row : Fin SourceViews.grammar.terms.length) :
    ¬ UsesBareCollection (SourceViews.grammar.terms.get row) := by
  fin_cases row <;> simp [SourceViews.grammar, UsesBareCollection, GrammarRule.bareParams]

variable {literalScalars? : String → Option (List Nat)} {input : List Nat}

mutual
  def reify {sort : String} {start stop : Nat} {tree : CST} :
      DerivesAt literalScalars? SourceViews.profile SourceViews.grammar input sort start stop tree → Pattern
    | .lexical row _ formed => ScalarCore.leaf row _ formed
    | .structural row body => .apply (SourceViews.grammar.terms.get row).label (reifyItems body)

  def reifyItems {rule : GrammarRule} {items : List SyntaxItem}
      {start stop : Nat} {children : List CST} :
      ItemsDeriveAt literalScalars? SourceViews.profile SourceViews.grammar input
        rule items start stop children → List Pattern
    | .nil => []
    | .terminal _ _ rest => reifyItems rest
    | .nonterminal _ head rest => reify head :: reifyItems rest
end

mutual
  theorem reify_typed {sort : String} {start stop : Nat} {tree : CST}
      (source : DerivesAt literalScalars? SourceViews.profile SourceViews.grammar input sort start stop tree) :
      HasType ScalarCore.language FreeTypeContext.empty [] (reify source) (.base sort) :=
    match source with
    | .lexical row _ formed => (ScalarCore.leaf_closed row _ formed).1
    | .structural row body => by
      exact .constructor (ScalarCore.source_rows (List.get_mem SourceViews.grammar.terms row))
        (source_not_bare row) (reifyItems_typed body (source_parameter_order row))
    termination_by structural source

  theorem reifyItems_typed {rule : GrammarRule} {items : List SyntaxItem}
      {start stop : Nat} {children : List CST} {expected : List TermParam}
      (source : ItemsDeriveAt literalScalars? SourceViews.profile SourceViews.grammar input
        rule items start stop children)
      (layout : parameters? rule items = some expected) :
      ArgumentsHaveTypes ScalarCore.language FreeTypeContext.empty [] (reifyItems source) expected :=
    match source with
    | .nil => by cases layout; exact .nil
    | .terminal _ _ rest => reifyItems_typed rest layout
    | .nonterminal lookup head rest => by
      rename_i actualStop parameter resultSort middle childTree restItems restChildren
      cases tailLayout : parameters? rule restItems with
      | none => simp [parameters?, lookup, tailLayout] at layout
      | some tail =>
        simp [parameters?, lookup, tailLayout] at layout
        subst expected
        exact .cons trivial rfl (reify_typed head) (reifyItems_typed rest tailLayout)
    termination_by structural source
end

mutual
  theorem reify_shape {sort : String} {start stop : Nat} {tree : CST}
      (source : DerivesAt literalScalars? SourceViews.profile SourceViews.grammar input sort start stop tree) :
      isObjectPattern (reify source) = true ∧ (reify source).hasCanonicalBinderMetadata = true :=
    match source with
    | .lexical row _ formed => by
      exact ⟨(ScalarCore.leaf_closed row _ formed).2.2.2.1, (ScalarCore.leaf_closed row _ formed).2.2.1⟩
    | .structural _ body => reifyItems_shape body
    termination_by structural source

  theorem reifyItems_shape {rule : GrammarRule} {items : List SyntaxItem}
      {start stop : Nat} {children : List CST}
      (source : ItemsDeriveAt literalScalars? SourceViews.profile SourceViews.grammar input
        rule items start stop children) :
      isObjectPatternList (reifyItems source) = true ∧
        Pattern.hasCanonicalBinderMetadataList (reifyItems source) = true :=
    match source with
    | .nil => ⟨rfl, rfl⟩
    | .terminal _ _ rest => reifyItems_shape rest
    | .nonterminal _ head rest => by
      obtain ⟨headObject, headCanonical⟩ := reify_shape head
      obtain ⟨tailObject, tailCanonical⟩ := reifyItems_shape rest
      exact ⟨by simp only [reifyItems, isObjectPatternList, headObject, tailObject, Bool.and_self],
        by simp only [reifyItems, Pattern.hasCanonicalBinderMetadataList, headCanonical, tailCanonical, Bool.and_self]⟩
    termination_by structural source
end

theorem source_sort_declared {sort : String} {start stop : Nat} {tree : CST}
    (source : DerivesAt literalScalars? SourceViews.profile SourceViews.grammar input sort start stop tree) :
    sort ∈ ScalarCore.language.types := by
  cases source with
  | lexical row => exact (ScalarCore.leafSort row).property
  | structural row => fin_cases row <;> decide +kernel

def closedTerm {sort : String} {start stop : Nat} {tree : CST}
    (source : DerivesAt literalScalars? SourceViews.profile SourceViews.grammar input sort start stop tree) :
    ClosedTerm ScalarCore.language ⟨sort, source_sort_declared source⟩ :=
  ⟨reify source, by
    have typed := reify_typed source
    have safe : ScopeSafe ScalarCore.language (reify source) := typed.isWellScopedAt
    obtain ⟨object, canonical⟩ := reify_shape source
    exact ⟨typed, ground_of_closed_sorting (sort := ⟨sort, source_sort_declared source⟩) typed object safe,
      canonical, object, safe⟩⟩

#print axioms source_parameter_order
#print axioms reify_typed
#print axioms reify_shape
#print axioms source_sort_declared
#print axioms closedTerm

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceToCore
