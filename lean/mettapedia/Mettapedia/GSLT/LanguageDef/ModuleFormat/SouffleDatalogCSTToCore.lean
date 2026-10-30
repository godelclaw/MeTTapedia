import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogCorePrinter
import Mettapedia.GSLT.Parsing.DeclaredConstructorReifier

/-! Executable CST-to-Core construction joined to original source evidence.
This fold is independent of source derivation objects. Exact parser replay
must precede its use as a source reading: reification alone does not authorize
terminal spellings or structural spans. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.CSTToCore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Parsing
open LanguageDefScalarSyntax PresentationExprSemantics DeclaredConstructorReifier

def lexicalLeaf? (row : ScalarCore.Row) : CST → Option Pattern
  | .node label start stop [.terminal [point] before after] =>
    if label = (ScalarCore.lexicalState row).ruleLabel ∧ before = start ∧
        after = stop ∧ stop = start + 1 then
      if formed : SourceViews.profile.ClassEvidence (ScalarCore.lexicalState row).className point
      then some (ScalarCore.leaf row point formed) else none
    else none
  | _ => none

def lexical (sort : String) : Option (CST → Option Pattern) :=
  (CorePrinter.lexicalRow? sort).map lexicalLeaf?

def lower? (sort : String) (tree : CST) : Option Pattern :=
  DeclaredConstructorReifier.lower? SourceViews.grammar lexical sort tree

variable {literalScalars? : String → Option (List Nat)} {input : List Nat}

mutual
  theorem lower_source {sort : String} {start stop : Nat} {tree : CST}
      (source : DerivesAt literalScalars? SourceViews.profile SourceViews.grammar input sort start stop tree) :
      lower? sort tree = some (SourceToCore.reify source) :=
    match source with
    | @DerivesAt.lexical _ _ _ _ start point row _ formed => by
      change SourceViews.profile.ClassEvidence (ScalarCore.lexicalState row).className point at formed
      change DeclaredConstructorReifier.lower? SourceViews.grammar lexical
        (ScalarCore.lexicalState row).resultSort
          (.node (ScalarCore.lexicalState row).ruleLabel start (start + 1)
            [.terminal [point] start (start + 1)]) = some (ScalarCore.leaf row point formed)
      have selected : lexical (ScalarCore.lexicalState row).resultSort = some (lexicalLeaf? row) := by
        simp only [lexical, CorePrinter.lexical_row_exact, Option.map_some]
      rw [DeclaredConstructorReifier.lower?_lexical _ _ _ _ _ _ _ _ selected]
      simp [lexicalLeaf?, formed]
    | .structural row body => by
      simp only [lower?, DeclaredConstructorReifier.lower?, lexical,
        CorePrinter.structural_sort_not_lexical, Option.map_none, CorePrinter.structural_row_exact]
      change ((DeclaredConstructorReifier.lowerItems? SourceViews.grammar lexical
        (SourceViews.grammar.terms.get row) (SourceViews.grammar.terms.get row).syntaxPattern _).bind
          fun values => some (Pattern.apply (SourceViews.grammar.terms.get row).label values)) =
            some (Pattern.apply (SourceViews.grammar.terms.get row).label (SourceToCore.reifyItems body))
      rw [lowerItems_source body]
      rfl
    termination_by structural source

  theorem lowerItems_source {rule : GrammarRule} {items : List SyntaxItem}
      {start stop : Nat} {children : List CST}
      (source : ItemsDeriveAt literalScalars? SourceViews.profile SourceViews.grammar input
        rule items start stop children) :
      DeclaredConstructorReifier.lowerItems? SourceViews.grammar lexical rule items children =
        some (SourceToCore.reifyItems source) :=
    match source with
    | .nil => by simp [DeclaredConstructorReifier.lowerItems?, SourceToCore.reifyItems]
    | .terminal _ _ rest => by
      simpa only [DeclaredConstructorReifier.lowerItems?, SourceToCore.reifyItems] using lowerItems_source rest
    | .nonterminal lookup head rest => by
      have first := lower_source head
      simp only [lower?] at first
      simp [DeclaredConstructorReifier.lowerItems?, lookup, first, lowerItems_source rest, SourceToCore.reifyItems]
    termination_by structural source
end

/-- Source evidence is proof-only. The published term is computed from the
CST data, while the independent source fold proves its closed sorting. -/
def checkedTerm {sort : String} {start stop : Nat} (tree : CST)
    (source : Nonempty (DerivesAt literalScalars? SourceViews.profile SourceViews.grammar input
      sort start stop tree)) :
    ClosedTerm ScalarCore.language ⟨sort, by
      obtain ⟨witness⟩ := source
      exact SourceToCore.source_sort_declared witness⟩ :=
  ⟨(lower? sort tree).get (by
      obtain ⟨witness⟩ := source
      rw [lower_source witness]
      rfl), by
    obtain ⟨witness⟩ := source
    have available : (lower? sort tree).isSome = true := by rw [lower_source witness]; rfl
    have same : (lower? sort tree).get available = SourceToCore.reify witness := by
      apply Option.some.inj
      exact (Option.some_get _).trans (lower_source witness)
    rw [same]
    exact (SourceToCore.closedTerm witness).property⟩

theorem checkedTerm_lower {sort : String} {start stop : Nat} (tree : CST)
    (source : Nonempty (DerivesAt literalScalars? SourceViews.profile SourceViews.grammar input
      sort start stop tree)) :
    lower? sort tree = some (checkedTerm tree source).val :=
  (Option.some_get _).symm

#print axioms lower_source
#print axioms lowerItems_source
#print axioms checkedTerm
#print axioms checkedTerm_lower

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.CSTToCore
