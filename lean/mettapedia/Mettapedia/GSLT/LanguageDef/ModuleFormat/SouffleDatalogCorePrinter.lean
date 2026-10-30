import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourceToCore
import Mettapedia.GSLT.Parsing.DeclaredConstructorPrinter

/-! Printing reified Datalog source constructors through authored syntax.
The printer consumes Core patterns, not retained input slices or derivations.
Source evidence proves that this independent computation recovers the exact
source text. Semantic ProgramData printing and packed-parse selection remain
separate contracts. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.CorePrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open LanguageDefScalarSyntax LanguageDefScalarPrinter PresentationExprSemantics
open DeclaredConstructorPrinter

def literalScalars? (text : String) : Option (List Nat) := some (stringScalars text)

def lexicalRow? (sort : String) : Option ScalarCore.Row :=
  match (List.finRange SourceViews.profile.states.length).filter
      (fun row => (ScalarCore.lexicalState row).resultSort == sort) with
  | [row] => some row
  | _ => none

def lexical (sort : String) : Option (Pattern → Option (List Nat)) :=
  (lexicalRow? sort).map fun row pattern => (ScalarCore.readLeaf? row pattern).map (· :: [])

theorem lexical_row_exact (row : ScalarCore.Row) :
    lexicalRow? (ScalarCore.lexicalState row).resultSort = some row := by
  fin_cases row <;> decide +kernel

theorem structural_sort_not_lexical (row : Fin SourceViews.grammar.terms.length) :
    lexicalRow? (SourceViews.grammar.terms.get row).category = none := by
  fin_cases row <;> decide +kernel

theorem structural_row_exact (row : Fin SourceViews.grammar.terms.length) :
    constructor? SourceViews.grammar (SourceViews.grammar.terms.get row).label
      (SourceViews.grammar.terms.get row).category = some (SourceViews.grammar.terms.get row) := by
  fin_cases row <;> decide +kernel

def printScalars? (sort : String) (pattern : Pattern) : Option (List Nat) :=
  DeclaredConstructorPrinter.print? SourceViews.grammar stringScalars lexical sort pattern

def printText? (sort : String) (pattern : Pattern) : Option String :=
  (printScalars? sort pattern).map fun points => String.ofList (points.map Char.ofNat)

variable {input : List Nat}

mutual
  theorem print_reify {sort : String} {start stop : Nat} {tree : CST}
      (source : DerivesAt literalScalars? SourceViews.profile SourceViews.grammar input sort start stop tree) :
      printScalars? sort (SourceToCore.reify source) = some (render source) :=
    match source with
    | @DerivesAt.lexical _ _ _ _ _ point row _ formed => by
      change SourceViews.profile.ClassEvidence (ScalarCore.lexicalState row).className point at formed
      change DeclaredConstructorPrinter.print? SourceViews.grammar stringScalars lexical
        (ScalarCore.lexicalState row).resultSort (ScalarCore.leaf row point formed) = some [point]
      have selected : lexical (ScalarCore.lexicalState row).resultSort =
          some (fun pattern => (ScalarCore.readLeaf? row pattern).map (· :: [])) := by
        unfold lexical
        rw [lexical_row_exact]
        rfl
      have printed : DeclaredConstructorPrinter.print? SourceViews.grammar stringScalars lexical
          (ScalarCore.lexicalState row).resultSort (ScalarCore.leaf row point formed) =
          (ScalarCore.readLeaf? row (ScalarCore.leaf row point formed)).map (· :: []) := by
        unfold ScalarCore.leaf ScalarCore.wordLeaf
        exact DeclaredConstructorPrinter.print?_lexical _ _ _ _ _ _ _ selected
      rw [printed, ScalarCore.readLeaf?_leaf]
      rfl
    | .structural row body => by
      simp only [printScalars?, SourceToCore.reify, DeclaredConstructorPrinter.print?, lexical,
        structural_sort_not_lexical, Option.map_none, structural_row_exact]
      exact printItems_reify body
    termination_by structural source

  theorem printItems_reify {rule : GrammarRule} {items : List SyntaxItem}
      {start stop : Nat} {children : List CST}
      (source : ItemsDeriveAt literalScalars? SourceViews.profile SourceViews.grammar input
        rule items start stop children) :
      DeclaredConstructorPrinter.printItems? SourceViews.grammar stringScalars lexical
        rule items (SourceToCore.reifyItems source) = some (renderItems source) :=
    match source with
    | .nil => by simp [DeclaredConstructorPrinter.printItems?, SourceToCore.reifyItems, renderItems]
    | .terminal decoded _ rest => by
      simp only [literalScalars?, Option.some.injEq] at decoded
      simp [DeclaredConstructorPrinter.printItems?, SourceToCore.reifyItems,
        printItems_reify rest, renderItems, ← decoded]
    | .nonterminal lookup head rest => by
      simp only [DeclaredConstructorPrinter.printItems?, SourceToCore.reifyItems, lookup]
      have first := print_reify head
      simp only [printScalars?] at first
      simp [first, printItems_reify rest, renderItems]
    termination_by structural source
end

theorem full_scalars {sort : String} {tree : CST}
    (source : DerivesAt literalScalars? SourceViews.profile SourceViews.grammar input sort 0 input.length tree) :
    printScalars? sort (SourceToCore.reify source) = some input := by
  rw [print_reify, full_source source]

theorem full_text {text sort : String} {tree : CST}
    (source : DerivesAt literalScalars? SourceViews.profile SourceViews.grammar (stringScalars text)
      sort 0 (stringScalars text).length tree) :
    printText? sort (SourceToCore.reify source) = some text := by
  simp only [printText?, full_scalars source, Option.map_some]
  congr 1
  simp [stringScalars, List.map_map, Function.comp_def]

#print axioms print_reify
#print axioms printItems_reify
#print axioms full_scalars
#print axioms full_text

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.CorePrinter
