import Mettapedia.OSLF.Framework.GrammarDerives

/-! Printing constructor data through the actual authored syntax rows.
Lexical sorts supply their declared decoder. Structural lookup requires one
exact row, and every child slot is consumed in source order. This is a printer,
not a source parser or a policy that selects among packed parses. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.DeclaredConstructorPrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives

abbrev LexicalPrinter := String → Option (Pattern → Option (List Nat))

def constructor? (language : LanguageDef) (label sort : String) : Option GrammarRule :=
  match language.terms.filter (fun row => row.label == label && row.category == sort) with
  | [row] => some row
  | _ => none

mutual
  def print? (language : LanguageDef) (literal : String → List Nat)
      (lexical : LexicalPrinter) (sort : String) : Pattern → Option (List Nat)
    | pattern@(.apply label children) =>
      match lexical sort with
      | some readLeaf => readLeaf pattern
      | none => do
        let row ← constructor? language label sort
        printItems? language literal lexical row row.syntaxPattern children
    | _ => none
    termination_by pattern => (sizeOf pattern, 0)

  def printItems? (language : LanguageDef) (literal : String → List Nat)
      (lexical : LexicalPrinter) (rule : GrammarRule)
      (items : List SyntaxItem) (children : List Pattern) : Option (List Nat) :=
    match items, children with
    | [], [] => some []
    | .terminal token :: rest, children => do
      let tail ← printItems? language literal lexical rule rest children
      pure (literal token ++ tail)
    | .nonTerminal parameter :: rest, head :: tail => do
      let sort ← paramSort? rule parameter
      let first ← print? language literal lexical sort head
      let later ← printItems? language literal lexical rule rest tail
      pure (first ++ later)
    | _, _ => none
    termination_by (sizeOf children, items.length + 1)
end

theorem print?_lexical (language : LanguageDef) (literal : String → List Nat)
    (lexical : LexicalPrinter) (sort label : String) (children : List Pattern)
    (readLeaf : Pattern → Option (List Nat)) (selected : lexical sort = some readLeaf) :
    print? language literal lexical sort (.apply label children) = readLeaf (.apply label children) := by
  rw [print?, selected]

end Mettapedia.GSLT.Parsing.DeclaredConstructorPrinter
