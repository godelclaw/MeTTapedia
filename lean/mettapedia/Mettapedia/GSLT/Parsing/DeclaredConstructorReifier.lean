import Mettapedia.GSLT.Parsing.DeclaredConstructorPrinter
import Mettapedia.GSLT.Parsing.PresentationExprSemantics

/-! Reify raw CST data with the same authored constructor lookup used by the
printer. The source checker supplies terminal recognition and span authority;
this fold only constructs data and refuses missing or extra children. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.DeclaredConstructorReifier

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open PresentationExprSemantics
open DeclaredConstructorPrinter (constructor?)

abbrev LexicalDecoder := String → Option (CST → Option Pattern)

mutual
  def lower? (language : LanguageDef) (lexical : LexicalDecoder) (sort : String) :
      CST → Option Pattern
    | tree@(.node label _ _ children) =>
      match lexical sort with
      | some readLeaf => readLeaf tree
      | none => do
        let row ← constructor? language label sort
        let values ← lowerItems? language lexical row row.syntaxPattern children
        pure (.apply label values)
    | _ => none
    termination_by tree => (sizeOf tree, 0)

  def lowerItems? (language : LanguageDef) (lexical : LexicalDecoder) (rule : GrammarRule)
      (items : List SyntaxItem) (children : List CST) : Option (List Pattern) :=
    match items, children with
    | [], [] => some []
    | .terminal _ :: rest, children => lowerItems? language lexical rule rest children
    | .nonTerminal parameter :: rest, head :: tail => do
      let sort ← paramSort? rule parameter
      let first ← lower? language lexical sort head
      let later ← lowerItems? language lexical rule rest tail
      pure (first :: later)
    | _, _ => none
    termination_by (sizeOf children, items.length + 1)
end

theorem lower?_lexical (language : LanguageDef) (lexical : LexicalDecoder)
    (sort label : String) (start stop : Nat) (children : List CST)
    (readLeaf : CST → Option Pattern) (selected : lexical sort = some readLeaf) :
    lower? language lexical sort (.node label start stop children) =
      readLeaf (.node label start stop children) := by
  rw [lower?, selected]

end Mettapedia.GSLT.Parsing.DeclaredConstructorReifier
