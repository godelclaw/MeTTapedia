import Mettapedia.OSLF.Framework.GrammarDerives

/-! Constructor argument order induced by authored scalar syntax items.
Terminals carry recognition evidence, while each named nonterminal contributes
its actual declared base sort. Missing parameter lookups fail explicitly. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GrammarArgumentLayout

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives

def parameters? (rule : GrammarRule) : List SyntaxItem → Option (List TermParam)
  | [] => some []
  | .terminal _ :: rest => parameters? rule rest
  | .nonTerminal parameter :: rest => do
      let sort ← paramSort? rule parameter
      let tail ← parameters? rule rest
      pure (.simple parameter (.base sort) :: tail)
  | _ :: _ => none

end Mettapedia.GSLT.Parsing.GrammarArgumentLayout
