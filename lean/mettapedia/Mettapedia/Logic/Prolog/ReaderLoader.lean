import Mettapedia.Logic.Prolog.ReaderSource

/-!
# Sequential Prolog source loading

Prolog directives can change the operator environment used to read the next
term. This module therefore alternates parsing and directive effects instead
of parsing a whole file under one fixed table.

The effect function is explicit: the reader itself neither pretends to
execute arbitrary directives nor imports host state. A runtime loader can
execute a directive and return the resulting table; the pinned-source reader
can use the checked read-time operator profile in `ReaderDirective`.
-/

namespace Mettapedia.Logic.Prolog.ReaderLoader

open ReaderOperator ReaderSource

/-- A read-time effect may inspect every classified form and update the
operator table before the following term is parsed. -/
abbrev Effect (epsilon : Type) :=
  ReaderSource.Form -> ReaderOperator.Table ->
    Except epsilon ReaderOperator.Table

inductive Error (epsilon : Type) where
  | lexer (error : ReaderLexer.Error)
  | term (error : ReaderTerm.Error)
  | source (error : ReaderSource.Error)
  | effect (error : epsilon)
  | exhaustedInputMeasure

structure Result where
  forms : List ReaderSource.Form
  operators : ReaderOperator.Table

private def loadTokensAux (effect : Effect epsilon) : Nat ->
    ReaderOperator.Table -> List ReaderLexer.Token ->
    List ReaderSource.Form -> Except (Error epsilon) Result
  | 0, _, _, _ => .error .exhaustedInputMeasure
  | _ + 1, operators, [], reversed => .ok {
      forms := reversed.reverse
      operators
    }
  | fuel + 1, operators, tokens, reversed => do
      let parsed <- (ReaderTerm.parseOne operators tokens).mapError .term
      let form <- (ReaderSource.classify parsed.term).mapError .source
      let nextOperators <- (effect form operators).mapError .effect
      loadTokensAux effect fuel nextOperators parsed.remaining
        (form :: reversed)

/-- Read all terms from one token stream, applying effects strictly between
the completed current form and parsing the next form. -/
def loadTokensWith (effect : Effect epsilon) (operators : ReaderOperator.Table)
    (tokens : List ReaderLexer.Token) : Except (Error epsilon) Result :=
  loadTokensAux effect (tokens.length + 1) operators tokens []

/-- Lex and sequentially load one complete source buffer. -/
def loadSourceWith (effect : Effect epsilon)
    (operators : ReaderOperator.Table) (source : String) :
    Except (Error epsilon) Result :=
  match ReaderLexer.scan source with
  | .error error => .error (.lexer error)
  | .ok tokens => loadTokensWith effect operators tokens

/-- A profile that deliberately performs no read-time effects. -/
def noEffect : Effect Unit := fun _ operators => .ok operators

@[simp]
theorem loadTokensWith_empty (effect : Effect epsilon)
    (operators : ReaderOperator.Table) :
    loadTokensWith effect operators [] = .ok {
      forms := []
      operators
    } := rfl

end Mettapedia.Logic.Prolog.ReaderLoader
