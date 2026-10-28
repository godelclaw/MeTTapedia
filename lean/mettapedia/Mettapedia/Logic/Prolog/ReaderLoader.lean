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

/-- One stateful read-time transition.  `retain = false` removes the current
form from the loaded unit after it has been parsed.  This is needed for
source transformations such as conditional compilation, whose directives
and inactive arms do not become runtime loader goals. -/
structure Transition (state : Type) where
  state : state
  operators : ReaderOperator.Table
  retain : Bool

/-- A source processor may carry state across successive `read_term` calls,
update the operator table, and decide whether the current form survives into
the loaded unit.  It cannot manufacture a form or alter a parsed form. -/
abbrev Processor (state epsilon : Type) :=
  ReaderSource.Form -> state -> ReaderOperator.Table ->
    Except epsilon (Transition state)

inductive Error (epsilon : Type) where
  | lexer (error : ReaderLexer.Error)
  | term (error : ReaderTerm.Error)
  | source (error : ReaderSource.Error)
  | effect (error : epsilon)
  | exhaustedInputMeasure

structure Result where
  forms : List ReaderSource.Form
  operators : ReaderOperator.Table

structure StatefulResult (state : Type) extends Result where
  state : state

private def loadTokensStateAux (processor : Processor state epsilon) : Nat ->
    state -> ReaderOperator.Table -> List ReaderLexer.Token ->
    List ReaderSource.Form -> Except (Error epsilon) (StatefulResult state)
  | 0, _, _, _, _ => .error .exhaustedInputMeasure
  | _ + 1, currentState, operators, [], reversed => .ok {
      forms := reversed.reverse
      operators
      state := currentState
    }
  | fuel + 1, currentState, operators, tokens, reversed => do
      let parsed <- (ReaderTerm.parseOne operators tokens).mapError .term
      let form <- (ReaderSource.classify parsed.term).mapError .source
      let next <- (processor form currentState operators).mapError .effect
      loadTokensStateAux processor fuel next.state next.operators
        parsed.remaining (if next.retain then form :: reversed else reversed)

/-- Read a token stream with an explicit stateful source processor. -/
def loadTokensStateWith (processor : Processor state epsilon)
    (initialState : state)
    (operators : ReaderOperator.Table) (tokens : List ReaderLexer.Token) :
    Except (Error epsilon) (StatefulResult state) :=
  loadTokensStateAux processor (tokens.length + 1) initialState operators tokens []

/-- Lex and sequentially load one source buffer with an explicit stateful
source processor. -/
def loadSourceStateWith (processor : Processor state epsilon)
    (initialState : state)
    (operators : ReaderOperator.Table) (source : String) :
    Except (Error epsilon) (StatefulResult state) :=
  match ReaderLexer.scan source with
  | .error error => .error (.lexer error)
  | .ok tokens => loadTokensStateWith processor initialState operators tokens

private def liftEffect (effect : Effect epsilon) : Processor Unit epsilon :=
  fun form _ operators => do
    let nextOperators <- effect form operators
    pure { state := (), operators := nextOperators, retain := true }

/-- Read all terms from one token stream, applying effects strictly between
the completed current form and parsing the next form. -/
def loadTokensWith (effect : Effect epsilon) (operators : ReaderOperator.Table)
    (tokens : List ReaderLexer.Token) : Except (Error epsilon) Result :=
  match loadTokensStateWith (liftEffect effect) () operators tokens with
  | .error error => .error error
  | .ok result => .ok {
      forms := result.forms
      operators := result.operators
    }

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
