import Mettapedia.Logic.Prolog.ReaderDirective
import Mettapedia.Logic.Prolog.ReaderSWIProfile
import Lean.Data.Json.Printer

/-!
Executable side of the pinned Prolog-reader differential.  This is a test
driver, not another syntax representation used by the runtime: it projects
canonical `Logic.LP.Term` values to JSON solely for external comparison.
-/

open Mettapedia.Logic.Prolog
open Mettapedia.Logic.Prolog.SourceSignature

def termJsonAux : Nat -> SourceSignature.Term -> Lean.Json
  | 0, _ => .null
  | _ + 1, .var identity => .arr #[.str "v", .str identity.spelling,
      .num identity.occurrence]
  | _ + 1, .const (.atom name) => .arr #[.str "a", .str name]
  | _ + 1, .const (.integer value) =>
      .arr #[.str "i", .str (toString value)]
  | _ + 1, .const (.floatBits bits) =>
      .arr #[.str "f", .str (toString bits)]
  | _ + 1, .const (.string value) => .arr #[.str "s", .str value]
  | _ + 1, .const (.clauseReference reference) =>
      .arr #[.str "r", .num reference]
  | fuel + 1, .app indicator arguments =>
      .arr #[.str "c", .str indicator.name,
        .arr ((List.ofFn arguments).map (termJsonAux fuel)).toArray]

def termJson (term : SourceSignature.Term) : Lean.Json :=
  termJsonAux (term.size + 1) term

def emitTermsAux : Nat -> ReaderOperator.Table ->
    List ReaderLexer.Token -> IO Nat
  | 0, _, _ => throw <| IO.userError "reader input measure exhausted"
  | _ + 1, _, [] => pure 0
  | fuel + 1, operators, tokens => do
    let parsed <- match ReaderTerm.parseOne operators tokens with
      | .ok parsed => pure parsed
      | .error _ => throw <| IO.userError "term parse failure"
    IO.println (termJson parsed.term).compress
    let form <- match ReaderSource.classify parsed.term with
      | .ok form => pure form
      | .error _ => throw <| IO.userError "source classification failure"
    let next <- match ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa
        form operators with
      | .ok next => pure next
      | .error _ => throw <| IO.userError "directive profile failure"
    return (← emitTermsAux fuel next parsed.remaining) + 1

def emitTerms (operators : ReaderOperator.Table)
    (tokens : List ReaderLexer.Token) : IO Nat :=
  emitTermsAux (tokens.length + 1) operators tokens

def checkFile (path : String) : IO Nat := do
  let source <- IO.FS.readFile path
  let tokens <- match ReaderLexer.scan source with
    | .ok tokens => pure tokens
    | .error _ => throw <| IO.userError s!"lexer rejected {path}"
  emitTerms ReaderOperator.defaults tokens

def main (arguments : List String) : IO Unit := do
  let counts <- arguments.mapM checkFile
  if counts.sum = 317 then pure ()
  else throw <| IO.userError s!"expected 317 forms, got {counts.sum}"
