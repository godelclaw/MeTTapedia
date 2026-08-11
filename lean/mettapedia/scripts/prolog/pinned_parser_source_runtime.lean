import Mettapedia.Logic.Prolog.ReaderSWIProfile
import Mettapedia.Logic.Prolog.ReaderUnitClosure
import Mettapedia.Logic.Prolog.SourceRuntime
import Mettapedia.Logic.Prolog.SourceRuntimeRegression
import Mettapedia.Logic.LP.RuntimeReadback

/-!
Execute real pinned `parser.pl` DCG clauses through the canonical shared
runtime.  The loaded source slice retains unresolved loader obligations; this
canary claims only the exercised `swrite_exp([])` and `swrite_exp([a])` paths.
-/

open Mettapedia.Logic
open Mettapedia.Logic.Prolog

def resolver (dcgBasicsSource listsSource errorSource : String) :
    ReaderUnitClosure.Resolver String Unit := fun request =>
  match ReaderSWIProfile.sourceKey? request.source with
  | some "library(dcg/basics)" =>
      .ok [.source "library(dcg/basics)" dcgBasicsSource]
  | some "library(lists)" => .ok [.source "library(lists)" listsSource]
  | some "library(error)" => .ok [.source "library(error)" errorSource]
  | some key => .ok [.external key]
  | none => .error ()

def loadProgram (parserSource dcgBasicsSource listsSource errorSource : String) :
    IO SourceSignature.Program := do
  let closure <- match ReaderUnitClosure.loadWith 32
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults
      (resolver dcgBasicsSource listsSource errorSource) "parser" parserSource with
    | .ok closure => pure closure
    | .error _ => throw <| IO.userError "source-unit closure failed"
  let linked <- match ReaderUnitClosure.linkDisjoint closure with
    | .ok linked => pure linked
    | .error _ => throw <| IO.userError "source-unit predicates collided"
  if linked.program.length != 297 ||
      closure.external.map (·.key) != ["library(pairs)", "library(debug)"] ||
      linked.declarations.length != 4 || linked.pendingGoals.length != 3 then
    throw <| IO.userError "source-unit boundary changed"
  pure linked.program

def codesIdentity : SourceSignature.Variable := {
  spelling := "Codes"
  occurrence := 0
}

def query : SourceSignature.Goal :=
  SourceSignature.call "phrase" [
    SourceSignature.compound "swrite_exp" [SourceSignature.nil],
    .var codesIdentity,
    SourceSignature.nil
  ]

def atomListQuery : SourceSignature.Goal :=
  SourceSignature.call "phrase" [
    SourceSignature.compound "swrite_exp" [
      SourceSignature.list [SourceSignature.atom "a"]
    ],
    .var codesIdentity,
    SourceSignature.nil
  ]

def termIdentity : SourceSignature.Variable := {
  spelling := "Term"
  occurrence := 0
}

def environmentIdentity : SourceSignature.Variable := {
  spelling := "Environment"
  occurrence := 0
}

/-- Exercise the parser in its forward direction on the smallest nonempty
S-expression.  This reaches pinned `dcg/basics:string_without//2`, including
its finite-list `memberchk/2` test, rather than merely exercising PeTTa's
writer DCGs. -/
def readQuery (codes : List Int) : SourceSignature.Goal :=
  SourceSignature.call "phrase" [
    SourceSignature.compound "sexpr" [
      .var termIdentity,
      SourceSignature.nil,
      .var environmentIdentity
    ],
    SourceSignature.list (codes.map SourceSignature.integer),
    SourceSignature.nil
  ]

def readAtomQuery : SourceSignature.Goal :=
  readQuery [40, 97, 41]

def integerListAux : Nat -> LP.Term SourceRuntime.Sigma.scoped ->
    Option (List Int)
  | 0, _ => none
  | _ + 1, .const (.atom "[]") => some []
  | fuel + 1, .app indicator arguments => do
      if indicator.name != "[|]" || indicator.arity != 2 then none else
        let [head, tail] := List.ofFn arguments | none
        let value <- match head with
          | .const (.integer value) => some value
          | _ => none
        let rest <- integerListAux fuel tail
        pure (value :: rest)
  | _ + 1, _ => none

def integerList? (term : LP.Term SourceRuntime.Sigma.scoped) :
    Option (List Int) :=
  integerListAux (term.size + 1) term

def answerCodes? (answer : LP.RuntimeQuery.Answer SourceRuntime.Sigma) :
    Option (List Int) := do
  let (_, address) <- answer.queryVarMap.find? fun entry =>
    decide (entry.1 = LP.ScopedVar.at 0 codesIdentity)
  let term <- match LP.RuntimeReadback.Heap.readTerm answer.memory.heap address with
    | .ok term => some term
    | .error _ => none
  integerList? term

def answerTerm? (answer : LP.RuntimeQuery.Answer SourceRuntime.Sigma) :
    Option (LP.Term SourceRuntime.Sigma.scoped) := do
  let (_, address) <- answer.queryVarMap.find? fun entry =>
    decide (entry.1 = LP.ScopedVar.at 0 termIdentity)
  match LP.RuntimeReadback.Heap.readTerm answer.memory.heap address with
  | .ok term => some term
  | .error _ => none

def renderCodes (values : List Int) : String :=
  "[" ++ String.intercalate "," (values.map toString) ++ "]"

def renderTermAux : Nat -> LP.Term SourceRuntime.Sigma.scoped -> String
  | 0, _ => "..."
  | _ + 1, .var identity =>
      s!"_{identity.scope}_{identity.name.occurrence}"
  | _ + 1, .const (.atom name) => name
  | _ + 1, .const (.integer value) => toString value
  | _ + 1, .const (.floatBits bits) => s!"float({bits})"
  | _ + 1, .const (.string value) => s!"string({value})"
  | _ + 1, .const (.clauseReference reference) => s!"ref({reference})"
  | fuel + 1, .app indicator arguments =>
      let rendered := (List.ofFn arguments).map (renderTermAux fuel)
      indicator.name ++ "(" ++ String.intercalate "," rendered ++ ")"

def renderTerm (term : LP.Term SourceRuntime.Sigma.scoped) : String :=
  renderTermAux (term.size + 1) term

def execute (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) : IO (List Int × Nat × Nat) := do
  let session <- match SourceRuntime.openEmpty program goal with
    | .ok session => pure session
    | .error _ => throw <| IO.userError "runtime failed to open"
  let (codes, resumed) <- match SourceRuntime.pullSession 8192 session with
    | .answer answer resumed =>
        match answerCodes? answer with
        | some codes => pure (codes, resumed)
        | none => throw <| IO.userError "answer readback failed"
    | .open _ => throw <| IO.userError "runtime remained open"
    | .terminal (.completed _) _ =>
        throw <| IO.userError "runtime completed without an answer"
    | .terminal (.runtimeError error _) _ =>
        throw <| IO.userError s!"runtime error: {repr error}"
    | .terminal (.raised packet _) _ =>
        throw <| IO.userError s!"runtime raised: {renderTerm packet.term}"
  match SourceRuntime.pullSession 8192 resumed with
  | .terminal (.completed memory) _ =>
      pure (codes, memory.heap.size, memory.trail.size)
  | .answer _ _ => throw <| IO.userError "runtime produced an extra answer"
  | .open _ => throw <| IO.userError "runtime remained open after answer"
  | .terminal _ _ => throw <| IO.userError "runtime did not complete"

def executeTerm (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) :
    IO (LP.Term SourceRuntime.Sigma.scoped × Nat × Nat) := do
  let session <- match SourceRuntime.openEmpty program goal with
    | .ok session => pure session
    | .error _ => throw <| IO.userError "runtime failed to open"
  let (term, resumed) <- match SourceRuntime.pullSession 32768 session with
    | .answer answer resumed =>
        match answerTerm? answer with
        | some term => pure (term, resumed)
        | none => throw <| IO.userError "term answer readback failed"
    | .open _ => throw <| IO.userError "runtime remained open"
    | .terminal (.completed _) _ =>
        throw <| IO.userError "runtime completed without a term answer"
    | .terminal (.runtimeError error _) _ =>
        throw <| IO.userError s!"runtime error: {repr error}"
    | .terminal (.raised packet _) _ =>
        throw <| IO.userError s!"runtime raised: {renderTerm packet.term}"
  match SourceRuntime.pullSession 32768 resumed with
  | .terminal (.completed memory) _ =>
      pure (term, memory.heap.size, memory.trail.size)
  | .answer _ _ => throw <| IO.userError "runtime produced an extra term answer"
  | .open _ => throw <| IO.userError "runtime remained open after term answer"
  | .terminal _ _ => throw <| IO.userError "runtime term query did not complete"

def checkRead (program : SourceSignature.Program) (label : String)
    (codes : List Int) (expected : SourceSignature.Term) : IO Unit := do
  let (actual, heapSize, trailSize) ← executeTerm program (readQuery codes)
  if SourceRuntimeRegression.runtimeTermShape actual ==
      SourceRuntimeRegression.runtimeTermShape (LP.Term.atScope 0 expected) then
    pure ()
  else
    throw <| IO.userError s!"{label}: expected {renderTerm (LP.Term.atScope 0 expected)}, got {renderTerm actual}"
  if heapSize != 0 || trailSize != 0 then
    throw <| IO.userError s!"{label}: cleanup left {heapSize}/{trailSize}"
  IO.println s!"{label}=exact"

def main (arguments : List String) : IO Unit := do
  let [parserPath, dcgBasicsPath, listsPath, errorPath] := arguments
    | throw <| IO.userError
        "usage: pinned_parser_source_runtime \
         <parser.pl> <dcg/basics.pl> <lists.pl> <error.pl>"
  let program <- loadProgram
    (← IO.FS.readFile parserPath)
    (← IO.FS.readFile dcgBasicsPath)
    (← IO.FS.readFile listsPath)
    (← IO.FS.readFile errorPath)
  let (emptyCodes, emptyHeap, emptyTrail) <- execute program query
  let (atomListCodes, atomListHeap, atomListTrail) <-
    execute program atomListQuery
  let (readAtom, readAtomHeap, readAtomTrail) <-
    executeTerm program readAtomQuery
  IO.println s!"empty_codes={renderCodes emptyCodes}"
  IO.println s!"empty_cleanup={emptyHeap}/{emptyTrail}"
  IO.println s!"atom_list_codes={renderCodes atomListCodes}"
  IO.println s!"atom_list_cleanup={atomListHeap}/{atomListTrail}"
  IO.println s!"read_atom={renderTerm readAtom}"
  IO.println s!"read_cleanup={readAtomHeap}/{readAtomTrail}"
  checkRead program "read_list" [40, 97, 32, 98, 41]
    (SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"])
  checkRead program "read_string" [40, 34, 97, 34, 41]
    (SourceSignature.list [SourceSignature.string "a"])
  checkRead program "read_nested" [40, 40, 97, 41, 41]
    (SourceSignature.list [SourceSignature.list [SourceSignature.atom "a"]])
