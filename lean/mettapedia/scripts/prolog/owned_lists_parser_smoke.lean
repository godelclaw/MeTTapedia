import Mettapedia.Logic.Prolog.OwnedLists
import Mettapedia.Logic.Prolog.ReaderModuleLink
import Mettapedia.Logic.Prolog.ReaderSWIProfile
import Mettapedia.Logic.Prolog.ReaderUnitClosure
import Mettapedia.Logic.Prolog.SourceRuntime

/-!
Run pinned `parser.pl` and `dcg/basics.pl` against the owned finite `lists`
module.  This is an integration smoke gate: no source from `library(lists)` is
read from the host or pinned SWI tree.  Parsing `(1)` reaches
`dcg_basics:number//1`, whose source calls `append/2`.
-/

open Mettapedia.Logic
open Mettapedia.Logic.Prolog

private def resolver (dcgBasicsSource errorSource pairsSource : String) :
    ReaderUnitClosure.Resolver String Unit := fun request =>
  match ReaderSWIProfile.sourceKey? request.source with
  | some "library(dcg/basics)" =>
      .ok [.source "library(dcg/basics)" dcgBasicsSource]
  | some "library(lists)" => .ok [.source "library(lists)" OwnedLists.source]
  | some "library(error)" => .ok [.source "library(error)" errorSource]
  | some "library(pairs)" => .ok [.source "library(pairs)" pairsSource]
  | some key => .ok [.external key]
  | none => .error ()

private def result : SourceSignature.Variable := {
  spelling := "Result"
  occurrence := 0
}

private def environment : SourceSignature.Variable := {
  spelling := "Environment"
  occurrence := 0
}

private def parserNumberGoal : SourceSignature.Goal :=
  .conj
    (SourceSignature.call "phrase" [
      SourceSignature.compound "sexpr" [.var result, SourceSignature.nil, .var environment],
      SourceSignature.list [SourceSignature.integer 40, SourceSignature.integer 49,
        SourceSignature.integer 41],
      SourceSignature.nil])
    (.unify (.var result) (SourceSignature.list [SourceSignature.integer 1]))

private def requireCompletedAnswer (session : SourceRuntime.Session) : IO Unit := do
  match SourceRuntime.pullSession 65536 session with
  | .answer _ resumed =>
      match SourceRuntime.pullSession 65536 resumed with
      | .terminal (.completed memory) _ =>
          if memory.heap.size = 0 && memory.trail.size = 0 then
            IO.println "owned_lists_parser_number=exact"
          else
            throw <| IO.userError s!"owned parser cleanup left \
              {memory.heap.size}/{memory.trail.size}"
      | .answer _ _ => throw <| IO.userError "owned parser produced an extra answer"
      | .open _ => throw <| IO.userError "owned parser remained open after answer"
      | .terminal _ _ => throw <| IO.userError "owned parser did not complete"
  | .open _ => throw <| IO.userError "owned parser remained open"
  | .terminal (.completed _) _ =>
      throw <| IO.userError "owned parser completed without an answer"
  | .terminal (.runtimeError error _) _ =>
      throw <| IO.userError s!"owned parser runtime error: {repr error}"
  | .terminal (.raised _ _) _ => throw <| IO.userError "owned parser raised"

def main (arguments : List String) : IO Unit := do
  let [parserPath, dcgBasicsPath, errorPath, pairsPath] := arguments
    | throw <| IO.userError
        "usage: owned_lists_parser_smoke <parser.pl> <dcg/basics.pl> <error.pl> <pairs.pl>"
  let closure ← match ReaderUnitClosure.loadWith 32
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults
      (resolver (← IO.FS.readFile dcgBasicsPath) (← IO.FS.readFile errorPath)
        (← IO.FS.readFile pairsPath))
      "parser" (← IO.FS.readFile parserPath) with
    | .ok closure => pure closure
    | .error _ => throw <| IO.userError "owned parser source-unit closure failed"
  let linked ← match ReaderUnitClosure.linkDisjoint closure with
    | .ok linked => pure linked
    | .error _ => throw <| IO.userError "owned parser source-unit collision"
  if closure.external.map (·.key) != ["library(debug)"] then
    throw <| IO.userError "owned parser unexpectedly retained a source external"
  if !(linked.program.any fun clause =>
      clause.head.symbol = { name := "append", arity := 2 }) ||
      !(linked.program.any fun clause =>
        clause.head.symbol = { name := "memberchk", arity := 2 }) then
    throw <| IO.userError "owned parser source did not link required list exports"
  let session ← match SourceRuntime.openEmpty linked.program parserNumberGoal with
    | .ok session => pure session
    | .error error => throw <| IO.userError s!"owned parser failed to open: {repr error}"
  requireCompletedAnswer session
