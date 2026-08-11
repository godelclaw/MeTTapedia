import Mettapedia.Logic.Prolog.ReaderSWIProfile
import Mettapedia.Logic.Prolog.ReaderUnitClosure

/-!
Load pinned PeTTa's `parser.pl` and the pinned SWI `library(dcg/basics)` source
through the canonical source-unit loader.  System-library dependencies remain
explicit rather than being silently dropped or replaced by Lean builtins.
-/

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

def printUnit (named : ReaderUnitClosure.NamedUnit String) : IO Unit :=
  IO.println s!"unit:{named.key} clauses={named.unit.program.length} \
imports={named.unit.imports.length} directives={named.unit.directives.length}"

def main (arguments : List String) : IO Unit := do
  let [parserPath, dcgBasicsPath, listsPath, errorPath] := arguments
    | throw <| IO.userError
        "usage: pinned_parser_unit_closure \
         <parser.pl> <dcg/basics.pl> <lists.pl> <error.pl>"
  let parserSource <- IO.FS.readFile parserPath
  let dcgBasicsSource <- IO.FS.readFile dcgBasicsPath
  let listsSource <- IO.FS.readFile listsPath
  let errorSource <- IO.FS.readFile errorPath
  let closure <- match ReaderUnitClosure.loadWith 32
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults
      (resolver dcgBasicsSource listsSource errorSource) "parser" parserSource with
    | .ok closure => pure closure
    | .error _ => throw <| IO.userError "source-unit closure failed"
  let linked <- match ReaderUnitClosure.linkDisjoint closure with
    | .ok linked => pure linked
    | .error _ => throw <| IO.userError "source-unit predicates collided"
  if closure.units.map (·.key) !=
      ["parser", "library(dcg/basics)", "library(lists)", "library(error)"] then
    throw <| IO.userError "unexpected source-unit discovery order"
  if closure.external.map (·.key) != ["library(pairs)", "library(debug)"] then
    throw <| IO.userError "unexpected explicit external dependencies"
  if linked.program.length != 297 then
    throw <| IO.userError s!"unexpected canonical clause count: \
      {linked.program.length}"
  if linked.declarations.length != 4 || linked.pendingGoals.length != 3 then
    throw <| IO.userError s!"unexpected retained loader-obligation count: \
      declarations={linked.declarations.length}, pending={linked.pendingGoals.length}"
  IO.println s!"units={closure.units.length}"
  for named in closure.units do
    printUnit named
  for external in closure.external do
    IO.println s!"external={external.key} options={external.request.options.length}"
  IO.println s!"linked_clauses={linked.program.length}"
  IO.println s!"declarations={linked.declarations.length}"
  IO.println s!"pending_goals={linked.pendingGoals.length}"
