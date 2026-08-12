import Mettapedia.Logic.Prolog.ReaderSWIProfile
import Mettapedia.Logic.Prolog.ReaderUnit

/-!
Load pinned SWI `library(assoc)` through the canonical conditional source
loader.  This gate proves that the private C fast path is absent and the
portable Prolog arm is selected.  It also checks that all retained `=>` rules
are represented by the executable single-sided clause neck rather than a
synthetic predicate named `=>`. Pinned SWI itself has the private predicate
and takes the other arm; this gate checks source selection in the verified
runtime environment rather than equality of the selected arm.
-/

open Mettapedia.Logic.Prolog

def goalCallsPrivateBtree : SourceSignature.Goal -> Bool
  | .call atom => atom.symbol.name = "$btree_find_node"
  | .conj left right | .disj left right =>
      goalCallsPrivateBtree left || goalCallsPrivateBtree right
  | .ifThenElse condition thenBranch elseBranch
  | .softIfThenElse condition thenBranch elseBranch =>
      goalCallsPrivateBtree condition || goalCallsPrivateBtree thenBranch ||
        goalCallsPrivateBtree elseBranch
  | .once goal | .transaction goal | .neg goal => goalCallsPrivateBtree goal
  | .findall _ generator _ => goalCallsPrivateBtree generator
  | .catch guarded _ recovery =>
      goalCallsPrivateBtree guarded || goalCallsPrivateBtree recovery
  | _ => false

def main (arguments : List String) : IO Unit := do
  let [assocPath] := arguments
    | throw <| IO.userError "usage: pinned_assoc_conditional <assoc.pl>"
  let source <- IO.FS.readFile assocPath
  let unit <- match ReaderUnit.loadConditionalSourceWith
      ReaderSWIProfile.pinnedPeTTaCondition
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults source with
    | .ok unit => pure unit
    | .error _ => throw <| IO.userError "conditional source loading failed"
  let names := unit.program.map (fun clause => clause.head.symbol.name)
  let privateCalls := unit.program.countP fun clause =>
    goalCallsPrivateBtree clause.body
  let ssuHeads := unit.program.countP fun clause =>
    clause.neck = .singleSided
  let getAssocHeads := names.count "get_assoc"
  IO.println s!"items={unit.items.length}"
  IO.println s!"clauses={unit.program.length}"
  IO.println s!"directives={unit.directives.length}"
  IO.println s!"pending_goals={unit.pendingGoals.length}"
  IO.println s!"private_btree_calls={privateCalls}"
  IO.println s!"ssu_rules={ssuHeads}"
  IO.println s!"get_assoc_heads={getAssocHeads}"
  if unit.items.length != 110 || unit.program.length != 106 ||
      unit.directives.length != 4 || !unit.pendingGoals.isEmpty ||
      privateCalls != 0 || ssuHeads != 18 || getAssocHeads != 10 then
    throw <| IO.userError "pinned assoc shape changed"
