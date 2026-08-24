import Mettapedia.Logic.Prolog.ReaderModuleLink
import Mettapedia.Logic.Prolog.ReaderSWIProfile
import Mettapedia.Logic.Prolog.SourceRuntimeRegression

/-!
# Owned finite list library

This is newly authored Prolog source for the small, relational list core used
by the pinned PeTTa sources.  It is parsed, module-linked, and executed by the
canonical shared runtime; this file introduces neither a list evaluator nor a
new dispatch action.  The present scope is finite proper lists.
-/

namespace Mettapedia.Logic.Prolog.OwnedLists

open ReaderModuleLink ReaderUnitClosure SourceSignature

/-- The first owned replacement slice for `library(lists)`.  The definitions
are deliberately ordinary source clauses, retaining Prolog's source order and
backtracking behavior. -/
def source : String :=
  ":- module(lists, [append/3, member/2, reverse/2, select/3, last/2]).\n\
   append([], Rest, Rest).\n\
   append([Head|Tail], Rest, [Head|Joined]) :- append(Tail, Rest, Joined).\n\
   member(Element, [Element|_]).\n\
   member(Element, [_|Tail]) :- member(Element, Tail).\n\
   reverse(List, Reversed) :- reverse_(List, [], Reversed).\n\
   reverse_([], Accumulator, Accumulator).\n\
   reverse_([Head|Tail], Accumulator, Reversed) :- \
     reverse_(Tail, [Head|Accumulator], Reversed).\n\
   select(Element, [Element|Tail], Tail).\n\
   select(Element, [Head|Tail], [Head|Rest]) :- select(Element, Tail, Rest).\n\
   last([Element], Element).\n\
   last([_|Tail], Element) :- last(Tail, Element)."

private def sourceKey? : SourceSignature.Term → Option String :=
  ReaderSWIProfile.sourceKey?

private def emptyImports : ReaderDirective.ImportProfile Unit := fun _ => .ok []

private def resolver : ReaderUnitClosure.Resolver String Unit := fun request =>
  match sourceKey? request.source with
  | some "library(lists)" => .ok [.source "library(lists)" source]
  | _ => .error ()

private def rootSource : String :=
  ":- use_module(library(lists)).\n\
   joined(Result) :- append([a], [b,c], Result).\n\
   member_result(Element) :- member(Element, [a,b,c]).\n\
   reversed(Result) :- reverse([a,b,c], Result).\n\
   selected(Element) :- select(Element, [a,b], _).\n\
   final(Element) :- last([a,b,c], Element)."

private def closure? : Option (ReaderUnitClosure.Closure String) :=
  match ReaderUnitClosure.loadWith 4
      (ReaderDirective.effectWith emptyImports) ReaderOperator.defaults
      resolver "root" rootSource with
  | .ok closure => some closure
  | .error _ => none

private def linked? : Option (ReaderUnitClosure.FlatLink String) := do
  let closure ← closure?
  match ReaderModuleLink.link sourceKey? closure with
  | .ok linked => some linked
  | .error _ => none

private def x : SourceSignature.Variable := { spelling := "X", occurrence := 0 }

private def goal (name : String) : SourceSignature.Goal :=
  SourceSignature.call name [.var x]

/-- The owned module is a closed source dependency: no source unit or export
is borrowed from an external library. -/
def selfContained : Bool :=
  linked?.map (fun linked => linked.external.isEmpty) == some true

/-- `append/3` is relational source code, not an engine service, and produces
the exact source-order finite list result. -/
def appendExecutes : Bool :=
  linked?.bind (fun linked =>
    SourceRuntimeRegression.runAtomBagsFor linked.program (goal "joined") x) ==
    some ([["a", "b", "c"]], 0, 0)

/-- `member/2` retains ordinary left-to-right DFS answer order. -/
def memberOrder : Bool :=
  linked?.bind (fun linked =>
    SourceRuntimeRegression.runAtomsFor linked.program (goal "member_result") x) ==
    some (["a", "b", "c"], 0, 0)

/-- Tail-recursive `reverse/2` uses only ordinary clause entry and unification. -/
def reverseExecutes : Bool :=
  linked?.bind (fun linked =>
    SourceRuntimeRegression.runAtomBagsFor linked.program (goal "reversed") x) ==
    some ([["c", "b", "a"]], 0, 0)

/-- `select/3` exposes both deletion positions in source order. -/
def selectOrder : Bool :=
  linked?.bind (fun linked =>
    SourceRuntimeRegression.runAtomsFor linked.program (goal "selected") x) ==
    some (["a", "b"], 0, 0)

/-- `last/2` is another ordinary recursive clause path, not a host helper. -/
def lastExecutes : Bool :=
  linked?.bind (fun linked =>
    SourceRuntimeRegression.runAtomsFor linked.program (goal "final") x) ==
    some (["c"], 0, 0)

#guard selfContained
#guard appendExecutes
#guard memberOrder
#guard reverseExecutes
#guard selectOrder
#guard lastExecutes

end Mettapedia.Logic.Prolog.OwnedLists
