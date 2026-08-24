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
  ":- module(lists, [append/2, append/3, member/2, memberchk/2, reverse/2, select/3, last/2, flatten/2, list_to_set/2]).\n\
   append(Lists, Joined) :- append_(Lists, Joined).\n\
   append_([], []).\n\
   append_([List|Lists], Joined) :- append(List, Tail, Joined), append_(Lists, Tail).\n\
   append([], Rest, Rest).\n\
   append([Head|Tail], Rest, [Head|Joined]) :- append(Tail, Rest, Joined).\n\
   member(Element, [Element|_]).\n\
   member(Element, [_|Tail]) :- member(Element, Tail).\n\
   memberchk(Element, List) :- member(Element, List), !.\n\
   reverse(List, Reversed) :- reverse_(List, [], Reversed).\n\
   reverse_([], Accumulator, Accumulator).\n\
   reverse_([Head|Tail], Accumulator, Reversed) :- \
     reverse_(Tail, [Head|Accumulator], Reversed).\n\
   select(Element, [Element|Tail], Tail).\n\
   select(Element, [Head|Tail], [Head|Rest]) :- select(Element, Tail, Rest).\n\
   last([Element], Element).\n\
   last([_|Tail], Element) :- last(Tail, Element).\n\
   flatten(List, Flat) :- flatten_(List, [], Flat), !.\n\
   flatten_([], Tail, Tail).\n\
   flatten_([Head|Tail], FlatTail, Flat) :- !, \
     flatten_(Head, FlatHeadTail, Flat), flatten_(Tail, FlatTail, FlatHeadTail).\n\
   flatten_(Element, Tail, [Element|Tail]).\n\
   list_to_set(List, Set) :- list_to_set_(List, [], Set).\n\
   list_to_set_([], _, []).\n\
   list_to_set_([Head|Tail], Seen, Set) :- member_eq(Head, Seen), !, \
     list_to_set_(Tail, Seen, Set).\n\
   list_to_set_([Head|Tail], Seen, [Head|Set]) :- \
     list_to_set_(Tail, [Head|Seen], Set).\n\
   member_eq(Element, [Candidate|_]) :- Element == Candidate, !.\n\
   member_eq(Element, [_|Tail]) :- member_eq(Element, Tail)."

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
   concatenated(Result) :- append([[a,b],[c],[]], Result).\n\
   member_result(Element) :- member(Element, [a,b,c]).\n\
   member_checked(Element) :- memberchk(Element, [a,b,a]).\n\
   reversed(Result) :- reverse([a,b,c], Result).\n\
   selected(Element) :- select(Element, [a,b], _).\n\
   final(Element) :- last([a,b,c], Element).\n\
   flattened(Result) :- flatten([a,[b,[c]],[]], Result).\n\
   unique(Result) :- list_to_set([b,a,b,c,a], Result)."

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

/-- Finite `append/2` joins a proper list of proper lists.  This is the
concrete list operation used by `dcg/basics:number//1`. -/
def appendTwoExecutes : Bool :=
  linked?.bind (fun linked =>
    SourceRuntimeRegression.runAtomBagsFor linked.program (goal "concatenated") x) ==
    some ([["a", "b", "c"]], 0, 0)

/-- `member/2` retains ordinary left-to-right DFS answer order. -/
def memberOrder : Bool :=
  linked?.bind (fun linked =>
    SourceRuntimeRegression.runAtomsFor linked.program (goal "member_result") x) ==
    some (["a", "b", "c"], 0, 0)

/-- `memberchk/2` consumes the source `member/2` alternatives through the
ordinary predicate cut: it exposes only the first matching occurrence. -/
def memberchkExecutes : Bool :=
  linked?.bind (fun linked =>
    SourceRuntimeRegression.runAtomsFor linked.program (goal "member_checked") x) ==
    some (["a"], 0, 0)

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

/-- `flatten/2` is owned source code for the finite proper-list nesting that
the translator uses when it assembles its goal prefixes.  Its outer cut makes
the finite result deterministic, matching the source-library contract. -/
def flattenExecutes : Bool :=
  linked?.bind (fun linked =>
    SourceRuntimeRegression.runAtomBagsFor linked.program (goal "flattened") x) ==
    some ([["a", "b", "c"]], 0, 0)

/-- The owned finite `list_to_set/2` uses strict identity and a source cut to
keep first occurrences in input order.  It deliberately exercises the same
shared hard-frame/cut machinery as the rest of the library. -/
def listToSetExecutes : Bool :=
  linked?.bind (fun linked =>
    SourceRuntimeRegression.runAtomBagsFor linked.program (goal "unique") x) ==
    some ([["b", "a", "c"]], 0, 0)

#guard selfContained
#guard appendExecutes
#guard appendTwoExecutes
#guard memberOrder
#guard memberchkExecutes
#guard reverseExecutes
#guard selectOrder
#guard lastExecutes
#guard flattenExecutes
#guard listToSetExecutes

end Mettapedia.Logic.Prolog.OwnedLists
