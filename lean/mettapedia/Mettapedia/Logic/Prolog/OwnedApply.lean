import Mettapedia.Logic.Prolog.ReaderModuleLink
import Mettapedia.Logic.Prolog.ReaderSWIProfile
import Mettapedia.Logic.Prolog.SourceRuntimeRegression

/-!
# Owned finite apply library

The finite `include/3`, `exclude/3`, and `foldl/4` slice required by the
pinned PeTTa sources is ordinary owned Prolog.  The only meta-operation is
the shared runtime's existing `call/N`; this file does not define an evaluator
or a dispatch action.
-/

namespace Mettapedia.Logic.Prolog.OwnedApply

open ReaderModuleLink ReaderUnitClosure SourceSignature

/-- Newly authored source replacement for the finite proper-list `apply`
operations used by PeTTa. -/
def source : String :=
  ":- module(apply, [include/3, exclude/3, foldl/4]).\n\
   include(_, [], []).\n\
   include(Goal, [Element|Tail], [Element|Included]) :- call(Goal, Element), !, \
   include(Goal, Tail, Included).\n\
   include(Goal, [_|Tail], Included) :- include(Goal, Tail, Included).\n\
   exclude(_, [], []).\n\
   exclude(Goal, [Element|Tail], Excluded) :- call(Goal, Element), !, \
   exclude(Goal, Tail, Excluded).\n\
   exclude(Goal, [Element|Tail], [Element|Excluded]) :- \
   exclude(Goal, Tail, Excluded).\n\
   foldl(_, [], Value, Value).\n\
   foldl(Goal, [Element|Tail], Before, After) :- call(Goal, Element, Before, Next), \
   foldl(Goal, Tail, Next, After)."

private def sourceKey? : SourceSignature.Term → Option String :=
  ReaderSWIProfile.sourceKey?

private def emptyImports : ReaderDirective.ImportProfile Unit := fun _ => .ok []

private def resolver : ReaderUnitClosure.Resolver String Unit := fun request =>
  match sourceKey? request.source with
  | some "library(apply)" => .ok [.source "library(apply)" source]
  | _ => .error ()

private def rootSource : String :=
  ":- use_module(library(apply)).\n\
   keep(a).\n\
   keep(c).\n\
   remove(b).\n\
   add(Element, Before, After) :- After is Before + Element.\n\
   included(Result) :- include(keep, [a,b,c], Result).\n\
   excluded(Result) :- exclude(remove, [a,b,c], Result).\n\
   summed(Result) :- foldl(add, [2,3,4], 0, Result)."

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

/-- Ordered finite list answers from the owned `apply` source, for direct SWI
differential rendering on the shared runtime. -/
def atomBagsFor (name : String) : Option (List (List String) × Nat × Nat) :=
  linked?.bind fun linked =>
    SourceRuntimeRegression.runAtomBagsFor linked.program (goal name) x

/-- Ordered finite integer answers from the owned `apply` source. -/
def integersFor (name : String) : Option (List Int × Nat × Nat) :=
  linked?.bind fun linked =>
    SourceRuntimeRegression.runIntegersFor linked.program (goal name) x

/-- The small owned module is a closed source dependency. -/
def selfContained : Bool :=
  linked?.map (fun linked => linked.external.isEmpty) == some true

/-- `include/3` applies its closure left-to-right and keeps matching values. -/
def includeExecutes : Bool :=
  atomBagsFor "included" ==
    some ([["a", "c"]], 0, 0)

/-- `exclude/3` discards exactly the matching values. -/
def excludeExecutes : Bool :=
  atomBagsFor "excluded" ==
    some ([["a", "c"]], 0, 0)

/-- `foldl/4` reaches the same engine-owned `call/N` and integer arithmetic
transitions on every input element. -/
def foldlExecutes : Bool :=
  integersFor "summed" ==
    some ([9], 0, 0)

#guard selfContained
#guard includeExecutes
#guard excludeExecutes
#guard foldlExecutes

end Mettapedia.Logic.Prolog.OwnedApply
