import Mettapedia.Logic.Prolog.ReaderUnitClosure

namespace Mettapedia.Logic.Prolog.ReaderUnitClosureRegression

open ReaderOperator ReaderUnit ReaderUnitClosure SourceSignature

private def emptyImports : ReaderDirective.ImportProfile _root_.Unit :=
  fun _ => .ok []

private def effect := ReaderDirective.effectWith emptyImports

private def atomName? : SourceSignature.Term -> Option String
  | .const (.atom name) => some name
  | _ => none

private def rootSource : String :=
  ":- use_module(dep, [helper/1]).\n\
   :- use_module(system).\n\
   :- set_prolog_flag(unknown, true).\n\
   main(X) :- helper(X)."

private def dependencySource : String :=
  ":- use_module(root).\n\
   :- initialization(prepare).\n\
   helper(a)."

private def resolver : Resolver String _root_.Unit := fun request =>
  match atomName? request.source with
  | some "dep" => .ok [.source "dep" dependencySource]
  | some "root" => .ok [.source "root" rootSource]
  | some "system" => .ok [.external "system"]
  | _ => .error ()

private def clauseNames (program : SourceSignature.Program) : List String :=
  program.map fun value => value.head.symbol.name

/-- Cyclic source requests are visited once, import options reach the resolver,
the external dependency remains explicit, and loader goals survive linking. -/
def finiteCycleAndObligationsAreRetained : Bool :=
  match loadWith 8 effect defaults resolver "root" rootSource with
  | .error _ => false
  | .ok closure =>
      match linkDisjoint closure with
      | .error _ => false
      | .ok linked =>
          closure.units.length == 2 &&
            closure.external.length == 1 &&
            clauseNames linked.program == ["main", "helper"] &&
            linked.pendingGoals.length == 2 &&
            match closure.units with
            | root :: _ =>
                match root.unit.imports with
                | selected :: _ => selected.options.length == 1
                | _ => false
            | _ => false

#guard finiteCycleAndObligationsAreRetained

private def collisionRoot : String :=
  ":- use_module(dep_collision). p(a)."

private def collisionResolver : Resolver String _root_.Unit := fun request =>
  match atomName? request.source with
  | some "dep_collision" => .ok [.source "dep_collision" "p(b)."]
  | _ => .error ()

/-- Flattening rejects two source units that define the same predicate,
instead of silently giving module-local predicates one global identity. -/
def moduleCollisionFailsClosed : Bool :=
  match loadWith 4 effect defaults collisionResolver "root" collisionRoot with
  | .error _ => false
  | .ok closure =>
      match linkDisjoint closure with
      | .error (.predicateCollision symbol) =>
          symbol.name == "p" && symbol.arity == 1
      | .ok _ => false

#guard moduleCollisionFailsClosed

/-- Closure fuel is a semantic open boundary: a discovered source cannot be
dropped merely because the caller stopped after reading the root. -/
def insufficientFuelFailsOpen : Bool :=
  match loadWith 1 effect defaults resolver "root" rootSource with
  | .error .exhaustedInputMeasure => true
  | _ => false

#guard insufficientFuelFailsOpen

end Mettapedia.Logic.Prolog.ReaderUnitClosureRegression
