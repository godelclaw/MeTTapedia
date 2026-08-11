import Mettapedia.Logic.Prolog.ReaderDirective
import Mettapedia.Logic.Prolog.ReaderDCG

/-!
# Prolog source units on the canonical representation

`ReaderLoader` preserves directives because reading a Prolog file is not the
same operation as extracting a list of clauses.  This module classifies those
directives without introducing another term, goal, clause, or evaluator:
every payload remains a `SourceSignature.Term`, `SourceSignature.Goal`, or
`SourceSignature.Clause` consumed by the shared `Logic.LP`/`Logic.Prolog`
runtime.

Source order is retained explicitly.  Queries and malformed recognized loader
directives fail closed.  Declarations and load-time goals remain visible until
a loader with the corresponding semantics executes them.
-/

namespace Mettapedia.Logic.Prolog.ReaderUnit

open ReaderSource SourceSignature

/-- The source-loading behavior named by an import directive. -/
inductive ImportKind where
  | useModule
  | autoload
  | ensureLoaded
  | reexport
deriving DecidableEq, Repr

/-- One import request.  `options` retains an import selector or other
directive arguments verbatim; the source resolver is not allowed to erase it.
-/
structure Import where
  kind : ImportKind
  source : SourceSignature.Term
  options : List SourceSignature.Term

/-- One module declaration, still expressed using canonical source terms.
The export list is retained verbatim because operators and predicate exports
have different loader consequences. -/
structure ModuleDecl where
  name : SourceSignature.Term
  exports : SourceSignature.Term

/-- Loader-visible source directives.  Unknown directives are not discarded:
they remain explicit load-time goals. -/
inductive Directive where
  | moduleDecl (value : ModuleDecl)
  | import (value : Import)
  | declaration (goal : SourceSignature.Goal)
  | initialization (goal : SourceSignature.Goal)
  | loadGoal (goal : SourceSignature.Goal)

/-- One source-ordered unit item after DCG expansion. -/
inductive Item where
  | clause (value : SourceSignature.Clause)
  | directive (value : Directive)

/-- A loaded source unit.  `items` is the source-order authority; the program
and directive views below are projections rather than stored copies. -/
structure Unit where
  items : List Item
  operators : ReaderOperator.Table

inductive Error (epsilon : Type) where
  | reader (error : ReaderLoader.Error epsilon)
  | query (position : Nat)
  | dcg (position : Nat) (error : ReaderDCG.Error)
  | malformedDirective (position : Nat) (name : String)

private def arguments (atom : SourceSignature.Atom) :
    List SourceSignature.Term :=
  List.ofFn atom.args

private def declarationName : String -> Bool
  | "dynamic" | "multifile" | "discontiguous" | "public"
  | "meta_predicate" | "module_transparent" | "thread_local"
  | "volatile" | "table" => true
  | _ => false

private def directiveOfGoal (position : Nat) : SourceSignature.Goal ->
    Except (Error epsilon) Directive
  | goal@(.call atom) =>
      match atom.symbol.name, arguments atom with
      | "module", [name, exports] =>
          .ok (.moduleDecl { name, exports })
      | "module", _ => .error (.malformedDirective position "module")
      | "use_module", [source] =>
          .ok (.import { kind := .useModule, source, options := [] })
      | "use_module", [source, selection] =>
          .ok (.import { kind := .useModule, source, options := [selection] })
      | "use_module", _ =>
          .error (.malformedDirective position "use_module")
      | "autoload", [source] =>
          .ok (.import { kind := .autoload, source, options := [] })
      | "autoload", [source, selection] =>
          .ok (.import { kind := .autoload, source, options := [selection] })
      | "autoload", _ =>
          .error (.malformedDirective position "autoload")
      | "ensure_loaded", [source] =>
          .ok (.import { kind := .ensureLoaded, source, options := [] })
      | "ensure_loaded", _ =>
          .error (.malformedDirective position "ensure_loaded")
      | "reexport", [source] =>
          .ok (.import { kind := .reexport, source, options := [] })
      | "reexport", [source, selection] =>
          .ok (.import { kind := .reexport, source, options := [selection] })
      | "reexport", _ =>
          .error (.malformedDirective position "reexport")
      | "initialization", [_] | "initialization", [_, _] =>
          .ok (.initialization goal)
      | "initialization", _ =>
          .error (.malformedDirective position "initialization")
      | name, _ =>
          if declarationName name then .ok (.declaration goal)
          else .ok (.loadGoal goal)
  | goal => .ok (.loadGoal goal)

private def itemsAux : Nat -> List ReaderSource.Form ->
    Except (Error epsilon) (List Item)
  | _, [] => .ok []
  | position, .clause clause :: rest => do
      let tail <- itemsAux (position + 1) rest
      pure (.clause clause :: tail)
  | position, .dcg head body :: rest => do
      let clause <- (ReaderDCG.expand head body).mapError (.dcg position)
      let tail <- itemsAux (position + 1) rest
      pure (.clause clause :: tail)
  | position, .directive goal :: rest => do
      let directive <- directiveOfGoal position goal
      let tail <- itemsAux (position + 1) rest
      pure (.directive directive :: tail)
  | position, .query _ :: _ => .error (.query position)

/-- Classify a sequential reader result as one source unit. -/
def ofLoaded (loaded : ReaderLoader.Result) : Except (Error epsilon) Unit := do
  let items <- itemsAux 0 loaded.forms
  pure { items, operators := loaded.operators }

/-- Read and classify one complete source unit.  Read-time effects and loader
directives remain separate responsibilities. -/
def loadSourceWith (effect : ReaderLoader.Effect epsilon)
    (operators : ReaderOperator.Table) (source : String) :
    Except (Error epsilon) Unit := do
  let loaded <- (ReaderLoader.loadSourceWith effect operators source).mapError
    .reader
  ofLoaded loaded

namespace Item

def clause? : Item -> Option SourceSignature.Clause
  | Item.clause value => some value
  | Item.directive _ => none

def directive? : Item -> Option Directive
  | Item.clause _ => none
  | Item.directive value => some value

end Item

namespace Unit

/-- Canonical clauses in source order, including expanded DCG rules. -/
def program (unit : Unit) : SourceSignature.Program :=
  unit.items.filterMap Item.clause?

/-- Loader obligations in source order. -/
def directives (unit : Unit) : List Directive :=
  unit.items.filterMap Item.directive?

def imports (unit : Unit) : List Import :=
  unit.directives.filterMap fun
    | .import request => some request
    | _ => none

def moduleDecls (unit : Unit) : List ModuleDecl :=
  unit.directives.filterMap fun
    | .moduleDecl declaration => some declaration
    | _ => none

def pendingGoals (unit : Unit) : List SourceSignature.Goal :=
  unit.directives.filterMap fun
    | .initialization goal | .loadGoal goal => some goal
    | _ => none

def declarations (unit : Unit) : List SourceSignature.Goal :=
  unit.directives.filterMap fun
    | .declaration goal => some goal
    | _ => none

end Unit

private theorem itemsAux_clause_map (position : Nat)
    (clauses : SourceSignature.Program) :
    itemsAux (epsilon := epsilon) position
        (clauses.map ReaderSource.Form.clause) =
      .ok (clauses.map Item.clause) := by
  induction clauses generalizing position with
  | nil => rfl
  | cons clause rest inductionHypothesis =>
      simp only [List.map_cons, itemsAux]
      rw [inductionHypothesis (position + 1)]
      rfl

@[simp]
theorem ofLoaded_clause_map (clauses : SourceSignature.Program)
    (operators : ReaderOperator.Table) :
    ofLoaded (epsilon := epsilon) {
      forms := clauses.map ReaderSource.Form.clause
      operators
    } = .ok {
      items := clauses.map Item.clause
      operators
    } := by
  simp only [ofLoaded]
  rw [itemsAux_clause_map 0 clauses]
  rfl

end Mettapedia.Logic.Prolog.ReaderUnit
