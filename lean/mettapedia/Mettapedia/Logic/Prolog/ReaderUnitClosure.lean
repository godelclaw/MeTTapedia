import Mettapedia.Logic.Prolog.ReaderUnit

/-!
# Finite source-unit dependency closure

This module discovers imported Prolog source units without adding a resolver or
module evaluator.  A caller supplies a pure import resolver.  Resolved source
buffers are read through `ReaderUnit`; unresolved host/library dependencies
remain explicit.

`linkDisjoint` is deliberately weaker than SWI module linking.  It only forms a
flat canonical program when different source units define disjoint predicate
indicators.  Import selectors, private visibility, declarations,
initializations, and external dependencies remain recorded, so this result is
not an execution-readiness certificate.
-/

namespace Mettapedia.Logic.Prolog.ReaderUnitClosure

open ReaderUnit SourceSignature

/-- Resolution of one import request either supplies another source unit or
records an explicit dependency on an external facility. -/
inductive Dependency (key : Type) where
  | source (key : key) (source : String)
  | external (key : key)

/-- Import resolution sees the complete request, including selection options.
It may expand a list-valued source into multiple dependencies. -/
abbrev Resolver (key rho : Type) :=
  ReaderUnit.Import -> Except rho (List (Dependency key))

structure NamedUnit (key : Type) where
  key : key
  unit : ReaderUnit.Unit

structure External (key : Type) where
  key : key
  request : ReaderUnit.Import

/-- A finite discovered closure in deterministic work-list order. -/
structure Closure (key : Type) where
  units : List (NamedUnit key)
  external : List (External key)

inductive Error (key epsilon rho : Type) where
  | source (key : key) (error : ReaderUnit.Error epsilon)
  | resolve (request : ReaderUnit.Import) (error : rho)
  | exhaustedInputMeasure

private structure Pending (key : Type) where
  key : key
  source : String

private structure State (key : Type) where
  pending : List (Pending key)
  seen : List key
  reversedUnits : List (NamedUnit key)
  reversedExternal : List (External key)

private def resolveImport (resolver : Resolver key rho)
    (request : ReaderUnit.Import) :
    Except (Error key epsilon rho)
      (List (Pending key) × List (External key)) := do
  let dependencies <- (resolver request).mapError (.resolve request)
  pure (dependencies.foldl (fun (sources, external) dependency =>
    match dependency with
    | .source key source => (sources ++ [{ key, source }], external)
    | .external key => (sources, external ++ [{ key, request }])) ([], []))

private def resolveImports (resolver : Resolver key rho) :
    List ReaderUnit.Import ->
      Except (Error key epsilon rho)
        (List (Pending key) × List (External key))
  | [] => .ok ([], [])
  | request :: rest => do
      let (currentSources, currentExternal) <-
        resolveImport (epsilon := epsilon) resolver request
      let (laterSources, laterExternal) <- resolveImports resolver rest
      pure (currentSources ++ laterSources, currentExternal ++ laterExternal)

private def loop [DecidableEq key]
    (effect : ReaderLoader.Effect epsilon)
    (operators : ReaderOperator.Table) (resolver : Resolver key rho) :
    Nat -> State key -> Except (Error key epsilon rho) (Closure key)
  | _, { pending := [], reversedUnits, reversedExternal, .. } => .ok {
      units := reversedUnits.reverse
      external := reversedExternal.reverse
    }
  | 0, { pending := _ :: _, .. } => .error .exhaustedInputMeasure
  | fuel + 1, state@{ pending := next :: rest, .. } =>
      if next.key ∈ state.seen then
        loop effect operators resolver fuel { state with pending := rest }
      else do
        let unit <- (ReaderUnit.loadSourceWith effect operators next.source).mapError
          (.source next.key)
        let (sources, external) <-
          resolveImports (epsilon := epsilon) resolver unit.imports
        loop effect operators resolver fuel {
          pending := rest ++ sources
          seen := next.key :: state.seen
          reversedUnits := { key := next.key, unit } :: state.reversedUnits
          reversedExternal := external.reverse ++ state.reversedExternal
        }

/-- Discover one finite dependency closure.  Fuel counts work-list entries,
including repeated cyclic requests; exhaustion is explicit rather than a
partial host computation. -/
def loadWith [DecidableEq key]
    (fuel : Nat) (effect : ReaderLoader.Effect epsilon)
    (operators : ReaderOperator.Table) (resolver : Resolver key rho)
    (rootKey : key) (rootSource : String) :
    Except (Error key epsilon rho) (Closure key) :=
  loop effect operators resolver fuel {
    pending := [{ key := rootKey, source := rootSource }]
    seen := []
    reversedUnits := []
    reversedExternal := []
  }

def definedSymbols (program : SourceSignature.Program) :
    List SourceSignature.PredicateIndicator :=
  (program.map fun value => value.head.symbol).eraseDups

def firstOverlap (left right : List SourceSignature.PredicateIndicator) :
    Option SourceSignature.PredicateIndicator :=
  left.find? fun symbol => symbol ∈ right

inductive LinkError where
  | predicateCollision (symbol : SourceSignature.PredicateIndicator)

/-- A collision-free flat union plus every obligation that prevents this
union from being mistaken for complete module execution. -/
structure FlatLink (key : Type) where
  program : SourceSignature.Program
  units : List (NamedUnit key)
  external : List (External key)
  declarations : List (key × SourceSignature.Goal)
  pendingGoals : List (key × SourceSignature.Goal)

private structure LinkState (key : Type) where
  program : SourceSignature.Program
  symbols : List SourceSignature.PredicateIndicator
  reversedDeclarations : List (key × SourceSignature.Goal)
  reversedPendingGoals : List (key × SourceSignature.Goal)

private def linkAux : List (NamedUnit key) -> LinkState key ->
    Except LinkError (LinkState key)
  | [], state => .ok state
  | named :: rest, state =>
      let nextSymbols := definedSymbols named.unit.program
      match firstOverlap nextSymbols state.symbols with
      | some symbol => .error (.predicateCollision symbol)
      | none =>
          linkAux rest {
            program := state.program ++ named.unit.program
            symbols := state.symbols ++ nextSymbols
            reversedDeclarations :=
              (named.unit.declarations.map fun goal => (named.key, goal)).reverse ++
                state.reversedDeclarations
            reversedPendingGoals :=
              (named.unit.pendingGoals.map fun goal => (named.key, goal)).reverse ++
                state.reversedPendingGoals
          }

/-- Conservatively flatten a closure only when distinct source units do not
define the same predicate indicator.  The result retains all unresolved
loader work and makes no module-equivalence claim. -/
def linkDisjoint (closure : Closure key) : Except LinkError (FlatLink key) := do
  let state <- linkAux closure.units {
    program := []
    symbols := []
    reversedDeclarations := []
    reversedPendingGoals := []
  }
  pure {
    program := state.program
    units := closure.units
    external := closure.external
    declarations := state.reversedDeclarations.reverse
    pendingGoals := state.reversedPendingGoals.reverse
  }

end Mettapedia.Logic.Prolog.ReaderUnitClosure
