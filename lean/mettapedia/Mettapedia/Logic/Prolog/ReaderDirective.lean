import Mettapedia.Logic.Prolog.ReaderLoader

/-!
# Read-time directive effects

SWI executes directives between `read_term` calls. Only effects that change
the reader environment belong here: local `op/3`, operators exported by a
`module/2` declaration, and operators imported by `use_module`/`autoload`/
`ensure_loaded`. All other directive behavior remains the runtime loader's
responsibility.
-/

namespace Mettapedia.Logic.Prolog.ReaderDirective

open ReaderOperator SourceSignature

structure Update where
  priority : Nat
  specifier : ReaderOperator.Specifier
  names : List String
deriving DecidableEq, Repr

/-- Resolve one canonical source-sink term to the operators exported by that
source. A fail-closed profile reports unknown imports instead of silently
assuming that they export no operators. -/
abbrev ImportProfile (rho : Type) :=
  SourceSignature.Term -> Except rho (List Update)

inductive Error (rho : Type) where
  | malformedOperatorDirective
  | operator (error : ReaderOperator.Error)
  | import (error : rho)

private def application? : SourceSignature.Term ->
    Option (String × List SourceSignature.Term)
  | .const (.atom name) => some (name, [])
  | .app indicator arguments => some (indicator.name, List.ofFn arguments)
  | _ => none

private def atomName? : SourceSignature.Term -> Option String
  | .const (.atom name) => some name
  | _ => none

private def properListAux : Nat -> SourceSignature.Term ->
    Option (List SourceSignature.Term)
  | 0, _ => none
  | _ + 1, .const (.atom "[]") => some []
  | fuel + 1, term =>
      match application? term with
      | some ("[|]", [head, tail]) => do
          let rest <- properListAux fuel tail
          pure (head :: rest)
      | _ => none

private def properList? (term : SourceSignature.Term) :
    Option (List SourceSignature.Term) :=
  properListAux (term.size + 1) term

private def specifier? : String -> Option ReaderOperator.Specifier
  | "fx" => some .fx
  | "fy" => some .fy
  | "xf" => some .xf
  | "yf" => some .yf
  | "xfx" => some .xfx
  | "xfy" => some .xfy
  | "yfx" => some .yfx
  | _ => none

private def operatorNames? (term : SourceSignature.Term) : Option (List String) :=
  match atomName? term with
  | some name => some [name]
  | none => do
      let terms <- properList? term
      terms.mapM atomName?

private def decodeUpdateArguments
    (arguments : List SourceSignature.Term) : Option Update := do
  let [priorityTerm, specifierTerm, namesTerm] := arguments | none
  let priority <- match priorityTerm with
    | .const (.integer (.ofNat value)) => some value
    | _ => none
  let specifierName <- atomName? specifierTerm
  let specifier <- specifier? specifierName
  let names <- operatorNames? namesTerm
  pure { priority, specifier, names }

private def decodeUpdate? (term : SourceSignature.Term) : Option Update := do
  let (name, arguments) <- application? term
  if name = "op" then decodeUpdateArguments arguments else none

private def applyUpdate (update : Update) (operators : ReaderOperator.Table) :
    Except (Error rho) ReaderOperator.Table :=
  update.names.foldlM (fun table name =>
    (ReaderOperator.declare update.priority update.specifier name table).mapError
      .operator) operators

private def applyUpdates (updates : List Update)
    (operators : ReaderOperator.Table) :
    Except (Error rho) ReaderOperator.Table :=
  updates.foldlM (fun table update => applyUpdate update table) operators

private def importSources (term : SourceSignature.Term) :
    List SourceSignature.Term :=
  match properList? term with
  | some sources => sources
  | none => [term]

private def applyImports (profile : ImportProfile rho)
    (sourceTerm : SourceSignature.Term) (operators : ReaderOperator.Table) :
    Except (Error rho) ReaderOperator.Table :=
  (importSources sourceTerm).foldlM (fun table source => do
    let updates <- (profile source).mapError .import
    applyUpdates updates table) operators

private def applyExportList (exports : SourceSignature.Term)
    (operators : ReaderOperator.Table) :
    Except (Error rho) ReaderOperator.Table := do
  let entries <- match properList? exports with
    | some entries => pure entries
    | none => .error .malformedOperatorDirective
  entries.foldlM (fun table entry =>
    match application? entry with
    | some ("op", arguments) =>
        match decodeUpdateArguments arguments with
        | some update => applyUpdate update table
        | none => .error .malformedOperatorDirective
    | _ => .ok table) operators

private def applyCall (profile : ImportProfile rho)
    (atom : SourceSignature.Atom) (operators : ReaderOperator.Table) :
    Except (Error rho) ReaderOperator.Table :=
  let arguments := List.ofFn atom.args
  match atom.symbol.name, arguments with
  | "op", arguments =>
      match decodeUpdateArguments arguments with
      | some update => applyUpdate update operators
      | none => .error .malformedOperatorDirective
  | "module", [_moduleName, exports] => applyExportList exports operators
  | "use_module", source :: _ => applyImports profile source operators
  | "autoload", source :: _ => applyImports profile source operators
  | "ensure_loaded", [source] => applyImports profile source operators
  | _, _ => .ok operators

private def applyGoal (profile : ImportProfile rho) :
    SourceSignature.Goal -> ReaderOperator.Table ->
      Except (Error rho) ReaderOperator.Table
  | .call atom, operators => applyCall profile atom operators
  | .conj left right, operators => do
      let afterLeft <- applyGoal profile left operators
      applyGoal profile right afterLeft
  | _, operators => .ok operators

/-- Reader effect that applies only read-time operator consequences. The
directive itself remains in the returned source-form list for ordinary runtime
execution. -/
def effectWith (profile : ImportProfile rho) :
    ReaderLoader.Effect (Error rho) :=
  fun form operators =>
    match form with
    | .directive goal => applyGoal profile goal operators
    | _ => .ok operators

end Mettapedia.Logic.Prolog.ReaderDirective
