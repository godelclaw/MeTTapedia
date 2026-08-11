import Mettapedia.Logic.Prolog.ReaderModuleLink
import Mettapedia.Logic.Prolog.ReaderSWIProfile

namespace Mettapedia.Logic.Prolog.ReaderModuleLinkRegression

open ReaderModuleLink ReaderUnitClosure SourceSignature

private def emptyImports : ReaderDirective.ImportProfile Unit := fun _ => .ok []

private def rootSource : String :=
  ":- use_module(lib).\n\
   exp(user).\n\
   run(X) :- helper(X).\n\
   auto(X) :- available(X)."

private def librarySource : String :=
  ":- module(lib, [helper/1]).\n\
   :- use_module(other).\n\
   helper(X) :- worker(X).\n\
   worker(lib).\n\
   exp(module)."

private def otherSource : String :=
  ":- module(other, [available/1]).\n\
   available(implicit)."

private def sourceKey? : SourceSignature.Term → Option String
  | .const (.atom name) => some name
  | _ => none

private def resolver : ReaderUnitClosure.Resolver String Unit := fun request =>
  match sourceKey? request.source with
  | some "lib" => .ok [.source "lib" librarySource]
  | some "other" => .ok [.source "other" otherSource]
  | _ => .error ()

private def closure? : Option (ReaderUnitClosure.Closure String) :=
  match ReaderUnitClosure.loadWith 8
      (ReaderDirective.effectWith emptyImports) ReaderOperator.defaults
      resolver "root" rootSource with
  | .ok closure => some closure
  | .error _ => none

private def linked? : Option (ReaderUnitClosure.FlatLink String) := do
  let closure ← closure?
  match ReaderModuleLink.link sourceKey? closure with
  | .ok linked => some linked
  | .error _ => none

def flatLinkRejectsCollision : Bool :=
  match closure? with
  | some closure =>
      match ReaderUnitClosure.linkDisjoint closure with
      | .error (.predicateCollision { name := "exp", arity := 1 }) => true
      | _ => false
  | none => false

/- The old flat linker really does reject the same-name predicates. -/
#guard flatLinkRejectsCollision

def linkedNames : Option (List String) := do
  let linked ← linked?
  pure (linked.program.map fun clause => clause.head.symbol.name)

/- The flat linker rejects the duplicate `exp/1`, while module-aware linking
keeps the user predicate and qualifies every library-local definition. -/
#guard linkedNames == some
  ["exp", "run", "auto", "lib:helper", "lib:worker", "lib:exp",
    "other:available"]

def runTarget : Option String := do
  let linked ← linked?
  let run ← linked.program.find? fun clause => clause.head.symbol.name = "run"
  match run.body with
  | .call atom => some atom.symbol.name
  | _ => none

/- The imported call is rewritten to the exported module predicate. -/
#guard runTarget == some "lib:helper"

def helperTarget : Option String := do
  let linked ← linked?
  let helper ← linked.program.find? fun clause =>
    clause.head.symbol.name = "lib:helper"
  match helper.body with
  | .call atom => some atom.symbol.name
  | _ => none

/- A call to a private predicate in the module resolves locally. -/
#guard helperTarget == some "lib:worker"

def autoTarget : Option String := do
  let linked ← linked?
  let auto ← linked.program.find? fun clause => clause.head.symbol.name = "auto"
  match auto.body with
  | .call atom => some atom.symbol.name
  | _ => none

/- An otherwise unresolved call uses the unique loaded export.  The private
`lib:worker/1` above is deliberately not eligible for this path. -/
#guard autoTarget == some "other:available"

private def ambiguousRootSource : String :=
  ":- use_module(loader).\n\
   ambiguous(X) :- candidate(X)."

private def ambiguousLoaderSource : String :=
  ":- module(loader, []).\n\
   :- use_module(a).\n\
   :- use_module(b)."

private def candidateSource (moduleName value : String) : String :=
  ":- module(" ++ moduleName ++ ", [candidate/1]).\n" ++
    "candidate(" ++ value ++ ")."

private def ambiguousResolver : ReaderUnitClosure.Resolver String Unit :=
    fun request =>
  match sourceKey? request.source with
  | some "loader" => .ok [.source "loader" ambiguousLoaderSource]
  | some "a" => .ok [.source "a" (candidateSource "a" "left")]
  | some "b" => .ok [.source "b" (candidateSource "b" "right")]
  | _ => .error ()

def ambiguousUniqueExportFails : Bool :=
  match ReaderUnitClosure.loadWith 8
      (ReaderDirective.effectWith emptyImports) ReaderOperator.defaults
      ambiguousResolver "root" ambiguousRootSource with
  | .error _ => false
  | .ok closure =>
      match ReaderModuleLink.link sourceKey? closure with
      | .error (.ambiguousImport "root"
          { name := "candidate", arity := 1 } "a" "b") => true
      | _ => false

/- Static autoload never chooses between two loaded exporters by accident. -/
#guard ambiguousUniqueExportFails

private def encodedCollisionRoot : String :=
  ":- use_module(lib).\n\
   'lib:helper'(literal)."

def encodedQualificationCollisionFails : Bool :=
  match ReaderUnitClosure.loadWith 4
      (ReaderDirective.effectWith emptyImports) ReaderOperator.defaults
      resolver "root" encodedCollisionRoot with
  | .error _ => false
  | .ok closure =>
      match ReaderModuleLink.link sourceKey? closure with
      | .error (.qualifiedNameCollision
          { name := "lib:helper", arity := 1 }) => true
      | _ => false

/- String-backed qualification fails closed when source text already uses the
generated spelling literally; it never aliases two Prolog predicates. -/
#guard encodedQualificationCollisionFails

/- Qualification never fabricates reflective provenance: original units own
the source terms, while every transformed executable clause is explicit. -/
#guard linked?.map (fun linked =>
  linked.program.all fun clause => clause.sourceTerm.isNone) == some true

end Mettapedia.Logic.Prolog.ReaderModuleLinkRegression
