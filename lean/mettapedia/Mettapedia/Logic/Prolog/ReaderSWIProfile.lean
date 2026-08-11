import Mettapedia.Logic.Prolog.ReaderDirective

/-!
# Pinned SWI read-time operator profile

This module records only the operator exports needed while reading the pinned
PeTTa Prolog source closure.  It is deliberately fail-closed: an import not in
the measured closure is an error rather than an assumption that the imported
source exports no operators.

The declarations come from the module headers shipped by SWI-Prolog V10.1.9.
`library(janus)` exports the prefix operators `@` and `#`; `library(clpfd)`
exports its finite-domain operator family.  The other pinned imports below
were measured to add no operators to the importing module.
-/

namespace Mettapedia.Logic.Prolog.ReaderSWIProfile

open ReaderDirective SourceSignature

inductive Error where
  | malformedImportSource
  | unclassifiedImport (source : String)
deriving DecidableEq, Repr

private def update (priority : Nat) (specifier : ReaderOperator.Specifier)
    (name : String) : ReaderDirective.Update := {
  priority
  specifier
  names := [name]
}

/-- Operators exported by SWI V10.1.9 `library(janus)`. -/
def janusOperators : List ReaderDirective.Update := [
  update 200 .fy "@",
  update 50 .fx "#"
]

/-- Operators exported by SWI V10.1.9 `library(clpfd)`. -/
def clpfdOperators : List ReaderDirective.Update := [
  update 760 .yfx "#<==>",
  update 750 .xfy "#==>",
  update 750 .yfx "#<==",
  update 740 .yfx "#\\/",
  update 730 .yfx "#\\",
  update 720 .yfx "#/\\",
  update 710 .fy "#\\",
  update 700 .xfx "#>",
  update 700 .xfx "#<",
  update 700 .xfx "#>=",
  update 700 .xfx "#=<",
  update 700 .xfx "#=",
  update 700 .xfx "#\\=",
  update 700 .xfx "in",
  update 700 .xfx "ins",
  update 700 .xfx "in_set",
  update 450 .xfx ".."
]

private def pathAux : Nat -> SourceSignature.Term -> Option String
  | 0, _ => none
  | _ + 1, .const (.atom name) => some name
  | fuel + 1, .app indicator arguments =>
      match indicator.name, List.ofFn arguments with
      | "/", [left, right] => do
          let leftPath <- pathAux fuel left
          let rightPath <- pathAux fuel right
          pure (leftPath ++ "/" ++ rightPath)
      | _, _ => none
  | _ + 1, _ => none

def path? (term : SourceSignature.Term) : Option String :=
  pathAux (term.size + 1) term

/-- Canonical stable spelling used by both the read-time operator profile and
source-unit dependency resolvers. -/
def sourceKey? (term : SourceSignature.Term) : Option String :=
  match term with
  | .const (.atom name) => some name
  | .app indicator arguments =>
      match indicator.name, List.ofFn arguments with
      | "library", [path] => return "library(" ++ (← path? path) ++ ")"
      | _, _ => none
  | _ => none

private def operatorEmptyImports : List String := [
  "library(uuid)",
  "library(random)",
  "library(error)",
  "library(listing)",
  "library(aggregate)",
  "library(thread)",
  "library(lists)",
  "library(yall)",
  "library(apply)",
  "library(apply_macros)",
  "library(process)",
  "library(filesex)",
  "library(readutil)",
  "library(pcre)",
  "library(dcg/basics)"
]

/-- Fail-closed read-time operator profile for the pinned PeTTa source
closure.  `metta` is a non-module source loaded by `main.pl`; reading it
imports Janus before CLP(FD), so its resulting reader environment contains
both exported operator families. -/
def pinnedPeTTa : ReaderDirective.ImportProfile Error := fun source =>
  match sourceKey? source with
  | none => .error .malformedImportSource
  | some "library(janus)" => .ok janusOperators
  | some "library(clpfd)" => .ok clpfdOperators
  | some "metta" => .ok (janusOperators ++ clpfdOperators)
  | some key =>
      if key ∈ operatorEmptyImports then .ok []
      else .error (.unclassifiedImport key)

end Mettapedia.Logic.Prolog.ReaderSWIProfile
