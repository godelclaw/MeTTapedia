import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceContinuation
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionTraceAccounting

/-!
# Authored nested workflow and retained guard controls

The actual module rule matches a bag inside a workflow. Jobs include the
workflow occurrence under its workspace container. Each physical token
allocation starts its own retained premise continuation.
-/

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../../../metta/gslt/module/CollectionNestedGuardedPetri.module"

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching CanonicalBags
open WellSorted CollectionOccurrenceHandoff RecursiveCollectionHandoff

def authored : LanguageDef :=
  CollectionNestedGuardedPetri.language.toOption.getD (LanguageDef.empty "")

def language : LanguageDef :=
  (authored.toCore.toOption.map (·.language)).getD (LanguageDef.empty "")

#guard CollectionNestedGuardedPetri.language.isOk
#guard authored.toCore.isOk
#guard language.rewrites.length == 1
#guard language.rewrites[0]?.map (·.premises) == some [.relationQuery "permit" []]

/-- A premise may read an already captured collection; an undeclared query
variable cannot gain a binding merely by appearing in a query. -/
def queried (metavariable : String) : LanguageDef :=
  { authored with «rewrites» := authored.rewrites.map fun rule =>
    { rule with premises := [.relationQuery "inspect" [.fvar metavariable]] } }

#guard (queried "rest").toCore.isOk
#guard !(queried "missing").toCore.isOk
#guard ((queried "rest").toCore.toOption.bind fun core => core.language.rewrites[0]?).map
  (·.premises) == some [.relationQuery "inspect" [.fvar "rest"]]

def token (label : String) : Pattern := .apply label []
def marking (items : List Pattern) : Pattern := .collection .hashBag items none
def workflow (items : List Pattern) : Pattern := .apply "Flow" [marking items]
def boxed (items : List Pattern) : Pattern := .apply "Box" [workflow items]

def source : Pattern := boxed [token "A", token "A", token "B"]
def expected : Pattern := canon (boxed [token "A", token "B", token "B"])

def plan (permitted : Bool) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile
    { language, freeTypes := [], provider :=
      { signatures := [{ relation := "permit", argumentTypes := [], modes := [] }],
        rows := if permitted then [{ relation := "permit", values := [] }] else [] } }
    { sites := .all, includeDerivedEquations := false }

structure Retained where
  job : Job
  request : RecursiveCollectionContinuation.Request

/-- This bounded control driver prepares actual published matcher answers.
Its budget does not establish whole-source completeness. -/
def prepared (permitted : Bool) (source : Pattern) (bound : List TypeExpr := []) : List Retained :=
  (jobs (plan permitted) bound (.base "Workspace") source).attach.flatMap fun selected =>
    let job := selected.val
    let valid := (jobs_exact _ _ _ _ _).mp selected.property
    let matched := RecursiveCollectionMachine.run job.request 100
      (RecursiveCollectionMachine.start job.request)
    matched.answers.attach.flatMap fun published =>
      match made : prepare job.request published.val with
      | none => []
      | some ordinary =>
        let matching := prepare_valid job.request published.val
          (RecursiveCollectionMachine.published_trace_valid job.request 100 published.property) made
        match CollectionOccurrenceContinuation.request? (plan permitted) bound (.base "Workspace") source
            job valid published.val ordinary matching 0 with
        | none => []
        | some request => [⟨job, request⟩]

def outcomes (retained : Retained) (work : Nat) : List Complete.DeepRoot.Firing :=
  RecursiveCollectionContinuation.publication retained.request
    (RecursiveCollectionContinuation.run retained.request work
      (RecursiveCollectionContinuation.start retained.request))

def receipts (permitted : Bool) (source : Pattern) (work : Nat) (bound : List TypeExpr := []) :
    List GeneralRuleJobs.Receipt :=
  (prepared permitted source bound).flatMap fun retained =>
    (outcomes retained work).filterMap fun firing =>
      CollectionOccurrenceContinuation.finish? (plan permitted) bound (.base "Workspace")
        retained.job retained.request.prepared firing

def checkControls : IO Unit := do
  for permitted in [true, false] do
    let retained := prepared permitted source
    unless retained.length == 2 do
      throw (IO.userError "Nested workflow lost a physical token allocation")
    unless (retained.map (·.request.prepared.history)).eraseDups.length == 2 do
      throw (IO.userError "Nested workflow conflated allocation histories")
    let completed := receipts permitted source 80
    unless completed.length == (if permitted then 2 else 0) do
      throw (IO.userError "Nested workflow guard produced the wrong receipt count")
    unless completed.all (fun receipt => canon receipt.target == expected) do
      throw (IO.userError "Nested workflow changed an outer context or token multiplicity")
    for frame in retained do
      let request := frame.request
      let initial := RecursiveCollectionContinuation.start request
      unless initial.answers.isEmpty do
        throw (IO.userError "A raw nested match published before its guard ran")
      let uninterrupted := RecursiveCollectionContinuation.run request 80 initial
      let interrupted := RecursiveCollectionContinuation.run request 47
        (RecursiveCollectionContinuation.run request 33 initial)
      unless RecursiveCollectionContinuation.publication request uninterrupted ==
          RecursiveCollectionContinuation.publication request interrupted do
        throw (IO.userError "Resuming a nested guard lost or repeated a publication")
      unless uninterrupted.agenda.isEmpty && uninterrupted.unresolved.isEmpty do
        throw (IO.userError "Nested workflow retained unresolved work")
  unless (prepared true (boxed [token "B"])).isEmpty do
    throw (IO.userError "A missing token generated a nested match")
  let ambient := boxed [token "A", .bvar 0, token "A", token "B"]
  let ambientTarget := canon (boxed [token "B", .bvar 0, token "A", token "B"])
  let underBinder := receipts true ambient 80 [.base "Place"]
  unless underBinder.length == 2 &&
      underBinder.all (fun receipt => canon receipt.target == ambientTarget) do
    throw (IO.userError "Nested execution lost the ambient binder context")
  IO.println "NestedCollectionContinuationControls: guard, multiplicity, outer context and resumption passed"

#eval checkControls

end Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls
