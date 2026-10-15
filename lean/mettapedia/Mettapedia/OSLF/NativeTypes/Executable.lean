import Mettapedia.OSLF.NativeTypes.Instances.Local.Driver
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver
import Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver
import Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax
import Mettapedia.OSLF.NativeTypes.Runtime.Search
import Mettapedia.OSLF.NativeTypes.Runtime.Query
import Mettapedia.OSLF.NativeTypes.Runtime.Profiles
import Mettapedia.OSLF.NativeTypes.Runtime.Local
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceCoverageClaims

open Mettapedia.OSLF.Framework

/-!
# Executable generated native type systems

One generation request selects an earned execution profile. The authored
local profile accepts arbitrary presentations satisfying its computed local
admission checks. The proper-child lambda, canonical rho and original
machine profiles check the entire supplied snapshot and operational fragment
against the presentation for which their independent comparisons were proved.
No language name chooses an algorithm and no supplied presentation is replaced.

All successful requests return an installed generated driver with actual
suspended operational and formula work. The native checker and named query
interpreter consume one retained work account.
Generation refusal is separate from source or formula refusal, semantic
falsehood, and unfinished budgeted search.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation (LanguageFragment)
open Mettapedia.OSLF.NativeTypes.Runtime.Description (Driver)
open Mettapedia.OSLF.NativeTypes.Runtime (Installed)
open GeneralOccurrenceFrontier.CoverageClaims (snapshotKey SnapshotKey snapshotKey_decode)

inductive Adapter where
  | scopedLambda
  | canonicalRho
  | originalMachine
  deriving DecidableEq, Repr

inductive GenerationIssue where
  | authoredLocal (reason : Mettapedia.OSLF.NativeTypes.Instances.Local.Driver.GenerationIssue)
  | snapshotMismatch (adapter : Adapter)
  | fragmentMismatch (adapter : Adapter)
  deriving DecidableEq, Repr

inductive Request where
  | authored (snapshot : Snapshot) (fragment : LanguageFragment)
      (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
      (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex
        (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot fragment).language)
      (bound : List TypeExpr) (expected : TypeExpr)
      (mask : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool)
  | scopedLambda (snapshot : Snapshot) (fragment : LanguageFragment)
      (configuration : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.Configuration)
      (context : Ctx LambdaContextualRung.sig)
  | canonicalRho (snapshot : Snapshot) (fragment : LanguageFragment)
      (configuration : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Configuration)
  | originalMachine (snapshot : Snapshot) (fragment : LanguageFragment)
      (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)

def Request.snapshot : Request → Snapshot
  | .authored snapshot _ _ _ _ _ _ => snapshot
  | .scopedLambda snapshot _ _ _ => snapshot
  | .canonicalRho snapshot _ _ => snapshot
  | .originalMachine snapshot _ _ _ => snapshot

def Request.fragment : Request → LanguageFragment
  | .authored _ fragment _ _ _ _ _ => fragment
  | .scopedLambda _ fragment _ _ => fragment
  | .canonicalRho _ fragment _ => fragment
  | .originalMachine _ fragment _ _ => fragment

def Request.logic : Request → Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment
  | .authored _ _ logic _ _ _ _ => logic
  | .scopedLambda _ _ configuration _ => configuration.logic
  | .canonicalRho _ _ configuration => configuration.logic
  | .originalMachine _ _ configuration _ => configuration.logic

def Request.selectedSnapshot (request : Request) : Snapshot :=
  Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot request.snapshot request.fragment

private def authorize (adapter : Adapter) (supplied expected : Snapshot)
    (fragment expectedFragment : LanguageFragment) (driver : Installed) :
    Except GenerationIssue Installed :=
  if snapshotKey supplied = snapshotKey expected then
    if fragment = expectedFragment then .ok driver
    else .error (.fragmentMismatch adapter)
  else .error (.snapshotMismatch adapter)

/-- Explicit adapter selection does not weaken authored-language admission.
Each specialized call checks the full snapshot, including providers and laws,
and exactly the operational settings consumed by its proved backend. -/
def generate : Request → Except GenerationIssue Installed
  | .authored snapshot fragment logic vertex bound expected mask =>
      let output := Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex
      if foundation : output.plan.complete = true then
        if equationFree : output.plan.equations = [] then
          if generic : GeneralExecutionTotalAdmission.checkGeneric output.plan = true then
            .ok (Mettapedia.OSLF.NativeTypes.Runtime.Local.installedLocal
              output bound expected foundation equationFree generic mask)
          else .error (.authoredLocal .premiseCoverageRequired)
        else .error (.authoredLocal .equationCoverageRequired)
      else .error (.authoredLocal (.operationalObligations output.plan.obligations))
  | .scopedLambda snapshot fragment configuration context =>
      authorize .scopedLambda snapshot Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot
        fragment (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.fragment configuration)
        (Mettapedia.OSLF.NativeTypes.Runtime.Profiles.lambda configuration context)
  | .canonicalRho snapshot fragment configuration =>
      authorize .canonicalRho snapshot Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot
        fragment Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment (Mettapedia.OSLF.NativeTypes.Runtime.Profiles.rho configuration)
  | .originalMachine snapshot fragment configuration bound =>
      authorize .originalMachine snapshot Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot
        fragment Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment (Mettapedia.OSLF.NativeTypes.Runtime.Local.partrec configuration bound)

private theorem authorize_success {adapter : Adapter} {supplied expected : Snapshot}
    {fragment expectedFragment : LanguageFragment} {earned output : Installed}
    (success : authorize adapter supplied expected fragment expectedFragment earned = .ok output) :
    supplied = expected ∧ fragment = expectedFragment ∧ output = earned := by
  unfold authorize at success
  split at success
  · rename_i same
    split at success
    · rename_i selected
      have snapshot := congrArg SnapshotKey.decode same
      simp only [snapshotKey_decode] at snapshot
      exact ⟨snapshot, selected, (Except.ok.inj success).symm⟩
    · cases success
  · cases success

theorem generate_success_inputs {request : Request} {output : Installed}
    (success : generate request = .ok output) :
    output.native.generated.snapshot = request.selectedSnapshot ∧
      output.native.generated.languageFragment = request.fragment ∧
      output.native.generated.logicFragment = request.logic := by
  cases request with
  | authored snapshot fragment logic vertex bound expected mask =>
      unfold generate at success
      dsimp only at success
      split at success
      · split at success
        · split at success
          · have same := Except.ok.inj success
            subst output
            exact ⟨rfl, rfl, rfl⟩
          · cases success
        · cases success
      · cases success
  | scopedLambda snapshot fragment configuration context =>
      obtain ⟨rfl, rfl, rfl⟩ := authorize_success success
      exact ⟨rfl, rfl, rfl⟩
  | canonicalRho snapshot fragment configuration =>
      obtain ⟨rfl, rfl, rfl⟩ := authorize_success success
      exact ⟨rfl, rfl, rfl⟩
  | originalMachine snapshot fragment configuration bound =>
      obtain ⟨rfl, rfl, rfl⟩ := authorize_success success
      exact ⟨rfl, rfl, rfl⟩

theorem generate_success_snapshot {request : Request} {output : Installed}
    (success : generate request = .ok output) :
    output.native.generated.snapshot = request.selectedSnapshot := (generate_success_inputs success).1

theorem generate_success_fragment {request : Request} {output : Installed}
    (success : generate request = .ok output) :
    output.native.generated.languageFragment = request.fragment := (generate_success_inputs success).2.1

theorem generate_success_logic {request : Request} {output : Installed}
    (success : generate request = .ok output) :
    output.native.generated.logicFragment = request.logic := (generate_success_inputs success).2.2

/-- The actual compiled rule/equation/context plan retains the supplied dials.
The specialized operational comparison is the adapter's earned theorem;
this retention law does not assert generic recursive-premise decidability. -/
theorem generate_success_plan {request : Request} {output : Installed}
    (success : generate request = .ok output) :
    output.native.generated.plan = compile request.selectedSnapshot request.fragment.operational := by
  unfold Mettapedia.OSLF.NativeTypes.Generation.Generated.plan
  rw [generate_success_snapshot success, generate_success_fragment success]

/-- Starting and resuming retain the same formula continuation and occurrence
jobs. They never compute the exhaustive decision bound. -/
def start (installed : Installed) (formula : installed.native.Formula) (raw : Pattern) :
    Mettapedia.OSLF.NativeTypes.Runtime.Session installed.native installed.runtime formula raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.start installed.native installed.runtime formula raw

def resume {installed : Installed} {formula : installed.native.Formula} {raw : Pattern}
    (budget : Nat) (session : Mettapedia.OSLF.NativeTypes.Runtime.Session installed.native installed.runtime formula raw) :
    Mettapedia.OSLF.NativeTypes.Runtime.Session installed.native installed.runtime formula raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.resume budget session

def check (installed : Installed) (formula : installed.native.Formula) {raw : Pattern}
    (source : installed.native.Decoded raw) (budget : Nat) :
    Mettapedia.OSLF.NativeTypes.Runtime.Session installed.native installed.runtime formula raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.check installed.native installed.runtime formula source budget

def search (installed : Installed) (formula : installed.native.Formula) (raw : Pattern) (budget : Nat) :
    Mettapedia.OSLF.NativeTypes.Runtime.Session installed.native installed.runtime formula raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.search installed.native installed.runtime formula raw budget

def ask (installed : Installed) (query : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Query) (raw : Pattern) (budget : Nat) :
    Mettapedia.OSLF.NativeTypes.Runtime.NamedSession installed.native installed.runtime query raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.ask installed.native installed.runtime query raw budget

def startQuery (installed : Installed) (query : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Query) (raw : Pattern) :
    Mettapedia.OSLF.NativeTypes.Runtime.NamedSession installed.native installed.runtime query raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.startQuery installed.native installed.runtime query raw

def resumeQuery {installed : Installed} {query : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Query} {raw : Pattern}
    (budget : Nat) (session : Mettapedia.OSLF.NativeTypes.Runtime.NamedSession installed.native installed.runtime query raw) :
    Mettapedia.OSLF.NativeTypes.Runtime.NamedSession installed.native installed.runtime query raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.resumeQuery budget session

def decisionBound (installed : Installed) (formula : installed.native.Formula) {raw : Pattern}
    (source : installed.native.Decoded raw) : Nat :=
  Mettapedia.OSLF.NativeTypes.Runtime.decisionBound installed.native installed.runtime formula source

theorem check_positive (installed : Installed) (formula : installed.native.Formula) {raw : Pattern}
    (source : installed.native.Decoded raw) (budget : Nat)
    (read : (check installed formula source budget).readout = .judgment (.decided true)) :
    Mettapedia.OSLF.NativeTypes.Runtime.Description.Meaning installed.native formula raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.positive (check installed formula source budget) read

theorem check_negative (installed : Installed) (formula : installed.native.Formula) {raw : Pattern}
    (source : installed.native.Decoded raw) (budget : Nat)
    (read : (check installed formula source budget).readout = .judgment (.decided false)) :
    ¬ Mettapedia.OSLF.NativeTypes.Runtime.Description.Meaning installed.native formula raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.negative (check installed formula source budget) read

theorem check_complete (installed : Installed) (formula : installed.native.Formula) {raw : Pattern}
    (source : installed.native.Decoded raw)
    (formed : Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed
      installed.native.generated.logicFragment installed.native.leafAdmission formula)
    (profile : installed.native.profileAdmission = some true) (budget : Nat)
    (enough : decisionBound installed formula source ≤ budget) :
    ∃ answer, (check installed formula source budget).readout = .judgment (.decided answer) :=
  Mettapedia.OSLF.NativeTypes.Runtime.check_complete installed.native installed.runtime formula source formed profile budget enough

theorem search_positive (installed : Installed) (formula : installed.native.Formula) (raw : Pattern) (budget : Nat)
    (read : (search installed formula raw budget).readout = .judgment (.decided true)) :
    Mettapedia.OSLF.NativeTypes.Runtime.Description.Meaning installed.native formula raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.positive (search installed formula raw budget) read

theorem search_negative (installed : Installed) (formula : installed.native.Formula) (raw : Pattern) (budget : Nat)
    (read : (search installed formula raw budget).readout = .judgment (.decided false)) :
    ¬ Mettapedia.OSLF.NativeTypes.Runtime.Description.Meaning installed.native formula raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.negative (search installed formula raw budget) read

theorem search_complete (installed : Installed) (formula : installed.native.Formula) (raw : Pattern)
    (sourceAdmitted : ∃ source, installed.native.admitted source ∧ installed.native.render source = raw)
    (formed : Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed
      installed.native.generated.logicFragment installed.native.leafAdmission formula)
    (profile : installed.native.profileAdmission = some true) (budget : Nat)
    (enough : ∀ source : installed.native.Decoded raw, decisionBound installed formula source ≤ budget) :
    ∃ answer, (search installed formula raw budget).readout = .judgment (.decided answer) :=
  Mettapedia.OSLF.NativeTypes.Runtime.search_complete installed.native installed.runtime
    formula raw sourceAdmitted formed profile budget enough

theorem search_resume (installed : Installed) (formula : installed.native.Formula) (raw : Pattern)
    (first more : Nat) :
    search installed formula raw (first + more) = resume more (search installed formula raw first) :=
  Mettapedia.OSLF.NativeTypes.Runtime.search_resume installed.native installed.runtime formula raw first more

theorem resume_add {installed : Installed} {formula : installed.native.Formula} {raw : Pattern}
    (first more : Nat) (session : Mettapedia.OSLF.NativeTypes.Runtime.Session installed.native installed.runtime formula raw) :
    resume (first + more) session = resume more (resume first session) :=
  Mettapedia.OSLF.NativeTypes.Runtime.resume_add first more session

theorem search_spent_le (installed : Installed) (formula : installed.native.Formula) (raw : Pattern)
    (budget : Nat) : (search installed formula raw budget).spent ≤ budget :=
  Mettapedia.OSLF.NativeTypes.Runtime.search_spent_le installed.native installed.runtime formula raw budget

theorem resume_spent_le {installed : Installed} {formula : installed.native.Formula} {raw : Pattern}
    (budget : Nat) (session : Mettapedia.OSLF.NativeTypes.Runtime.Session installed.native installed.runtime formula raw) :
    (resume budget session).spent ≤ session.spent + budget :=
  Mettapedia.OSLF.NativeTypes.Runtime.resume_spent_le budget session

theorem search_conclusive_mono (installed : Installed) (formula : installed.native.Formula) (raw : Pattern)
    {small large : Nat} (answer : Bool)
    (read : (search installed formula raw small).readout = .judgment (.decided answer))
    (ordered : small ≤ large) : search installed formula raw large = search installed formula raw small :=
  Mettapedia.OSLF.NativeTypes.Runtime.search_conclusive_mono installed.native installed.runtime formula raw answer read ordered

/-- Every retained observation contains an actual semantic firing. A settled
query may cancel later jobs and does not claim complete occurrence coverage. -/
theorem observation_step (installed : Installed) (formula : installed.native.Formula) (raw : Pattern)
    (session : Mettapedia.OSLF.NativeTypes.Runtime.Session installed.native installed.runtime formula raw)
    (observation : Mettapedia.OSLF.NativeTypes.Decision.Machine.Observation installed.runtime.cursor)
    (listed : observation ∈ session.observations) :
    installed.native.system.Step observation.source
      (installed.runtime.cursor.target observation.source observation.receipt) :=
  Mettapedia.OSLF.NativeTypes.Runtime.observation_step session observation listed

theorem ask_positive (installed : Installed) (query : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Query) (raw : Pattern) (budget : Nat)
    (read : (ask installed query raw budget).readout = .checked (.judgment (.decided true))) :
    Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning installed.native query raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.named_positive (ask installed query raw budget) read

theorem ask_negative (installed : Installed) (query : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Query) (raw : Pattern) (budget : Nat)
    (read : (ask installed query raw budget).readout = .checked (.judgment (.decided false))) :
    ¬ Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning installed.native query raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.named_negative (ask installed query raw budget) read

theorem ask_complete (installed : Installed) (query : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Query)
    (formula : installed.native.Formula) (raw : Pattern)
    (resolved : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Resolves installed.native query formula)
    (sourceAdmitted : ∃ source, installed.native.admitted source ∧ installed.native.render source = raw)
    (formed : Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed
      installed.native.generated.logicFragment installed.native.leafAdmission formula)
    (profile : installed.native.profileAdmission = some true) (budget : Nat)
    (enough : ∀ source : installed.native.Decoded raw, decisionBound installed formula source ≤ budget) :
    ∃ answer, (ask installed query raw budget).readout = .checked (.judgment (.decided answer)) :=
  Mettapedia.OSLF.NativeTypes.Runtime.ask_complete installed.native installed.runtime
    query formula raw resolved sourceAdmitted formed profile budget enough

theorem ask_resume (installed : Installed) (query : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Query) (raw : Pattern)
    (first more : Nat) :
    ask installed query raw (first + more) = resumeQuery more (ask installed query raw first) :=
  Mettapedia.OSLF.NativeTypes.Runtime.ask_resume installed.native installed.runtime query raw first more

theorem ask_spent_le (installed : Installed) (query : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Query) (raw : Pattern)
    (budget : Nat) : (ask installed query raw budget).spent ≤ budget :=
  Mettapedia.OSLF.NativeTypes.Runtime.ask_spent_le installed.native installed.runtime query raw budget

theorem ask_conclusive_mono (installed : Installed) (query : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Query) (raw : Pattern)
    {small large : Nat} (answer : Bool)
    (read : (ask installed query raw small).readout = .checked (.judgment (.decided answer)))
    (ordered : small ≤ large) :
    (ask installed query raw large).readout = .checked (.judgment (.decided answer)) :=
  Mettapedia.OSLF.NativeTypes.Runtime.ask_conclusive_mono installed.native installed.runtime query raw answer read ordered

end Mettapedia.OSLF.NativeTypes.Executable
