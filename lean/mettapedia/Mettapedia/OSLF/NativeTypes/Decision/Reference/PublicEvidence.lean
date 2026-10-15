import Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax
import Mettapedia.OSLF.NativeTypes.Decision.Reference.Recorded

open Mettapedia.OSLF.Framework

/-!
# Public native judgments with their stopping horizon and receipt view

The recorded entry point has exactly the existing public checker's result.
It additionally retains the first conclusive local exploration horizon.
Requesting its frontier view yields the actual typed receipt family at that
horizon, preserving ordered origins and the independently checked coverage
status. Formula refusals and source refusals perform no semantic search.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Runtime.Description
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Decision.Admission
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Recorded

inductive Report (driver : Driver) (formula : driver.Formula) (raw : Pattern) where
  | refusedSource (reason : SourceIssue)
  | refusedFormula (source : driver.Decoded raw) (reason : Refusal)
  | rejectedProfile (source : driver.Decoded raw)
  | unresolvedProfile (source : driver.Decoded raw)
  | observed (source : driver.Decoded raw)
      (formed : Formed driver.generated.logicFragment driver.leafAdmission formula)
      (profile : driver.profileAdmission = some true)
      (record : Record (denotation driver.tests formula source.val))

def Report.result {driver : Driver} {formula : driver.Formula} {raw : Pattern} :
    Report driver formula raw → Mettapedia.OSLF.NativeTypes.Runtime.Description.Result driver formula raw
  | .refusedSource reason => .refusedSource reason
  | .refusedFormula source reason => .checked source (.refused reason)
  | .rejectedProfile source => .checked source .rejectedCube
  | .unresolvedProfile source => .checked source .unresolvedCube
  | .observed source _ _ record => .checked source (.semantic record.outcome)

def Report.readout {driver : Driver} {formula : driver.Formula} {raw : Pattern}
    (report : Report driver formula raw) : Mettapedia.OSLF.NativeTypes.Runtime.Description.Readout := report.result.readout

def Report.horizon {driver : Driver} {formula : driver.Formula} {raw : Pattern} :
    Report driver formula raw → Option Nat
  | .observed _ _ _ record => some record.horizon
  | _ => none

def Report.frontier {driver : Driver} {formula : driver.Formula} {raw : Pattern} :
    Report driver formula raw → Option (Sigma fun source : driver.Decoded raw =>
      FrontierView driver.backend source.val)
  | .observed source _ _ record => some ⟨source, frontierView driver.backend record⟩
  | _ => none

def checkSource (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget : Nat) : Report driver formula raw :=
  match formation : firstRefusal driver.generated.logicFragment driver.leafAdmission formula with
  | some reason => .refusedFormula source reason
  | none => match profile : driver.profileAdmission with
    | none => .unresolvedProfile source
    | some false => .rejectedProfile source
    | some true => .observed source ((firstRefusal_exact _ _ formula).mp formation) profile
        (Mettapedia.OSLF.NativeTypes.Decision.Reference.Recorded.run driver.backend driver.tests formula source.val budget)

def search (driver : Driver) (formula : driver.Formula) (raw : Pattern) (budget : Nat) :
    Report driver formula raw :=
  match driver.decode raw with
  | .error reason => .refusedSource reason
  | .ok source => checkSource driver formula source budget

theorem checkSource_result (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget : Nat) :
    (checkSource driver formula source budget).result =
      Mettapedia.OSLF.NativeTypes.Runtime.Description.check driver formula source budget := by
  unfold checkSource Mettapedia.OSLF.NativeTypes.Runtime.Description.check
  unfold Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission.check Mettapedia.OSLF.NativeTypes.Decision.Admission.check
  unfold Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission.checkingView
  dsimp only
  split
  · rename_i reason formation
    simp only [formation, Report.result]
  · rename_i formation
    split
    · rename_i profile
      simp only [formation, profile, Report.result]
    · rename_i profile
      simp only [formation, profile, Report.result]
    · rename_i profile
      simp only [formation, profile, Report.result, run_outcome]

theorem search_result (driver : Driver) (formula : driver.Formula) (raw : Pattern) (budget : Nat) :
    (search driver formula raw budget).result =
      Mettapedia.OSLF.NativeTypes.Runtime.Description.search driver formula raw budget := by
  unfold search Mettapedia.OSLF.NativeTypes.Runtime.Description.search
  cases driver.decode raw with
  | error reason => rfl
  | ok source => exact checkSource_result driver formula source budget

theorem positive (driver : Driver) (formula : driver.Formula) (raw : Pattern)
    (report : Report driver formula raw)
    (read : report.readout = .judgment (.decided true)) : Meaning driver formula raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.Description.positive driver formula raw report.result read

theorem negative (driver : Driver) (formula : driver.Formula) (raw : Pattern)
    (report : Report driver formula raw)
    (read : report.readout = .judgment (.decided false)) : ¬ Meaning driver formula raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.Description.negative driver formula raw report.result read

theorem observed_horizon_bounded (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget horizon : Nat)
    (retained : (checkSource driver formula source budget).horizon = some horizon) : horizon ≤ budget := by
  unfold checkSource at retained
  split at retained
  · cases retained
  · split at retained
    · cases retained
    · cases retained
    · simp only [Report.horizon, Option.some.injEq] at retained
      rw [← retained]
      exact run_horizon_le driver.backend driver.tests formula source.val budget

theorem conclusive_mono (driver : Driver) (formula : driver.Formula) (raw : Pattern)
    {small large : Nat} (answer : Bool)
    (read : (search driver formula raw small).readout = .judgment (.decided answer))
    (ordered : small ≤ large) :
    (search driver formula raw large).readout = .judgment (.decided answer) := by
  simp only [Report.readout, search_result] at read ⊢
  exact Mettapedia.OSLF.NativeTypes.Runtime.Description.conclusive_mono driver formula raw answer read ordered

end Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidence
