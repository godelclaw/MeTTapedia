import Mettapedia.OSLF.NativeTypes.Runtime.Session
import Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.OSLF.Framework

/-!
# Starting, checking and resuming generated native judgments

Admission checks run once before a session starts. Every formula branch and
operational matcher then consumes the same retained transition budget. The
computable exhaustive bound is a separate operation used by the completeness
theorem; ordinary checking never computes it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Runtime.Description
open Mettapedia.OSLF.NativeTypes.Decision.Admission

def startSource (driver : Driver) (runtime : Engine driver) (formula : driver.Formula)
    {raw : Pattern} (source : driver.Decoded raw) : Session driver runtime formula raw :=
  match firstRefusal driver.generated.logicFragment driver.leafAdmission formula with
  | some reason => .refusedFormula source reason
  | none => match driver.profileAdmission with
    | some true => .running source (Mettapedia.OSLF.NativeTypes.Decision.Machine.start
        runtime.cursor runtime.leaves formula source.val source.property.1)
    | some false => .rejectedCube source
    | none => .unresolvedCube source

def start (driver : Driver) (runtime : Engine driver) (formula : driver.Formula) (raw : Pattern) :
    Session driver runtime formula raw :=
  match driver.decode raw with
  | .error reason => .refusedSource reason
  | .ok source => startSource driver runtime formula source

def check (driver : Driver) (runtime : Engine driver) (formula : driver.Formula)
    {raw : Pattern} (source : driver.Decoded raw) (budget : Nat) : Session driver runtime formula raw :=
  resume budget (startSource driver runtime formula source)

def search (driver : Driver) (runtime : Engine driver) (formula : driver.Formula)
    (raw : Pattern) (budget : Nat) : Session driver runtime formula raw :=
  resume budget (start driver runtime formula raw)

def decisionBound (driver : Driver) (runtime : Engine driver) (formula : driver.Formula)
    {raw : Pattern} (source : driver.Decoded raw) : Nat :=
  Mettapedia.OSLF.NativeTypes.Decision.Machine.totalBound runtime.cursor runtime.leaves formula source.val source.property.1

theorem startSource_spent (driver : Driver) (runtime : Engine driver) (formula : driver.Formula)
    {raw : Pattern} (source : driver.Decoded raw) : (startSource driver runtime formula source).spent = 0 := by
  unfold startSource
  split
  · rfl
  · split <;> rfl

theorem start_spent (driver : Driver) (runtime : Engine driver) (formula : driver.Formula) (raw : Pattern) :
    (start driver runtime formula raw).spent = 0 := by
  unfold start
  split
  · rfl
  · exact startSource_spent driver runtime formula _

theorem check_spent_le (driver : Driver) (runtime : Engine driver) (formula : driver.Formula)
    {raw : Pattern} (source : driver.Decoded raw) (budget : Nat) :
    (check driver runtime formula source budget).spent ≤ budget := by
  have bound := resume_spent_le budget (startSource driver runtime formula source)
  rw [startSource_spent, Nat.zero_add] at bound
  exact bound

theorem search_spent_le (driver : Driver) (runtime : Engine driver) (formula : driver.Formula)
    (raw : Pattern) (budget : Nat) : (search driver runtime formula raw budget).spent ≤ budget := by
  have bound := resume_spent_le budget (start driver runtime formula raw)
  rw [start_spent, Nat.zero_add] at bound
  exact bound

theorem check_resume (driver : Driver) (runtime : Engine driver) (formula : driver.Formula)
    {raw : Pattern} (source : driver.Decoded raw) (first more : Nat) :
    check driver runtime formula source (first + more) = resume more (check driver runtime formula source first) :=
  resume_add first more (startSource driver runtime formula source)

theorem search_resume (driver : Driver) (runtime : Engine driver) (formula : driver.Formula)
    (raw : Pattern) (first more : Nat) :
    search driver runtime formula raw (first + more) = resume more (search driver runtime formula raw first) :=
  resume_add first more (start driver runtime formula raw)

theorem check_complete (driver : Driver) (runtime : Engine driver) (formula : driver.Formula)
    {raw : Pattern} (source : driver.Decoded raw)
    (formed : Formed driver.generated.logicFragment driver.leafAdmission formula)
    (profile : driver.profileAdmission = some true) (budget : Nat)
    (enough : decisionBound driver runtime formula source ≤ budget) :
    ∃ answer, (check driver runtime formula source budget).readout = .judgment (.decided answer) := by
  have accepted := (firstRefusal_exact driver.generated.logicFragment driver.leafAdmission formula).mpr formed
  obtain ⟨answer, read⟩ := Mettapedia.OSLF.NativeTypes.Decision.Machine.complete_at_bound
    runtime.cursor runtime.leaves formula source.val source.property.1 budget enough
  refine ⟨answer, ?_⟩
  unfold check startSource
  rw [accepted, profile]
  change (Session.running source (Mettapedia.OSLF.NativeTypes.Decision.Machine.run
    runtime.cursor runtime.leaves formula source.val source.property.1 budget)).readout = _
  rw [running_readout, read]

theorem search_complete (driver : Driver) (runtime : Engine driver) (formula : driver.Formula)
    (raw : Pattern)
    (sourceAdmitted : ∃ source, driver.admitted source ∧ driver.render source = raw)
    (formed : Formed driver.generated.logicFragment driver.leafAdmission formula)
    (profile : driver.profileAdmission = some true) (budget : Nat)
    (enough : ∀ source : driver.Decoded raw, decisionBound driver runtime formula source ≤ budget) :
    ∃ answer, (search driver runtime formula raw budget).readout = .judgment (.decided answer) := by
  have accepted := driver.decode_complete raw sourceAdmitted
  cases decoded : driver.decode raw with
  | error reason => rw [decoded] at accepted; cases accepted
  | ok source =>
    simpa only [search, start, decoded, check] using
      check_complete driver runtime formula source formed profile budget (enough source)

theorem search_conclusive_mono (driver : Driver) (runtime : Engine driver) (formula : driver.Formula)
    (raw : Pattern) {small large : Nat} (answer : Bool)
    (read : (search driver runtime formula raw small).readout = .judgment (.decided answer))
    (ordered : small ≤ large) :
    search driver runtime formula raw large = search driver runtime formula raw small := by
  obtain ⟨more, rfl⟩ := Nat.exists_eq_add_of_le ordered
  rw [search_resume, resume_conclusive _ answer read]

end Mettapedia.OSLF.NativeTypes.Runtime
