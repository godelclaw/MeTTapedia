import Mettapedia.OSLF.NativeTypes.Runtime.Search
import Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax

open Mettapedia.OSLF.Framework

/-!
# Named generated formulas through retained native sessions

Constructor names are resolved by the generated catalogue. The named query
retains the resulting formula and its resolution proof while it pauses and
resumes. Every search and every displayed receipt uses the same formula machine.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Runtime.Description (Driver)
open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query Resolves elaborate elaborate_exact)

inductive NamedSession (driver : Driver) (runtime : Engine driver) (query : Query) (raw : Pattern) where
  | unknownConstructor (name : String)
  | checked (formula : driver.Formula) (resolved : Resolves driver query formula)
      (session : Session driver runtime formula raw)

def NamedSession.nativeAnswer {driver : Driver} {runtime : Engine driver} {query : Query} {raw : Pattern} :
    NamedSession driver runtime query raw → Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Answer driver query raw
  | .unknownConstructor name => .unknownConstructor name
  | .checked formula resolved session => .checked formula resolved session.nativeResult

def NamedSession.readout {driver : Driver} {runtime : Engine driver} {query : Query} {raw : Pattern}
    (session : NamedSession driver runtime query raw) : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout :=
  session.nativeAnswer.readout

def NamedSession.spent {driver : Driver} {runtime : Engine driver} {query : Query} {raw : Pattern} :
    NamedSession driver runtime query raw → Nat
  | .unknownConstructor _ => 0
  | .checked _ _ session => session.spent

def NamedSession.observations {driver : Driver} {runtime : Engine driver} {query : Query} {raw : Pattern} :
    NamedSession driver runtime query raw → List (Mettapedia.OSLF.NativeTypes.Decision.Machine.Observation runtime.cursor)
  | .unknownConstructor _ => []
  | .checked _ _ session => session.observations

def startQuery (driver : Driver) (runtime : Engine driver) (query : Query) (raw : Pattern) :
    NamedSession driver runtime query raw :=
  match compiled : elaborate driver query with
  | .error name => .unknownConstructor name
  | .ok formula => .checked formula ((elaborate_exact driver query formula).mp compiled)
      (start driver runtime formula raw)

def resumeQuery {driver : Driver} {runtime : Engine driver} {query : Query} {raw : Pattern}
    (fuel : Nat) : NamedSession driver runtime query raw → NamedSession driver runtime query raw
  | .unknownConstructor name => .unknownConstructor name
  | .checked formula resolved session => .checked formula resolved (resume fuel session)

def ask (driver : Driver) (runtime : Engine driver) (query : Query) (raw : Pattern) (budget : Nat) :
    NamedSession driver runtime query raw := resumeQuery budget (startQuery driver runtime query raw)

theorem resumeQuery_add {driver : Driver} {runtime : Engine driver} {query : Query} {raw : Pattern}
    (first more : Nat) (session : NamedSession driver runtime query raw) :
    resumeQuery (first + more) session = resumeQuery more (resumeQuery first session) := by
  cases session with
  | unknownConstructor => rfl
  | checked formula resolved session =>
    exact congrArg (NamedSession.checked formula resolved) (resume_add first more session)

theorem ask_resume (driver : Driver) (runtime : Engine driver) (query : Query) (raw : Pattern)
    (first more : Nat) :
    ask driver runtime query raw (first + more) = resumeQuery more (ask driver runtime query raw first) :=
  resumeQuery_add first more (startQuery driver runtime query raw)

theorem ask_readout (driver : Driver) (runtime : Engine driver) (query : Query) (raw : Pattern) (budget : Nat) :
    (ask driver runtime query raw budget).readout =
      match elaborate driver query with
      | .error name => .unknownConstructor name
      | .ok formula => .checked (search driver runtime formula raw budget).readout := by
  unfold ask startQuery
  split <;> rename_i value found <;>
    simp only [resumeQuery, NamedSession.readout, NamedSession.nativeAnswer,
      Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Answer.readout, found, search, Session.readout]

theorem ask_spent_le (driver : Driver) (runtime : Engine driver) (query : Query) (raw : Pattern) (budget : Nat) :
    (ask driver runtime query raw budget).spent ≤ budget := by
  unfold ask startQuery
  split
  · exact Nat.zero_le _
  · exact search_spent_le driver runtime _ raw budget

theorem named_positive {driver : Driver} {runtime : Engine driver} {query : Query} {raw : Pattern}
    (session : NamedSession driver runtime query raw)
    (read : session.readout = .checked (.judgment (.decided true))) :
    Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning driver query raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.positive session.nativeAnswer read

theorem named_negative {driver : Driver} {runtime : Engine driver} {query : Query} {raw : Pattern}
    (session : NamedSession driver runtime query raw)
    (read : session.readout = .checked (.judgment (.decided false))) :
    ¬ Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning driver query raw :=
  Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.negative session.nativeAnswer read

theorem ask_complete (driver : Driver) (runtime : Engine driver) (query : Query)
    (formula : driver.Formula) (raw : Pattern)
    (resolved : Resolves driver query formula)
    (sourceAdmitted : ∃ source, driver.admitted source ∧ driver.render source = raw)
    (formed : Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed driver.generated.logicFragment driver.leafAdmission formula)
    (profile : driver.profileAdmission = some true) (budget : Nat)
    (enough : ∀ source : driver.Decoded raw, decisionBound driver runtime formula source ≤ budget) :
    ∃ value, (ask driver runtime query raw budget).readout = .checked (.judgment (.decided value)) := by
  have compiled := (elaborate_exact driver query formula).mpr resolved
  obtain ⟨value, read⟩ := search_complete driver runtime formula raw sourceAdmitted formed profile budget enough
  exact ⟨value, by rw [ask_readout, compiled]; exact congrArg Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout.checked read⟩

theorem ask_conclusive_mono (driver : Driver) (runtime : Engine driver) (query : Query) (raw : Pattern)
    {small large : Nat} (value : Bool)
    (read : (ask driver runtime query raw small).readout = .checked (.judgment (.decided value)))
    (ordered : small ≤ large) :
    (ask driver runtime query raw large).readout = .checked (.judgment (.decided value)) := by
  cases compiled : elaborate driver query with
  | error name => rw [ask_readout, compiled] at read; cases read
  | ok formula =>
    have prior : (search driver runtime formula raw small).readout = .judgment (.decided value) := by
      rw [ask_readout, compiled] at read
      exact Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout.checked.inj read
    have later := search_conclusive_mono driver runtime formula raw value prior ordered
    simpa only [ask_readout, compiled, later] using
      congrArg Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout.checked prior

end Mettapedia.OSLF.NativeTypes.Runtime
