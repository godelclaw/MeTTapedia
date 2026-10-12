import Mettapedia.OSLF.NativeTypes.Decision.Admission
import Mettapedia.OSLF.NativeTypes.Decision.Reference.Receipts
import Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission

open Mettapedia.OSLF.Framework

/-!
# One public interface for executable generated native judgments

The language adapter supplies a proved operational backend, an exact source
decoder and generated leaf interpretations. Admission, checking and search
are shared. A refused source or formula never becomes a negative judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime.Description

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

inductive SourceIssue where
  | outsideProfile
  | illScopedOrSorted
  deriving DecidableEq, Repr

/-- The executable realization of one generated language profile. Concrete
instances must construct all laws from their actual matcher and equations. -/
structure Driver where
  generated : Mettapedia.OSLF.NativeTypes.Generation.Generated
  profile : Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission.Choice generated := .uniform
  expected : TypeExpr
  system : Mettapedia.GSLT.GSLT.{0}
  admitted : system.Term → Prop
  render : system.Term → Pattern
  render_injective : Function.Injective render
  decode : (raw : Pattern) → Except SourceIssue
    {source : system.Term // admitted source ∧ render source = raw}
  decode_complete : ∀ raw, (∃ source, admitted source ∧ render source = raw) →
    (decode raw).isOk = true
  backend : Backend.{0,0} system admitted
  Leaf : Type
  tests : Leaf → Test system admitted
  leafAdmission : Mettapedia.OSLF.NativeTypes.Decision.Admission.LeafAdmission Leaf
  lookup : String → Option Leaf

def Driver.profileContract (driver : Driver) : Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission.Contract :=
  driver.profile.contract

def Driver.profileAdmission (driver : Driver) : Option Bool := driver.profile.status

/-- Root constructor leaves use the original generated formation checker;
their independently specified formation rule includes the declared carrier. -/
def rootAdmission {Leaf : Type} (generated : Mettapedia.OSLF.NativeTypes.Generation.Generated)
    (expected : TypeExpr) (index : Leaf → Nat) :
    Mettapedia.OSLF.NativeTypes.Decision.Admission.LeafAdmission Leaf where
  admitted leaf := Mettapedia.OSLF.NativeTypes.Structural.Formed generated.snapshot.language generated.atomSort
    generated.logicFragment expected (.root (index leaf))
  probe leaf := (generated.elaborate expected (.root (index leaf))).map (fun _ => ())
  exact leaf := by
    rw [← Mettapedia.OSLF.NativeTypes.Generation.generated_formation_iff]
    cases generated.elaborate expected (.root (index leaf)) <;> rfl

abbrev Driver.Formula (driver : Driver) := Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula driver.Leaf

abbrev Driver.Decoded (driver : Driver) (raw : Pattern) :=
  {source : driver.system.Term // driver.admitted source ∧ driver.render source = raw}

/-- The original raw request means an admitted source with the requested
native predicate. Injective readback makes negative judgments unambiguous. -/
def Meaning (driver : Driver) (formula : driver.Formula) (raw : Pattern) : Prop :=
  ∃ source, driver.admitted source ∧ driver.render source = raw ∧
    denotation driver.tests formula source

theorem meaning_at_decoded (driver : Driver) (formula : driver.Formula) (raw : Pattern)
    (decoded : driver.Decoded raw) :
    Meaning driver formula raw ↔ denotation driver.tests formula decoded.val := by
  constructor
  · rintro ⟨source, _, equal, holds⟩
    have same : source = decoded.val := driver.render_injective (equal.trans decoded.property.2.symm)
    exact same ▸ holds
  · intro holds
    exact ⟨decoded.val, decoded.property.1, decoded.property.2, holds⟩

inductive Result (driver : Driver) (formula : driver.Formula) (raw : Pattern) where
  | refusedSource (reason : SourceIssue)
  | checked (source : driver.Decoded raw)
      (verdict : Mettapedia.OSLF.NativeTypes.Decision.Admission.Verdict
        (denotation driver.tests formula source.val))

inductive Readout where
  | sourceRefused (reason : SourceIssue)
  | judgment (answer : Mettapedia.OSLF.NativeTypes.Generation.CheckResult)
  deriving DecidableEq, Repr

def Result.readout {driver : Driver} {formula : driver.Formula} {raw : Pattern} :
    Result driver formula raw → Readout
  | .refusedSource reason => .sourceRefused reason
  | .checked _ verdict => .judgment verdict.readout

/-- Check the generated formula after exact source decoding. -/
def check (driver : Driver) (formula : driver.Formula) {raw : Pattern}
    (source : driver.Decoded raw) (budget : Nat) : Result driver formula raw :=
  .checked source (Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission.check driver.generated driver.profileAdmission driver.backend
    driver.tests driver.leafAdmission formula source.val budget)

/-- Raw-program entry point. The decoder and generated admission run before
any semantic search; every failure retains its actual reason. -/
def search (driver : Driver) (formula : driver.Formula) (raw : Pattern)
    (budget : Nat) : Result driver formula raw :=
  match driver.decode raw with
  | .error reason => .refusedSource reason
  | .ok source => check driver formula source budget

theorem positive (driver : Driver) (formula : driver.Formula) (raw : Pattern)
    (result : Result driver formula raw)
    (read : result.readout = .judgment (.decided true)) : Meaning driver formula raw := by
  cases result with
  | refusedSource reason => cases read
  | checked source verdict =>
    exact (meaning_at_decoded driver formula raw source).mpr
      (Mettapedia.OSLF.NativeTypes.Decision.Admission.positive verdict (Readout.judgment.inj read))

theorem negative (driver : Driver) (formula : driver.Formula) (raw : Pattern)
    (result : Result driver formula raw)
    (read : result.readout = .judgment (.decided false)) : ¬ Meaning driver formula raw := by
  cases result with
  | refusedSource reason => cases read
  | checked source verdict =>
    intro holds
    exact Mettapedia.OSLF.NativeTypes.Decision.Admission.negative verdict (Readout.judgment.inj read)
      ((meaning_at_decoded driver formula raw source).mp holds)

def decisionBound (driver : Driver) (formula : driver.Formula) (raw : Pattern) : Except SourceIssue Nat :=
  (driver.decode raw).map fun source => workBound driver.backend driver.tests formula source.val

theorem decoded_complete (driver : Driver) (formula : driver.Formula) (raw : Pattern)
    (source : driver.Decoded raw)
    (formed : Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed driver.generated.logicFragment driver.leafAdmission formula)
    (cube : driver.profileAdmission = some true) (budget : Nat)
    (enough : workBound driver.backend driver.tests formula source.val ≤ budget) :
    ∃ answer, (check driver formula source budget).readout = .judgment (.decided answer) := by
  obtain ⟨answer, read⟩ := Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission.complete driver.generated driver.profileAdmission driver.backend
    driver.tests driver.leafAdmission formula source.val formed cube source.property.1 budget enough
  exact ⟨answer, congrArg Readout.judgment read⟩

/-- A computable bound is sufficient for every admitted raw source and
formed formula at an admitted generated vertex. -/
theorem search_complete (driver : Driver) (formula : driver.Formula) (raw : Pattern)
    (sourceAdmitted : ∃ source, driver.admitted source ∧ driver.render source = raw)
    (formed : Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed driver.generated.logicFragment driver.leafAdmission formula)
    (cube : driver.profileAdmission = some true) (budget : Nat)
    (enough : ∀ source : driver.Decoded raw,
      workBound driver.backend driver.tests formula source.val ≤ budget) :
    ∃ answer, (search driver formula raw budget).readout = .judgment (.decided answer) := by
  have accepted := driver.decode_complete raw sourceAdmitted
  cases decoded : driver.decode raw with
  | error reason => rw [decoded] at accepted; cases accepted
  | ok source =>
    simpa only [search, decoded] using decoded_complete driver formula raw source formed cube budget (enough source)

theorem conclusive_mono (driver : Driver) (formula : driver.Formula) (raw : Pattern)
    {small large : Nat} (answer : Bool)
    (read : (search driver formula raw small).readout = .judgment (.decided answer))
    (ordered : small ≤ large) :
    (search driver formula raw large).readout = .judgment (.decided answer) := by
  cases decoded : driver.decode raw with
  | error reason => simp [search, decoded, Result.readout] at read
  | ok source =>
    have prior : (Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission.check driver.generated driver.profileAdmission driver.backend driver.tests
        driver.leafAdmission formula source.val small).readout = .decided answer := by
      simpa only [search, decoded, check, Result.readout, Readout.judgment.injEq] using read
    simpa only [search, decoded, check, Result.readout] using congrArg Readout.judgment
      (Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission.conclusive_mono driver.generated driver.profileAdmission driver.backend driver.tests
        driver.leafAdmission formula source.val answer prior ordered)

end Mettapedia.OSLF.NativeTypes.Runtime.Description
