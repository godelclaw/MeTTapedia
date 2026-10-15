import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

open Mettapedia.OSLF.Framework

/-!
# Selected logic and cube admission for composite native questions

Formation is specified by inference rules independently of the executable
refusal search. Disabled operations and rejected cube coordinates retain
their specific refusal; unresolved cube obligations and unfinished semantic
work remain unresolved. Every conclusive answer still carries its native proof.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Admission

open Mettapedia.GSLT
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Structural (Connective ConnectiveFragment)
open Mettapedia.OSLF.NativeTypes.Generation (Generated CheckResult)

universe u v w

inductive Refusal where
  | unavailable (connective : Connective)
  | possibility
  | leaf (reason : Mettapedia.OSLF.NativeTypes.Structural.Refusal)
  deriving DecidableEq, Repr

/-- Leaf admission can retain the generated former's carrier, universe and
schema checks. The fragment rules below remain independent of these checks. -/
structure LeafAdmission (Leaf : Type w) where
  admitted : Leaf → Prop
  probe : Leaf → Except Mettapedia.OSLF.NativeTypes.Structural.Refusal Unit
  exact : ∀ leaf, (probe leaf).isOk = true ↔ admitted leaf

inductive Formed {Leaf : Type w} (fragment : ConnectiveFragment)
    (admission : LeafAdmission Leaf) : Formula Leaf → Prop where
  | atom (leaf : Leaf) (accepted : admission.admitted leaf) : Formed fragment admission (.atom leaf)
  | top (enabled : fragment.admits .top = true) : Formed fragment admission .top
  | bottom (enabled : fragment.admits .bottom = true) : Formed fragment admission .bottom
  | conj {first second} (enabled : fragment.admits .conjunction = true)
      (left : Formed fragment admission first) (right : Formed fragment admission second) :
      Formed fragment admission (.conj first second)
  | disj {first second} (enabled : fragment.admits .disjunction = true)
      (left : Formed fragment admission first) (right : Formed fragment admission second) :
      Formed fragment admission (.disj first second)
  | neg {formula} (enabled : fragment.admits .negation = true) (inside : Formed fragment admission formula) :
      Formed fragment admission (.neg formula)
  | imp {first second} (enabled : fragment.admits .implication = true)
      (left : Formed fragment admission first) (right : Formed fragment admission second) :
      Formed fragment admission (.imp first second)
  | possibility {formula} (enabled : fragment.core.possibility = true) (inside : Formed fragment admission formula) :
      Formed fragment admission (.possibility formula)
  | outgoingUniversal {formula} (enabled : fragment.core.modal = true) (inside : Formed fragment admission formula) :
      Formed fragment admission (.outgoingUniversal formula)

def denyUnless (enabled : Bool) (refusal : Refusal) (inside : Option Refusal) : Option Refusal :=
  if enabled then inside else some refusal

private theorem denyUnless_none (enabled : Bool) (refusal : Refusal) (inside : Option Refusal) :
    denyUnless enabled refusal inside = none ↔ enabled = true ∧ inside = none := by
  cases enabled <;> simp [denyUnless]

private theorem optionOr_none (first second : Option Refusal) :
    first.or second = none ↔ first = none ∧ second = none := by
  cases first <;> cases second <;> simp

def firstRefusal {Leaf : Type w} (fragment : ConnectiveFragment)
    (admission : LeafAdmission Leaf) : Formula Leaf → Option Refusal
  | .atom leaf => match admission.probe leaf with
    | .ok _ => none
    | .error reason => some (.leaf reason)
  | .top => denyUnless (fragment.admits .top) (.unavailable .top) none
  | .bottom => denyUnless (fragment.admits .bottom) (.unavailable .bottom) none
  | .conj first second => denyUnless (fragment.admits .conjunction) (.unavailable .conjunction)
      ((firstRefusal fragment admission first).or (firstRefusal fragment admission second))
  | .disj first second => denyUnless (fragment.admits .disjunction) (.unavailable .disjunction)
      ((firstRefusal fragment admission first).or (firstRefusal fragment admission second))
  | .neg formula => denyUnless (fragment.admits .negation) (.unavailable .negation)
      (firstRefusal fragment admission formula)
  | .imp first second => denyUnless (fragment.admits .implication) (.unavailable .implication)
      ((firstRefusal fragment admission first).or (firstRefusal fragment admission second))
  | .possibility formula => denyUnless fragment.core.possibility .possibility (firstRefusal fragment admission formula)
  | .outgoingUniversal formula => denyUnless fragment.core.modal (.unavailable .modal) (firstRefusal fragment admission formula)

theorem firstRefusal_exact {Leaf : Type w} (fragment : ConnectiveFragment)
    (admission : LeafAdmission Leaf) (formula : Formula Leaf) :
    firstRefusal fragment admission formula = none ↔ Formed fragment admission formula := by
  induction formula with
  | atom leaf =>
    have probeExact := admission.exact leaf
    cases found : admission.probe leaf with
    | error reason =>
      constructor
      · simp [firstRefusal, found]
      · intro formed
        cases formed with
        | atom _ accepted =>
          have impossible := probeExact.mpr accepted
          rw [found] at impossible
          cases impossible
    | ok value =>
      constructor
      · intro _; exact .atom leaf (probeExact.mp (by rw [found]; rfl))
      · intro _; simp [firstRefusal, found]
  | top =>
    rw [firstRefusal, denyUnless_none]
    constructor
    · intro enabled; exact .top enabled.1
    · intro formed; cases formed with | top enabled => exact ⟨enabled, rfl⟩
  | bottom =>
    rw [firstRefusal, denyUnless_none]
    constructor
    · intro enabled; exact .bottom enabled.1
    · intro formed; cases formed with | bottom enabled => exact ⟨enabled, rfl⟩
  | conj first second left right =>
    rw [firstRefusal, denyUnless_none, optionOr_none, left, right]
    constructor
    · rintro ⟨enabled, first, second⟩; exact .conj enabled first second
    · intro formed; cases formed with | conj enabled first second => exact ⟨enabled, first, second⟩
  | disj first second left right =>
    rw [firstRefusal, denyUnless_none, optionOr_none, left, right]
    constructor
    · rintro ⟨enabled, first, second⟩; exact .disj enabled first second
    · intro formed; cases formed with | disj enabled first second => exact ⟨enabled, first, second⟩
  | neg formula ih =>
    rw [firstRefusal, denyUnless_none, ih]
    constructor
    · rintro ⟨enabled, inside⟩; exact .neg enabled inside
    · intro formed; cases formed with | neg enabled inside => exact ⟨enabled, inside⟩
  | imp first second left right =>
    rw [firstRefusal, denyUnless_none, optionOr_none, left, right]
    constructor
    · rintro ⟨enabled, first, second⟩; exact .imp enabled first second
    · intro formed; cases formed with | imp enabled first second => exact ⟨enabled, first, second⟩
  | possibility formula ih =>
    rw [firstRefusal, denyUnless_none, ih]
    constructor
    · rintro ⟨enabled, inside⟩; exact .possibility enabled inside
    · intro formed; cases formed with | possibility enabled inside => exact ⟨enabled, inside⟩
  | outgoingUniversal formula ih =>
    rw [firstRefusal, denyUnless_none, ih]
    constructor
    · rintro ⟨enabled, inside⟩; exact .outgoingUniversal enabled inside
    · intro formed; cases formed with | outgoingUniversal enabled inside => exact ⟨enabled, inside⟩

inductive Verdict (statement : Prop) : Type where
  | semantic (result : Outcome statement)
  | refused (reason : Refusal)
  | rejectedCube
  | unresolvedCube

def Verdict.readout {statement : Prop} : Verdict statement → CheckResult
  | .semantic result => match result.answer with
    | some answer => .decided answer
    | none => .unknown
  | .refused (.unavailable connective) => .refused connective
  | .refused .possibility => .refusedPossibility
  | .refused (.leaf reason) => .illFormed reason
  | .rejectedCube => .rejectedCube
  | .unresolvedCube => .unknown

def check {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (generated : Generated) (backend : Backend.{u,v} system admitted)
    (tests : Leaf → Test system admitted) (admission : LeafAdmission Leaf)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat) :
    Verdict (denotation tests formula source) :=
  match firstRefusal generated.logicFragment admission formula with
  | some reason => .refused reason
  | none => match generated.equationAdmission with
    | some true => .semantic (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check backend tests formula source budget)
    | some false => .rejectedCube
    | none => .unresolvedCube

theorem positive {statement : Prop} (result : Verdict statement)
    (read : result.readout = .decided true) : statement := by
  cases result with
  | semantic result =>
    cases found : result.answer with
    | none => simp [Verdict.readout, found] at read
    | some answer =>
      have equal : answer = true := by simpa [Verdict.readout, found] using read
      exact result.positive (by simpa [equal] using found)
  | refused reason => cases reason <;> simp [Verdict.readout] at read
  | rejectedCube => simp [Verdict.readout] at read
  | unresolvedCube => simp [Verdict.readout] at read

theorem negative {statement : Prop} (result : Verdict statement)
    (read : result.readout = .decided false) : ¬ statement := by
  cases result with
  | semantic result =>
    cases found : result.answer with
    | none => simp [Verdict.readout, found] at read
    | some answer =>
      have equal : answer = false := by simpa [Verdict.readout, found] using read
      exact result.negative (by simpa [equal] using found)
  | refused reason => cases reason <;> simp [Verdict.readout] at read
  | rejectedCube => simp [Verdict.readout] at read
  | unresolvedCube => simp [Verdict.readout] at read

theorem complete {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (generated : Generated) (backend : Backend.{u,v} system admitted)
    (tests : Leaf → Test system admitted) (admission : LeafAdmission Leaf)
    (formula : Formula Leaf) (source : system.Term)
    (formed : Formed generated.logicFragment admission formula)
    (cube : generated.equationAdmission = some true) (sourceAdmitted : admitted source)
    (budget : Nat) (enough : workBound backend tests formula source ≤ budget) :
    ∃ answer, (check generated backend tests admission formula source budget).readout = .decided answer := by
  have accepted := (firstRefusal_exact generated.logicFragment admission formula).mpr formed
  obtain ⟨answer, read⟩ := Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.checked_complete backend tests formula source sourceAdmitted budget enough
  exact ⟨answer, by simp [check, accepted, cube, Verdict.readout, read]⟩

theorem conclusive_mono {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (generated : Generated) (backend : Backend.{u,v} system admitted)
    (tests : Leaf → Test system admitted) (admission : LeafAdmission Leaf)
    (formula : Formula Leaf) (source : system.Term) {small large : Nat} (answer : Bool)
    (read : (check generated backend tests admission formula source small).readout = .decided answer)
    (ordered : small ≤ large) :
    (check generated backend tests admission formula source large).readout = .decided answer := by
  unfold check at read ⊢
  cases refusal : firstRefusal generated.logicFragment admission formula with
  | some reason => cases reason <;> simp [refusal, Verdict.readout] at read
  | none =>
    cases cube : generated.equationAdmission with
    | none => simp [refusal, cube, Verdict.readout] at read
    | some value =>
      cases value with
      | false => simp [refusal, cube, Verdict.readout] at read
      | true =>
        simp only [refusal, cube, Verdict.readout] at read ⊢
        cases found : (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check backend tests formula source small).answer with
        | none => simp [found] at read
        | some value =>
          have equal : value = answer := by simpa [found] using read
          have enlarged := Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.conclusive_mono backend tests formula source answer
            (by simpa [equal] using found) ordered
          simp [enlarged]

theorem refused_exact {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (generated : Generated) (backend : Backend.{u,v} system admitted)
    (tests : Leaf → Test system admitted) (admission : LeafAdmission Leaf)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat) (reason : Refusal)
    (refusal : firstRefusal generated.logicFragment admission formula = some reason) :
    check generated backend tests admission formula source budget = .refused reason := by
  simp [check, refusal]

end Mettapedia.OSLF.NativeTypes.Decision.Admission
