import Mettapedia.OSLF.NativeTypes.Runtime.Description

open Mettapedia.OSLF.Framework

/-!
# Named generated queries

Constructor names resolve through the generated driver's actual catalogue.
The recursive query syntax adds no language-specific checker. Unknown names,
disabled connectives, invalid sources and unfinished search remain distinct
from a proved negative native judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Runtime.Description
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

inductive Query where
  | constructor (name : String)
  | top
  | bottom
  | conj (left right : Query)
  | disj (left right : Query)
  | neg (inner : Query)
  | imp (left right : Query)
  | possibility (inner : Query)
  | outgoingUniversal (inner : Query)
  | separating (name : String) (left right : Query)
  deriving DecidableEq, Repr

private def combine {Item : Type} (operation : Item → Item → Item)
    (left right : Except String Item) : Except String Item :=
  match left, right with
  | .error reason, _ => .error reason
  | .ok _, .error reason => .error reason
  | .ok first, .ok second => .ok (operation first second)

def elaborate (driver : Driver) : Query → Except String driver.Formula
  | .constructor name => match driver.lookup name with
    | none => .error name
    | some leaf => .ok (.atom leaf)
  | .top => .ok .top
  | .bottom => .ok .bottom
  | .conj left right => combine Formula.conj (elaborate driver left) (elaborate driver right)
  | .disj left right => combine Formula.disj (elaborate driver left) (elaborate driver right)
  | .neg inner => (elaborate driver inner).map Formula.neg
  | .imp left right => combine Formula.imp (elaborate driver left) (elaborate driver right)
  | .possibility inner => (elaborate driver inner).map Formula.possibility
  | .outgoingUniversal inner => (elaborate driver inner).map Formula.outgoingUniversal
  | .separating name left right => match driver.spatialLookup name with
    | none => .error name
    | some index => combine (Formula.separating index) (elaborate driver left) (elaborate driver right)

/-- Independent compositional interpretation of catalogue names. -/
inductive Resolves (driver : Driver) : Query → driver.Formula → Prop where
  | constructor {name leaf} (lookup : driver.lookup name = some leaf) :
      Resolves driver (.constructor name) (.atom leaf)
  | top : Resolves driver .top .top
  | bottom : Resolves driver .bottom .bottom
  | conj {left right first second} (leftProof : Resolves driver left first) (rightProof : Resolves driver right second) :
      Resolves driver (.conj left right) (.conj first second)
  | disj {left right first second} (leftProof : Resolves driver left first) (rightProof : Resolves driver right second) :
      Resolves driver (.disj left right) (.disj first second)
  | neg {inner result} (resolved : Resolves driver inner result) : Resolves driver (.neg inner) (.neg result)
  | imp {left right first second} (leftProof : Resolves driver left first) (rightProof : Resolves driver right second) :
      Resolves driver (.imp left right) (.imp first second)
  | possibility {inner result} (resolved : Resolves driver inner result) :
      Resolves driver (.possibility inner) (.possibility result)
  | outgoingUniversal {inner result} (resolved : Resolves driver inner result) :
      Resolves driver (.outgoingUniversal inner) (.outgoingUniversal result)
  | separating {name index left right first second} (lookup : driver.spatialLookup name = some index)
      (leftProof : Resolves driver left first) (rightProof : Resolves driver right second) :
      Resolves driver (.separating name left right) (.separating index first second)

private theorem combine_ok {Item : Type} (operation : Item → Item → Item)
    (left right : Except String Item) (result : Item) :
    combine operation left right = .ok result ↔
      ∃ first second, left = .ok first ∧ right = .ok second ∧ operation first second = result := by
  cases left <;> cases right <;> simp [combine]

private theorem map_ok {Item : Type} (operation : Item → Item)
    (input : Except String Item) (result : Item) :
    input.map operation = .ok result ↔ ∃ value, input = .ok value ∧ operation value = result := by
  cases input <;> simp [Except.map]

theorem elaborate_exact (driver : Driver) (query : Query) (formula : driver.Formula) :
    elaborate driver query = .ok formula ↔ Resolves driver query formula := by
  induction query generalizing formula with
  | constructor name =>
    constructor
    · intro output
      cases found : driver.lookup name with
      | none => simp [elaborate, found] at output
      | some leaf =>
        have equal : Formula.atom leaf = formula := by simpa [elaborate, found] using output
        subst formula
        exact .constructor found
    · intro resolved
      cases resolved with
      | constructor found => simp [elaborate, found]
  | top =>
    constructor
    · intro output
      have equal : (Formula.top : driver.Formula) = formula := Except.ok.inj output
      subst formula
      exact .top
    · intro resolved; cases resolved; rfl
  | bottom =>
    constructor
    · intro output
      have equal : (Formula.bottom : driver.Formula) = formula := Except.ok.inj output
      subst formula
      exact .bottom
    · intro resolved; cases resolved; rfl
  | conj left right leftIH rightIH =>
    rw [elaborate, combine_ok]
    constructor
    · rintro ⟨first, second, firstOk, secondOk, rfl⟩
      exact .conj ((leftIH first).mp firstOk) ((rightIH second).mp secondOk)
    · intro resolved
      cases resolved with
      | conj first second => exact ⟨_, _, (leftIH _).mpr first, (rightIH _).mpr second, rfl⟩
  | disj left right leftIH rightIH =>
    rw [elaborate, combine_ok]
    constructor
    · rintro ⟨first, second, firstOk, secondOk, rfl⟩
      exact .disj ((leftIH first).mp firstOk) ((rightIH second).mp secondOk)
    · intro resolved
      cases resolved with
      | disj first second => exact ⟨_, _, (leftIH _).mpr first, (rightIH _).mpr second, rfl⟩
  | imp left right leftIH rightIH =>
    rw [elaborate, combine_ok]
    constructor
    · rintro ⟨first, second, firstOk, secondOk, rfl⟩
      exact .imp ((leftIH first).mp firstOk) ((rightIH second).mp secondOk)
    · intro resolved
      cases resolved with
      | imp first second => exact ⟨_, _, (leftIH _).mpr first, (rightIH _).mpr second, rfl⟩
  | neg inner ih =>
    rw [elaborate, map_ok]
    constructor
    · rintro ⟨result, output, rfl⟩
      exact .neg ((ih result).mp output)
    · intro resolved
      cases resolved with
      | neg inner => exact ⟨_, (ih _).mpr inner, rfl⟩
  | possibility inner ih =>
    rw [elaborate, map_ok]
    constructor
    · rintro ⟨result, output, rfl⟩
      exact .possibility ((ih result).mp output)
    · intro resolved
      cases resolved with
      | possibility inner => exact ⟨_, (ih _).mpr inner, rfl⟩
  | outgoingUniversal inner ih =>
    rw [elaborate, map_ok]
    constructor
    · rintro ⟨result, output, rfl⟩
      exact .outgoingUniversal ((ih result).mp output)
    · intro resolved
      cases resolved with
      | outgoingUniversal inner => exact ⟨_, (ih _).mpr inner, rfl⟩
  | separating name left right leftIH rightIH =>
    constructor
    · intro output
      cases found : driver.spatialLookup name with
      | none => simp [elaborate, found] at output
      | some index =>
        rw [elaborate, found, combine_ok] at output
        obtain ⟨first, second, firstOk, secondOk, rfl⟩ := output
        exact .separating found ((leftIH first).mp firstOk) ((rightIH second).mp secondOk)
    · intro resolved
      cases resolved with
      | separating found first second =>
        rw [elaborate, found, combine_ok]
        exact ⟨_, _, (leftIH _).mpr first, (rightIH _).mpr second, rfl⟩

theorem resolution_unique {driver : Driver} {query : Query} {first second : driver.Formula}
    (left : Resolves driver query first) (right : Resolves driver query second) : first = second :=
  Except.ok.inj (((elaborate_exact driver query first).mpr left).symm.trans
    ((elaborate_exact driver query second).mpr right))

def Meaning (driver : Driver) (query : Query) (raw : Pattern) : Prop :=
  ∃ formula, Resolves driver query formula ∧ Mettapedia.OSLF.NativeTypes.Runtime.Description.Meaning driver formula raw

inductive Answer (driver : Driver) (query : Query) (raw : Pattern) where
  | unknownConstructor (name : String)
  | checked (formula : driver.Formula) (resolved : Resolves driver query formula)
      (result : Mettapedia.OSLF.NativeTypes.Runtime.Description.Result driver formula raw)

inductive Readout where
  | unknownConstructor (name : String)
  | checked (result : Mettapedia.OSLF.NativeTypes.Runtime.Description.Readout)
  deriving DecidableEq, Repr

def Answer.readout {driver : Driver} {query : Query} {raw : Pattern} : Answer driver query raw → Readout
  | .unknownConstructor name => .unknownConstructor name
  | .checked _ _ result => .checked result.readout

def ask (driver : Driver) (query : Query) (raw : Pattern) (budget : Nat) : Answer driver query raw :=
  match compiled : elaborate driver query with
  | .error name => .unknownConstructor name
  | .ok formula => .checked formula ((elaborate_exact driver query formula).mp compiled)
      (search driver formula raw budget)

theorem ask_readout (driver : Driver) (query : Query) (raw : Pattern) (budget : Nat) :
    (ask driver query raw budget).readout =
      match elaborate driver query with
      | .error name => .unknownConstructor name
      | .ok formula => .checked (search driver formula raw budget).readout := by
  unfold ask
  split <;> rename_i value found <;> simp only [Answer.readout] <;> rw [found]

theorem positive {driver : Driver} {query : Query} {raw : Pattern} (answer : Answer driver query raw)
    (read : answer.readout = .checked (.judgment (.decided true))) : Meaning driver query raw := by
  cases answer with
  | unknownConstructor name => cases read
  | checked formula resolved result =>
    exact ⟨formula, resolved, Mettapedia.OSLF.NativeTypes.Runtime.Description.positive driver formula raw result (Readout.checked.inj read)⟩

theorem negative {driver : Driver} {query : Query} {raw : Pattern} (answer : Answer driver query raw)
    (read : answer.readout = .checked (.judgment (.decided false))) : ¬ Meaning driver query raw := by
  cases answer with
  | unknownConstructor name => cases read
  | checked formula resolved result =>
    rintro ⟨other, otherResolved, holds⟩
    have same := resolution_unique resolved otherResolved
    subst other
    exact Mettapedia.OSLF.NativeTypes.Runtime.Description.negative driver formula raw result (Readout.checked.inj read) holds

theorem complete (driver : Driver) (query : Query) (formula : driver.Formula) (raw : Pattern)
    (resolved : Resolves driver query formula)
    (sourceAdmitted : ∃ source, driver.admitted source ∧ driver.render source = raw)
    (formed : Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed driver.generated.logicFragment driver.leafAdmission formula)
    (cube : driver.profileAdmission = some true) (budget : Nat)
    (enough : ∀ source : driver.Decoded raw,
      workBound driver.backend driver.tests formula source.val ≤ budget) :
    ∃ value, (ask driver query raw budget).readout = .checked (.judgment (.decided value)) := by
  have compiled := (elaborate_exact driver query formula).mpr resolved
  obtain ⟨value, read⟩ := Mettapedia.OSLF.NativeTypes.Runtime.Description.search_complete driver formula raw
    sourceAdmitted formed cube budget enough
  exact ⟨value, by rw [ask_readout, compiled]; exact congrArg Readout.checked read⟩

theorem conclusive_mono (driver : Driver) (query : Query) (raw : Pattern)
    {small large : Nat} (value : Bool)
    (read : (ask driver query raw small).readout = .checked (.judgment (.decided value)))
    (ordered : small ≤ large) :
    (ask driver query raw large).readout = .checked (.judgment (.decided value)) := by
  cases compiled : elaborate driver query with
  | error name => rw [ask_readout, compiled] at read; cases read
  | ok formula =>
    have prior : (search driver formula raw small).readout = .judgment (.decided value) := by
      rw [ask_readout, compiled] at read
      exact Readout.checked.inj read
    have later := Mettapedia.OSLF.NativeTypes.Runtime.Description.conclusive_mono driver formula raw value prior ordered
    rw [ask_readout, compiled]
    exact congrArg Readout.checked later

end Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax
