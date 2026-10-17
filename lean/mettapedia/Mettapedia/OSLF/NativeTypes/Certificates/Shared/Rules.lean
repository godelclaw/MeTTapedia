import Mettapedia.OSLF.NativeTypes.Certificates.FiniteTree

/-!
# Checked sharing of finite rule evidence

Rows refer to earlier rows by position. Every premise slot is checked against
its independent rule judgment, including repeated slots. A successful decoder
constructs an ordinary derivation in the original presentation. Sharing does
not identify operational events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.Shared

open Mettapedia.TypeTheory

universe u
variable {P : Presentation.{u}}

structure Row (P : Presentation.{u}) where
  rule : P.Rule
  references : Fin (P.premises rule).length → Nat

abbrev Entry (P : Presentation.{u}) := Sigma P.Derivation

variable [DecidableEq P.Judgment]

def lookup? (table : List (Entry P)) (position : Nat) (wanted : P.Judgment) :
    Option (P.Derivation wanted) :=
  match table[position]? with
  | none => none
  | some ⟨actual, tree⟩ => if same : actual = wanted then some (same ▸ tree) else none

/-- Independent row validity checks only referenced judgments and earlier-row
bounds. It is not a global derivability premise. -/
def ValidRow (table : List P.Judgment) (row : Row P) : Prop :=
  ∀ position, table[row.references position]? = some ((P.premises row.rule).get position)

def allFin? : {n : Nat} → (F : Fin n → Type u) → ((position : Fin n) → Option (F position)) →
    Option ((position : Fin n) → F position)
  | 0, _, _ => some (fun position => nomatch position)
  | n + 1, F, select => do
      let first ← select 0
      let rest ← allFin? (fun position : Fin n => F position.succ) (fun position => select position.succ)
      pure (Fin.cases first rest)

theorem allFin?_some {n : Nat} {F : Fin n → Type u} {select : (position : Fin n) → Option (F position)}
    {values : (position : Fin n) → F position}
    (found : allFin? F select = some values) (position : Fin n) : select position = some (values position) := by
  induction n with
  | zero => exact Fin.elim0 position
  | succ n ih =>
      unfold allFin? at found
      obtain ⟨first, atFirst, later⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨rest, atRest, same⟩ := Option.bind_eq_some_iff.mp later
      cases Option.some.inj same
      cases position using Fin.cases with
      | zero => exact atFirst
      | succ position => exact ih atRest position

theorem allFin?_complete {n : Nat} {F : Fin n → Type u} {select : (position : Fin n) → Option (F position)}
    (present : ∀ position, (select position).isSome = true) : (allFin? F select).isSome = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have head := present 0
      have tail := ih (fun position => present position.succ)
      cases first : select 0 with
      | none => rw [first] at head; cases head
      | some value =>
          cases rest : allFin? (fun position : Fin n => F position.succ) (fun position => select position.succ) with
          | none => rw [rest] at tail; cases tail
          | some values =>
              simp only [allFin?, first, rest]
              rfl

def decodeRow? (table : List (Entry P)) (row : Row P) : Option (Entry P) := do
  let children ← allFin? (fun position => P.Derivation ((P.premises row.rule).get position))
    (fun position => lookup? table (row.references position) ((P.premises row.rule).get position))
  pure ⟨P.conclusion row.rule, .node ⟨row.rule, rfl⟩ (fun position => children position.down)⟩

def decodeFrom? (table : List (Entry P)) : List (Row P) → Option (List (Entry P))
  | [] => some table
  | row :: rest => do
      let entry ← decodeRow? table row
      decodeFrom? (table ++ [entry]) rest

structure Certificate (P : Presentation.{u}) where
  rows : List (Row P)
  root : Nat

def reconstruct? (certificate : Certificate P) (wanted : P.Judgment) : Option (P.Derivation wanted) := do
  let table ← decodeFrom? [] certificate.rows
  lookup? table certificate.root wanted

def check (certificate : Certificate P) (wanted : P.Judgment) : Bool :=
  (reconstruct? certificate wanted).isSome

theorem accepted_original (certificate : Certificate P) (wanted : P.Judgment)
    (accepted : check certificate wanted = true) :
    ∃ derivation : P.Derivation wanted, reconstruct? certificate wanted = some derivation ∧
      Tree.check (Tree.erase derivation) wanted = true := by
  cases found : reconstruct? certificate wanted with
  | none => simp only [check, found, Option.isSome_none] at accepted; cases accepted
  | some tree => exact ⟨tree, rfl, Tree.check_erase tree⟩

/-! ## Direct checking with a judgment-only table -/

/-- Inspect the actual premise slots in order, stopping at the first refused
reference. The second component counts performed slot checks, including a
failing slot. It does not price list lookup or judgment equality. -/
def inspectPremises (table : List P.Judgment) (row : Row P) :
    List (Fin (P.premises row.rule).length) → Bool × Nat
  | [] => (true, 0)
  | position :: rest =>
      if table[row.references position]? = some ((P.premises row.rule).get position) then
        let later := inspectPremises table row rest
        (later.1, later.2 + 1)
      else (false, 1)

def inspectRow (table : List P.Judgment) (row : Row P) : Bool × Nat :=
  inspectPremises table row (List.finRange (P.premises row.rule).length)

/-- Actual execution data of the plain-table checker. No derivation, proof
function or expanded certificate is stored in the returned table. -/
structure JudgmentCheck (P : Presentation.{u}) where
  table : Option (List P.Judgment)
  rows : Nat
  premiseChecks : Nat

/-- Every row is validated before appending its literal conclusion. A bad
unused row refuses as it does in the original reconstruction checker. -/
def inspectRows (table : List P.Judgment) : List (Row P) → JudgmentCheck P
  | [] => ⟨some table, 0, 0⟩
  | row :: rest =>
      let inspected := inspectRow table row
      if inspected.1 then
        let later := inspectRows (table ++ [P.conclusion row.rule]) rest
        ⟨later.table, later.rows + 1, inspected.2 + later.premiseChecks⟩
      else ⟨none, 1, inspected.2⟩

/-- Static inventory of the certificate's premise occurrences. Unlike the
performed counter, it includes slots after a refusal. -/
def premiseSlots (rows : List (Row P)) : Nat :=
  (rows.map (fun row => (P.premises row.rule).length)).sum

/-- The final root comparison is counted separately from premise checks.
The counts describe this implementation's control flow; they are not machine
steps and carry no uncharged equality-cost hypothesis. -/
def checkJudgmentsWithWork (certificate : Certificate P) (wanted : P.Judgment) : Bool × Nat × Nat :=
  let inspected := inspectRows [] certificate.rows
  match inspected.table with
  | none => (false, inspected.rows, inspected.premiseChecks)
  | some table => (decide (table[certificate.root]? = some wanted),
      inspected.rows, inspected.premiseChecks + 1)

def checkJudgments (certificate : Certificate P) (wanted : P.Judgment) : Bool :=
  (checkJudgmentsWithWork certificate wanted).1

end Mettapedia.OSLF.NativeTypes.Certificates.Shared
