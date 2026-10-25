import Mettapedia.Machines.ContextualSequenceObservation

/-!
# Root observations over globally named cells

A compiled region already names its variables globally within its live cursor.
Its root observer follows that cell store directly, without constructing a
second substitution state. The query below records every cell lookup, stops at
an expression without visiting its children, and refines the independent full
image relation. Root-decreasing stores give a constructive termination bound.

Fuel here bounds the model's alias walk, not language evaluation fuel. Native
cursor lifetime, cell-index validity, occurs checking and emitted C refinement
remain implementation obligations. Constructor classification and its query
bounds are provided by ContextualSequenceObservation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CellRootObservation

open ContextualSequenceObservation

abbrev CellStore (Literal : Type) := Nat → Option (Term Nat Literal)

variable {Literal : Type}

def lexicalStore (cells : CellStore Literal) : Store Unit Nat Literal :=
  fun _ cell => (cells cell).map fun value => ⟨value, ()⟩

def query : Nat → Term Nat Literal →
    ReadOnlyQuery.Program Nat (Option (Term Nat Literal)) (Option (Term Nat Literal))
  | 0, _ => .pure none
  | fuel + 1, .var cell => .read cell fun stored =>
      match stored with
      | none => .pure (some (.var cell))
      | some entered => query fuel entered
  | _ + 1, value => .pure (some value)

theorem query_sound (cells : CellStore Literal) (fuel : Nat)
    (source target : Term Nat Literal)
    (found : (ReadOnlyQuery.run cells (query fuel source)).answer = some target) :
    RootRead (lexicalStore cells) ⟨source, ()⟩ ⟨target, ()⟩ := by
  induction fuel generalizing source target with
  | zero => simp [query, ReadOnlyQuery.run] at found
  | succ fuel ih =>
    cases source with
    | leaf literal =>
      simp only [query, ReadOnlyQuery.run, Option.some.injEq] at found
      subst target
      exact .leaf
    | expr fields =>
      simp only [query, ReadOnlyQuery.run, Option.some.injEq] at found
      subst target
      exact .expression
    | var cell =>
      cases stored : cells cell with
      | none =>
        simp only [query, ReadOnlyQuery.run, stored, Option.some.injEq] at found
        subst target
        exact .free (by simp [lexicalStore, stored])
      | some entered =>
        simp only [query, ReadOnlyQuery.run, stored] at found
        exact .binding (by simp [lexicalStore, stored]) (ih entered target found)

theorem query_read_bound (cells : CellStore Literal) (fuel : Nat)
    (source : Term Nat Literal) :
    (ReadOnlyQuery.run cells (query fuel source)).reads.length ≤ fuel := by
  induction fuel generalizing source with
  | zero => simp [query, ReadOnlyQuery.run]
  | succ fuel ih =>
    cases source with
    | leaf _ => simp [query, ReadOnlyQuery.run]
    | expr _ => simp [query, ReadOnlyQuery.run]
    | var cell =>
      cases stored : cells cell with
      | none => simp [query, ReadOnlyQuery.run, stored]
      | some entered => simpa [query, ReadOnlyQuery.run, stored] using Nat.succ_le_succ (ih entered)

def rootRank (rank : Nat → Nat) : Term Nat Literal → Nat
  | .var cell => rank cell + 1
  | .leaf _ => 0
  | .expr _ => 0

def RootDecreasing (cells : CellStore Literal) (rank : Nat → Nat) : Prop :=
  ∀ cell entered, cells cell = some entered →
    rootRank rank entered < rootRank rank (.var cell : Term Nat Literal)

theorem query_complete_of_rank (cells : CellStore Literal) (rank : Nat → Nat)
    (decreasing : RootDecreasing cells rank) (fuel : Nat) (source : Term Nat Literal)
    (enough : rootRank rank source < fuel) :
    ∃ target, (ReadOnlyQuery.run cells (query fuel source)).answer = some target := by
  induction fuel generalizing source with
  | zero => omega
  | succ fuel ih =>
    cases source with
    | leaf literal => exact ⟨.leaf literal, rfl⟩
    | expr fields => exact ⟨.expr fields, rfl⟩
    | var cell =>
      cases stored : cells cell with
      | none => exact ⟨.var cell, by simp [query, ReadOnlyQuery.run, stored]⟩
      | some entered =>
        have smaller := decreasing cell entered stored
        obtain ⟨target, found⟩ := ih entered (by omega)
        exact ⟨target, by simpa [query, ReadOnlyQuery.run, stored] using found⟩

theorem successful_query_preserves_full_image (cells : CellStore Literal)
    (fuel : Nat) (source target : Term Nat Literal)
    (found : (ReadOnlyQuery.run cells (query fuel source)).answer = some target)
    (result : Term (Unit × Nat) Literal) :
    Image (lexicalStore cells) ⟨source, ()⟩ result ↔
      Image (lexicalStore cells) ⟨target, ()⟩ result :=
  root_image_iff (query_sound cells fuel source target found) result

theorem successful_query_preserves_shape (cells : CellStore Literal)
    (fuel : Nat) (source target : Term Nat Literal)
    (found : (ReadOnlyQuery.run cells (query fuel source)).answer = some target)
    (result : Term (Unit × Nat) Literal)
    (whole : Image (lexicalStore cells) ⟨source, ()⟩ result) :
    rootShape target = rootShape result :=
  root_shape_refines_full_image (query_sound cells fuel source target found) whole

/-- An expression observation does not read its cells, regardless of width. -/
theorem expression_needs_no_cell_reads (cells : CellStore Literal) (fuel : Nat)
    (fields : List (Term Nat Literal)) :
    ReadOnlyQuery.run cells (query (fuel + 1) (.expr fields)) =
      ⟨some (.expr fields), []⟩ := rfl

/-- Reuse is valid under the exact reads, rather than a previous source state. -/
theorem unchanged_cell_reads_preserve_query (first second : CellStore Literal)
    (fuel : Nat) (source : Term Nat Literal)
    (unchanged : ReadOnlyQuery.Agrees second
      (ReadOnlyQuery.run first (query fuel source)).reads) :
    ReadOnlyQuery.run second (query fuel source) =
      ReadOnlyQuery.run first (query fuel source) :=
  ReadOnlyQuery.run_eq_of_agrees first second (query fuel source) unchanged

def chain (length : Nat) : CellStore Nat := fun cell =>
  if cell < length then some (.var (cell + 1)) else some (.expr [.leaf 7, .var 99])

theorem chain_example :
    (ReadOnlyQuery.run (chain 3) (query 5 (.var 0))).answer =
      some (.expr [.leaf 7, .var 99]) := by rfl

theorem chain_cost_example :
    (ReadOnlyQuery.run (chain 3) (query 5 (.var 0))).reads.length = 4 := by decide

theorem insufficient_fuel_is_not_absence :
    (ReadOnlyQuery.run (chain 3) (query 4 (.var 0))).answer = none := by decide

def cycle : CellStore Nat := fun cell => if cell = 0 then some (.var 0) else none

theorem cycle_declines (fuel : Nat) :
    (ReadOnlyQuery.run cycle (query fuel (.var 0))).answer = none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [query, ReadOnlyQuery.run, cycle] using ih

theorem changed_alias_changes_shape :
    (ReadOnlyQuery.run (fun _ => some (.expr [.leaf 1] : Term Nat Nat))
      (query 2 (.var 0))).answer ≠
    (ReadOnlyQuery.run (fun _ => some (.expr [.leaf 1, .leaf 2] : Term Nat Nat))
      (query 2 (.var 0))).answer := by simp [query, ReadOnlyQuery.run]

end Mettapedia.Machines.CellRootObservation
