import Mettapedia.Languages.MeTTa.PeTTa.Effects

/-!
# Pattern removal through ordered exact deletion

A private sequential ground-row space may implement one pattern removal by
taking its ordered matching snapshot and deleting each selected occurrence
exactly once. Repeated rows stay repeated in the snapshot. This construction
preserves the final row list, including its order, but not intermediate
observations, atomic publication or the number of deletion operations.

The theorem qualifies the row transformation used by the explicit dialect
adapter. It is not verification of a native matcher, allocator or C execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.PatternRemovalTransport

universe u
variable {Row : Type u} [BEq Row]

/-- Delete one concrete occurrence for each occurrence in the snapshot. -/
def eraseSnapshot (rows selected : List Row) : List Row :=
  selected.foldl (fun current row => current.erase row) rows

private theorem eraseSnapshot_step (rows : List Row) (first : Row) (rest : List Row) :
    eraseSnapshot rows (first :: rest) = eraseSnapshot (rows.erase first) rest := rfl

variable [LawfulBEq Row]

private theorem eraseSnapshot_cons (row : Row) (rows selected : List Row)
    (absent : row ∉ selected) :
    eraseSnapshot (row :: rows) selected = row :: eraseSnapshot rows selected := by
  induction selected generalizing rows with
  | nil => rfl
  | cons first rest ih =>
      have distinct : first ≠ row := by
        intro same
        subst first
        exact absent (by simp)
      have restAbsent : row ∉ rest := fun member => absent (by simp [member])
      have separate : ¬(row == first) := by
        simpa only [beq_iff_eq] using Ne.symm distinct
      simp only [eraseSnapshot_step, List.erase_cons_tail separate]
      exact ih _ restAbsent

/-- Ordered matching followed by exact deletion equals the original pattern
filter. The result retains unselected occurrences in their original order. -/
theorem eraseSnapshot_filter (rows : List Row) (selected : Row → Bool) :
    eraseSnapshot rows (rows.filter selected) = rows.filter (fun row => !selected row) := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
      cases chosen : selected first with
      | true => simpa [List.filter_cons, chosen, eraseSnapshot] using ih
      | false =>
          have absent : first ∉ rest.filter selected := by
            simp [List.mem_filter, chosen]
          simpa [List.filter_cons, chosen, eraseSnapshot_cons first rest _ absent] using
            congrArg (List.cons first) ih

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State removalMatches)
open NamedSpaces (Handle)

/-- The translated private-space operation computes its snapshot before any
deletion. Its final store uses the existing store update operation. -/
def eraseThroughSnapshot (before : State) (handle : Handle) (pattern : Atom) :
    Option State := do
  let rows ← before.read handle
  let selected := rows.filter (removalMatches pattern)
  before.write handle (eraseSnapshot rows selected)

theorem eraseThroughSnapshot_eq (before : State) (handle : Handle) (pattern : Atom) :
    eraseThroughSnapshot before handle pattern = Effects.erase before handle pattern := by
  simp only [eraseThroughSnapshot, Effects.erase, eraseSnapshot_filter]

/-- The space and cell frame laws belong to the very same final store. -/
theorem eraseThroughSnapshot_frame {before after : State} {handle : Handle} {pattern : Atom}
    (erased : eraseThroughSnapshot before handle pattern = some after) :
    (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  rw [eraseThroughSnapshot_eq] at erased
  exact ⟨fun other different => Effects.erase_read_other erased different,
    Effects.erase_preserves_cells erased⟩

/-- A concrete snapshot retains duplicate occurrences; collapsing them into
support before deletion would leave a stale row behind. -/
example : eraseSnapshot [1, 1, 2] ([1, 1, 2].filter (· == 1)) = [2] := by decide

example : eraseSnapshot [1, 1, 2] [1] ≠ [2] := by decide

/-- Endpoint agreement does not make the target's operation count one. -/
example : ([1, 1, 2].filter (· == 1)).length = 2 := by decide

example (rows : List Atom) (name : String) :
    eraseSnapshot rows (rows.filter (removalMatches (.var name))) = rows := by
  change eraseSnapshot rows (rows.filter (fun _ => false)) = rows
  simp [eraseSnapshot]

end Mettapedia.Languages.MeTTa.PeTTa.PatternRemovalTransport
