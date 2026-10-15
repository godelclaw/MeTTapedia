import Mettapedia.Machines.Cursor.SharedFactor

/-!
# Completed PeTTa table and memo view retention

Ordinary completed tables retain their captured answers across world edits.
Memo views additionally require their governing equation edition to match.
Both paths require the caller key and completion status. These checks concern
reuse of already selected, immutable answers; they do not merge independent
choice instances, infer an equation's forwarding eligibility, or reclaim a
reader-owned allocation when a cache entry is evicted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.TableReuse

open Mettapedia.Machines.Cursor.SharedFactor

universe u
variable {Input : Type u}

inductive Mode where
  | tabled
  | memo
  deriving DecidableEq, Repr

structure Entry (Input : Type u) where
  view : View Input
  equationEdition : Nat
  deriving DecidableEq, Repr

def admissible [DecidableEq Input] (mode : Mode) (caller : Input) (edition : Nat)
    (entry : Entry Input) : Bool :=
  entry.view.completed && decide (entry.view.caller = caller) &&
    (mode == .tabled || decide (entry.equationEdition = edition))

def lookup [DecidableEq Input] (mode : Mode) (caller : Input) (edition : Nat)
    (entry : Option (Entry Input)) : Option (View Input) := do
  let selected ← entry
  if admissible mode caller edition selected then some selected.view else none

/-- The static-world table path preserves the captured view, rather than
silently updating it to answers from the current world. -/
theorem completed_table_retained [DecidableEq Input] (entry : Entry Input)
    (complete : entry.view.completed = true) (edition : Nat) :
    lookup .tabled entry.view.caller edition (some entry) = some entry.view := by
  simp [lookup, admissible, complete]

theorem completed_memo_retained [DecidableEq Input] (entry : Entry Input)
    (complete : entry.view.completed = true) :
    lookup .memo entry.view.caller entry.equationEdition (some entry) = some entry.view := by
  simp [lookup, admissible, complete]

theorem changed_memo_edition_refused [DecidableEq Input] (entry : Entry Input)
    (edition : Nat) (different : entry.equationEdition ≠ edition) :
    lookup .memo entry.view.caller edition (some entry) = none := by
  simp [lookup, admissible, different]

theorem unrelated_caller_refused [DecidableEq Input] (entry : Entry Input)
    (mode : Mode) (caller : Input) (edition : Nat) (different : entry.view.caller ≠ caller) :
    lookup mode caller edition (some entry) = none := by
  simp [lookup, admissible, different]

theorem incomplete_not_exhausted [DecidableEq Input] (entry : Entry Input)
    (mode : Mode) (caller : Input) (edition : Nat) (incomplete : entry.view.completed = false) :
    lookup mode caller edition (some entry) = none := by
  simp [lookup, admissible, incomplete]

private def saved : Entry Nat := ⟨⟨7, 0, 2, true⟩, 3⟩

theorem table_and_memo_have_different_update_policies :
    lookup .tabled 7 4 (some saved) = some saved.view ∧
      lookup .memo 7 4 (some saved) = none := by decide

theorem eviction_refuses_cache_lookup :
    lookup .memo 7 3 (none : Option (Entry Nat)) = none := rfl

end Mettapedia.Languages.MeTTa.PeTTa.TableReuse
