import Mettapedia.Machines.Cursor.TailSummary
import Mettapedia.Machines.UnboundSubtermSubstitution
import Mathlib.Tactic

/-!
# Reusing singleton support inside an ordered frame inventory

The reference visits constructor children right to left, retaining each
qualified cell at its first occurrence. Qualification may discard a cell or
attach its lexical frame. The constructor summary is computed independently
from the term. A singleton subtree contributes exactly one inventory update;
it does not require another traversal of its internal occurrences.

The work model counts visited term nodes after summaries are available. It
excludes summary construction, native set probes, allocation and frame-store
updates. Native metadata truthfulness, immutable DAG representation and C
lifetimes remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SubtreeSupportInventory

open Cursor.TailSummary

abbrev Term := UnboundSubtermSubstitution.Term Nat Unit

def summary : Term → Vars
  | .literal _ => .none
  | .var cell => .one cell
  | .pair left right => Vars.join (summary left) (summary right)

variable {Key : Type*} [DecidableEq Key]

def insert (qualify : Nat → Option Key) (cell : Nat) (known : List Key) : List Key :=
  match qualify cell with
  | none => known
  | some key => if key ∈ known then known else known ++ [key]

theorem insert_idempotent (qualify : Nat → Option Key) (cell : Nat) (known : List Key) :
    insert qualify cell (insert qualify cell known) = insert qualify cell known := by
  cases observed : qualify cell with
  | none => simp [insert, observed]
  | some key =>
      by_cases present : key ∈ known <;> simp [insert, observed, present]

def reference (qualify : Nat → Option Key) : Term → List Key → List Key
  | .literal _, known => known
  | .var cell, known => insert qualify cell known
  | .pair left right, known => reference qualify left (reference qualify right known)

theorem precise_summary_reference (qualify : Nat → Option Key) (term : Term) :
    ∀ known, summary term ≠ .many →
      reference qualify term known =
        match summary term with
        | .none => known
        | .one cell => insert qualify cell known
        | .many => known := by
  induction term with
  | literal value => simp [summary, reference]
  | var cell => simp [summary, reference]
  | pair left right ihLeft ihRight =>
      intro known precise
      cases leftSummary : summary left <;> cases rightSummary : summary right
      all_goals simp_all [summary, Vars.join, reference]
      all_goals simp_all [insert_idempotent]

def collect (qualify : Nat → Option Key) : Term → List Key → List Key
  | .literal _, known => known
  | .var cell, known => insert qualify cell known
  | .pair left right, known =>
      match summary (.pair left right) with
      | .none => known
      | .one cell => insert qualify cell known
      | .many => collect qualify left (collect qualify right known)

theorem collect_eq_reference (qualify : Nat → Option Key) (term : Term) (known : List Key) :
    collect qualify term known = reference qualify term known := by
  induction term generalizing known with
  | literal value => rfl
  | var cell => rfl
  | pair left right ihLeft ihRight =>
      cases observed : summary (.pair left right) with
      | none =>
          simpa [collect, observed] using
            (precise_summary_reference qualify (.pair left right) known (by simp [observed])).symm
      | one cell =>
          simpa [collect, observed] using
            (precise_summary_reference qualify (.pair left right) known (by simp [observed])).symm
      | many => simp [collect, observed, reference, ihLeft, ihRight]

theorem singleton_collect (qualify : Nat → Option Key) (term : Term) (cell : Nat)
    (single : summary term = .one cell) (known : List Key) :
    collect qualify term known = insert qualify cell known := by
  rw [collect_eq_reference]
  simpa [single] using precise_summary_reference qualify term known (by simp [single])

theorem closed_collect (qualify : Nat → Option Key) (term : Term)
    (closed : summary term = .none) (known : List Key) :
    collect qualify term known = known := by
  rw [collect_eq_reference]
  simpa [closed] using precise_summary_reference qualify term known (by simp [closed])

def demand (qualify : Nat → Option Key) : Term → Finset Key
  | .literal _ => ∅
  | .var cell => match qualify cell with
    | none => ∅
    | some key => {key}
  | .pair left right => demand qualify left ∪ demand qualify right

theorem insert_inventory (qualify : Nat → Option Key) (cell : Nat) (known : List Key) :
    (insert qualify cell known).toFinset = known.toFinset ∪ demand qualify (.var cell) := by
  cases observed : qualify cell with
  | none => simp [insert, demand, observed]
  | some key =>
      by_cases present : key ∈ known <;>
        simp [insert, demand, observed, present, Finset.union_singleton]

theorem insert_nodup (qualify : Nat → Option Key) (cell : Nat) (known : List Key)
    (unique : known.Nodup) : (insert qualify cell known).Nodup := by
  cases observed : qualify cell with
  | none => simpa [insert, observed] using unique
  | some key =>
      by_cases present : key ∈ known
      · simpa [insert, observed, present] using unique
      · simp only [insert, observed, if_neg present]
        apply unique.append (by simp)
        intro item member singleton
        have same : item = key := by simpa using singleton
        exact present (same ▸ member)

theorem reference_inventory (qualify : Nat → Option Key) (term : Term) (known : List Key) :
    (reference qualify term known).toFinset = known.toFinset ∪ demand qualify term := by
  induction term generalizing known with
  | literal value => simp [reference, demand]
  | var cell => exact insert_inventory qualify cell known
  | pair left right ihLeft ihRight =>
      simp [reference, demand, ihLeft, ihRight,
        Finset.union_left_comm, Finset.union_comm]

theorem reference_nodup (qualify : Nat → Option Key) (term : Term) (known : List Key)
    (unique : known.Nodup) : (reference qualify term known).Nodup := by
  induction term generalizing known with
  | literal value => exact unique
  | var cell => exact insert_nodup qualify cell known unique
  | pair left right ihLeft ihRight => exact ihLeft _ (ihRight _ unique)

theorem collect_length (qualify : Nat → Option Key) (term : Term) (known : List Key)
    (unique : known.Nodup) :
    (collect qualify term known).length =
      known.length + (demand qualify term \ known.toFinset).card := by
  rw [collect_eq_reference]
  calc
    (reference qualify term known).length =
        (reference qualify term known).toFinset.card :=
      (List.toFinset_card_of_nodup (reference_nodup qualify term known unique)).symm
    _ = (known.toFinset ∪ demand qualify term).card := by rw [reference_inventory]
    _ = (demand qualify term \ known.toFinset).card + known.toFinset.card := by
      rw [Finset.union_comm]
      exact (Finset.card_sdiff_add_card _ _).symm
    _ = known.length + (demand qualify term \ known.toFinset).card := by
      rw [List.toFinset_card_of_nodup unique, Nat.add_comm]

/-- Any successful publication trace must name every demanded coordinate
that was absent initially; duplicates cannot reduce its event count. -/
theorem publication_lower_bound (qualify : Nat → Option Key) (term : Term)
    (known events : List Key)
    (covers : demand qualify term ⊆ known.toFinset ∪ events.toFinset) :
    (demand qualify term \ known.toFinset).card ≤ events.length := by
  have included : demand qualify term \ known.toFinset ⊆ events.toFinset := by
    intro key member
    obtain ⟨needed, absent⟩ := Finset.mem_sdiff.mp member
    rcases Finset.mem_union.mp (covers needed) with old | published
    · exact (absent old).elim
    · exact published
  exact (Finset.card_le_card included).trans (List.toFinset_card_le events)

/-- The inventory performs the minimum number of new-coordinate publications
in the stated event model. It is not a bound on total native execution cost. -/
theorem collect_minimal_publications (qualify : Nat → Option Key) (term : Term)
    (known events : List Key) (unique : known.Nodup)
    (covers : demand qualify term ⊆ known.toFinset ∪ events.toFinset) :
    (collect qualify term known).length - known.length ≤ events.length := by
  rw [collect_length qualify term known unique]
  simpa using publication_lower_bound qualify term known events covers

def referenceVisits : Term → Nat
  | .literal _ | .var _ => 1
  | .pair left right => 1 + referenceVisits left + referenceVisits right

def visits : Term → Nat
  | .literal _ | .var _ => 1
  | .pair left right =>
      match summary (.pair left right) with
      | .none | .one _ => 1
      | .many => 1 + visits left + visits right

theorem visits_positive (term : Term) : 1 ≤ visits term := by
  cases term with
  | literal value => rfl
  | var cell => rfl
  | pair left right =>
      cases observed : summary (.pair left right) with
      | none => simp [visits, observed]
      | one cell => simp [visits, observed]
      | many => simp only [visits, observed]; omega

theorem visits_le_reference (term : Term) : visits term ≤ referenceVisits term := by
  induction term with
  | literal value => rfl
  | var cell => rfl
  | pair left right ihLeft ihRight =>
      cases observed : summary (.pair left right) <;>
        simp_all [visits, referenceVisits] <;> omega

theorem singleton_one_visit (term : Term) (cell : Nat) (single : summary term = .one cell) :
    visits term = 1 := by
  cases term with
  | literal value => rfl
  | var atCell => rfl
  | pair left right => simp [visits, single]

def spine (cell : Nat) : Nat → Term
  | 0 => .var cell
  | depth + 1 => .pair (.literal ()) (spine cell depth)

theorem spine_summary (cell depth : Nat) : summary (spine cell depth) = .one cell := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [spine, summary, ih, Vars.join]

theorem spine_reference_visits (cell depth : Nat) :
    referenceVisits (spine cell depth) = 2 * depth + 1 := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [spine, referenceVisits, ih]; omega

theorem spine_one_visit (cell depth : Nat) : visits (spine cell depth) = 1 :=
  singleton_one_visit _ cell (spine_summary cell depth)

theorem mixed_spines_visits (left right depth : Nat) (distinct : left ≠ right) :
    visits (.pair (spine left depth) (spine right depth)) = 3 := by
  simp [visits, summary, spine_summary, Vars.join, distinct, spine_one_visit]

theorem mixed_spines_reference_visits (left right depth : Nat) :
    referenceVisits (.pair (spine left depth) (spine right depth)) = 4 * depth + 3 := by
  simp [referenceVisits, spine_reference_visits]
  omega

namespace Controls

def qualify (frame : Nat) (cell : Nat) : Option (Nat × Nat) := some (frame, cell)

theorem duplicate_subtrees_keep_first_occurrence_order :
    collect (qualify 7) (.pair (spine 1 8) (spine 2 8)) [] = [(7, 2), (7, 1)] := by decide

theorem existing_coordinates_are_not_appended_again :
    collect (qualify 7) (.pair (spine 1 8) (spine 2 8)) [(7, 1)] = [(7, 1), (7, 2)] := by decide

theorem lexical_frames_remain_distinct :
    collect (qualify 2) (spine 1 8) (collect (qualify 1) (spine 1 8) []) = [(1, 1), (2, 1)] := by
  decide

theorem ignored_coordinates_have_no_effect :
    collect (fun _ => (none : Option Nat)) (.pair (spine 1 8) (spine 2 8)) [4] = [4] := by decide

theorem many_support_cannot_be_replaced_by_one_cell :
    collect (qualify 7) (.pair (.var 1) (.var 2)) [] ≠ insert (qualify 7) 1 [] := by decide

end Controls

end Mettapedia.Machines.SubtreeSupportInventory
