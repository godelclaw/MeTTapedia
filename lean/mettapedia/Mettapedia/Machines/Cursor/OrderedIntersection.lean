import Mettapedia.Machines.Cursor.AlternatingProgress
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeWhile
import Mathlib.Tactic

/-!
# Ordered two-way key intersection

The active iterator starts no later than its peer. A seek skips keys below
the peer, and an emitted match advances past its distinct key. Both actions
rotate the iterators. This executable navigation model returns the ascending
support intersection and derives its alternating progress trace.

`seekTo` specifies the retained suffix, not the native binary-search cost.
Physical duplicate ranges and their weights are handled separately. The
native range iterator must refine these distinct-key projections.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.OrderedIntersection

open AlternatingProgress

variable {Key : Type*} [LinearOrder Key]

def seekTo (target : Key) (keys : List Key) : List Key :=
  keys.dropWhile (fun key => decide (key < target))

def Ready : List Key → List Key → Prop
  | [], _ | _, [] => True
  | a :: _, b :: _ => a ≤ b

def navigate (first second : List Key) : Option (List Key × Nat) :=
  match first, second with
  | [], _ | _, [] => some ([], 0)
  | a :: tail, b :: rest =>
      if b < a then none
      else if a = b then
        match navigate (b :: rest) tail with
        | none => none
        | some (keys, work) => some (a :: keys, work + 1)
      else
        match navigate (b :: rest) (seekTo b tail) with
        | none => none
        | some (keys, work) => some (keys, work + 1)
termination_by first.length + second.length
decreasing_by
  all_goals simp_wf
  · omega
  · have bound := List.length_dropWhile_le (fun key => decide (key < b)) tail
    change (seekTo b tail).length ≤ tail.length at bound
    omega

theorem seek_length_le (target : Key) (keys : List Key) :
    (seekTo target keys).length ≤ keys.length :=
  List.length_dropWhile_le _ _

theorem seek_sorted (target : Key) (keys : List Key)
    (sorted : keys.Pairwise (· < ·)) :
    (seekTo target keys).Pairwise (· < ·) :=
  sorted.sublist (List.dropWhile_sublist _)

theorem seek_membership (target : Key) (keys : List Key)
    (sorted : keys.Pairwise (· < ·)) (key : Key) :
    key ∈ seekTo target keys ↔ key ∈ keys ∧ target ≤ key := by
  induction keys with
  | nil => simp [seekTo]
  | cons head tail ih =>
      have ordered := List.pairwise_cons.mp sorted
      by_cases before : head < target
      · simp only [seekTo, List.dropWhile_cons, decide_eq_true before, ↓reduceIte]
        rw [← seekTo, ih ordered.2]
        constructor
        · rintro ⟨member, lower⟩
          exact ⟨by simp [member], lower⟩
        · rintro ⟨member, lower⟩
          rcases List.mem_cons.mp member with equal | member
          · subst key
            exact False.elim (not_le_of_gt before lower)
          · exact ⟨member, lower⟩
      · have lower : target ≤ head := le_of_not_gt before
        simp only [seekTo, List.dropWhile_cons, decide_eq_false before, Bool.false_eq_true,
          ↓reduceIte]
        constructor
        · intro member
          refine ⟨member, ?_⟩
          rcases List.mem_cons.mp member with equal | member
          · simpa [equal] using lower
          · exact lower.trans (le_of_lt (ordered.1 key member))
        · exact fun member => member.1

theorem swap_trace {current : Bool} {left right work : Nat}
    (trace : Execution current left right work) :
    Execution (!current) right left work := by
  induction trace with
  | exhausted left right empty current =>
      exact Execution.exhausted right left empty.symm (!current)
  | left positive progress rest ih => exact Execution.right positive progress ih
  | right positive progress rest ih => exact Execution.left positive progress ih

/-- The returned keys are independently specified by membership in both
inputs. Sortedness supplies exact ordered delivery and excludes duplicates. -/
theorem navigate_spec (first second : List Key)
    (firstSorted : first.Pairwise (· < ·))
    (secondSorted : second.Pairwise (· < ·)) (ready : Ready first second) :
    ∃ keys work, navigate first second = some (keys, work) ∧
      (∀ key, key ∈ keys ↔ key ∈ first ∧ key ∈ second) ∧
      keys.Pairwise (· < ·) ∧ Execution true first.length second.length work := by
  have aux : ∀ (size : Nat) (first second : List Key), first.length + second.length = size →
      first.Pairwise (· < ·) → second.Pairwise (· < ·) → Ready first second →
      ∃ keys work, navigate first second = some (keys, work) ∧
        (∀ key, key ∈ keys ↔ key ∈ first ∧ key ∈ second) ∧
        keys.Pairwise (· < ·) ∧ Execution true first.length second.length work := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro first second sizeEq firstSorted secondSorted ready
      cases first with
      | nil =>
          refine ⟨[], 0, by simp [navigate], by simp, by simp, ?_⟩
          exact Execution.exhausted 0 second.length (Or.inl rfl) true
      | cons a tail =>
        cases second with
        | nil =>
            refine ⟨[], 0, by simp [navigate], by simp, by simp, ?_⟩
            exact Execution.exhausted (a :: tail).length 0 (Or.inr rfl) true
        | cons b rest =>
          have ordered := List.pairwise_cons.mp firstSorted
          have lower : a ≤ b := ready
          have notAhead : ¬b < a := not_lt_of_ge lower
          by_cases same : a = b
          · subst b
            have nextReady : Ready (a :: rest) tail := by
              cases tail with
              | nil => trivial
              | cons c cs => exact le_of_lt (ordered.1 c (by simp))
            obtain ⟨keys, work, run, members, sorted, trace⟩ :=
              ih ((a :: rest).length + tail.length) (by simp_all; omega)
                (a :: rest) tail rfl secondSorted ordered.2 nextReady
            refine ⟨a :: keys, work + 1, ?_, ?_, ?_, ?_⟩
            · simp only [navigate, lt_self_iff_false, ↓reduceIte, run]
            · intro key
              simp only [List.mem_cons, members]
              tauto
            · apply List.pairwise_cons.mpr
              refine ⟨?_, sorted⟩
              intro key member
              exact ordered.1 key ((members key).mp member).2
            · exact Execution.left (by simp) (by simp) (swap_trace trace)
          · have nextSorted := seek_sorted b tail ordered.2
            have nextReady : Ready (b :: rest) (seekTo b tail) := by
              cases suffix : seekTo b tail with
              | nil => trivial
              | cons c cs =>
                  exact ((seek_membership b tail ordered.2 c).mp
                    (by simp [suffix])).2
            have tailSize := seek_length_le b tail
            obtain ⟨keys, work, run, members, sorted, trace⟩ :=
              ih ((b :: rest).length + (seekTo b tail).length) (by simp_all; omega)
                (b :: rest) (seekTo b tail) rfl secondSorted nextSorted nextReady
            refine ⟨keys, work + 1, ?_, ?_, sorted, ?_⟩
            · simp only [navigate, notAhead, same, ↓reduceIte, run]
            · intro key
              rw [members, seek_membership b tail ordered.2 key]
              have rightLower : key ∈ b :: rest → b ≤ key := by
                intro member
                rcases List.mem_cons.mp member with equal | member
                · simp [equal]
                · exact le_of_lt ((List.pairwise_cons.mp secondSorted).1 key member)
              constructor
              · rintro ⟨right, left, _⟩
                exact ⟨by simp [left], right⟩
              · rintro ⟨left, right⟩
                have keyLower := rightLower right
                rcases List.mem_cons.mp left with equal | left
                · subst key
                  exact False.elim (same (le_antisymm lower keyLower))
                · exact ⟨right, left, keyLower⟩
            · exact Execution.left (by simp) (by simpa using Nat.lt_succ_of_le tailSize)
                (swap_trace trace)
  exact aux (first.length + second.length) first second rfl firstSorted secondSorted ready

theorem navigate_progress_bound (first second keys : List Key) (work : Nat)
    (firstSorted : first.Pairwise (· < ·)) (secondSorted : second.Pairwise (· < ·))
    (ready : Ready first second) (run : navigate first second = some (keys, work)) :
    work ≤ 2 * min first.length second.length := by
  obtain ⟨found, count, computed, _, _, trace⟩ :=
    navigate_spec first second firstSorted secondSorted ready
  have equal : (found, count) = (keys, work) := Option.some.inj (computed.symm.trans run)
  cases equal
  exact advances_le_twice_smaller trace

/-- The initial head ordering selects the earlier iterator. Empty inputs
terminate immediately, as in the range cursor. -/
def intersection (left right : List Key) : Option (List Key × Nat) :=
  match left, right with
  | a :: _, b :: _ => if b < a then navigate right left else navigate left right
  | _, _ => navigate left right

theorem intersection_spec (left right : List Key)
    (leftSorted : left.Pairwise (· < ·)) (rightSorted : right.Pairwise (· < ·)) :
    ∃ keys work, intersection left right = some (keys, work) ∧
      (∀ key, key ∈ keys ↔ key ∈ left ∧ key ∈ right) ∧
      keys.Pairwise (· < ·) ∧ work ≤ 2 * min left.length right.length := by
  cases left with
  | nil =>
      refine ⟨[], 0, by simp [intersection, navigate], by simp, by simp, by simp⟩
  | cons a tail =>
    cases right with
    | nil =>
        refine ⟨[], 0, by simp [intersection, navigate], by simp, by simp, by simp⟩
    | cons b rest =>
      by_cases earlier : b < a
      · obtain ⟨keys, work, run, members, sorted, trace⟩ :=
          navigate_spec (b :: rest) (a :: tail) rightSorted leftSorted (le_of_lt earlier)
        refine ⟨keys, work, by simp [intersection, earlier, run], ?_, sorted, ?_⟩
        · intro key
          simpa only [and_comm] using members key
        · simpa only [min_comm] using advances_le_twice_smaller trace
      · obtain ⟨keys, work, run, members, sorted, trace⟩ :=
          navigate_spec (a :: tail) (b :: rest) leftSorted rightSorted (le_of_not_gt earlier)
        exact ⟨keys, work, by simp [intersection, earlier, run], members, sorted,
          advances_le_twice_smaller trace⟩

theorem intersection_progress_bound (left right keys : List Key) (work : Nat)
    (leftSorted : left.Pairwise (· < ·)) (rightSorted : right.Pairwise (· < ·))
    (run : intersection left right = some (keys, work)) :
    work ≤ 2 * min left.length right.length := by
  obtain ⟨found, count, computed, _, _, bound⟩ :=
    intersection_spec left right leftSorted rightSorted
  have equal : (found, count) = (keys, work) := Option.some.inj (computed.symm.trans run)
  cases equal
  exact bound

def intersectionAdvances (left right : List Key) : Nat :=
  match intersection left right with
  | none => 0
  | some (_, work) => work

def intersectionKeys (left right : List Key) : List Key :=
  match intersection left right with
  | none => []
  | some (keys, _) => keys

theorem intersection_advances_le (left right : List Key)
    (leftSorted : left.Pairwise (· < ·)) (rightSorted : right.Pairwise (· < ·)) :
    intersectionAdvances left right ≤ 2 * min left.length right.length := by
  obtain ⟨keys, work, run, _, _, bound⟩ := intersection_spec left right leftSorted rightSorted
  simpa only [intersectionAdvances, run] using bound

theorem intersection_keys_exact (left right : List Key)
    (leftSorted : left.Pairwise (· < ·)) (rightSorted : right.Pairwise (· < ·)) :
    (intersectionKeys left right).Pairwise (· < ·) ∧
      (intersectionKeys left right).toFinset = left.toFinset ∩ right.toFinset := by
  obtain ⟨keys, work, run, members, sorted, _⟩ := intersection_spec left right leftSorted rightSorted
  simp only [intersectionKeys, run]
  refine ⟨sorted, ?_⟩
  ext key
  simpa only [List.mem_toFinset, Finset.mem_inter] using members key

theorem sparse_intersection :
    navigate ([0, 2, 4, 8] : List Nat) [1, 2, 3, 8, 9] = some ([2, 8], 7) := by
  norm_num [navigate, seekTo, List.dropWhile]

theorem wrong_initial_iterator_is_refused :
    navigate ([3] : List Nat) [1, 3] = none := by norm_num [navigate]

theorem unsorted_keys_can_lose_a_match :
    intersection ([0, 3, 1] : List Nat) [1] = some ([], 2) ∧
      1 ∈ ([0, 3, 1] : List Nat) ∧ 1 ∈ ([1] : List Nat) := by
  norm_num [intersection, navigate, seekTo, List.dropWhile]
  rw [navigate]
  simp

theorem repeated_keys_need_a_separate_occurrence_account :
    intersection ([1, 1] : List Nat) [1] = some ([1, 1], 2) ∧
      ¬([1, 1] : List Nat).Pairwise (· < ·) := by
  norm_num [intersection, navigate, List.pairwise_cons]

end Mettapedia.Machines.Cursor.OrderedIntersection
