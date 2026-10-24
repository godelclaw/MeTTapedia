import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mettapedia.Algorithms.Retrieval.OrderedGroupedFold
import Mettapedia.Algorithms.Collections.AtomicIngress

/-!
Bulk ordered totals from a shared sorted key traversal. Each row observes
exactly the sorted subsequence of its own keys. The update is arbitrary;
no associativity, commutativity or floating-point reassociation is assumed.
This is a schedule law, not a verification of native storage or publication.
-/

namespace Mettapedia.Algorithms.Retrieval.BulkPreparation

variable {Key Row R : Type*}

section Frequencies

variable [DecidableEq Key]

def frequencies (events : List Key) : Key → Nat :=
  GroupedFold.grouped (fun total (_ : Unit) => total + 1) (fun _ => 0)
    (events.map (fun key => (key, ())))

omit [DecidableEq Key] in
private theorem count_traversal (events : List Key) (keep : Key → Bool) (initial : Nat) :
    events.foldl (fun total key => if keep key then total + 1 else total) initial =
      initial + (events.filter keep).length := by
  induction events generalizing initial with
  | nil => simp
  | cons key rest ih =>
      cases selected : keep key <;>
        simp [selected, ih, Nat.add_comm, Nat.add_left_comm]

/-- Frequencies count occurrences, including repetitions, rather than the
cardinality of their support. -/
theorem frequencies_eq_occurrences (events : List Key) (key : Key) :
    frequencies events key = (events.filter (fun candidate => decide (candidate = key))).length := by
  simpa [frequencies, GroupedFold.observe_grouped, List.foldl_map] using
    count_traversal events (fun candidate => decide (candidate = key)) 0

example : frequencies ([2, 2, 1] : List Nat) 2 = 2 := by decide +kernel

example : frequencies ([2, 2] : List Nat) 2 ≠ ({2} : Finset Nat).card := by
  decide +kernel

end Frequencies

section WeightPublication

/-- The scalar policy remains an opaque completed computation. Publishing
in bulk does not change its arithmetic or combine separate weights. -/
def weightRow (compute : Key → Nat → R) (entry : Key × Nat) : Key × R :=
  (entry.1, compute entry.1 entry.2)

def publishWeights (compute : Key → Nat → R) (admit : (Key × R) → Bool)
    (counts : List (Key × Nat)) (destination : List (Key × R)) : Option (List (Key × R)) :=
  Collections.AtomicIngress.publication destination
    (Collections.AtomicIngress.stage (fun entry => [weightRow compute entry]) admit [] counts)

/-- One validated publication agrees with separate ordered insertions.
Repeated keys remain repeated rows; no dictionary replacement is inferred. -/
theorem weight_publication_eq_separate (compute : Key → Nat → R)
    (admit : (Key × R) → Bool) (counts : List (Key × Nat))
    (destination : List (Key × R)) :
    publishWeights compute admit counts destination =
      if (counts.map (weightRow compute)).all admit then
        some (counts.foldl (fun rows entry => rows ++ [weightRow compute entry]) destination)
      else none := by
  have mapped : counts.flatMap (fun entry => [weightRow compute entry]) =
      counts.map (weightRow compute) := by
    induction counts with
    | nil => rfl
    | cons entry rest ih => simp [ih]
  simpa only [publishWeights, mapped] using
    Collections.AtomicIngress.publication_eq_sequential
      (fun entry => [weightRow compute entry]) admit counts destination

example : publishWeights (fun (key : Nat) count => key + count)
    (fun _ => true) [(2, 1), (2, 3)] [] = some [(2, 3), (2, 5)] := by decide

example : publishWeights (fun (key : Nat) count => key + count)
    (fun entry => entry.2 != 5) [(2, 1), (2, 3)] [(9, 9)] = none := by decide

end WeightPublication

variable [LinearOrder Key]

theorem sorted_restriction (available selected : Finset Key)
    (subset : selected ⊆ available) :
    available.sort.filter (fun key => decide (key ∈ selected)) = selected.sort := by
  have same : List.Perm (available.sort.filter (fun key => decide (key ∈ selected))) selected.sort := by
    apply (List.perm_ext_iff_of_nodup
      ((available.sort_nodup _).filter _) (selected.sort_nodup _)).mpr
    intro key
    simp only [List.mem_filter, Finset.mem_sort, decide_eq_true_eq]
    exact ⟨And.right, fun member => ⟨subset member, member⟩⟩
  exact same.eq_of_pairwise' ((available.pairwise_sort _).filter _) (selected.pairwise_sort _)

def allKeys (rows : Finset Row) (keys : Row → Finset Key) : Finset Key :=
  rows.biUnion keys

def sharedTotals (step : R → Key → R) (initial : Row → R)
    (rows : Finset Row) (keys : Row → Finset Key) : Row → R :=
  (allKeys rows keys).sort.foldl
    (fun totals key row => if key ∈ keys row then step (totals row) key else totals row)
    initial

private theorem observe_traversal (step : R → Key → R) (keys : Row → Finset Key)
    (events : List Key) (initial : Row → R) (row : Row) :
    (events.foldl
      (fun totals key row => if key ∈ keys row then step (totals row) key else totals row)
      initial) row =
      events.foldl (fun total key => if key ∈ keys row then step total key else total)
        (initial row) := by
  induction events generalizing initial with
  | nil => rfl
  | cons key rest ih =>
      simpa only [List.foldl_cons] using
        ih (fun row => if key ∈ keys row then step (initial row) key else initial row)

/-- One global traversal agrees with each row's separate ordered fold, even
when the update has a non-associative schedule. -/
theorem sharedTotals_eq_separate (step : R → Key → R) (initial : Row → R)
    (rows : Finset Row) (keys : Row → Finset Key) (row : Row) (member : row ∈ rows) :
    sharedTotals step initial rows keys row =
      (keys row).sort.foldl step (initial row) := by
  rw [sharedTotals, observe_traversal]
  have subset : keys row ⊆ allKeys rows keys := by
    intro key present
    exact Finset.mem_biUnion.mpr ⟨row, member, present⟩
  have schedule := sorted_restriction (allKeys rows keys) (keys row) subset
  rw [← schedule, List.foldl_filter]
  simp

example : sharedTotals (fun (total : Nat) key => 10 * total + key)
    (fun (_ : Bool) => 0) {false, true}
    (fun row => if row then {2, 5} else {1, 5}) true = 25 := by
  rw [sharedTotals_eq_separate _ _ _ _ true (by simp)]
  change ({2, 5} : Finset Nat).sort.foldl (fun total key => 10 * total + key) 0 = 25
  rw [Finset.sort_insert (r := fun a b : Nat => a ≤ b) (by simp) (by simp),
      Finset.sort_singleton]
  decide +kernel

example : ([5, 2] : List Nat).foldl (fun total key => 10 * total + key) 0 ≠
    ([2, 5] : List Nat).foldl (fun total key => 10 * total + key) 0 := by
  decide +kernel

#print axioms sorted_restriction
#print axioms sharedTotals_eq_separate
#print axioms frequencies_eq_occurrences
#print axioms weight_publication_eq_separate

end Mettapedia.Algorithms.Retrieval.BulkPreparation
