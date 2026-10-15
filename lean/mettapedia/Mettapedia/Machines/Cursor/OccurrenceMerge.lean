import Mettapedia.Machines.Cursor.Sequence
import Mathlib.Data.Finset.Max

/-!
# Lazy declaration-order merging of occurrence streams

Each discrimination-trie branch supplies an increasing stream of logical row
indices. Equal indices from overlapping branches describe one occurrence;
equal payloads at different indices remain different occurrences. A pull
selects the least live head and advances all branches at that head.

The independent reference retains the entire remaining finite occurrence
set. The lazy transition retains the branch suffixes. Their local comparison
lifts through the existing cursor protocol to arbitrary bounded clients,
including suspended and early-stopping clients.

The native heap is a realization of least-head selection, checked separately
against declaration-order row oracles. These laws concern the merge transition
and its head/advance accounting, not compiled C, allocator bytes or CPU time.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.OccurrenceMerge

open Mettapedia.TypeTheory.IndexedPolynomial

def rows : List (List Nat) → Finset Nat
  | [] => ∅
  | stream :: rest => stream.toFinset ∪ rows rest

def heads : List (List Nat) → Finset Nat
  | [] => ∅
  | [] :: rest => heads rest
  | (head :: _) :: rest => insert head (heads rest)

def Ordered (streams : List (List Nat)) : Prop :=
  ∀ stream ∈ streams, stream.Pairwise (· < ·)

def advanceHead (head : Nat) : List Nat → List Nat
  | [] => []
  | first :: rest => if first = head then rest else first :: rest

def advanceHeads (head : Nat) (streams : List (List Nat)) : List (List Nat) :=
  streams.map (advanceHead head)

theorem rows_eq_flatten (streams : List (List Nat)) :
    rows streams = streams.flatten.toFinset := by
  induction streams with
  | nil => simp [rows]
  | cons stream rest ih => simp [rows, ih]

theorem heads_subset_rows (streams : List (List Nat)) :
    heads streams ⊆ rows streams := by
  induction streams with
  | nil => simp [heads, rows]
  | cons stream rest ih =>
      cases stream with
      | nil => simpa [heads, rows] using ih
      | cons first tail =>
          intro value member
          simp only [heads, Finset.mem_insert] at member
          rcases member with equal | member
          · subst value; simp [rows]
          · exact Finset.mem_union_right _ (ih member)

theorem rows_nonempty_iff (streams : List (List Nat)) :
    (rows streams).Nonempty ↔ (heads streams).Nonempty := by
  induction streams with
  | nil => simp [rows, heads]
  | cons stream rest ih =>
      cases stream with
      | nil => simpa [rows, heads] using ih
      | cons first tail =>
          constructor
          · intro _; exact ⟨first, by simp [heads]⟩
          · intro _; exact ⟨first, by simp [rows]⟩

theorem head_le_member {first value : Nat} {tail : List Nat}
    (ordered : (first :: tail).Pairwise (· < ·))
    (member : value ∈ first :: tail) : first ≤ value := by
  rcases List.mem_cons.mp member with equal | member
  · subst value; exact Nat.le_refl _
  · exact Nat.le_of_lt ((List.pairwise_cons.mp ordered).1 value member)

theorem head_mem_heads (first : Nat) (tail : List Nat)
    (streams : List (List Nat)) (belongs : first :: tail ∈ streams) :
    first ∈ heads streams := by
  induction streams with
  | nil => simp at belongs
  | cons stream rest ih =>
      rcases List.mem_cons.mp belongs with equal | tailMember
      · subst stream; simp [heads]
      · have following := ih tailMember
        cases stream with
        | nil => exact following
        | cons head tail => exact Finset.mem_insert_of_mem following

theorem least_head_le_rows (streams : List (List Nat))
    (ordered : Ordered streams) (nonempty : (heads streams).Nonempty) :
    ∀ value ∈ rows streams, (heads streams).min' nonempty ≤ value := by
  intro value member
  rw [rows_eq_flatten] at member
  obtain ⟨stream, belongs, member⟩ := List.mem_flatten.mp (List.mem_toFinset.mp member)
  cases stream with
  | nil => simp at member
  | cons first tail =>
      have atHead := head_mem_heads first tail streams belongs
      exact (Finset.min'_le _ _ atHead).trans
        (head_le_member (ordered _ belongs) member)

theorem least_head_eq_least_row (streams : List (List Nat))
    (ordered : Ordered streams) (nonempty : (heads streams).Nonempty) :
    (rows streams).min' ((rows_nonempty_iff streams).mpr nonempty) =
      (heads streams).min' nonempty := by
  apply (Finset.min'_eq_iff _ _ _).mpr
  exact ⟨heads_subset_rows streams (Finset.min'_mem _ _),
    least_head_le_rows streams ordered nonempty⟩

theorem advanceHead_ordered (head : Nat) (stream : List Nat)
    (ordered : stream.Pairwise (· < ·)) :
    (advanceHead head stream).Pairwise (· < ·) := by
  cases stream with
  | nil => exact ordered
  | cons first rest =>
      by_cases equal : first = head
      · simpa [advanceHead, equal] using (List.pairwise_cons.mp ordered).2
      · simpa [advanceHead, equal] using ordered

theorem advanceHeads_ordered (head : Nat) (streams : List (List Nat))
    (ordered : Ordered streams) : Ordered (advanceHeads head streams) := by
  intro next member
  obtain ⟨stream, belongs, equal⟩ := List.mem_map.mp member
  subst next
  exact advanceHead_ordered head stream (ordered stream belongs)

theorem advanceHead_rows (head : Nat) (stream : List Nat)
    (ordered : stream.Pairwise (· < ·))
    (lower : ∀ value ∈ stream, head ≤ value) :
    (advanceHead head stream).toFinset = stream.toFinset.erase head := by
  cases stream with
  | nil => simp [advanceHead]
  | cons first rest =>
      have increasing := (List.pairwise_cons.mp ordered).1
      by_cases equal : first = head
      · subst first
        have absent : head ∉ rest.toFinset := by
          intro member
          exact Nat.lt_irrefl _ (increasing head (List.mem_toFinset.mp member))
        simp [advanceHead, Finset.erase_insert absent]
      · have absent : head ∉ (first :: rest).toFinset := by
          intro member
          rcases List.mem_cons.mp (List.mem_toFinset.mp member) with same | member
          · exact equal same.symm
          · have le := lower first (by simp)
            have lt := increasing head member
            omega
        rw [Finset.erase_eq_self.mpr absent]
        simp [advanceHead, equal]

theorem advanceHeads_rows (head : Nat) (streams : List (List Nat))
    (ordered : Ordered streams) (lower : ∀ value ∈ rows streams, head ≤ value) :
    rows (advanceHeads head streams) = (rows streams).erase head := by
  induction streams with
  | nil => simp [rows, advanceHeads]
  | cons stream rest ih =>
      have firstOrdered := ordered stream (by simp)
      have restOrdered : Ordered rest := fun s member => ordered s (by simp [member])
      have firstLower : ∀ value ∈ stream, head ≤ value := by
        intro value member
        exact lower value (by simp [rows, member])
      have restLower : ∀ value ∈ rows rest, head ≤ value := by
        intro value member
        exact lower value (Finset.mem_union_right _ member)
      simp only [advanceHeads, List.map_cons, rows]
      rw [advanceHead_rows head stream firstOrdered firstLower,
        ← advanceHeads, ih restOrdered restLower, Finset.erase_union_distrib]

structure State where
  streams : List (List Nat)
  ordered : Ordered streams

def lazyProvider : Provider (Sequence.protocol Nat) where
  State _ _ := State
  step state _ :=
    if nonempty : (heads state.streams).Nonempty then
      let head := (heads state.streams).min' nonempty
      ⟨some head, ⟨advanceHeads head state.streams,
        advanceHeads_ordered head state.streams state.ordered⟩⟩
    else
      ⟨none, state⟩

def referenceProvider : Provider (Sequence.protocol Nat) where
  State _ _ := Finset Nat
  step values _ :=
    if nonempty : values.Nonempty then
      let head := values.min' nonempty
      ⟨some head, values.erase head⟩
    else
      ⟨none, values⟩

def referenceHom : Hom lazyProvider referenceProvider where
  map state := rows state.streams
  step state _ := by
    by_cases nonempty : (heads state.streams).Nonempty
    · have values : (rows state.streams).Nonempty :=
        (rows_nonempty_iff state.streams).mpr nonempty
      simp only [lazyProvider, referenceProvider, nonempty, values, dite_true]
      rw [least_head_eq_least_row state.streams state.ordered nonempty]
      congr 1
      exact (advanceHeads_rows _ state.streams state.ordered
        (least_head_le_rows state.streams state.ordered nonempty))
    · have values : ¬ (rows state.streams).Nonempty :=
        fun values => nonempty ((rows_nonempty_iff state.streams).mp values)
      simp [lazyProvider, referenceProvider, nonempty, values]

/-- Reply-dependent clients retain exactly the same observations and residual
control, independently of the charges assigned to the two representations. -/
theorem bounded_client_observation {Return : Unit → Unit → Type}
    (client : Client (P := Sequence.protocol Nat) (Return := Return))
    (lazyCost : Charge lazyProvider) (referenceCost : Charge referenceProvider)
    (fuel : Nat) (packet : Packet lazyProvider client ()) :
    referenceHom.outcome client
      (advance lazyProvider client lazyCost fuel packet).2 =
      (advance referenceProvider client referenceCost fuel
        (referenceHom.packet client packet)).2 :=
  Hom.advance client referenceHom lazyCost referenceCost fuel packet

def remaining (streams : List (List Nat)) : Nat :=
  (streams.map List.length).sum

def headAdvance (head : Nat) (stream : List Nat) : Nat :=
  if stream.head? = some head then 1 else 0

def advances (head : Nat) (streams : List (List Nat)) : Nat :=
  (streams.map (headAdvance head)).sum

theorem advanceHead_account (head : Nat) (stream : List Nat) :
    (advanceHead head stream).length + headAdvance head stream = stream.length := by
  cases stream with
  | nil => simp [advanceHead, headAdvance]
  | cons first rest =>
      by_cases equal : first = head <;> simp [advanceHead, headAdvance, equal]

/-- A pull advances each tied branch once; every such advance consumes one
remaining leaf. No other leaf is traversed by this abstract transition. -/
theorem advanceHeads_account (head : Nat) (streams : List (List Nat)) :
    remaining (advanceHeads head streams) + advances head streams = remaining streams := by
  induction streams with
  | nil => simp [remaining, advances, advanceHeads]
  | cons stream rest ih =>
      have first := advanceHead_account head stream
      simp only [remaining, advances, advanceHeads, List.map_cons,
        List.map_map, List.sum_cons] at ih ⊢
      omega

theorem advances_le_branches (head : Nat) (streams : List (List Nat)) :
    advances head streams ≤ streams.length := by
  induction streams with
  | nil => simp [advances]
  | cons stream rest ih =>
      have bound : headAdvance head stream ≤ 1 := by
        unfold headAdvance
        split <;> omega
      simp only [advances, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      omega

theorem advances_positive (head : Nat) (streams : List (List Nat))
    (member : head ∈ heads streams) : 1 ≤ advances head streams := by
  induction streams with
  | nil => simp [heads] at member
  | cons stream rest ih =>
      cases stream with
      | nil => simpa [heads, advances, headAdvance] using ih member
      | cons first tail =>
          rcases Finset.mem_insert.mp member with equal | following
          · subst first; simp [advances, headAdvance]
          · have lower := ih following
            simp only [advances, List.map_cons, List.sum_cons] at lower ⊢
            omega

/-- Finite captured streams cannot yield indefinitely: every nonterminal
pull strictly decreases the number of remaining branch leaves. -/
theorem remaining_decreases (streams : List (List Nat))
    (nonempty : (heads streams).Nonempty) :
    remaining (advanceHeads ((heads streams).min' nonempty) streams) <
      remaining streams := by
  have account := advanceHeads_account ((heads streams).min' nonempty) streams
  have positive := advances_positive ((heads streams).min' nonempty) streams
    (Finset.min'_mem _ _)
  omega

/-- The per-branch traversal positions have fixed cardinality even when a
large candidate bag is consumed. The head frontier is no larger. -/
theorem branch_slots_preserved (head : Nat) (streams : List (List Nat)) :
    (advanceHeads head streams).length = streams.length := by
  simp [advanceHeads]

theorem frontier_slots_bounded (streams : List (List Nat)) :
    (streams.filterMap List.head?).length ≤ streams.length :=
  List.length_filterMap_le List.head? streams

/-- A cached head orders by occurrence before branch ordinal. The native
representation chooses a power-of-two radix and checks the captured range
before using a machine word; these laws make those admission bounds explicit. -/
def packedHead (radix occurrence branch : Nat) : Nat :=
  radix * occurrence + branch

theorem packedHead_decode (radix occurrence branch : Nat)
    (positive : 0 < radix) (bounded : branch < radix) :
    packedHead radix occurrence branch / radix = occurrence ∧
    packedHead radix occurrence branch % radix = branch := by
  constructor
  · rw [packedHead, Nat.add_comm, Nat.add_mul_div_left _ _ positive,
      Nat.div_eq_of_lt bounded, Nat.zero_add]
  · rw [packedHead, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt bounded]

theorem packedHead_order (radix firstRow secondRow firstBranch secondBranch : Nat)
    (firstBound : firstBranch < radix) (secondBound : secondBranch < radix) :
    packedHead radix firstRow firstBranch < packedHead radix secondRow secondBranch ↔
      firstRow < secondRow ∨ (firstRow = secondRow ∧ firstBranch < secondBranch) := by
  unfold packedHead
  constructor
  · intro less
    rcases lt_trichotomy firstRow secondRow with earlier | same | later
    · exact Or.inl earlier
    · exact Or.inr ⟨same, by subst secondRow; omega⟩
    · have gap := Nat.mul_le_mul_left radix (Nat.succ_le_of_lt later)
      simp only [Nat.mul_succ] at gap
      omega
  · rintro (earlier | ⟨same, less⟩)
    · have gap := Nat.mul_le_mul_left radix (Nat.succ_le_of_lt earlier)
      simp only [Nat.mul_succ] at gap
      omega
    · subst secondRow; omega

theorem packedHead_bounded (radix ceiling capacity occurrence branch : Nat)
    (rowBound : occurrence < ceiling) (branchBound : branch < radix)
    (fits : radix * ceiling ≤ capacity) :
    packedHead radix occurrence branch < capacity := by
  have gap := Nat.mul_le_mul_left radix (Nat.succ_le_of_lt rowBound)
  simp only [Nat.mul_succ] at gap
  unfold packedHead
  omega

def capture (ceiling : Nat) (stream : List Nat) : List Nat :=
  stream.filter (fun index => decide (index < ceiling))

/-- Appends outside the captured logical-update ceiling cannot enter a
retained read. Deletion/compaction requires retaining the original rows. -/
theorem append_above_ceiling_invisible (ceiling : Nat) (before appended : List Nat)
    (outside : ∀ index ∈ appended, ceiling ≤ index) :
    capture ceiling (before ++ appended) = capture ceiling before := by
  have empty : capture ceiling appended = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro index member
    simpa using Nat.not_lt_of_ge (outside index member)
  unfold capture at empty ⊢
  rw [List.filter_append, empty, List.append_nil]

namespace Controls

def interleaved : State := ⟨[[0, 4, 8], [1, 4, 7], [], [2, 5]], by
  intro stream member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide⟩

theorem overlapping_branches_same_occurrence :
    rows interleaved.streams = {0, 1, 2, 4, 5, 7, 8} ∧
    advances 4 [[4, 8], [4, 7], [], [5]] = 2 ∧
    rows (advanceHeads 4 [[4, 8], [4, 7], [], [5]]) = {5, 7, 8} := by
  decide

theorem distinct_indices_preserve_duplicate_payloads :
    ([3, 5] : List Nat).map (fun _ => "same-fact") = ["same-fact", "same-fact"] ∧
    rows [[3], [5]] = {3, 5} := by
  decide

/-- A head-only selector is incorrect without increasing branch streams. -/
theorem unsorted_branch_refutes_head_selection :
    (heads [[2, 1]]).min' (by decide) = 2 ∧
    (rows [[2, 1]]).min' (by decide) = 1 := by
  decide

/-- Restarting after suspension repeats an already delivered occurrence. -/
theorem rewind_changes_next_occurrence :
    (heads interleaved.streams).min' (by decide) = 0 ∧
    (heads (advanceHeads 0 interleaved.streams)).min' (by decide) = 1 := by
  decide

theorem capture_does_not_follow_live_appends :
    capture 3 [0, 1, 2, 3, 4] = [0, 1, 2] ∧
    capture 3 [0, 1, 2, 3, 4] ≠ [0, 1, 2, 3, 4] := by
  decide

theorem unbounded_branch_refutes_packed_order :
    packedHead 4 1 5 > packedHead 4 2 0 ∧ 1 < 2 := by
  decide

end Controls

end Mettapedia.Machines.Cursor.OccurrenceMerge
