import Mettapedia.Machines.Cursor.Amortized
import Mettapedia.Machines.Cursor.RelationalAmortized
import Mettapedia.GSLT.Contracts.RunAccounts
import Mettapedia.Machines.MatchIndexProjection
import Mettapedia.Machines.ResourceOwnershipOptimality
import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.Cursor.ReadOnlyQuery
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort

/-!
# A finite worklist tracer and its graph work

`run` maintains disjoint expanded and pending sets. It selects a pending
address, reads its references, marks the address, and inserts its successors
after subtracting the expanded set. Thus cycles and shared descendants do not
cause repeated expansion. Its executable definitions never use `Live` or
`footprint`. The allocation cardinality supplies a termination bound, not an
enumeration of all allocated cells' references.

The counters concern heap expansions and the explicit reference loop's visits.
Root enumeration, the allocation-cardinality bound, frontier selection, set
membership/insertion/difference, and the retained audit log have separate
representation costs, including sorting the outgoing reference enumeration.
In particular, these theorems do not make the `Finset`
implementation a constant-time set or establish physical linear runtime.
References in the existing heap model are sets: repeated pointer slots within
one concrete runtime cell would require a slot enumeration and its own cost.

Address ordering supplies executable frontier selection. No finite address
universe, acyclicity, exclusive ownership, or bound on future heaps is required.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResourceOwnership.TraceWork

open Mettapedia.GSLT.Dynamics.StoreReachability (Reach)

universe uValue uOwner

variable {Address : Type} {Value : Type uValue} {Owner : Type uOwner}
  [LinearOrder Address]

/-- One lookup exposes a cell's distinct outgoing references. -/
def successors (heap : Heap Address Value) (address : Address) : Finset Address :=
  ((heap.lookup address).map Cell.references).getD ∅

omit [LinearOrder Address] in
theorem mem_successors (heap : Heap Address Value) (address next : Address) :
    next ∈ successors heap address ↔
      ∃ cell, heap.lookup address = some cell ∧ next ∈ cell.references := by
  cases found : heap.lookup address <;> simp [successors, found]

theorem successors_live (heap : Heap Address Value) (roots : Roots Owner Address)
    {address next : Address} (live : Live heap roots address)
    (edge : next ∈ successors heap address) : Live heap roots next := by
  obtain ⟨cell, found, reference⟩ := (mem_successors heap address next).mp edge
  exact live_step heap roots live found reference

structure State (Address : Type) where
  seen : Finset Address
  pending : Finset Address
  deriving DecidableEq

/-- The address is marked before successors enter the frontier. -/
def advance (state : State Address) (address : Address)
    (references : Finset Address) : State Address where
  seen := insert address state.seen
  pending := (state.pending ∪ references) \ insert address state.seen

/-- An explicit reference-enumeration loop, with one tick for every list
entry even when the target is already expanded or pending. Set operations
inside each iteration are not charged as constant-time operations. -/
def scanReferences (seen : Finset Address) :
    Finset Address → List Address → Finset Address × Nat
  | pending, [] => (pending, 0)
  | pending, address :: rest =>
      let pending := if address ∈ seen then pending else insert address pending
      let scanned := scanReferences seen pending rest
      (scanned.1, scanned.2 + 1)

theorem scanReferences_eq (seen pending : Finset Address) (references : List Address) :
    scanReferences seen pending references =
      (pending ∪ (references.toFinset \ seen), references.length) := by
  induction references generalizing pending with
  | nil => simp [scanReferences]
  | cons address rest ih =>
      simp only [scanReferences, ih, List.toFinset_cons, List.length_cons]
      apply Prod.ext
      · ext node
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert]
        split <;> rename_i condition
        · constructor
          · tauto
          · rintro (old | ⟨same | later, fresh⟩)
            · exact Or.inl old
            · subst node
              exact False.elim (fresh condition)
            · exact Or.inr ⟨later, fresh⟩
        · simp only [Finset.mem_insert]
          constructor
          · rintro ((rfl | old) | later)
            · exact Or.inr ⟨Or.inl rfl, condition⟩
            · exact Or.inl old
            · exact Or.inr ⟨Or.inr later.1, later.2⟩
          · tauto
      · rfl

/-- Prepare one expansion by reading each reference through `scanReferences`.
Sorting supplies a concrete enumeration of the finite reference set. -/
def expansion (state : State Address) (address : Address)
    (references : Finset Address) : State Address × Nat :=
  let seen := insert address state.seen
  let scanned := scanReferences seen (state.pending \ seen) (references.sort (· ≤ ·))
  (⟨seen, scanned.1⟩, scanned.2)

theorem expansion_eq (state : State Address) (address : Address)
    (references : Finset Address) :
    expansion state address references = (advance state address references, references.card) := by
  simp only [expansion, scanReferences_eq, Finset.sort_toFinset, Finset.length_sort]
  congr 2
  ext node
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

structure Trace (Address : Type) where
  final : State Address
  expanded : List Address
  edgeVisits : Nat
  deriving DecidableEq

/-- Fuel bounds expansion rounds. An empty frontier returns immediately. -/
def run (heap : Heap Address Value) : Nat → State Address → Trace Address
  | 0, state => ⟨state, [], 0⟩
  | fuel + 1, state =>
      if nonempty : state.pending.Nonempty then
        let address := state.pending.min' nonempty
        let references := successors heap address
        let step := expansion state address references
        let rest := run heap fuel step.1
        ⟨rest.final, address :: rest.expanded, step.2 + rest.edgeVisits⟩
      else ⟨state, [], 0⟩

/-- Invalid roots are ignored, just as in `Heap.toStore`; no validity premise
is needed for the tracer's equivalence with the existing semantics. -/
def initial (heap : Heap Address Value) (roots : Roots Owner Address) : State Address where
  seen := ∅
  pending := rootAddresses roots ∩ heap.allocated

def trace (heap : Heap Address Value) (roots : Roots Owner Address) : Trace Address :=
  run heap heap.allocated.card (initial heap roots)

/-- Local frontier invariant: expanded nodes have exposed all their outgoing
edges, and every exposed but unexpanded address is pending. -/
structure Invariant (heap : Heap Address Value) (roots : Roots Owner Address)
    (state : State Address) : Prop where
  seen_live : ∀ address ∈ state.seen, Live heap roots address
  pending_live : ∀ address ∈ state.pending, Live heap roots address
  disjoint : Disjoint state.seen state.pending
  roots_covered : rootAddresses roots ∩ heap.allocated ⊆ state.seen ∪ state.pending
  edges_covered : ∀ address ∈ state.seen,
    successors heap address ⊆ state.seen ∪ state.pending

theorem initial_invariant (heap : Heap Address Value) (roots : Roots Owner Address) :
    Invariant heap roots (initial heap roots) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [initial]
  · intro address member
    rcases Finset.mem_inter.mp member with ⟨root, allocated⟩
    exact Reach.root ⟨allocated, root⟩
  · simp [initial]
  · simp [initial]
  · simp [initial]

theorem advance_union (state : State Address) (address : Address)
    (references : Finset Address) :
    (advance state address references).seen ∪
      (advance state address references).pending =
        insert address (state.seen ∪ state.pending ∪ references) := by
  ext node
  simp only [advance, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert]
  tauto

theorem advance_invariant (heap : Heap Address Value) (roots : Roots Owner Address)
    (state : State Address) (invariant : Invariant heap roots state)
    {address : Address} (member : address ∈ state.pending) :
    Invariant heap roots (advance state address (successors heap address)) := by
  have live := invariant.pending_live address member
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro node inside
    rcases Finset.mem_insert.mp inside with rfl | old
    · exact live
    · exact invariant.seen_live node old
  · intro node inside
    rcases Finset.mem_sdiff.mp inside with ⟨exposed, _⟩
    rcases Finset.mem_union.mp exposed with pending | edge
    · exact invariant.pending_live node pending
    · exact successors_live heap roots live edge
  · apply Finset.disjoint_left.mpr
    intro node expanded pending
    exact (Finset.mem_sdiff.mp pending).2 expanded
  · rw [advance_union]
    intro node rooted
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (invariant.roots_covered rooted))
  · intro node inside next edge
    rw [advance_union]
    rcases Finset.mem_insert.mp inside with rfl | old
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ edge)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (invariant.edges_covered node old edge))

theorem run_invariant (heap : Heap Address Value) (roots : Roots Owner Address)
    (fuel : Nat) (state : State Address) (invariant : Invariant heap roots state) :
    Invariant heap roots (run heap fuel state).final := by
  induction fuel generalizing state with
  | zero => exact invariant
  | succ fuel ih =>
      simp only [run, expansion_eq]
      split
      next nonempty =>
        exact ih _ (advance_invariant heap roots state invariant
          (Finset.min'_mem _ nonempty))
      next _ => exact invariant

theorem selected_fresh (heap : Heap Address Value) (roots : Roots Owner Address)
    (state : State Address) (invariant : Invariant heap roots state)
    {address : Address} (member : address ∈ state.pending) : address ∉ state.seen :=
  fun old => Finset.disjoint_left.mp invariant.disjoint old member

theorem run_seen (heap : Heap Address Value) (fuel : Nat) (state : State Address)
    (address : Address) :
    address ∈ (run heap fuel state).final.seen ↔
      address ∈ state.seen ∨ address ∈ (run heap fuel state).expanded := by
  induction fuel generalizing state with
  | zero => simp [run]
  | succ fuel ih =>
      simp only [run, expansion_eq]
      split
      next nonempty =>
        rw [ih]
        simp only [advance, Finset.mem_insert, List.mem_cons]
        tauto
      next _ => simp

theorem expanded_fresh (heap : Heap Address Value) (roots : Roots Owner Address)
    (fuel : Nat) (state : State Address) (invariant : Invariant heap roots state) :
    ∀ address ∈ (run heap fuel state).expanded, address ∉ state.seen := by
  induction fuel generalizing state with
  | zero => simp [run]
  | succ fuel ih =>
      simp only [run, expansion_eq]
      split
      next nonempty =>
        intro address member
        rcases List.mem_cons.mp member with rfl | later
        · exact selected_fresh heap roots state invariant (Finset.min'_mem _ nonempty)
        · have fresh := ih _ (advance_invariant heap roots state invariant
            (Finset.min'_mem _ nonempty)) address later
          exact fun old => fresh (Finset.mem_insert_of_mem old)
      next _ => simp

theorem expanded_nodup (heap : Heap Address Value) (roots : Roots Owner Address)
    (fuel : Nat) (state : State Address) (invariant : Invariant heap roots state) :
    (run heap fuel state).expanded.Nodup := by
  induction fuel generalizing state with
  | zero => simp [run]
  | succ fuel ih =>
      simp only [run, expansion_eq]
      split
      next nonempty =>
        have nextInvariant := advance_invariant heap roots state invariant
          (Finset.min'_mem _ nonempty)
        refine List.nodup_cons.mpr ⟨?_, ih _ nextInvariant⟩
        intro repeated
        exact expanded_fresh heap roots fuel _ nextInvariant _ repeated
          (Finset.mem_insert_self _ _)
      next _ => simp

theorem run_exhausted (heap : Heap Address Value) (roots : Roots Owner Address)
    (fuel : Nat) (state : State Address) (invariant : Invariant heap roots state)
    (enough : heap.allocated.card ≤ state.seen.card + fuel) :
    (run heap fuel state).final.pending = ∅ := by
  induction fuel generalizing state with
  | zero =>
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro address member
      have fresh := selected_fresh heap roots state invariant member
      have subset : insert address state.seen ⊆ heap.allocated := by
        intro node inside
        rcases Finset.mem_insert.mp inside with rfl | old
        · exact live_allocated heap roots (invariant.pending_live node member)
        · exact live_allocated heap roots (invariant.seen_live node old)
      have bound := Finset.card_le_card subset
      rw [Finset.card_insert_of_notMem fresh] at bound
      omega
  | succ fuel ih =>
      simp only [run, expansion_eq]
      split
      next nonempty =>
        apply ih _ (advance_invariant heap roots state invariant
          (Finset.min'_mem _ nonempty))
        have fresh := selected_fresh heap roots state invariant (Finset.min'_mem _ nonempty)
        simp only [advance, Finset.card_insert_of_notMem fresh]
        omega
      next empty => exact Finset.not_nonempty_iff_eq_empty.mp empty

theorem exhausted_seen (heap : Heap Address Value) (roots : Roots Owner Address)
    (state : State Address) (invariant : Invariant heap roots state)
    (empty : state.pending = ∅) : state.seen = footprint heap roots := by
  apply Finset.ext
  intro address
  rw [mem_footprint]
  constructor
  · exact invariant.seen_live address
  · intro live
    induction live with
    | root rooted =>
        simpa only [empty, Finset.union_empty] using
          invariant.roots_covered (Finset.mem_inter.mpr ⟨rooted.2, rooted.1⟩)
    | @step previous address _ edge ih =>
        simpa only [empty, Finset.union_empty] using
          invariant.edges_covered previous ih ((mem_successors heap previous address).mpr edge)

theorem trace_exhausted (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).final.pending = ∅ := by
  apply run_exhausted heap roots _ _ (initial_invariant heap roots)
  simp [initial]

/-- Two-sided adequacy with the semantic collector's live set. -/
theorem trace_eq_footprint (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).final.seen = footprint heap roots :=
  exhausted_seen heap roots _
    (run_invariant heap roots _ _ (initial_invariant heap roots)) (trace_exhausted heap roots)

theorem trace_expanded_nodup (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).expanded.Nodup :=
  expanded_nodup heap roots _ _ (initial_invariant heap roots)

theorem trace_expanded_iff_live (heap : Heap Address Value) (roots : Roots Owner Address)
    (address : Address) : address ∈ (trace heap roots).expanded ↔ Live heap roots address := by
  have seen := run_seen heap heap.allocated.card (initial heap roots) address
  change address ∈ (trace heap roots).final.seen ↔ _ at seen
  rw [trace_eq_footprint, mem_footprint] at seen
  simpa [initial, trace] using seen.symm

theorem trace_expanded_toFinset (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).expanded.toFinset = footprint heap roots := by
  ext address
  simp only [List.mem_toFinset, trace_expanded_iff_live, mem_footprint]

theorem trace_expansion_count (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).expanded.length = (footprint heap roots).card := by
  rw [← trace_expanded_toFinset]
  exact (List.toFinset_card_of_nodup (trace_expanded_nodup heap roots)).symm

theorem run_edgeVisits (heap : Heap Address Value) (fuel : Nat) (state : State Address) :
    (run heap fuel state).edgeVisits =
      ((run heap fuel state).expanded.map fun address => (successors heap address).card).sum := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [run, expansion_eq]
      split
      next _ => simp only [List.map_cons, List.sum_cons, ih]
      next _ => rfl

/-- The explicit scan loop visits every distinct outgoing reference of each
live cell once. Edges leading to an already seen cell still contribute a tick.
Sorting and set operations may themselves inspect addresses additionally. -/
theorem trace_edge_count (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).edgeVisits =
      ∑ address ∈ footprint heap roots, (successors heap address).card := by
  rw [show (trace heap roots).edgeVisits =
      ((trace heap roots).expanded.map fun address => (successors heap address).card).sum from
      run_edgeVisits heap _ _, ← trace_expanded_toFinset]
  exact (List.sum_toFinset _ (trace_expanded_nodup heap roots)).symm

/-- A heap built from the computed marking set, rather than deciding semantic
reachability at lookup time. The marking set is retained in this heap value. -/
def collectTraced (heap : Heap Address Value) (roots : Roots Owner Address) :
    Heap Address Value :=
  let marked := (trace heap roots).final.seen
  { lookup := fun address => if address ∈ marked then heap.lookup address else none
    allocated := marked
    allocated_iff := by
      intro address
      by_cases inside : address ∈ marked
      · simp only [inside, if_pos, true_iff]
        apply (heap.allocated_iff address).mp
        exact live_allocated heap roots ((mem_footprint heap roots address).mp
          (trace_eq_footprint heap roots ▸ inside))
      · simp [inside]
    closed := by
      intro address cell found next reference
      split at found
      next inside =>
        change next ∈ (trace heap roots).final.seen
        rw [trace_eq_footprint, mem_footprint]
        apply live_step heap roots _ found reference
        exact (mem_footprint heap roots address).mp (trace_eq_footprint heap roots ▸ inside)
      next _ => cases found }

theorem collectTraced_allocated (heap : Heap Address Value) (roots : Roots Owner Address) :
    (collectTraced heap roots).allocated = (collect heap roots).allocated :=
  trace_eq_footprint heap roots

theorem collectTraced_lookup (heap : Heap Address Value) (roots : Roots Owner Address)
    (address : Address) :
    (collectTraced heap roots).lookup address = (collect heap roots).lookup address := by
  classical
  simp only [collectTraced, trace_eq_footprint, mem_footprint, collect]

/-- Changing root labels or duplicating an address under another owner does
not repeat graph work. Enumerating those owner roots still has its own cost. -/
theorem trace_congr_rootAddresses (heap : Heap Address Value)
    (roots other : Roots Owner Address) (same : rootAddresses roots = rootAddresses other) :
    trace heap roots = trace heap other := by
  simp only [trace, initial, same]

/-! ## Lower bounds for complete traversal surveys

The comparison class starts from root occurrences, queries complete cells,
and certifies closure by following every outgoing reference of each queried
cell. Its local obligations mention roots and one-step edges, not the desired
transitive footprint. Reachability induction then forces every live cell to
occur in its query log. Repeated queries and unrelated queried cells are
permitted, but cannot improve the resulting graph-work lower bounds.

This excludes algorithms reusing a previous marking summary, special semantic
knowledge of the heap, reference counting, region reclamation, and moving or
compressed representations. It is not a black-box lower bound on all possible
collectors or a lower bound on wall-clock time.
-/

/-- The local requirements of a completed, full-reference traversal survey. -/
structure CompleteSurvey (heap : Heap Address Value) (roots : Roots Owner Address)
    (queries : List Address) : Prop where
  roots_queried : ∀ pair ∈ roots, pair.2 ∈ heap.allocated → pair.2 ∈ queries
  references_queried : ∀ address ∈ queries, ∀ next ∈ successors heap address, next ∈ queries

theorem completeSurvey_covers (heap : Heap Address Value) (roots : Roots Owner Address)
    (queries : List Address) (survey : CompleteSurvey heap roots queries) :
    footprint heap roots ⊆ queries.toFinset := by
  intro address member
  rw [List.mem_toFinset]
  have live := (mem_footprint heap roots address).mp member
  clear member
  induction live with
  | root rooted =>
      obtain ⟨pair, member, same⟩ := Finset.mem_image.mp rooted.2
      exact same ▸ survey.roots_queried pair member (same.symm ▸ rooted.1)
  | @step previous address _ edge ih =>
      exact survey.references_queried previous ih address
        ((mem_successors heap previous address).mpr edge)

theorem trace_completeSurvey (heap : Heap Address Value) (roots : Roots Owner Address) :
    CompleteSurvey heap roots (trace heap roots).expanded := by
  constructor
  · intro pair member allocated
    exact (trace_expanded_iff_live heap roots pair.2).mpr
      (live_of_root heap roots member allocated)
  · intro address queried next edge
    exact (trace_expanded_iff_live heap roots next).mpr
      (successors_live heap roots ((trace_expanded_iff_live heap roots address).mp queried) edge)

/-- Each query in this comparison class enumerates its complete reference
set. This includes repeated enumeration when a cell is queried repeatedly. -/
def surveyEdgeWork (heap : Heap Address Value) (queries : List Address) : Nat :=
  (queries.map fun address => (successors heap address).card).sum

theorem finiteSum_le_listSum (weight : Address → Nat) (queries : List Address) :
    (∑ address ∈ queries.toFinset, weight address) ≤ (queries.map weight).sum := by
  induction queries with
  | nil => simp
  | cons address rest ih =>
      simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
      by_cases repeated : address ∈ rest.toFinset
      · rw [Finset.insert_eq_of_mem repeated]
        omega
      · rw [Finset.sum_insert repeated]
        omega

theorem trace_minimal_expansions (heap : Heap Address Value) (roots : Roots Owner Address)
    (queries : List Address) (survey : CompleteSurvey heap roots queries) :
    (trace heap roots).expanded.length ≤ queries.length := by
  rw [trace_expansion_count]
  exact (Finset.card_le_card (completeSurvey_covers heap roots queries survey)).trans
    (List.toFinset_card_le queries)

theorem trace_minimal_edgeVisits (heap : Heap Address Value) (roots : Roots Owner Address)
    (queries : List Address) (survey : CompleteSurvey heap roots queries) :
    (trace heap roots).edgeVisits ≤ surveyEdgeWork heap queries := by
  rw [trace_edge_count]
  exact (Finset.sum_le_sum_of_subset
    (f := fun address => (successors heap address).card)
    (completeSurvey_covers heap roots queries survey)).trans
      (finiteSum_le_listSum _ queries)

/-- Both graph-work lower bounds are attained by the actual worklist run. -/
theorem trace_attains_graph_work_minimum (heap : Heap Address Value)
    (roots : Roots Owner Address) :
    CompleteSurvey heap roots (trace heap roots).expanded ∧
      (trace heap roots).edgeVisits = surveyEdgeWork heap (trace heap roots).expanded ∧
      ∀ queries, CompleteSurvey heap roots queries →
        (trace heap roots).expanded.length ≤ queries.length ∧
          (trace heap roots).edgeVisits ≤ surveyEdgeWork heap queries := by
  refine ⟨trace_completeSurvey heap roots, run_edgeVisits heap _ _, ?_⟩
  intro queries survey
  exact ⟨trace_minimal_expansions heap roots queries survey,
    trace_minimal_edgeVisits heap roots queries survey⟩

theorem trace_graph_work_exact (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).expanded.length + (trace heap roots).edgeVisits =
      (footprint heap roots).card +
        ∑ address ∈ footprint heap roots, (successors heap address).card := by
  rw [trace_expansion_count, trace_edge_count]

/-! ## Executable controls -/

namespace Controls

open Examples

/-- The same algorithm handles arbitrarily long current heaps over `Nat`;
there is no fixed global address cap hidden in the finite allocation set. -/
theorem chain_expansion_count (last : Nat) :
    (trace (chainHeap last) oneRoot).expanded.length = last + 1 := by
  rw [trace_expansion_count, chain_footprint]
  exact Finset.card_range _

def sharedCycleRoots : Roots Nat (Fin 3) := {(0, 0), (1, 2)}

/-- The second root and the back edge share node 2, but every node is expanded
once. The closing edge 2 -> 1 is still counted. -/
theorem shared_cycle_once :
    (trace cyclicHeap sharedCycleRoots).expanded = [0, 1, 2] ∧
      (trace cyclicHeap sharedCycleRoots).edgeVisits = 3 := by
  change (run cyclicHeap 3 (initial cyclicHeap sharedCycleRoots)).expanded = [0, 1, 2] ∧
    (run cyclicHeap 3 (initial cyclicHeap sharedCycleRoots)).edgeVisits = 3
  simp only [run, expansion_eq]
  decide

theorem unrelated_garbage_not_expanded :
    (trace cyclicHeap ({(0, 1)} : Roots Nat (Fin 3))).expanded = [1, 2] ∧
      (trace cyclicHeap ({(0, 1)} : Roots Nat (Fin 3))).edgeVisits = 2 ∧
      (collectTraced cyclicHeap ({(0, 1)} : Roots Nat (Fin 3))).lookup 0 = none := by
  change (run cyclicHeap 3 (initial cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)))).expanded = [1, 2] ∧
    (run cyclicHeap 3 (initial cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)))).edgeVisits = 2 ∧ _
  simp only [collectTraced, trace]
  change (run cyclicHeap 3 (initial cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)))).expanded = [1, 2] ∧
    (run cyclicHeap 3 (initial cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)))).edgeVisits = 2 ∧
    (if 0 ∈ (run cyclicHeap 3 (initial cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)))).final.seen
      then cyclicHeap.lookup 0 else none) = none
  simp only [run, expansion_eq]
  decide

theorem duplicate_root_addresses_same_graph_work :
    trace cyclicHeap ({(0, 1), (1, 1)} : Roots Nat (Fin 3)) =
      trace cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)) :=
  trace_congr_rootAddresses cyclicHeap _ _ (by decide)

/-- Repeated entries in an input enumeration still consume visits, even when
the queue correctly deduplicates their target. -/
theorem repeated_reference_is_counted :
    scanReferences ({0} : Finset Nat) ∅ [0, 1, 1] = ({1}, 3) := by decide

/-- Stopping after one expansion leaves a live descendant unexpanded. A
budget boundary therefore cannot be reported as completed tracing. -/
theorem premature_stop_loses_live_descendant :
    (run cyclicHeap 1 (initial cyclicHeap sharedCycleRoots)).final.pending ≠ ∅ ∧
      1 ∉ (run cyclicHeap 1 (initial cyclicHeap sharedCycleRoots)).final.seen ∧
      Live cyclicHeap sharedCycleRoots 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [run, expansion_eq]
    decide
  · simp only [run, expansion_eq]
    decide
  · apply (trace_expanded_iff_live cyclicHeap sharedCycleRoots 1).mp
    rw [shared_cycle_once.1]
    decide

theorem root_queries_alone_do_not_certify_closure :
    ¬ CompleteSurvey cyclicHeap ({(0, 0)} : Roots Nat (Fin 3)) [0] := by
  intro survey
  have impossible := survey.references_queried 0 (by decide) 1 (by decide)
  simp at impossible

theorem redundant_queries_strictly_more_work :
    CompleteSurvey cyclicHeap sharedCycleRoots [0, 1, 2, 1] ∧
      (trace cyclicHeap sharedCycleRoots).expanded.length < ([0, 1, 2, 1] : List (Fin 3)).length ∧
      (trace cyclicHeap sharedCycleRoots).edgeVisits <
        surveyEdgeWork cyclicHeap [0, 1, 2, 1] := by
  refine ⟨?_, ?_, ?_⟩
  swap
  · rw [shared_cycle_once.1]
    decide
  swap
  · rw [shared_cycle_once.2]
    decide
  constructor
  · intro pair member _
    simp only [sharedCycleRoots, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> decide
  · intro address _ next _
    have bound := next.isLt
    have cases : next = 0 ∨ next = 1 ∨ next = 2 := by
      have : next.val = 0 ∨ next.val = 1 ∨ next.val = 2 := by omega
      rcases this with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases cases with rfl | rfl | rfl <;> decide

end Controls

end Mettapedia.Machines.ResourceOwnership.TraceWork

/-!
## Retained ordered resource copying

The source is a fixed finite heap with an ordered slot realization. A poll
consumes one root occurrence, writes one actual slot, or completes one shell.
A pending shell already has an identity, so cycles and shared targets use
backedges without recursive waiting. Only a fully closed graph is published.

The destination heap is an observation of the actual saved headers and slot
buffers; relocation is derived after execution. Its set-valued references are
a semantic readout, not a second producer or a charged list reconstruction.
Lookup, finite-set operations, shell allocation, source capture, native alias
canonicalization, disposal and finalizers retain separate representation and
service prices. Mutable source stability and authority to transport hidden
scope or Need resources are admission obligations, not consequences of these
fixed-source laws. The export-owner guard is separate from structural copying.
-/

namespace Mettapedia.Machines.ResourceOwnership.TraceWork.RetainedCopy

open Mettapedia.GSLT.Dynamics.StoreReachability (Reach)

universe v
variable {A : Type} {V : Type v} [LinearOrder A]

/-- An ordered physical-slot realization of the existing finite heap.
Repeated slots are retained even though heap reachability uses sets. -/
structure Source (A : Type) (V : Type v) [LinearOrder A] where
  heap : Heap A V
  slots : A → List A
  slots_exact : ∀ a, (slots a).toFinset = successors heap a

structure Frame (A : Type) where
  source : A
  remaining : List A
  deriving DecidableEq, Repr

/-- Images have their own owner namespace. Reserving an image does not
make its unfinished contents observable. -/
abbrev Image (A : Type) := Nat × A

structure State (A : Type) (V : Type v) [DecidableEq A] where
  owner : Nat
  originals : List A
  roots : List A
  frames : List (Frame A)
  reserved : Finset A
  complete : Finset A
  headers : A → Option (Cell A V)
  count : A → Nat
  written : A → Nat → Option (Image A)
  refused : Bool

def initial (owner : Nat) (roots : List A) : State A V where
  owner := owner
  originals := roots
  roots := roots
  frames := []
  reserved := ∅
  complete := ∅
  headers := fun _ => none
  count := fun _ => 0
  written := fun _ _ => none
  refused := false

def image (state : State A V) (a : A) : Image A := (state.owner, a)

def ready (state : State A V) : Bool :=
  !state.refused && state.roots.isEmpty && state.frames.isEmpty

def reserve (source : Source A V) (a : A) (state : State A V) : State A V :=
  { state with reserved := insert a state.reserved
               headers := Function.update state.headers a (source.heap.lookup a)
               count := Function.update state.count a 0
               written := Function.update state.written a (fun _ => none) }

def writeSlot (a b : A) (state : State A V) : State A V :=
  { state with
    count := Function.update state.count a (state.count a + 1)
    written := Function.update state.written a
      (Function.update (state.written a) (state.count a) (some (image state b))) }

def pushFresh (source : Source A V) (a : A) (state : State A V) : State A V :=
  { reserve source a state with frames := ⟨a, source.slots a⟩ :: state.frames }

/-- Exactly one root, slot, or node-completion action. Discovery reserves
before descent; an edge to an already pending shell never waits for that
shell's contents. No source list is mapped, reversed or concatenated. -/
def step (source : Source A V) (state : State A V) : State A V :=
  if state.refused then state else
  match state.frames with
  | frame :: frames =>
      match frame.remaining with
      | [] => { state with frames := frames, complete := insert frame.source state.complete }
      | child :: remaining =>
          let next := writeSlot frame.source child
            { state with frames := ⟨frame.source, remaining⟩ :: frames }
          if child ∈ state.reserved then next
          else
            match source.heap.lookup child with
            | none => { state with refused := true }
            | some _ =>
                let next := writeSlot frame.source child (pushFresh source child state)
                { next with frames := ⟨child, source.slots child⟩ ::
                    ⟨frame.source, remaining⟩ :: frames }
  | [] =>
      match state.roots with
      | [] => state
      | root :: roots =>
          let next := { state with roots := roots }
          if root ∈ state.reserved then next
          else
            match source.heap.lookup root with
            | none => { state with refused := true }
            | some _ =>
                { pushFresh source root state with roots := roots }

@[simp] theorem step_owner (source : Source A V) (state : State A V) :
    (step source state).owner = state.owner := by
  unfold step
  split
  · rfl
  · split
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl

theorem image_injective (state : State A V) : Function.Injective (image state) := by
  intro a b equal
  exact congrArg Prod.snd equal

theorem different_owner_images (first second : State A V) (different : first.owner ≠ second.owner)
    (a b : A) : image first a ≠ image second b := by
  intro equal
  exact different (congrArg Prod.fst equal)

def rootsOf (roots : List A) : Roots Unit A :=
  roots.toFinset.image fun a => ((), a)

theorem root_live (source : Source A V) (roots : List A)
    (valid : ∀ a ∈ roots, a ∈ source.heap.allocated) {a : A} (member : a ∈ roots) :
    Live source.heap (rootsOf roots) a := by
  exact live_of_root source.heap _
    (Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr member, rfl⟩) (valid a member)

theorem slot_live (source : Source A V) (roots : List A)
    {a b : A} (live : Live source.heap (rootsOf roots) a) (member : b ∈ source.slots a) :
    Live source.heap (rootsOf roots) b := by
  apply successors_live source.heap _ live
  rw [← source.slots_exact]
  exact List.mem_toFinset.mpr member

omit [LinearOrder A] in
theorem drop_head {xs : List A} {i : Nat} {a : A} {rest : List A}
    (equal : xs.drop i = a :: rest) : xs[i]? = some a := by
  have atHead := congrArg (fun ys => ys[0]?) equal
  simpa using atHead

omit [LinearOrder A] in
theorem drop_tail {xs : List A} {i : Nat} {a : A} {rest : List A}
    (equal : xs.drop i = a :: rest) : xs.drop (i + 1) = rest := by
  have tail := congrArg (List.drop 1) equal
  simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using tail

/-- The invariant concerns actual buffers and source coordinates, not an
assumed correct target heap. Captured source stability is separate from the
runtime's mutable-resource admission. -/
structure Invariant (source : Source A V) (roots : List A) (state : State A V) : Prop where
  not_refused : state.refused = false
  root_live : ∀ a ∈ state.roots, Live source.heap (rootsOf roots) a
  reserved_live : ∀ a ∈ state.reserved, Live source.heap (rootsOf roots) a
  roots_covered : ∀ a ∈ roots, a ∈ state.roots ∨ a ∈ state.reserved
  complete_reserved : state.complete ⊆ state.reserved
  complete_count : ∀ a ∈ state.complete, state.count a = (source.slots a).length
  header : ∀ a ∈ state.reserved, state.headers a = source.heap.lookup a
  bounded : ∀ a ∈ state.reserved, state.count a ≤ (source.slots a).length
  written_prefix : ∀ a ∈ state.reserved, ∀ i b, (source.slots a)[i]? = some b →
    i < state.count a → state.written a i = some (image state b) ∧ b ∈ state.reserved
  frames_reserved : ∀ frame ∈ state.frames, frame.source ∈ state.reserved
  frames_remaining : ∀ frame ∈ state.frames,
    frame.remaining = (source.slots frame.source).drop (state.count frame.source)
  frames_incomplete : ∀ frame ∈ state.frames, frame.source ∉ state.complete
  frame_sources_nodup : (state.frames.map Frame.source).Nodup
  unfinished : ∀ a ∈ state.reserved, a ∈ state.complete ∨ ∃ frame ∈ state.frames, frame.source = a
  originals_eq : state.originals = roots

theorem initial_invariant (source : Source A V) (roots : List A) (owner : Nat)
    (valid : ∀ a ∈ roots, a ∈ source.heap.allocated) :
    Invariant source roots (initial owner roots) := by
  constructor
  · rfl
  · intro a member; exact root_live source roots valid member
  · simp [initial]
  · intro a member; exact Or.inl member
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · rfl

theorem pushFresh_invariant (source : Source A V) (roots : List A)
    (state : State A V) (valid : Invariant source roots state) (a : A)
    (fresh : a ∉ state.reserved) (live : Live source.heap (rootsOf roots) a) :
    Invariant source roots (pushFresh source a state) := by
  have incomplete : a ∉ state.complete := fun member => fresh (valid.complete_reserved member)
  have distinct : ∀ frame ∈ state.frames, frame.source ≠ a := by
    intro frame member equal
    exact fresh (equal ▸ valid.frames_reserved frame member)
  constructor
  · exact valid.not_refused
  · exact valid.root_live
  · intro b member
    rcases Finset.mem_insert.mp member with rfl | old
    · exact live
    · exact valid.reserved_live b old
  · intro b member
    rcases valid.roots_covered b member with pending | old
    · exact Or.inl pending
    · exact Or.inr (Finset.mem_insert_of_mem old)
  · intro b member
    exact Finset.mem_insert_of_mem (valid.complete_reserved member)
  · intro b member
    have different : b ≠ a := by rintro rfl; exact incomplete member
    simpa [pushFresh, reserve, different] using valid.complete_count b member
  · intro b member
    rcases Finset.mem_insert.mp member with rfl | old
    · simp [pushFresh, reserve]
    · have different : b ≠ a := by rintro rfl; exact fresh old
      simpa [pushFresh, reserve, different] using valid.header b old
  · intro b member
    rcases Finset.mem_insert.mp member with rfl | old
    · simp [pushFresh, reserve]
    · have different : b ≠ a := by rintro rfl; exact fresh old
      simpa [pushFresh, reserve, different] using valid.bounded b old
  · intro b member i child atSlot before
    rcases Finset.mem_insert.mp member with rfl | old
    · simp [pushFresh, reserve] at before
    · have different : b ≠ a := by rintro rfl; exact fresh old
      have earlier : i < state.count b := by simpa [pushFresh, reserve, different] using before
      obtain ⟨written, reserved⟩ := valid.written_prefix b old i child atSlot earlier
      exact ⟨by simpa [pushFresh, reserve, image, different] using written,
        Finset.mem_insert_of_mem reserved⟩
  · intro frame member
    rcases List.mem_cons.mp member with rfl | old
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (valid.frames_reserved frame old)
  · intro frame member
    rcases List.mem_cons.mp member with rfl | old
    · simp [pushFresh, reserve]
    · simpa [pushFresh, reserve, distinct frame old] using valid.frames_remaining frame old
  · intro frame member
    rcases List.mem_cons.mp member with rfl | old
    · exact incomplete
    · exact valid.frames_incomplete frame old
  · simp only [pushFresh, List.map_cons, List.nodup_cons]
    refine ⟨?_, valid.frame_sources_nodup⟩
    simp only [List.mem_map, not_exists, not_and]
    intro frame member equal
    exact distinct frame member equal
  · intro b member
    rcases Finset.mem_insert.mp member with rfl | old
    · exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    · rcases valid.unfinished b old with completed | ⟨frame, member, equal⟩
      · exact Or.inl completed
      · exact Or.inr ⟨frame, List.mem_cons_of_mem _ member, equal⟩
  · exact valid.originals_eq

theorem popRoot_invariant (source : Source A V) (roots : List A)
    (state : State A V) (valid : Invariant source roots state) (a : A) (rest : List A)
    (pending : state.roots = a :: rest) (reserved : a ∈ state.reserved) :
    Invariant source roots { state with roots := rest } := by
  refine { valid with root_live := ?_, roots_covered := ?_ }
  · intro b member
    exact valid.root_live b (pending ▸ List.mem_cons_of_mem a member)
  · intro b member
    rcases valid.roots_covered b member with unvisited | found
    · rw [pending] at unvisited
      rcases List.mem_cons.mp unvisited with rfl | later
      · exact Or.inr reserved
      · exact Or.inl later
    · exact Or.inr found

theorem finish_invariant (source : Source A V) (roots : List A)
    (state : State A V) (valid : Invariant source roots state)
    (frame : Frame A) (rest : List (Frame A))
    (stack : state.frames = frame :: rest) (empty : frame.remaining = []) :
    Invariant source roots
      { state with frames := rest, complete := insert frame.source state.complete } := by
  have member : frame ∈ state.frames := stack ▸ List.mem_cons_self
  have reserved := valid.frames_reserved frame member
  have count : state.count frame.source = (source.slots frame.source).length := by
    have remaining := valid.frames_remaining frame member
    rw [empty] at remaining
    have lengths := congrArg List.length remaining
    simp only [List.length_nil, List.length_drop] at lengths
    have bound := valid.bounded frame.source reserved
    omega
  have distinct : ∀ next ∈ rest, next.source ≠ frame.source := by
    have nodup := valid.frame_sources_nodup
    rw [stack] at nodup
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at nodup
    intro next inside equal
    exact nodup.1 next inside equal
  refine { valid with
    complete_reserved := ?_
    complete_count := ?_
    frames_reserved := ?_
    frames_remaining := ?_
    frames_incomplete := ?_
    frame_sources_nodup := ?_
    unfinished := ?_ }
  · intro a inside
    rcases Finset.mem_insert.mp inside with rfl | earlier
    · exact reserved
    · exact valid.complete_reserved earlier
  · intro a inside
    rcases Finset.mem_insert.mp inside with rfl | earlier
    · exact count
    · exact valid.complete_count a earlier
  · intro next inside
    exact valid.frames_reserved next (stack ▸ List.mem_cons_of_mem frame inside)
  · intro next inside
    exact valid.frames_remaining next (stack ▸ List.mem_cons_of_mem frame inside)
  · intro next inside inserted
    rcases Finset.mem_insert.mp inserted with equal | earlier
    · exact distinct next inside equal
    · exact valid.frames_incomplete next (stack ▸ List.mem_cons_of_mem frame inside) earlier
  · have nodup := valid.frame_sources_nodup
    rw [stack] at nodup
    exact (List.nodup_cons.mp nodup).2
  · intro a inside
    rcases valid.unfinished a inside with completed | ⟨next, member, equal⟩
    · exact Or.inl (Finset.mem_insert_of_mem completed)
    · rw [stack] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact Or.inl (equal ▸ Finset.mem_insert_self _ _)
      · exact Or.inr ⟨next, later, equal⟩

def advanceFrame (a b : A) (remaining : List A) (before after : List (Frame A))
    (state : State A V) : State A V :=
  { writeSlot a b state with frames := before ++ ⟨a, remaining⟩ :: after }

theorem advanceFrame_invariant (source : Source A V) (roots : List A)
    (state : State A V) (valid : Invariant source roots state)
    (a b : A) (remaining : List A) (before after : List (Frame A))
    (stack : state.frames = before ++ ⟨a, b :: remaining⟩ :: after)
    (distinct : ∀ frame ∈ before ++ after, frame.source ≠ a)
    (child : b ∈ state.reserved) :
    Invariant source roots (advanceFrame a b remaining before after state) := by
  let next := advanceFrame a b remaining before after state
  have oldMember : (⟨a, b :: remaining⟩ : Frame A) ∈ state.frames := by
    rw [stack]; simp
  have reserved := valid.frames_reserved _ oldMember
  have incomplete := valid.frames_incomplete _ oldMember
  have atTail : (source.slots a).drop (state.count a) = b :: remaining :=
    (valid.frames_remaining _ oldMember).symm
  have atHead := drop_head atTail
  have shorter := drop_tail atTail
  have enough : state.count a < (source.slots a).length := by
    have lengths := congrArg List.length atTail
    simp only [List.length_drop, List.length_cons] at lengths
    omega
  have sources : next.frames.map Frame.source = state.frames.map Frame.source := by
    simp [next, advanceFrame, stack]
  have oldFrame (frame : Frame A) (member : frame ∈ next.frames) :
      ∃ old ∈ state.frames, old.source = frame.source := by
    have inside : frame.source ∈ state.frames.map Frame.source := by
      rw [← sources]; exact List.mem_map.mpr ⟨frame, member, rfl⟩
    exact List.mem_map.mp inside
  constructor
  · exact valid.not_refused
  · exact valid.root_live
  · exact valid.reserved_live
  · exact valid.roots_covered
  · exact valid.complete_reserved
  · intro node member
    have different : node ≠ a := by rintro rfl; exact incomplete member
    simpa [next, advanceFrame, writeSlot, different] using valid.complete_count node member
  · exact valid.header
  · intro node member
    by_cases same : node = a
    · subst node
      simpa [next, advanceFrame, writeSlot] using Nat.succ_le_of_lt enough
    · simpa [next, advanceFrame, writeSlot, same] using valid.bounded node member
  · intro node member i value slot earlier
    by_cases same : node = a
    · subst node
      have bound : i < state.count a + 1 := by simpa [next, advanceFrame, writeSlot] using earlier
      by_cases position : i = state.count a
      · subst i
        have equal : value = b := Option.some.inj (slot.symm.trans atHead)
        subst value
        exact ⟨by simp [advanceFrame, writeSlot, image], child⟩
      · have old : i < state.count a := by omega
        obtain ⟨written, seen⟩ := valid.written_prefix a member i value slot old
        exact ⟨by simpa [next, advanceFrame, writeSlot, image, position] using written, seen⟩
    · have old : i < state.count node := by simpa [next, advanceFrame, writeSlot, same] using earlier
      obtain ⟨written, seen⟩ := valid.written_prefix node member i value slot old
      exact ⟨by simpa [next, advanceFrame, writeSlot, image, same] using written, seen⟩
  · intro frame member
    obtain ⟨old, inside, equal⟩ := oldFrame frame member
    exact equal ▸ valid.frames_reserved old inside
  · intro frame member
    change frame ∈ before ++ (⟨a, remaining⟩ : Frame A) :: after at member
    rcases List.mem_append.mp member with first | later
    · have different := distinct frame (List.mem_append_left _ first)
      have old := valid.frames_remaining frame (by rw [stack]; exact List.mem_append_left _ first)
      simpa [next, advanceFrame, writeSlot, different] using old
    · rcases List.mem_cons.mp later with rfl | last
      · simpa [next, advanceFrame, writeSlot] using shorter.symm
      · have different := distinct frame (List.mem_append_right _ last)
        have old := valid.frames_remaining frame (by rw [stack]; exact List.mem_append_right _ (List.mem_cons_of_mem _ last))
        simpa [next, advanceFrame, writeSlot, different] using old
  · intro frame member
    obtain ⟨old, inside, equal⟩ := oldFrame frame member
    exact equal ▸ valid.frames_incomplete old inside
  · rw [show (advanceFrame a b remaining before after state).frames.map Frame.source =
        state.frames.map Frame.source from sources]
    exact valid.frame_sources_nodup
  · intro node member
    rcases valid.unfinished node member with done | ⟨old, inside, equal⟩
    · exact Or.inl done
    · right
      have mapped : node ∈ next.frames.map Frame.source := by
        rw [sources]; exact List.mem_map.mpr ⟨old, inside, equal⟩
      exact List.mem_map.mp mapped
  · exact valid.originals_eq

theorem step_invariant (source : Source A V) (roots : List A)
    (state : State A V) (valid : Invariant source roots state) :
    Invariant source roots (step source state) := by
  have clear := valid.not_refused
  cases stack : state.frames with
  | nil =>
      cases pending : state.roots with
      | nil => simpa [step, clear, stack, pending] using valid
      | cons a rest =>
          by_cases seen : a ∈ state.reserved
          · have next := popRoot_invariant source roots state valid a rest pending seen
            simpa [step, clear, stack, pending, seen] using next
          · have live := valid.root_live a (pending ▸ List.mem_cons_self)
            have allocated := live_allocated source.heap _ live
            obtain ⟨cell, found⟩ := (source.heap.allocated_iff a).mp allocated
            have pushed := pushFresh_invariant source roots state valid a seen live
            have next := popRoot_invariant source roots (pushFresh source a state) pushed
              a rest pending (Finset.mem_insert_self _ _)
            simpa [step, clear, stack, pending, seen, found] using next
  | cons frame rest =>
      have member : frame ∈ state.frames := stack ▸ List.mem_cons_self
      have reserved := valid.frames_reserved frame member
      have distinct : ∀ next ∈ rest, next.source ≠ frame.source := by
        have nodup := valid.frame_sources_nodup
        rw [stack] at nodup
        simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at nodup
        intro next inside equal
        exact nodup.1 next inside equal
      cases remaining : frame.remaining with
      | nil =>
          have next := finish_invariant source roots state valid frame rest stack remaining
          simpa [step, clear, stack, remaining] using next
      | cons child tail =>
          have original : (source.slots frame.source).drop (state.count frame.source) = child :: tail :=
            (valid.frames_remaining frame member).symm.trans remaining
          have edge : child ∈ source.slots frame.source :=
            List.mem_of_mem_drop (original ▸ List.mem_cons_self)
          by_cases seen : child ∈ state.reserved
          · have next := advanceFrame_invariant source roots state valid frame.source child tail [] rest
              (by cases frame; simp_all) (by simpa using distinct) seen
            simpa [step, clear, stack, remaining, seen, advanceFrame, writeSlot, image] using next
          · have live := slot_live source roots (valid.reserved_live frame.source reserved) edge
            have allocated := live_allocated source.heap _ live
            obtain ⟨cell, found⟩ := (source.heap.allocated_iff child).mp allocated
            have different : child ≠ frame.source := by rintro rfl; exact seen reserved
            have pushed := pushFresh_invariant source roots state valid child seen live
            have next := advanceFrame_invariant source roots (pushFresh source child state) pushed
              frame.source child tail [⟨child, source.slots child⟩] rest
              (by cases frame; simp_all [pushFresh]) (by
                intro next inside
                simp only [List.singleton_append, List.mem_cons] at inside
                rcases inside with rfl | later
                · exact different
                · exact distinct next later) (Finset.mem_insert_self _ _)
            simpa [step, clear, stack, remaining, seen, found, advanceFrame] using next

def frameWork (frame : Frame A) : Nat := 1 + frame.remaining.length

def potential (source : Source A V) (state : State A V) : Nat :=
  state.roots.length + (state.frames.map frameWork).sum +
    (SDiff.sdiff source.heap.allocated state.reserved).sum (fun a => 1 + (source.slots a).length)

@[simp] theorem initial_potential (source : Source A V) (roots : List A) (owner : Nat) :
    potential source (initial owner roots) =
      roots.length + source.heap.allocated.sum (fun a => 1 + (source.slots a).length) := by
  simp [potential, initial]

theorem reserve_credits (source : Source A V) (state : State A V) (a : A)
    (allocated : a ∈ source.heap.allocated) (fresh : a ∉ state.reserved) :
    (SDiff.sdiff source.heap.allocated state.reserved).sum (fun b => 1 + (source.slots b).length) =
      (1 + (source.slots a).length) +
        (SDiff.sdiff source.heap.allocated (insert a state.reserved)).sum
          (fun b => 1 + (source.slots b).length) := by
  have exactSet : SDiff.sdiff source.heap.allocated state.reserved =
      insert a (SDiff.sdiff source.heap.allocated (insert a state.reserved)) := by
    ext b
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨present, absent⟩
      by_cases equal : b = a
      · exact Or.inl equal
      · exact Or.inr ⟨present, not_or.mpr ⟨equal, absent⟩⟩
    · rintro (rfl | ⟨present, absent⟩)
      · exact ⟨allocated, fresh⟩
      · exact ⟨present, fun member => absent (Or.inr member)⟩
  rw [exactSet, Finset.sum_insert]
  simp

theorem pushFresh_potential (source : Source A V) (state : State A V) (a : A)
    (allocated : a ∈ source.heap.allocated) (fresh : a ∉ state.reserved) :
    potential source (pushFresh source a state) = potential source state := by
  have credits := reserve_credits source state a allocated fresh
  simp only [potential, pushFresh, reserve, List.map_cons, List.sum_cons, frameWork]
  omega

theorem popRoot_potential (source : Source A V) (state : State A V) (a : A) (rest : List A)
    (pending : state.roots = a :: rest) :
    potential source { state with roots := rest } + 1 = potential source state := by
  simp only [potential, pending, List.length_cons]
  omega

theorem finish_potential (source : Source A V) (state : State A V)
    (frame : Frame A) (rest : List (Frame A))
    (stack : state.frames = frame :: rest) (empty : frame.remaining = []) :
    potential source { state with frames := rest, complete := insert frame.source state.complete } + 1 =
      potential source state := by
  simp only [potential, stack, List.map_cons, List.sum_cons, frameWork, empty, List.length_nil]
  omega

theorem advanceFrame_potential (source : Source A V) (state : State A V)
    (a b : A) (remaining : List A) (before after : List (Frame A))
    (stack : state.frames = before ++ ⟨a, b :: remaining⟩ :: after) :
    potential source (advanceFrame a b remaining before after state) + 1 =
      potential source state := by
  simp only [potential, advanceFrame, writeSlot, stack, List.map_append,
    List.sum_append, List.map_cons, List.sum_cons, frameWork, List.length_cons]
  omega

theorem step_potential (source : Source A V) (roots : List A)
    (state : State A V) (valid : Invariant source roots state) (running : ready state = false) :
    potential source (step source state) + 1 = potential source state := by
  have clear := valid.not_refused
  cases stack : state.frames with
  | nil =>
      cases pending : state.roots with
      | nil => simp [ready, clear, stack, pending] at running
      | cons a rest =>
          by_cases seen : a ∈ state.reserved
          · simpa [step, clear, stack, pending, seen] using popRoot_potential source state a rest pending
          · have live := valid.root_live a (pending ▸ List.mem_cons_self)
            have allocated := live_allocated source.heap _ live
            obtain ⟨cell, found⟩ := (source.heap.allocated_iff a).mp allocated
            have removed := popRoot_potential source (pushFresh source a state) a rest pending
            rw [pushFresh_potential source state a allocated seen] at removed
            simpa [step, clear, stack, pending, seen, found] using removed
  | cons frame rest =>
      have member : frame ∈ state.frames := stack ▸ List.mem_cons_self
      cases remaining : frame.remaining with
      | nil => simpa [step, clear, stack, remaining] using finish_potential source state frame rest stack remaining
      | cons child tail =>
          have original : (source.slots frame.source).drop (state.count frame.source) = child :: tail :=
            (valid.frames_remaining frame member).symm.trans remaining
          have edge : child ∈ source.slots frame.source :=
            List.mem_of_mem_drop (original ▸ List.mem_cons_self)
          by_cases seen : child ∈ state.reserved
          · have decrease := advanceFrame_potential source state frame.source child tail [] rest
              (by cases frame; simp_all)
            simpa [step, clear, stack, remaining, seen, advanceFrame, writeSlot, image] using decrease
          · have live := slot_live source roots (valid.reserved_live _ (valid.frames_reserved frame member)) edge
            have allocated := live_allocated source.heap _ live
            obtain ⟨cell, found⟩ := (source.heap.allocated_iff child).mp allocated
            have decrease := advanceFrame_potential source (pushFresh source child state)
              frame.source child tail [⟨child, source.slots child⟩] rest
              (by cases frame; simp_all [pushFresh])
            rw [pushFresh_potential source state child allocated seen] at decrease
            simpa [step, clear, stack, remaining, seen, found, advanceFrame] using decrease

theorem ready_lists (state : State A V) (finished : ready state = true) :
    state.roots = [] ∧ state.frames = [] := by
  have fields : (state.refused = false ∧ state.roots = []) ∧ state.frames = [] := by
    simpa [ready, Bool.and_eq_true] using finished
  exact ⟨fields.1.2, fields.2⟩

theorem ready_complete (source : Source A V) (roots : List A) (state : State A V)
    (valid : Invariant source roots state) (finished : ready state = true) :
    state.complete = state.reserved := by
  apply Finset.Subset.antisymm valid.complete_reserved
  intro a reserved
  rcases valid.unfinished a reserved with done | ⟨frame, member, _⟩
  · exact done
  · rw [(ready_lists state finished).2] at member
    cases member

def references (state : State A V) (a : A) : Finset (Image A) :=
  (Finset.range (state.count a)).biUnion fun i => (state.written a i).toFinset

theorem complete_references (source : Source A V) (roots : List A) (state : State A V)
    (valid : Invariant source roots state) (a : A) (done : a ∈ state.complete) :
    references state a = (successors source.heap a).image (image state) := by
  have reserved := valid.complete_reserved done
  have count := valid.complete_count a done
  ext target
  constructor
  · intro member
    obtain ⟨i, inside, stored⟩ := Finset.mem_biUnion.mp member
    have bound : i < (source.slots a).length := by simpa [count] using Finset.mem_range.mp inside
    let child := (source.slots a)[i]
    have atSlot : (source.slots a)[i]? = some child := by simp [child, bound]
    have written := (valid.written_prefix a reserved i child atSlot (by omega)).1
    have same : target = image state child := by
      have selected : state.written a i = some target := by simpa using stored
      exact Option.some.inj (selected.symm.trans written)
    apply Finset.mem_image.mpr
    refine ⟨child, ?_, same.symm⟩
    rw [← source.slots_exact]
    exact List.mem_toFinset.mpr (List.mem_of_getElem? atSlot)
  · intro member
    obtain ⟨child, edge, rfl⟩ := Finset.mem_image.mp member
    rw [← source.slots_exact] at edge
    have inList := List.mem_toFinset.mp edge
    obtain ⟨i, bound, equal⟩ := List.mem_iff_getElem.mp inList
    have atSlot : (source.slots a)[i]? = some child := by simp [bound, equal]
    have written := (valid.written_prefix a reserved i child atSlot (by omega)).1
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_range.mpr (by omega), by simp [written]⟩

theorem ready_edges (source : Source A V) (roots : List A) (state : State A V)
    (valid : Invariant source roots state) (finished : ready state = true)
    (a : A) (reserved : a ∈ state.reserved) :
    successors source.heap a ⊆ state.reserved := by
  intro child edge
  have done : a ∈ state.complete := by
    rw [ready_complete source roots state valid finished]
    exact reserved
  rw [← source.slots_exact] at edge
  obtain ⟨i, bound, equal⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp edge)
  have atSlot : (source.slots a)[i]? = some child := by simp [bound, equal]
  exact (valid.written_prefix a reserved i child atSlot (by have := valid.complete_count a done; omega)).2

theorem rootsOf_addresses (roots : List A) : rootAddresses (rootsOf roots) = roots.toFinset := by
  simp [rootAddresses, rootsOf, Finset.image_image]

theorem ready_footprint (source : Source A V) (roots : List A) (state : State A V)
    (valid : Invariant source roots state) (finished : ready state = true) :
    state.reserved = footprint source.heap (rootsOf roots) := by
  apply exhausted_seen source.heap (rootsOf roots) ⟨state.reserved, ∅⟩
  · constructor
    · exact valid.reserved_live
    · simp
    · simp
    · intro a inside
      have member : a ∈ roots := by
        have root := (Finset.mem_inter.mp inside).1
        rw [rootsOf_addresses] at root
        exact List.mem_toFinset.mp root
      rcases valid.roots_covered a member with unvisited | reserved
      · rw [(ready_lists state finished).1] at unvisited
        cases unvisited
      · exact Finset.mem_union_left _ reserved
    · intro a reserved
      simpa using ready_edges source roots state valid finished a reserved
  · rfl

/-- Readout of the actual private slot buffer; this is not a producer step. -/
def copiedCell (state : State A V) (a : A) (header : Cell A V) : Cell (Image A) V :=
  ⟨header.value, references state a, header.bytes⟩

def copiedLookup (state : State A V) (target : Image A) : Option (Cell (Image A) V) :=
  if target.1 = state.owner ∧ target.2 ∈ state.complete then
    (state.headers target.2).map (copiedCell state target.2)
  else none

theorem copiedLookup_image (state : State A V) (a : A) :
    copiedLookup state (image state a) =
      if a ∈ state.complete then (state.headers a).map (copiedCell state a) else none := by
  simp [copiedLookup, image]

theorem copiedLookup_foreign (state : State A V) (owner : Nat) (a : A)
    (different : owner ≠ state.owner) : copiedLookup state (owner, a) = none := by
  simp [copiedLookup, different]

theorem copiedLookup_complete (source : Source A V) (roots : List A) (state : State A V)
    (valid : Invariant source roots state) (a : A) (done : a ∈ state.complete) :
    copiedLookup state (image state a) =
      (source.heap.lookup a).map (Cell.relocate (image state) id) := by
  rw [copiedLookup_image, if_pos done, valid.header a (valid.complete_reserved done)]
  cases found : source.heap.lookup a with
  | none => rfl
  | some cell =>
      simp only [Option.map_some]
      congr 1
      unfold copiedCell Cell.relocate
      congr 1
      simpa [successors, found] using complete_references source roots state valid a done

/-- Only a globally closed copy has a heap readout. Pending nodes cannot
manufacture the closure evidence required by the existing heap owner. -/
def destination (source : Source A V) (roots : List A) (state : State A V)
    (valid : Invariant source roots state) (finished : ready state = true) : Heap (Image A) V where
  lookup := copiedLookup state
  allocated := state.complete.image (image state)
  allocated_iff target := by
    constructor
    · intro member
      obtain ⟨a, done, rfl⟩ := Finset.mem_image.mp member
      have live := valid.reserved_live a (valid.complete_reserved done)
      obtain ⟨cell, found⟩ := (source.heap.allocated_iff a).mp (live_allocated source.heap _ live)
      refine ⟨Cell.relocate (image state) id cell, ?_⟩
      rw [copiedLookup_complete source roots state valid a done, found]
      rfl
    · rintro ⟨cell, found⟩
      by_cases condition : target.1 = state.owner ∧ target.2 ∈ state.complete
      · exact Finset.mem_image.mpr ⟨target.2, condition.2, Prod.ext condition.1.symm rfl⟩
      · simp [copiedLookup, condition] at found
  closed target cell found next edge := by
    by_cases condition : target.1 = state.owner ∧ target.2 ∈ state.complete
    · have selected : (state.headers target.2).map (copiedCell state target.2) = some cell := by
        simpa [copiedLookup, condition] using found
      obtain ⟨header, _, rfl⟩ := Option.map_eq_some_iff.mp selected
      change next ∈ references state target.2 at edge
      rw [complete_references source roots state valid target.2 condition.2] at edge
      obtain ⟨child, reference, rfl⟩ := Finset.mem_image.mp edge
      have seen := ready_edges source roots state valid finished target.2
        (valid.complete_reserved condition.2) reference
      have done : child ∈ state.complete := by
        rw [ready_complete source roots state valid finished]
        exact seen
      exact Finset.mem_image.mpr ⟨child, done, rfl⟩
    · simp [copiedLookup, condition] at found

/-- Relocation is derived from reservations, slot writes and exhaustion;
no target lookup or transport-correctness premise is supplied. -/
def relocation (source : Source A V) (roots : List A) (state : State A V)
    (valid : Invariant source roots state) (finished : ready state = true) :
    Relocation (collect source.heap (rootsOf roots)) (destination source roots state valid finished) where
  address := image state
  payload := id
  injective := image_injective state
  lookup_eq a := by
    change copiedLookup state (image state a) =
      ((collect source.heap (rootsOf roots)).lookup a).map (Cell.relocate (image state) id)
    by_cases live : Live source.heap (rootsOf roots) a
    · have seen : a ∈ state.reserved := by
        rw [ready_footprint source roots state valid finished, mem_footprint]
        exact live
      have done : a ∈ state.complete := by
        rw [ready_complete source roots state valid finished]
        exact seen
      rw [lookup_collect_of_live source.heap _ live]
      exact copiedLookup_complete source roots state valid a done
    · have absent : a ∉ state.complete := by
        intro done
        exact live (valid.reserved_live a (valid.complete_reserved done))
      rw [lookup_collect_of_not_live source.heap _ live, copiedLookup_image, if_neg absent]
      rfl

theorem ordered_slot_completion (source : Source A V) (roots : List A) (state : State A V)
    (valid : Invariant source roots state) (finished : ready state = true)
    (a : A) (seen : a ∈ state.reserved) (i : Nat) (b : A)
    (atSlot : (source.slots a)[i]? = some b) :
    state.written a i = some (image state b) ∧ b ∈ state.reserved := by
  have done : a ∈ state.complete := by
    rw [ready_complete source roots state valid finished]
    exact seen
  have bounds : i < (source.slots a).length := by
    by_contra outside
    have nil : (source.slots a)[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [nil] at atSlot
    contradiction
  apply valid.written_prefix a seen i b atSlot
  rw [valid.complete_count a done]
  exact bounds

section Protocol

variable {W : Type}

def protocol : Mettapedia.TypeTheory.IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := State A W
  Position _ := State A W
  next _ _ := ()

def provider (source : Source A W) : Cursor.Provider (protocol (A := A) (W := W)) where
  State _ _ := Unit
  step _ request := ⟨step source request, ()⟩

def client : Cursor.Client (P := protocol (A := A) (W := W))
    (Return := fun _ _ => Except (State A W) (State A W)) where
  V _ _ := State A W
  str := fun _ _ => TypeCat.ofHom fun state =>
    if state.refused then ⟨.inl (.error state), fun position => nomatch position⟩
    else if ready state then ⟨.inl (.ok state), fun position => nomatch position⟩
    else ⟨.inr state, fun reply => reply⟩

theorem client_ready (state : State A W) (clear : state.refused = false)
    (finished : ready state = true) :
    client.str () () state = ⟨.inl (.ok state), fun impossible => nomatch impossible⟩ := by
  change (if state.refused then _ else if ready state then _ else _) = _
  simp only [clear, Bool.false_eq_true, ↓reduceIte, finished]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    funext impossible
    nomatch impossible

theorem client_running (state : State A W) (clear : state.refused = false)
    (running : ready state = false) :
    client.str () () state = ⟨.inr state, fun reply => reply⟩ := by
  change (if state.refused then _ else if ready state then _ else _) = _
  simp only [clear, Bool.false_eq_true, ↓reduceIte, running]
  rfl

def charge (source : Source A W) : Cursor.Charge (provider source) := fun _ _ => 1

def packet (source : Source A W) (state : State A W) :
    Cursor.Packet (provider source) client () := ⟨(), state, ()⟩

def run (source : Source A W) (fuel : Nat) (state : State A W) :=
  Cursor.advance (provider source) client (charge source) fuel (packet source state)

def resume (source : Source A W) (fuel : Nat)
    (previous : Nat × Cursor.Outcome (provider source) client ()) :=
  Cursor.resume (provider source) client (charge source) fuel previous

theorem run_zero (source : Source A W) (state : State A W) :
    run source 0 state = (0, .paused (packet source state)) := rfl

theorem resume_zero (source : Source A W)
    (previous : Nat × Cursor.Outcome (provider source) client ()) :
    resume source 0 previous = previous := Cursor.resume_zero ..

theorem run_add (source : Source A W) (first second : Nat) (state : State A W) :
    run source (first + second) state = resume source second (run source first state) :=
  Cursor.advance_add ..

theorem resume_add (source : Source A W) (first second : Nat)
    (previous : Nat × Cursor.Outcome (provider source) client ()) :
    resume source (first + second) previous =
      resume source second (resume source first previous) := Cursor.resume_add ..

theorem run_ready (source : Source A W) (state : State A W)
    (clear : state.refused = false) (finished : ready state = true) (fuel : Nat) :
    run source (fuel + 1) state = (0, .done ⟨(), .ok state, ()⟩) := by
  simp only [run, packet, Cursor.advance]
  rw [client_ready state clear finished]

theorem run_step (source : Source A W) (state : State A W)
    (clear : state.refused = false) (running : ready state = false) (fuel : Nat) :
    run source (fuel + 1) state =
      ((run source fuel (step source state)).1 + 1, (run source fuel (step source state)).2) := by
  simp only [run, packet, Cursor.advance]
  rw [client_running state clear running]
  change (1 + (run source fuel (step source state)).1, (run source fuel (step source state)).2) = _
  simp only [Nat.add_comm]
  rfl

/-- Every finite admitted source graph completes through the actual cursor.
The undiscovered-heap measure is used only by this proof, never by a poll. -/
theorem finite_completion (source : Source A W) (roots : List A) (state : State A W)
    (valid : Invariant source roots state) :
    ∃ fuel spent final, fuel ≤ potential source state + 1 ∧
      run source fuel state = (spent, .done ⟨(), .ok final, ()⟩) ∧
      Invariant source roots final ∧ ready final = true ∧
      spent + potential source final = potential source state ∧ fuel = spent + 1 := by
  generalize measure : potential source state = bound
  induction bound using Nat.strong_induction_on generalizing state with
  | h bound ih =>
      by_cases finished : ready state = true
      · exact ⟨1, 0, state, by omega, run_ready source state valid.not_refused finished 0,
          valid, finished, by omega, rfl⟩
      · have running : ready state = false := Bool.eq_false_iff.mpr finished
        have decrease := step_potential source roots state valid running
        have smaller : potential source (step source state) < bound := by omega
        obtain ⟨fuel, spent, final, enough, result, invariant, done, balance, clock⟩ :=
          ih _ smaller (step source state) (step_invariant source roots state valid) rfl
        refine ⟨fuel + 1, spent + 1, final, by omega, ?_, invariant, done, by omega, by omega⟩
        rw [run_step source state valid.not_refused running, result]

def stateOf (source : Source A W) : Cursor.Outcome (provider source) client () → State A W
  | .paused ⟨_, state, _⟩ => state
  | .done ⟨_, .ok state, _⟩ => state
  | .done ⟨_, .error state, _⟩ => state

def published (source : Source A W) : Cursor.Outcome (provider source) client () → Option (State A W)
  | .done ⟨_, .ok state, _⟩ => some state
  | _ => none

/-- Every actual prefix retains its complete buffer invariant and exact
paid/remaining balance. This also covers pauses between a backedge write
and the target shell's completion. -/
theorem prefix_sound (source : Source A W) (roots : List A) (state : State A W)
    (valid : Invariant source roots state) (fuel : Nat) :
    Invariant source roots (stateOf source (run source fuel state).2) ∧
      (run source fuel state).1 + potential source (stateOf source (run source fuel state).2) =
        potential source state ∧
      (stateOf source (run source fuel state).2).owner = state.owner ∧
      (∀ final, published source (run source fuel state).2 = some final → ready final = true) := by
  induction fuel generalizing state with
  | zero =>
      change Invariant source roots state ∧ 0 + potential source state = potential source state ∧
        state.owner = state.owner ∧ (∀ final, none = some final → ready final = true)
      exact ⟨valid, by omega, rfl, fun _ impossible => by cases impossible⟩
  | succ fuel ih =>
      by_cases done : ready state = true
      · rw [run_ready source state valid.not_refused done]
        change Invariant source roots state ∧ 0 + potential source state = potential source state ∧
          state.owner = state.owner ∧ (∀ final, some state = some final → ready final = true)
        exact ⟨valid, by omega, rfl, fun final equal => Option.some.inj equal ▸ done⟩
      · have running : ready state = false := Bool.eq_false_iff.mpr done
        rw [run_step source state valid.not_refused running]
        obtain ⟨invariant, balance, owner, publication⟩ :=
          ih (step source state) (step_invariant source roots state valid)
        have decrease := step_potential source roots state valid running
        change Invariant source roots (stateOf source (run source fuel (step source state)).2) ∧
          (run source fuel (step source state)).1 + 1 +
            potential source (stateOf source (run source fuel (step source state)).2) =
              potential source state ∧
          (stateOf source (run source fuel (step source state)).2).owner = state.owner ∧ _
        exact ⟨invariant, by omega, owner.trans (step_owner source state), publication⟩

noncomputable def referenceWork (source : Source A W) (roots : List A) : Nat :=
  roots.length + (footprint source.heap (rootsOf roots)).sum
    (fun a => 1 + (source.slots a).length)

theorem completed_invoice (source : Source A W) (roots : List A) (owner fuel spent : Nat)
    (valid : ∀ a ∈ roots, a ∈ source.heap.allocated) (final : State A W)
    (result : run source fuel (initial owner roots) = (spent, .done ⟨(), .ok final, ()⟩)) :
    spent = referenceWork source roots := by
  have sound := prefix_sound source roots (initial owner roots)
    (initial_invariant source roots owner valid) fuel
  rw [result] at sound
  simp only [stateOf, published] at sound
  obtain ⟨invariant, balance, _, publication⟩ := sound
  have finished := publication final rfl
  have lists := ready_lists final finished
  have subset : final.reserved ⊆ source.heap.allocated := by
    intro a member
    exact live_allocated source.heap _ (invariant.reserved_live a member)
  have partition := Finset.sum_sdiff (f := fun a => 1 + (source.slots a).length) subset
  have exactFootprint := ready_footprint source roots final invariant finished
  rw [initial_potential] at balance
  simp only [potential, lists.1, lists.2, List.length_nil, List.map_nil, List.sum_nil,
    zero_add] at balance
  unfold referenceWork
  rw [← exactFootprint]
  omega

/-- Valid finite roots always reach publication, with the independent
reachable-graph invoice rather than a bill defined from the run. -/
theorem initial_completes (source : Source A W) (roots : List A) (owner : Nat)
    (valid : ∀ a ∈ roots, a ∈ source.heap.allocated) :
    ∃ fuel final, run source fuel (initial owner roots) =
        (referenceWork source roots, .done ⟨(), .ok final, ()⟩) ∧
      Invariant source roots final ∧ ready final = true := by
  obtain ⟨fuel, spent, final, _, result, invariant, done, _⟩ :=
    finite_completion source roots (initial owner roots) (initial_invariant source roots owner valid)
  have bill := completed_invoice source roots owner fuel spent valid final result
  exact ⟨fuel, final, bill ▸ result, invariant, done⟩

theorem initial_completes_exact (source : Source A W) (roots : List A) (owner : Nat)
    (valid : ∀ a ∈ roots, a ∈ source.heap.allocated) :
    ∃ final, run source (referenceWork source roots + 1) (initial owner roots) =
        (referenceWork source roots, .done ⟨(), .ok final, ()⟩) ∧
      Invariant source roots final ∧ ready final = true := by
  obtain ⟨fuel, spent, final, _, result, invariant, done, _, clock⟩ :=
    finite_completion source roots (initial owner roots) (initial_invariant source roots owner valid)
  have bill := completed_invoice source roots owner fuel spent valid final result
  refine ⟨final, ?_, invariant, done⟩
  simpa only [clock, bill] using result

theorem completed_relocation (source : Source A W) (roots : List A) (owner fuel spent : Nat)
    (valid : ∀ a ∈ roots, a ∈ source.heap.allocated) (final : State A W)
    (result : run source fuel (initial owner roots) = (spent, .done ⟨(), .ok final, ()⟩)) :
    ∃ invariant : Invariant source roots final, ∃ finished : ready final = true,
      Nonempty (Relocation (collect source.heap (rootsOf roots))
        (destination source roots final invariant finished)) := by
  have sound := prefix_sound source roots (initial owner roots)
    (initial_invariant source roots owner valid) fuel
  rw [result] at sound
  exact ⟨sound.1, sound.2.2.2 final rfl, ⟨relocation source roots final sound.1 (sound.2.2.2 final rfl)⟩⟩

theorem completed_ordered_inventory (source : Source A W) (roots : List A)
    (owner fuel spent : Nat) (valid : ∀ a ∈ roots, a ∈ source.heap.allocated) (final : State A W)
    (result : run source fuel (initial owner roots) = (spent, .done ⟨(), .ok final, ()⟩)) :
    final.originals = roots ∧ ∀ a ∈ footprint source.heap (rootsOf roots),
      final.count a = (source.slots a).length ∧ ∀ i b, (source.slots a)[i]? = some b →
        final.written a i = some (image final b) ∧ b ∈ final.reserved := by
  have sound := prefix_sound source roots (initial owner roots)
    (initial_invariant source roots owner valid) fuel
  rw [result] at sound
  have invariant : Invariant source roots final := sound.1
  have finished : ready final = true := sound.2.2.2 final rfl
  refine ⟨invariant.originals_eq, ?_⟩
  intro a live
  have seen : a ∈ final.reserved := by
    rw [ready_footprint source roots final invariant finished]
    exact live
  have done : a ∈ final.complete := by
    rw [ready_complete source roots final invariant finished]
    exact seen
  exact ⟨invariant.complete_count a done,
    fun i b atSlot => ordered_slot_completion source roots final invariant finished a seen i b atSlot⟩

def cancel (source : Source A W) (previous : Nat × Cursor.Outcome (provider source) client ()) :
    Nat × Cursor.Outcome (provider source) client () :=
  (previous.1, .done
    ⟨(), .error { stateOf source previous.2 with refused := true, roots := [], frames := [] }, ()⟩)

theorem cancel_paid (source : Source A W)
    (previous : Nat × Cursor.Outcome (provider source) client ()) :
    (cancel source previous).1 = previous.1 := rfl

theorem cancel_unpublished (source : Source A W)
    (previous : Nat × Cursor.Outcome (provider source) client ()) :
    published source (cancel source previous).2 = none := rfl

theorem cancel_keeps_private_writes (source : Source A W)
    (previous : Nat × Cursor.Outcome (provider source) client ()) :
    (stateOf source (cancel source previous).2).written = (stateOf source previous.2).written ∧
      (stateOf source (cancel source previous).2).reserved = (stateOf source previous.2).reserved := ⟨rfl, rfl⟩

end Protocol

/-- Structural relocation is separate from export authority. A resource may
be reused by the same result owner, but a previously claimed resource is not
silently cloned for a different result owner. Table access has its own price. -/
def claimExport (owner : Nat) (address : A) (claims : A → Option Nat) :
    Option (A → Option Nat) :=
  match claims address with
  | none => some (Function.update claims address (some owner))
  | some previous => if previous = owner then some claims else none

theorem claimExport_fresh (owner : Nat) (address : A) (claims : A → Option Nat)
    (fresh : claims address = none) :
    claimExport owner address claims = some (Function.update claims address (some owner)) := by
  simp [claimExport, fresh]

theorem claimExport_reuse (owner : Nat) (address : A) (claims : A → Option Nat)
    (same : claims address = some owner) : claimExport owner address claims = some claims := by
  simp [claimExport, same]

theorem claimExport_foreign (owner previous : Nat) (address : A) (claims : A → Option Nat)
    (claimed : claims address = some previous) (foreign : previous ≠ owner) :
    claimExport owner address claims = none := by
  simp [claimExport, claimed, foreign]

theorem claimExport_grants_exact_owner (owner : Nat) (address : A)
    (before after : A → Option Nat) (accepted : claimExport owner address before = some after) :
    after address = some owner ∧ ∀ other, other ≠ address → after other = before other := by
  cases old : before address with
  | none =>
      rw [claimExport_fresh owner address before old] at accepted
      cases accepted
      exact ⟨by simp, fun other different => by simp [different]⟩
  | some previous =>
      by_cases same : previous = owner
      · subst previous
        rw [claimExport_reuse owner address before old] at accepted
        cases accepted
        exact ⟨old, fun _ _ => rfl⟩
      · rw [claimExport_foreign owner previous address before old same] at accepted
        cases accepted

namespace Controls

private def finiteSource (n : Nat) (slots : Fin n → List (Fin n)) : Source (Fin n) Nat where
  heap := {
    lookup := fun address => some ⟨address.val, (slots address).toFinset, 1⟩
    allocated := Finset.univ
    allocated_iff := fun _ => by simp
    closed := fun _ _ _ address _ => Finset.mem_univ address }
  slots := slots
  slots_exact := fun _ => rfl

private def selfSource : Source (Fin 1) Nat := finiteSource 1 (fun _ => [0])
private def mutualSource : Source (Fin 2) Nat :=
  finiteSource 2 (fun address => if address = 0 then [1] else [0])
private def duplicateSource : Source (Fin 3) Nat :=
  finiteSource 3 (fun address => if address = 0 then [1, 1, 2] else if address = 1 then [0] else [1])

private def cut {n : Nat} (source : Source (Fin n) Nat) (roots : List (Fin n)) (fuel : Nat) :=
  stateOf source (run source fuel (initial 7 roots)).2

/-- The first action reserves a private shell. A second action can write its
self-reference while the shell is pending, without publishing that shell. -/
theorem self_cycle_pending_backedge :
    (cut selfSource [0] 1).reserved = {0} ∧
      (cut selfSource [0] 1).complete = ∅ ∧
      (cut selfSource [0] 2).written 0 0 = some (7, 0) ∧
      (cut selfSource [0] 2).complete = ∅ ∧
      (published selfSource (run selfSource 2 (initial 7 [0])).2).isSome = false := by decide

theorem self_cycle_completes :
    (run selfSource 4 (initial 7 [0])).1 = 3 ∧
      (published selfSource (run selfSource 4 (initial 7 [0])).2).isSome = true ∧
      copiedLookup (cut selfSource [0] 4) (7, 0) = some ⟨0, {(7, 0)}, 1⟩ := by decide

theorem mutual_cycle_completes :
    (run mutualSource 6 (initial 7 [0])).1 = 5 ∧
      (cut mutualSource [0] 6).complete = {0, 1} ∧
      (cut mutualSource [0] 6).written 0 0 = some (7, 1) ∧
      (cut mutualSource [0] 6).written 1 0 = some (7, 0) ∧
      (published mutualSource (run mutualSource 6 (initial 7 [0])).2).isSome = true := by decide

/-- Duplicate slots retain multiplicity and order, while the shared image is
reserved and completed only once. -/
theorem ordered_duplicate_slots :
    (run duplicateSource 10 (initial 7 [0])).1 = 9 ∧
      (cut duplicateSource [0] 10).reserved.card = 3 ∧
      (cut duplicateSource [0] 10).count 0 = 3 ∧
      [(cut duplicateSource [0] 10).written 0 0,
       (cut duplicateSource [0] 10).written 0 1,
       (cut duplicateSource [0] 10).written 0 2] =
        [some (7, 1), some (7, 1), some (7, 2)] := by decide

theorem duplicate_roots_are_not_dropped :
    (run selfSource 5 (initial 7 [0, 0])).1 = 4 ∧
      (cut selfSource [0, 0] 5).originals = [0, 0] ∧
      (cut selfSource [0, 0] 5).reserved.card = 1 ∧
      (published selfSource (run selfSource 5 (initial 7 [0, 0])).2).isSome = true := by decide

theorem pause_preserves_cycle_prefix :
    run mutualSource (2 + 4) (initial 7 [0]) =
      resume mutualSource 4 (run mutualSource 2 (initial 7 [0])) := run_add ..

theorem zero_does_not_reserve :
    (run selfSource 0 (initial 7 [0])).1 = 0 ∧
      (cut selfSource [0] 0).reserved = ∅ ∧
      (published selfSource (run selfSource 0 (initial 7 [0])).2).isSome = false := by decide

theorem unfinished_complete_node_is_not_publication :
    (cut selfSource [0] 3).complete = {0} ∧
      (published selfSource (run selfSource 3 (initial 7 [0])).2).isSome = false := by decide

theorem cancelled_cycle_retains_private_receipt :
    (cancel selfSource (run selfSource 2 (initial 7 [0]))).1 = 2 ∧
      (stateOf selfSource (cancel selfSource (run selfSource 2 (initial 7 [0]))).2).written 0 0 =
        some (7, 0) ∧
      published selfSource (cancel selfSource (run selfSource 2 (initial 7 [0]))).2 = none := by decide

theorem foreign_owner_has_no_image_lookup :
    copiedLookup (cut selfSource [0] 4) (8, 0) = none := by decide

theorem empty_roots_publish_empty :
    (run selfSource 1 (initial 7 [])).1 = 0 ∧
      (cut selfSource [] 1).complete = ∅ ∧
      (published selfSource (run selfSource 1 (initial 7 [])).2).isSome = true := by decide

private def reorderedSource (reverse : Bool) : Source (Fin 3) Nat :=
  finiteSource 3 (fun address => if address = 0 then
    (if reverse then [2, 1] else [1, 2]) else [])

/-- A set of graph edges alone cannot certify the actual slot order. -/
theorem reorder_is_observable :
    (cut (reorderedSource false) [0] 7).count 0 =
      (cut (reorderedSource true) [0] 7).count 0 ∧
      references (cut (reorderedSource false) [0] 7) 0 =
        references (cut (reorderedSource true) [0] 7) 0 ∧
      (cut (reorderedSource false) [0] 7).written 0 0 ≠
        (cut (reorderedSource true) [0] 7).written 0 0 := by decide

private def wideSource (width : Nat) : Source (Fin 1) Nat :=
  finiteSource 1 (fun _ => List.replicate width 0)

theorem arbitrary_duplicate_width_invoice (width : Nat) :
    referenceWork (wideSource width) [0] = width + 2 := by
  have graph : footprint (wideSource width).heap (rootsOf [0]) = {0} := by
    ext address
    have only := Fin.eq_zero address
    subst address
    simp only [Finset.mem_singleton, iff_true]
    rw [mem_footprint]
    exact root_live (wideSource width) [0] (a := 0)
      (by intro a _; exact Finset.mem_univ a) (by simp)
  rw [referenceWork, graph]
  simp [wideSource, finiteSource]
  omega

theorem wide_duplicate_run :
    (run (wideSource 32) 35 (initial 7 [0])).1 = 34 ∧
      (cut (wideSource 32) [0] 35).count 0 = 32 ∧
      (cut (wideSource 32) [0] 35).reserved.card = 1 ∧
      (published (wideSource 32) (run (wideSource 32) 35 (initial 7 [0])).2).isSome = true := by decide

private def absentSource : Source Nat Nat where
  heap := {
    lookup := fun _ => none
    allocated := ∅
    allocated_iff := fun _ => by simp
    closed := by intro _ _ impossible; cases impossible }
  slots := fun _ => []
  slots_exact := fun _ => rfl

theorem absent_root_refuses_without_publication :
    (run absentSource 2 (initial 7 [0])).1 = 1 ∧
      (stateOf absentSource (run absentSource 2 (initial 7 [0])).2).refused = true ∧
      (published absentSource (run absentSource 2 (initial 7 [0])).2).isSome = false := by decide

theorem same_result_reuses_export_identity :
    (claimExport 7 (0 : Nat) (Function.update (fun _ => none) 0 (some 7))).isSome = true := by decide

theorem cross_result_export_is_refused :
    claimExport 8 (0 : Nat) (Function.update (fun _ => none) 0 (some 7)) = none := by
  exact claimExport_foreign 8 7 0 _ (by simp) (by decide)

theorem copying_does_not_grant_export_authority :
    copiedLookup (cut selfSource [0] 4) (7, 0) ≠ none ∧
      claimExport 8 (0 : Fin 1) (fun _ => some 7) = none := by
  constructor
  · decide
  · exact claimExport_foreign 8 7 0 _ rfl (by decide)

end Controls

end Mettapedia.Machines.ResourceOwnership.TraceWork.RetainedCopy

/-! ## Source locality of retained resource copying

Each copy action consults at most one fresh node's header and ordered slots.
The changing-source adapter reuses the existing copy step and sampled read
provider. Agreement of its actual accumulated node observations with one fixed
admitted source determines the full saved copy state and declared action
invoice. Checked completion composes the existing relocation construction.

Native coherent node responses, canonical visible identities, captured Need
and resource authority, lifetime/version protection and independent source
capture closure remain source-instance obligations. Full-log validation and
allocation/cleanup retain separate prices; no physical slot bound follows.
-/

namespace Mettapedia.Machines.ResourceOwnership.TraceWork.RetainedCopy.SourceLocality

open Mettapedia.Machines.ReadOnlyQuery (Reads Agrees checkReads)

universe v
variable {A : Type} {V : Type v} [LinearOrder A]

abbrev Node (A : Type) (V : Type v) := Option (Cell A V) × List A

def observe (source : Source A V) (address : A) : Node A V :=
  (source.heap.lookup address, source.slots address)

/-- The existing step consults exactly this fresh root/child, if any. A backedge,
completion, already reserved root, empty state or refused state reads no node. -/
def readIntent (state : State A V) : Option A :=
  if state.refused then none else
  match state.frames with
  | frame :: _ => match frame.remaining with
    | [] => none
    | child :: _ => if child ∈ state.reserved then none else some child
  | [] => match state.roots with
    | [] => none
    | root :: _ => if root ∈ state.reserved then none else some root

def localReads (source : Source A V) (state : State A V) : Reads A (Node A V) :=
  match readIntent state with
  | none => []
  | some address => [(address, observe source address)]

/-- Direct source inspection of the actual step establishes its entire local
support. No equality of target states or complete source functions is input. -/
theorem step_source_locality (first second : Source A V) (state : State A V)
    (same : ∀ address, readIntent state = some address →
      observe first address = observe second address) : step first state = step second state := by
  by_cases refused : state.refused = true
  · simp [step, refused]
  have clear : state.refused = false := Bool.eq_false_iff.mpr refused
  cases stack : state.frames with
  | nil =>
      cases roots : state.roots with
      | nil => simp [step, clear, stack, roots]
      | cons root rest =>
          by_cases seen : root ∈ state.reserved
          · simp [step, clear, stack, roots, seen]
          · have exactNode := same root (by simp [readIntent, clear, stack, roots, seen])
            have header := congrArg Prod.fst exactNode
            have slots := congrArg Prod.snd exactNode
            simp only [observe] at header slots
            simp [step, clear, stack, roots, seen, pushFresh, reserve, header, slots]
  | cons frame rest =>
      cases remaining : frame.remaining with
      | nil => simp [step, clear, stack, remaining]
      | cons child tail =>
          by_cases seen : child ∈ state.reserved
          · simp [step, clear, stack, remaining, seen]
          · have exactNode := same child (by simp [readIntent, clear, stack, remaining, seen])
            have header := congrArg Prod.fst exactNode
            have slots := congrArg Prod.snd exactNode
            simp only [observe] at header slots
            simp [step, clear, stack, remaining, seen, pushFresh, reserve, header, slots]

theorem step_of_local_agreement (first second : Source A V) (state : State A V)
    (valid : Agrees (observe second) (localReads first state)) :
    step first state = step second state := by
  apply step_source_locality first second state
  intro address intended
  exact (valid (address, observe first address) (by simp [localReads, intended])).symm

theorem no_intent_needs_no_source_agreement (first second : Source A V) (state : State A V)
    (none : readIntent state = Option.none) : step first state = step second state := by
  apply step_source_locality first second state
  intro address intended
  rw [none] at intended
  cases intended

theorem local_read_is_actual (source : Source A V) (state : State A V)
    (address : A) (node : Node A V) (member : (address, node) ∈ localReads source state) :
    readIntent state = some address ∧ node = observe source address := by
  unfold localReads at member
  cases intended : readIntent state with
  | none => simp [intended] at member
  | some read =>
      simp only [intended, List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      exact ⟨rfl, rfl⟩

theorem at_most_one_node_read (source : Source A V) (state : State A V) :
    (localReads source state).length ≤ 1 := by
  unfold localReads
  cases readIntent state <;> simp

section Protocol

variable {W Context : Type}

def sampleNode (views : Context → Source A W) (evolve : Context → Context)
    (context : Context) (address : A) : Node A W × Context :=
  (observe (views context) address, evolve context)

/-- A source read reuses the actual sampled-query provider and its one-reply
log extension. A local copy action advances context without inventing a read. -/
def after (views : Context → Source A W) (evolve : Context → Context) (request : State A W)
    (saved : Context × Reads A (Node A W)) : Context × Reads A (Node A W) :=
  match readIntent request with
  | none => (evolve saved.1, saved.2)
  | some address =>
      ((Mettapedia.Machines.Cursor.ReadOnlyQuery.Sampled.provider (sampleNode views evolve)).step
        (base := PUnit.unit) (index := PUnit.unit) saved address).2

theorem after_world (views : Context → Source A W) (evolve : Context → Context)
    (request : State A W) (saved : Context × Reads A (Node A W)) :
    (after views evolve request saved).1 = evolve saved.1 := by
  unfold after
  cases readIntent request <;> rfl

theorem after_reads (views : Context → Source A W) (evolve : Context → Context)
    (request : State A W) (saved : Context × Reads A (Node A W)) :
    (after views evolve request saved).2 = (localReads (views saved.1) request).reverse ++ saved.2 := by
  unfold after localReads
  cases readIntent request <;> simp [Mettapedia.Machines.Cursor.ReadOnlyQuery.Sampled.provider, sampleNode]

theorem after_keeps_prior (views : Context → Source A W) (evolve : Context → Context)
    (request : State A W) (saved : Context × Reads A (Node A W)) :
    saved.2.reverse <+: (after views evolve request saved).2.reverse := by
  refine ⟨localReads (views saved.1) request, ?_⟩
  rw [after_reads, List.reverse_append, List.reverse_reverse]

theorem after_keeps_actual_read (views : Context → Source A W) (evolve : Context → Context)
    (request : State A W) (saved : Context × Reads A (Node A W)) (read : A × Node A W)
    (member : read ∈ localReads (views saved.1) request) :
    read ∈ (after views evolve request saved).2.reverse := by
  rw [after_reads, List.reverse_append, List.reverse_reverse]
  exact List.mem_append_right _ member

/-- Each provider poll executes the existing step once in that poll's view.
The view may change at the next poll; no global captured Source is assumed. -/
def provider (views : Context → Source A W) (evolve : Context → Context) :
    Cursor.Provider (RetainedCopy.protocol (A := A) (W := W)) where
  State _ _ := Context × Reads A (Node A W)
  step saved request := ⟨step (views saved.1) request, after views evolve request saved⟩

def charge (views : Context → Source A W) (evolve : Context → Context) :
    Cursor.Charge (provider views evolve) := fun _ _ => 1

def packet (views : Context → Source A W) (evolve : Context → Context)
    (state : State A W) (context : Context) (reads : Reads A (Node A W)) :
    Cursor.Packet (provider views evolve) RetainedCopy.client () := ⟨(), state, context, reads⟩

def advance (views : Context → Source A W) (evolve : Context → Context) (fuel : Nat)
    (state : State A W) (context : Context) (reads : Reads A (Node A W)) :=
  Cursor.advance (provider views evolve) RetainedCopy.client (charge views evolve) fuel
    (packet views evolve state context reads)

def resume (views : Context → Source A W) (evolve : Context → Context) (fuel : Nat)
    (previous : Nat × Cursor.Outcome (provider views evolve) RetainedCopy.client ()) :=
  Cursor.resume (provider views evolve) RetainedCopy.client (charge views evolve) fuel previous

def savedState (views : Context → Source A W) (evolve : Context → Context) :
    Cursor.Outcome (provider views evolve) RetainedCopy.client () → Context × Reads A (Node A W)
  | .paused ⟨_, _, saved⟩ => saved
  | .done ⟨_, _, saved⟩ => saved

def recorded (views : Context → Source A W) (evolve : Context → Context)
    (outcome : Cursor.Outcome (provider views evolve) RetainedCopy.client ()) : Reads A (Node A W) :=
  (savedState views evolve outcome).2.reverse

/-- Only provider bookkeeping is projected. Actual copy control and all its
reserved images, headers, slot buffers, original roots and refusal are kept. -/
def project (views : Context → Source A W) (evolve : Context → Context) (fixed : Source A W)
    (previous : Nat × Cursor.Outcome (provider views evolve) RetainedCopy.client ()) :
    Nat × Cursor.Outcome (RetainedCopy.provider fixed) RetainedCopy.client () :=
  (previous.1, Cursor.Outcome.mapState RetainedCopy.client (source := provider views evolve)
    (target := RetainedCopy.provider fixed) (fun _ => ()) previous.2)

theorem client_refused (state : State A W) (refused : state.refused = true) :
    RetainedCopy.client.str () () state = ⟨.inl (.error state), fun impossible => nomatch impossible⟩ := by
  change (if state.refused then _ else if ready state then _ else _) = _
  simp only [refused, ↓reduceIte]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    funext impossible
    nomatch impossible

theorem advance_zero (views : Context → Source A W) (evolve : Context → Context)
    (state : State A W) (context : Context) (reads : Reads A (Node A W)) :
    advance views evolve 0 state context reads = (0, .paused (packet views evolve state context reads)) := rfl

theorem advance_refused (views : Context → Source A W) (evolve : Context → Context)
    (state : State A W) (refused : state.refused = true) (context : Context)
    (reads : Reads A (Node A W)) (fuel : Nat) :
    advance views evolve (fuel + 1) state context reads =
      (0, .done ⟨(), .error state, context, reads⟩) := by
  simp only [advance, packet, Cursor.advance]
  rw [client_refused state refused]

theorem fixed_run_refused (fixed : Source A W) (state : State A W)
    (refused : state.refused = true) (fuel : Nat) :
    RetainedCopy.run fixed (fuel + 1) state = (0, .done ⟨(), .error state, ()⟩) := by
  simp only [RetainedCopy.run, RetainedCopy.packet, Cursor.advance]
  rw [client_refused state refused]

theorem advance_ready (views : Context → Source A W) (evolve : Context → Context)
    (state : State A W) (clear : state.refused = false) (finished : ready state = true)
    (context : Context) (reads : Reads A (Node A W)) (fuel : Nat) :
    advance views evolve (fuel + 1) state context reads = (0, .done ⟨(), .ok state, context, reads⟩) := by
  simp only [advance, packet, Cursor.advance]
  rw [RetainedCopy.client_ready state clear finished]

theorem advance_step (views : Context → Source A W) (evolve : Context → Context)
    (state : State A W) (clear : state.refused = false) (running : ready state = false)
    (context : Context) (reads : Reads A (Node A W)) (fuel : Nat) :
    advance views evolve (fuel + 1) state context reads =
      let saved := after views evolve state (context, reads)
      let rest := advance views evolve fuel (step (views context) state) saved.1 saved.2
      (rest.1 + 1, rest.2) := by
  simp only [advance, packet, Cursor.advance]
  rw [RetainedCopy.client_running state clear running]
  change (1 + (advance views evolve fuel (step (views context) state)
      (after views evolve state (context, reads)).1 (after views evolve state (context, reads)).2).1,
    (advance views evolve fuel (step (views context) state)
      (after views evolve state (context, reads)).1 (after views evolve state (context, reads)).2).2) = _
  simp only [Nat.add_comm]
  rfl

theorem recorded_keeps_prior (views : Context → Source A W) (evolve : Context → Context)
    (fuel : Nat) (state : State A W) (context : Context) (reads : Reads A (Node A W)) :
    reads.reverse <+: recorded views evolve (advance views evolve fuel state context reads).2 := by
  induction fuel generalizing state context reads with
  | zero => exact ⟨[], by simp [advance_zero, packet, recorded, savedState]⟩
  | succ fuel ih =>
      by_cases refused : state.refused = true
      · rw [advance_refused views evolve state refused]
        exact ⟨[], by simp [recorded, savedState]⟩
      · have clear : state.refused = false := Bool.eq_false_iff.mpr refused
        by_cases finished : ready state = true
        · rw [advance_ready views evolve state clear finished]
          exact ⟨[], by simp [recorded, savedState]⟩
        · have running : ready state = false := Bool.eq_false_iff.mpr finished
          rw [advance_step views evolve state clear running]
          exact (after_keeps_prior views evolve state (context, reads)).trans
            (ih (step (views context) state) (after views evolve state (context, reads)).1
              (after views evolve state (context, reads)).2)

/-- Every actual step's recorded node is retained in the eventual prefix,
including a header/slot pair captured before a later view changes. -/
theorem current_read_is_recorded (views : Context → Source A W) (evolve : Context → Context)
    (state : State A W) (context : Context) (reads : Reads A (Node A W)) (fuel : Nat)
    (read : A × Node A W) (member : read ∈ localReads (views context) state) :
    read ∈ recorded views evolve
      (advance views evolve fuel (step (views context) state)
        (after views evolve state (context, reads)).1 (after views evolve state (context, reads)).2).2 := by
  exact (recorded_keeps_prior views evolve fuel (step (views context) state)
    (after views evolve state (context, reads)).1 (after views evolve state (context, reads)).2).subset
      (after_keeps_actual_read views evolve state (context, reads) read member)

/-- Earned consulted-node agreement determines the actual entire bounded copy
execution, including unfinished buffers and all declared copy-action debits.
The premise does not assert source equality or any desired run equality. -/
theorem earned_prefix_eq_fixed (views : Context → Source A W) (evolve : Context → Context)
    (fixed : Source A W) (fuel : Nat) (state : State A W) (context : Context)
    (reads : Reads A (Node A W))
    (valid : Agrees (observe fixed) (recorded views evolve (advance views evolve fuel state context reads).2)) :
    project views evolve fixed (advance views evolve fuel state context reads) =
      RetainedCopy.run fixed fuel state := by
  induction fuel generalizing state context reads with
  | zero => rfl
  | succ fuel ih =>
      by_cases refused : state.refused = true
      · rw [advance_refused views evolve state refused, fixed_run_refused fixed state refused]
        rfl
      · have clear : state.refused = false := Bool.eq_false_iff.mpr refused
        by_cases finished : ready state = true
        · rw [advance_ready views evolve state clear finished,
            RetainedCopy.run_ready fixed state clear finished]
          rfl
        · have running : ready state = false := Bool.eq_false_iff.mpr finished
          rw [advance_step views evolve state clear running] at valid ⊢
          have atNode : Agrees (observe fixed) (localReads (views context) state) := by
            intro read member
            exact valid read (current_read_is_recorded views evolve state context reads fuel read member)
          have sameStep := step_of_local_agreement (views context) fixed state atNode
          have tail := ih (step (views context) state) (after views evolve state (context, reads)).1
            (after views evolve state (context, reads)).2 valid
          rw [sameStep] at tail
          rw [RetainedCopy.run_step fixed state clear running, sameStep]
          exact congrArg (fun saved => (saved.1 + 1, saved.2)) tail

def controlState (views : Context → Source A W) (evolve : Context → Context) :
    Cursor.Outcome (provider views evolve) RetainedCopy.client () → State A W
  | .paused ⟨_, state, _⟩ => state
  | .done ⟨_, .ok state, _⟩ => state
  | .done ⟨_, .error state, _⟩ => state

def published (views : Context → Source A W) (evolve : Context → Context) :
    Cursor.Outcome (provider views evolve) RetainedCopy.client () → Option (State A W)
  | .done ⟨_, .ok state, _⟩ => some state
  | _ => none

theorem projected_state (views : Context → Source A W) (evolve : Context → Context)
    (fixed : Source A W)
    (previous : Nat × Cursor.Outcome (provider views evolve) RetainedCopy.client ()) :
    RetainedCopy.stateOf fixed (project views evolve fixed previous).2 =
      controlState views evolve previous.2 := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => rcases packet with ⟨_, state, saved⟩; rfl
  | done finished => rcases finished with ⟨_, result, saved⟩; cases result <;> rfl

theorem projected_publication (views : Context → Source A W) (evolve : Context → Context)
    (fixed : Source A W)
    (previous : Nat × Cursor.Outcome (provider views evolve) RetainedCopy.client ()) :
    RetainedCopy.published fixed (project views evolve fixed previous).2 =
      published views evolve previous.2 := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => rcases packet with ⟨_, state, saved⟩; rfl
  | done finished => rcases finished with ⟨_, result, saved⟩; cases result <;> rfl

theorem checked_prefix_eq_fixed [DecidableEq W]
    (views : Context → Source A W) (evolve : Context → Context)
    (fixed : Source A W) (fuel : Nat) (state : State A W) (context : Context)
    (reads : Reads A (Node A W))
    (checked : checkReads (observe fixed)
      (recorded views evolve (advance views evolve fuel state context reads).2) = true) :
    project views evolve fixed (advance views evolve fuel state context reads) =
      RetainedCopy.run fixed fuel state :=
  earned_prefix_eq_fixed views evolve fixed fuel state context reads
    ((Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mp checked)

/-- Source reads are a subset of charged copy actions. Local writes, shell
completion and reserved-root visits remain charged even when they read no node. -/
theorem node_reads_le_paid_actions (views : Context → Source A W) (evolve : Context → Context)
    (fuel : Nat) (state : State A W) (context : Context) (reads : Reads A (Node A W)) :
    (recorded views evolve (advance views evolve fuel state context reads).2).length ≤
      reads.length + (advance views evolve fuel state context reads).1 := by
  induction fuel generalizing state context reads with
  | zero => simp [advance_zero, packet, recorded, savedState]
  | succ fuel ih =>
      by_cases refused : state.refused = true
      · rw [advance_refused views evolve state refused]
        simp [recorded, savedState]
      · have clear : state.refused = false := Bool.eq_false_iff.mpr refused
        by_cases finished : ready state = true
        · rw [advance_ready views evolve state clear finished]
          simp [recorded, savedState]
        · have running : ready state = false := Bool.eq_false_iff.mpr finished
          rw [advance_step views evolve state clear running]
          have bound := ih (step (views context) state) (after views evolve state (context, reads)).1
            (after views evolve state (context, reads)).2
          have length : (after views evolve state (context, reads)).2.length =
              (localReads (views context) state).length + reads.length := by
            rw [after_reads, List.length_append, List.length_reverse]
          have small := at_most_one_node_read (views context) state
          change (recorded views evolve (advance views evolve fuel (step (views context) state)
              (after views evolve state (context, reads)).1 (after views evolve state (context, reads)).2).2).length ≤
            reads.length + ((advance views evolve fuel (step (views context) state)
              (after views evolve state (context, reads)).1 (after views evolve state (context, reads)).2).1 + 1)
          omega

theorem advance_split (views : Context → Source A W) (evolve : Context → Context)
    (first second : Nat) (state : State A W) (context : Context) (reads : Reads A (Node A W)) :
    advance views evolve (first + second) state context reads =
      resume views evolve second (advance views evolve first state context reads) := Cursor.advance_add ..

theorem resume_zero (views : Context → Source A W) (evolve : Context → Context)
    (previous : Nat × Cursor.Outcome (provider views evolve) RetainedCopy.client ()) :
    resume views evolve 0 previous = previous := Cursor.resume_zero ..

theorem resume_keeps_recorded (views : Context → Source A W) (evolve : Context → Context)
    (fuel : Nat) (previous : Nat × Cursor.Outcome (provider views evolve) RetainedCopy.client ()) :
    recorded views evolve previous.2 <+: recorded views evolve (resume views evolve fuel previous).2 := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | done finished => exact ⟨[], by simp [resume, Cursor.resume]⟩
  | paused packet =>
      rcases packet with ⟨_, state, context, reads⟩
      exact recorded_keeps_prior views evolve fuel state context reads

theorem resumed_prefix_eq_fixed (views : Context → Source A W) (evolve : Context → Context)
    (fixed : Source A W) (fuel : Nat)
    (previous : Nat × Cursor.Outcome (provider views evolve) RetainedCopy.client ())
    (valid : Agrees (observe fixed) (recorded views evolve (resume views evolve fuel previous).2)) :
    project views evolve fixed (resume views evolve fuel previous) =
      RetainedCopy.resume fixed fuel (project views evolve fixed previous) := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | done finished => rfl
  | paused packet =>
      rcases packet with ⟨_, state, context, reads⟩
      have same := earned_prefix_eq_fixed views evolve fixed fuel state context reads valid
      exact congrArg (fun saved => (paid + saved.1, saved.2)) same

theorem earned_split_eq_fixed (views : Context → Source A W) (evolve : Context → Context)
    (fixed : Source A W) (first second : Nat) (state : State A W) (context : Context)
    (reads : Reads A (Node A W))
    (valid : Agrees (observe fixed)
      (recorded views evolve (advance views evolve (first + second) state context reads).2)) :
    project views evolve fixed (resume views evolve second (advance views evolve first state context reads)) =
      RetainedCopy.resume fixed second (RetainedCopy.run fixed first state) := by
  rw [advance_split] at valid
  have priorAgreement : Agrees (observe fixed)
      (recorded views evolve (advance views evolve first state context reads).2) := by
    intro read member
    exact valid read ((resume_keeps_recorded views evolve second
      (advance views evolve first state context reads)).subset member)
  rw [resumed_prefix_eq_fixed views evolve fixed second _ valid,
    earned_prefix_eq_fixed views evolve fixed first state context reads priorAgreement]

/-- Completion is transported only from the actual completed outcome. The
fixed-run equality is the result of locality and earned support, not input. -/
theorem fixed_completion_earned (views : Context → Source A W) (evolve : Context → Context)
    (fixed : Source A W) (fuel : Nat) (state final : State A W) (context : Context)
    (valid : Agrees (observe fixed) (recorded views evolve (advance views evolve fuel state context []).2))
    (finished : published views evolve (advance views evolve fuel state context []).2 = some final) :
    RetainedCopy.run fixed fuel state =
      ((advance views evolve fuel state context []).1, .done ⟨(), .ok final, ()⟩) := by
  have same := earned_prefix_eq_fixed views evolve fixed fuel state context [] valid
  cases result : (advance views evolve fuel state context []).2 with
  | paused packet => simp [published, result] at finished
  | done complete =>
      rcases complete with ⟨index, answer, saved⟩
      cases index
      cases answer with
      | error refused => simp [published, result] at finished
      | ok output =>
          simp only [result, published, Option.some.injEq] at finished
          subst output
          unfold project at same
          rw [result] at same
          exact same.symm

theorem completed_invoice (views : Context → Source A W) (evolve : Context → Context)
    (fixed : Source A W) (roots : List A) (owner fuel : Nat) (context : Context) (final : State A W)
    (rootsValid : ∀ a ∈ roots, a ∈ fixed.heap.allocated)
    (valid : Agrees (observe fixed)
      (recorded views evolve (advance views evolve fuel (initial owner roots) context []).2))
    (finished : published views evolve (advance views evolve fuel (initial owner roots) context []).2 = some final) :
    (advance views evolve fuel (initial owner roots) context []).1 = referenceWork fixed roots :=
  RetainedCopy.completed_invoice fixed roots owner fuel _ rootsValid final
    (fixed_completion_earned views evolve fixed fuel (initial owner roots) final context valid finished)

theorem completed_relocation (views : Context → Source A W) (evolve : Context → Context)
    (fixed : Source A W) (roots : List A) (owner fuel : Nat) (context : Context) (final : State A W)
    (rootsValid : ∀ a ∈ roots, a ∈ fixed.heap.allocated)
    (valid : Agrees (observe fixed)
      (recorded views evolve (advance views evolve fuel (initial owner roots) context []).2))
    (finished : published views evolve (advance views evolve fuel (initial owner roots) context []).2 = some final) :
    ∃ invariant : Invariant fixed roots final, ∃ ready : RetainedCopy.ready final = true,
      Nonempty (Relocation (collect fixed.heap (rootsOf roots))
        (destination fixed roots final invariant ready)) :=
  RetainedCopy.completed_relocation fixed roots owner fuel _ rootsValid final
    (fixed_completion_earned views evolve fixed fuel (initial owner roots) final context valid finished)

/-- Validation is an explicit fixed-view gate, not a source lifetime or
current-world grant. It inspects the complete earned log before readout. -/
def checkedPublication [DecidableEq W] (views : Context → Source A W)
    (evolve : Context → Context) (fixed : Source A W)
    (outcome : Cursor.Outcome (provider views evolve) RetainedCopy.client ()) : Option (State A W) :=
  if checkReads (observe fixed) (recorded views evolve outcome) then published views evolve outcome else none

theorem checkedPublication_refuses [DecidableEq W] (views : Context → Source A W)
    (evolve : Context → Context) (fixed : Source A W)
    (outcome : Cursor.Outcome (provider views evolve) RetainedCopy.client ())
    (invalid : checkReads (observe fixed) (recorded views evolve outcome) = false) :
    checkedPublication views evolve fixed outcome = none := by simp [checkedPublication, invalid]

theorem checkedPublication_admitted [DecidableEq W] (views : Context → Source A W)
    (evolve : Context → Context) (fixed : Source A W)
    (outcome : Cursor.Outcome (provider views evolve) RetainedCopy.client ()) (final : State A W)
    (accepted : checkedPublication views evolve fixed outcome = some final) :
    Agrees (observe fixed) (recorded views evolve outcome) ∧ published views evolve outcome = some final := by
  unfold checkedPublication at accepted
  split at accepted
  · rename_i checked
    exact ⟨(Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mp checked, accepted⟩
  · cases accepted

theorem checkedPublication_relocation [DecidableEq W] (views : Context → Source A W)
    (evolve : Context → Context) (fixed : Source A W) (roots : List A)
    (owner fuel : Nat) (context : Context) (final : State A W)
    (rootsValid : ∀ a ∈ roots, a ∈ fixed.heap.allocated)
    (accepted : checkedPublication views evolve fixed
      (advance views evolve fuel (initial owner roots) context []).2 = some final) :
    ∃ invariant : Invariant fixed roots final, ∃ ready : RetainedCopy.ready final = true,
      Nonempty (Relocation (collect fixed.heap (rootsOf roots))
        (destination fixed roots final invariant ready)) := by
  obtain ⟨agrees, finished⟩ := checkedPublication_admitted views evolve fixed _ final accepted
  exact completed_relocation views evolve fixed roots owner fuel context final rootsValid agrees finished

end Protocol

namespace Controls

private def finiteSource (n : Nat) (value : Fin n → Nat) (slots : Fin n → List (Fin n)) :
    Source (Fin n) Nat where
  heap := {
    lookup := fun address => some ⟨value address, (slots address).toFinset, 1⟩
    allocated := Finset.univ
    allocated_iff := fun _ => by simp
    closed := fun _ _ _ address _ => Finset.mem_univ address }
  slots := slots
  slots_exact := fun _ => rfl

/-- Only the not-yet-read child changes after the first provider action. -/
private def unreadViews (clock : Nat) : Source (Fin 2) Nat :=
  finiteSource 2 (fun address => if address = 0 then 0 else if clock = 0 then 10 else 20)
    (fun address => if address = 0 then [1] else [])
private def unreadRun := advance unreadViews Nat.succ 5 (initial 7 [0]) 0 []
private def unreadCut (fuel : Nat) := advance unreadViews Nat.succ fuel (initial 7 [0]) 0 []
private def unreadFinal := controlState unreadViews Nat.succ unreadRun.2

theorem unread_change_is_an_actual_changing_provider :
    (observe (unreadViews 0) 1).1 ≠ (observe (unreadViews 4) 1).1 ∧
      (savedState unreadViews Nat.succ unreadRun.2).1 = 4 ∧
      unreadRun.1 = 4 ∧ (recorded unreadViews Nat.succ unreadRun.2).length = 2 ∧
      unreadFinal.headers 1 = (unreadViews 4).heap.lookup 1 := by decide

theorem unread_change_full_support_accepts :
    checkReads (observe (unreadViews 4)) (recorded unreadViews Nat.succ unreadRun.2) = true := by decide

theorem changing_copy_is_exact_fixed_view_execution :
    project unreadViews Nat.succ (unreadViews 4) unreadRun =
      RetainedCopy.run (unreadViews 4) 5 (initial 7 [0]) :=
  checked_prefix_eq_fixed unreadViews Nat.succ (unreadViews 4) 5 (initial 7 [0]) 0 []
    unread_change_full_support_accepts

theorem changing_copy_is_not_initial_source_copy :
    (unreadFinal.headers 1).map Cell.value = some 20 ∧
      ((RetainedCopy.stateOf (unreadViews 0)
        (RetainedCopy.run (unreadViews 0) 5 (initial 7 [0])).2).headers 1).map Cell.value = some 10 := by decide

theorem changing_copy_keeps_actual_slot_and_root_inventory :
    unreadFinal.originals = [0] ∧ unreadFinal.count 0 = 1 ∧
      unreadFinal.written 0 0 = some (7, 1) ∧ unreadFinal.complete = {0, 1} := by decide

theorem actual_completion_earns_current_invoice :
    unreadRun.1 = referenceWork (unreadViews 4) [0] :=
  completed_invoice unreadViews Nat.succ (unreadViews 4) [0] 7 5 0 unreadFinal
    (by intro address _; exact Finset.mem_univ address)
    ((Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mp unread_change_full_support_accepts) rfl

theorem actual_completion_earns_derived_relocation :
    ∃ invariant : Invariant (unreadViews 4) [0] unreadFinal,
      ∃ done : ready unreadFinal = true,
      Nonempty (Relocation (collect (unreadViews 4).heap (rootsOf [0]))
        (destination (unreadViews 4) [0] unreadFinal invariant done)) :=
  completed_relocation unreadViews Nat.succ (unreadViews 4) [0] 7 5 0 unreadFinal
    (by intro address _; exact Finset.mem_univ address)
    ((Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mp unread_change_full_support_accepts) rfl

theorem checked_current_publication_uses_full_earned_support :
    checkedPublication unreadViews Nat.succ (unreadViews 4) unreadRun.2 = some unreadFinal := by
  unfold checkedPublication
  rw [unread_change_full_support_accepts]
  rfl

theorem partial_capture_is_not_completed_publication :
    (recorded unreadViews Nat.succ (unreadCut 1).2).length = 1 ∧
      (controlState unreadViews Nat.succ (unreadCut 1).2).reserved.card = 1 ∧
      published unreadViews Nat.succ (unreadCut 1).2 = none ∧
      checkedPublication unreadViews Nat.succ (unreadViews 4) (unreadCut 1).2 = none := by
  exact ⟨rfl, by decide, rfl, rfl⟩

theorem split_keeps_source_context_private_buffers_and_invoice :
    resume unreadViews Nat.succ 4 (unreadCut 1) = unreadRun :=
  (advance_split unreadViews Nat.succ 1 4 (initial 7 [0]) 0 []).symm

theorem split_copy_matches_existing_fixed_cursor :
    project unreadViews Nat.succ (unreadViews 4) (resume unreadViews Nat.succ 4 (unreadCut 1)) =
      RetainedCopy.resume (unreadViews 4) 4 (RetainedCopy.run (unreadViews 4) 1 (initial 7 [0])) :=
  earned_split_eq_fixed unreadViews Nat.succ (unreadViews 4) 1 4 (initial 7 [0]) 0 []
    ((Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mp unread_change_full_support_accepts)

theorem zero_allowance_keeps_actual_saved_source :
    resume unreadViews Nat.succ 0 (unreadCut 1) = unreadCut 1 := resume_zero ..

private def selfViews (_ : Nat) : Source (Fin 1) Nat := finiteSource 1 (fun _ => 7) (fun _ => [0])
private def foreignSelf : Source (Fin 1) Nat := finiteSource 1 (fun _ => 99) (fun _ => [])
private def selfCut (fuel : Nat) := advance selfViews Nat.succ fuel (initial 7 [0]) 0 []
private def pendingSelf := controlState selfViews Nat.succ (selfCut 1).2

theorem pending_self_backedge_has_no_new_source_intent :
    readIntent (initial 7 [0] : State (Fin 1) Nat) = some 0 ∧ readIntent pendingSelf = none := ⟨rfl, rfl⟩

theorem backedge_step_is_independent_of_changed_source :
    step (selfViews 0) pendingSelf = step foreignSelf pendingSelf :=
  no_intent_needs_no_source_agreement (selfViews 0) foreignSelf pendingSelf rfl

theorem local_backedge_and_completion_stay_charged :
    (selfCut 4).1 = 3 ∧ (recorded selfViews Nat.succ (selfCut 4).2).length = 1 ∧
      (controlState selfViews Nat.succ (selfCut 2).2).written 0 0 = some (7, 0) ∧
      published selfViews Nat.succ (selfCut 2).2 = none := by exact ⟨rfl, rfl, by decide, rfl⟩

/-- An earlier header changes while later child reads stay current. -/
private def headerViews (clock : Nat) : Source (Fin 2) Nat :=
  finiteSource 2 (fun address => if address = 0 then (if clock = 0 then 0 else 99) else 20)
    (fun address => if address = 0 then [1] else [])
private def headerRun := advance headerViews Nat.succ 5 (initial 7 [0]) 0 []

theorem later_read_check_does_not_cover_changed_earlier_header :
    checkReads (observe (headerViews 4)) (recorded headerViews Nat.succ headerRun.2).tail = true ∧
      checkReads (observe (headerViews 4)) (recorded headerViews Nat.succ headerRun.2) = false := by decide

theorem changed_earlier_header_refuses_current_publication :
    checkedPublication headerViews Nat.succ (headerViews 4) headerRun.2 = none :=
  checkedPublication_refuses headerViews Nat.succ (headerViews 4) headerRun.2
    later_read_check_does_not_cover_changed_earlier_header.2

theorem fixed_allocation_does_not_freeze_header_payloads :
    (headerViews 0).heap.allocated = (headerViews 4).heap.allocated ∧
      (observe (headerViews 0) 0).1 ≠ (observe (headerViews 4) 0).1 := by decide

/-- The heap's set-valued edges remain equal; only actual slot order changes. -/
private def reorderViews (clock : Nat) : Source (Fin 3) Nat :=
  finiteSource 3 Fin.val (fun address => if address = 0 then
    (if clock = 0 then [1, 2] else [2, 1]) else [])
private def reorderRun := advance reorderViews Nat.succ 7 (initial 7 [0]) 0 []

theorem header_only_validation_misses_ordered_slot_change :
    checkReads (fun address => (observe (reorderViews 6) address).1)
        ((recorded reorderViews Nat.succ reorderRun.2).map (fun read => (read.1, read.2.1))) = true ∧
      checkReads (observe (reorderViews 6)) (recorded reorderViews Nat.succ reorderRun.2) = false := by
  have actualLog : recorded reorderViews Nat.succ reorderRun.2 =
      [(0, observe (reorderViews 0) 0), (1, observe (reorderViews 1) 1),
        (2, observe (reorderViews 3) 2)] := rfl
  have rootHeader : (observe (reorderViews 6) 0).1 = (observe (reorderViews 0) 0).1 := by
    simp [observe, reorderViews, finiteSource, Finset.pair_comm]
  constructor
  · apply (Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mpr
    rw [actualLog]
    intro read member
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact rootHeader
    · rfl
    · rfl
  · apply Bool.eq_false_iff.mpr
    intro accepted
    have agrees := (Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mp accepted
    have node := agrees (0, observe (reorderViews 0) 0) (by rw [actualLog]; simp)
    have slots := congrArg Prod.snd node
    change ([2, 1] : List (Fin 3)) = [1, 2] at slots
    exact (by decide : ([2, 1] : List (Fin 3)) ≠ [1, 2]) slots

theorem changed_ordered_slots_refuse_current_publication :
    checkedPublication reorderViews Nat.succ (reorderViews 6) reorderRun.2 = none :=
  checkedPublication_refuses reorderViews Nat.succ (reorderViews 6) reorderRun.2
    header_only_validation_misses_ordered_slot_change.2

theorem stale_order_changes_the_actual_written_inventory :
    (controlState reorderViews Nat.succ reorderRun.2).written 0 0 = some (7, 1) ∧
      (RetainedCopy.stateOf (reorderViews 6)
        (RetainedCopy.run (reorderViews 6) 7 (initial 7 [0])).2).written 0 0 = some (7, 2) := by decide

private def duplicateViews (_ : Nat) : Source (Fin 2) Nat :=
  finiteSource 2 Fin.val (fun address => if address = 0 then [1, 1] else [])
private def duplicateRun := advance duplicateViews Nat.succ 6 (initial 7 [0]) 0 []

theorem duplicate_slots_share_one_consulted_node_without_losing_writes :
    duplicateRun.1 = 5 ∧ (recorded duplicateViews Nat.succ duplicateRun.2).length = 2 ∧
      (controlState duplicateViews Nat.succ duplicateRun.2).count 0 = 2 ∧
      (controlState duplicateViews Nat.succ duplicateRun.2).written 0 0 = some (7, 1) ∧
      (controlState duplicateViews Nat.succ duplicateRun.2).written 0 1 = some (7, 1) := by decide

end Controls

end Mettapedia.Machines.ResourceOwnership.TraceWork.RetainedCopy.SourceLocality

/-!
## Admitted rows as an existing retained-copy source

The adapter supplies exactly the existing source fields from earned finite
descriptor checks. Execution, buffers, completion, ordered inventory and the
declared copy invoice use the existing retained cursor without a new producer.
The rows still require independent capture authenticity and stable-source
admission before they describe a native current or protected resource view.
-/

namespace Mettapedia.Machines.ResourceOwnership.DescriptorAdmission.SourceAdapter

open TraceWork
open TraceWork.RetainedCopy

variable {A : Type} {V : Type} [LinearOrder A] [DecidableEq V]

def source (checked : Checked A V) : Source A V where
  heap := checked.heap
  slots := checked.slots
  slots_exact := checked.slots_exact

theorem source_lookup (checked : Checked A V) (address : A) :
    (source checked).heap.lookup address = header checked.rows address := rfl

theorem source_allocated (checked : Checked A V) :
    (source checked).heap.allocated = allocated checked.rows := rfl

theorem source_slots (checked : Checked A V) (address : A) :
    (source checked).slots address = slots checked.rows address := rfl

theorem roots_valid (checked : Checked A V) :
    ∀ a ∈ checked.roots, a ∈ (source checked).heap.allocated := checked.roots_allocated

theorem recorded_response (checked : Checked A V) (address : A) (descriptor : Descriptor A V)
    (member : (address, descriptor) ∈ checked.rows) :
    (source checked).heap.lookup address = descriptor.1 ∧
      (source checked).slots address = descriptor.2 := checked.realizes_row address descriptor member

/-- Finite completion is earned from the actual admission, with the existing
reachable-graph invoice and the existing cursor's completion poll. -/
theorem initial_completes (checked : Checked A V) (owner : Nat) :
    ∃ final, run (source checked) (referenceWork (source checked) checked.roots + 1)
        (initial owner checked.roots) =
      (referenceWork (source checked) checked.roots, .done ⟨(), .ok final, ()⟩) ∧
      Invariant (source checked) checked.roots final ∧ ready final = true :=
  initial_completes_exact (source checked) checked.roots owner (roots_valid checked)

theorem completed_invoice (checked : Checked A V) (owner fuel spent : Nat) (final : State A V)
    (result : run (source checked) fuel (initial owner checked.roots) =
      (spent, .done ⟨(), .ok final, ()⟩)) :
    spent = referenceWork (source checked) checked.roots :=
  RetainedCopy.completed_invoice (source checked) checked.roots owner fuel spent
    (roots_valid checked) final result

theorem completed_relocation (checked : Checked A V) (owner fuel spent : Nat) (final : State A V)
    (result : run (source checked) fuel (initial owner checked.roots) =
      (spent, .done ⟨(), .ok final, ()⟩)) :
    ∃ invariant : Invariant (source checked) checked.roots final, ∃ finished : ready final = true,
      Nonempty (Relocation (collect checked.heap (rootsOf checked.roots))
        (destination (source checked) checked.roots final invariant finished)) :=
  RetainedCopy.completed_relocation (source checked) checked.roots owner fuel spent
    (roots_valid checked) final result

theorem completed_ordered_inventory (checked : Checked A V) (owner fuel spent : Nat) (final : State A V)
    (result : run (source checked) fuel (initial owner checked.roots) =
      (spent, .done ⟨(), .ok final, ()⟩)) :
    final.originals = checked.roots ∧ ∀ a ∈ footprint checked.heap (rootsOf checked.roots),
      final.count a = (checked.slots a).length ∧ ∀ i b, (checked.slots a)[i]? = some b →
        final.written a i = some (image final b) ∧ b ∈ final.reserved :=
  RetainedCopy.completed_ordered_inventory (source checked) checked.roots owner fuel spent
    (roots_valid checked) final result

theorem accepted_rows_complete (rows : Rows A V) (roots : List A) (checked : Checked A V)
    (issued : admitRows rows roots = some checked) (owner : Nat) :
    ∃ final, run (source checked) (referenceWork (source checked) roots + 1) (initial owner roots) =
      (referenceWork (source checked) roots, .done ⟨(), .ok final, ()⟩) ∧
      final.originals = roots ∧
      (∀ address descriptor, (address, descriptor) ∈ rows →
        (source checked).heap.lookup address = descriptor.1 ∧
        (source checked).slots address = descriptor.2) := by
  obtain ⟨sameRows, sameRoots, _⟩ := admit_admitted rows roots checked issued
  obtain ⟨final, result, _, _⟩ := initial_completes checked owner
  have inventory := completed_ordered_inventory checked owner _ _ final result
  refine ⟨final, ?_, ?_, ?_⟩
  · simpa only [sameRoots] using result
  · simpa only [sameRoots] using inventory.1
  · intro address descriptor member
    exact recorded_response checked address descriptor (sameRows.symm ▸ member)

theorem zero_allowance (checked : Checked A V) (owner : Nat) :
    run (source checked) 0 (initial owner checked.roots) =
      (0, .paused ⟨(), initial owner checked.roots, ()⟩) := rfl

theorem split (checked : Checked A V) (owner first second : Nat) :
    run (source checked) (first + second) (initial owner checked.roots) =
      resume (source checked) second (run (source checked) first (initial owner checked.roots)) :=
  run_add (source checked) first second (initial owner checked.roots)

namespace Controls

private def self : Checked Nat Nat :=
  ⟨[(0, (some ⟨7, {0}, 8⟩, [0]))], [0], by decide⟩

private def pairCycle : Checked Nat Nat :=
  ⟨[(0, (some ⟨7, {1}, 8⟩, [1])), (1, (some ⟨9, {0}, 8⟩, [0]))], [0], by decide⟩

private def duplicates : Checked Nat Nat :=
  ⟨[(0, (some ⟨7, {1}, 8⟩, [1, 1])), (1, (some ⟨9, ∅, 8⟩, []))], [0, 0], by decide⟩

theorem empty_rows_complete_without_copy_debits :
    let checked : Checked Nat Nat := ⟨[], [], by decide⟩
    (run (source checked) 1 (initial 42 checked.roots)).1 = 0 ∧
      (published (source checked) (run (source checked) 1 (initial 42 checked.roots)).2).map
        (fun final => (final.originals, final.reserved.card)) = some ([], 0) := by decide

theorem self_cycle_copies_its_actual_backedge :
    (run (source self) 4 (initial 42 self.roots)).1 = 3 ∧
      (published (source self) (run (source self) 4 (initial 42 self.roots)).2).map
        (fun final => (final.originals, final.count 0, final.written 0 0, final.reserved.card)) =
        some ([0], 1, some (42, 0), 1) := by decide

theorem mutual_cycle_copies_both_directions :
    (run (source pairCycle) 6 (initial 42 pairCycle.roots)).1 = 5 ∧
      (published (source pairCycle) (run (source pairCycle) 6 (initial 42 pairCycle.roots)).2).map
        (fun final => (final.written 0 0, final.written 1 0, final.reserved.card)) =
        some (some (42, 1), some (42, 0), 2) := by decide

theorem duplicate_roots_and_slots_keep_their_occurrences :
    (run (source duplicates) 7 (initial 42 duplicates.roots)).1 = 6 ∧
      (published (source duplicates) (run (source duplicates) 7 (initial 42 duplicates.roots)).2).map
        (fun final => final.originals) = some [0, 0] ∧
      (published (source duplicates) (run (source duplicates) 7 (initial 42 duplicates.roots)).2).map
        (fun final => final.count 0) = some 2 ∧
      (published (source duplicates) (run (source duplicates) 7 (initial 42 duplicates.roots)).2).map
        (fun final => (final.written 0 0, final.written 0 1)) = some (some (42, 1), some (42, 1)) ∧
      (published (source duplicates) (run (source duplicates) 7 (initial 42 duplicates.roots)).2).map
        (fun final => final.reserved.card) = some 2 := by decide

theorem zero_does_not_publish_a_source_image :
    (run (source self) 0 (initial 42 self.roots)).1 = 0 ∧
      published (source self) (run (source self) 0 (initial 42 self.roots)).2 = none := by decide

theorem written_prefix_is_still_unpublished :
    (run (source self) 3 (initial 42 self.roots)).1 = 3 ∧
      published (source self) (run (source self) 3 (initial 42 self.roots)).2 = none := by decide

theorem missing_descendant_cannot_supply_a_copy_source :
    (admitRows ([(0, (some ⟨7, {1}, 8⟩, [1]))] : Rows Nat Nat) [0]).map source = none := by
  rw [admit_of_rejected _ _ (by decide)]
  rfl

end Controls

end Mettapedia.Machines.ResourceOwnership.DescriptorAdmission.SourceAdapter

/-!
## Nested mutable observation profiles

Finite read and write path inventories select an explicit observation family
on the existing ordered resource source. Actual topology-preserving writes
and the shared finite context closure derive its exact signature: initial
scalar reads plus write-to-read alias incidence, with two distinguishable
payloads required for necessity. No global equality or unification is selected.

Read-only and restricted mutable profiles may forget shared descendants;
alternate-path writes can reveal them. Ordered slots, alias identity and raw
binding representatives remain separate. Candidate filtering interprets rows
through the selected view and preserves their original occurrence coordinates.
The generic row-filter theorem is reused; syntax-only posting carriers are not
identified with native State or Space. Source capture, native interpretation,
refusal, memory, service prices and C refinement remain separate obligations.
-/

namespace Mettapedia.Machines.ResourceOwnership.TraceWork.NestedProfiles

open Mettapedia.GSLT.Core
open RetainedCopy

universe u
variable {A : Type} {V : Type u} [LinearOrder A]

/-- The existing ordered source paired with its selected root. -/
abbrev Client (A : Type) (V : Type u) [LinearOrder A] := Source A V × A

def read (client : Client A V) (path : List Nat) : Option V :=
  OrderedObservation.payload client.1.heap client.1.slots client.2 path

def incidence (client : Client A V) (written observed : List Nat) : Bool :=
  OrderedObservation.impact client.1.heap client.1.slots client.2 written observed

/-- Mutate only the selected endpoint's scalar payload. The ordered source
invariant is derived from the existing topology-preserving heap write. -/
def writeSource (source : Source A V) (root : A) (path : List Nat) (value : V) : Source A V where
  heap := OrderedObservation.write source.heap source.slots root path value
  slots := source.slots
  slots_exact address := by
    change (source.slots address).toFinset =
      (OrderedObservation.write source.heap source.slots root path value).dependencies address
    unfold OrderedObservation.write
    split
    · exact source.slots_exact address
    · rw [Heap.writePayload_dependencies]
      exact source.slots_exact address

/-- Reuse the existing one-scope operation graph. An edge is one declared
write-path coordinate and an actual payload, not another operation syntax. -/
abbrev Scope (V : Type u) (writes : List (List Nat)) :=
  Optimality.ContextualReferences.Scope (Fin writes.length × V)

def execute (writes : List (List Nat)) {a b : Scope V writes} (operation : a ⟶ b)
    (client : Client A V) : Client A V :=
  (writeSource client.1 client.2 writes[operation.1] operation.2, client.2)

def base (reads writes : List (List Nat)) (_ : Scope V writes) : PolicyFamily (Client A V) where
  Policy := Fin reads.length
  Result _ := Option V
  decide coordinate client := read client reads[coordinate]

def observations (reads writes : List (List Nat)) : PolicyFamily (Client A V) :=
  PolicyFamily.ContextClosure.family (execute writes) (base reads writes) .heap

/-- Initial ordered reads plus actual write-to-read alias incidence. Read
absence is retained; otherwise unobservable endpoint validity is omitted. -/
def signature (reads writes : List (List Nat)) (client : Client A V) :
    (Fin reads.length → Option V) × (Fin writes.length → Fin reads.length → Bool) :=
  (fun r => read client reads[r], fun w r => incidence client writes[w] reads[r])

theorem read_after_execute (reads writes : List (List Nat)) {a b : Scope V writes}
    (operation : a ⟶ b) (client : Client A V) (r : Fin reads.length) :
    read (execute writes operation client) reads[r] =
      if incidence client writes[operation.1] reads[r] then some operation.2
      else read client reads[r] :=
  OrderedObservation.payload_after_write client.1.heap client.1.slots client.2
    writes[operation.1] reads[r] operation.2

theorem incidence_after_execute (writes : List (List Nat)) {a b : Scope V writes}
    (operation : a ⟶ b) (client : Client A V) (left right : List Nat) :
    incidence (execute writes operation client) left right = incidence client left right :=
  OrderedObservation.impact_after_write client.1.heap client.1.slots client.2
    writes[operation.1] left right operation.2

theorem signature_stable (reads writes : List (List Nat)) {a b : Scope V writes}
    (operation : a ⟶ b) (left right : Client A V)
    (same : signature reads writes left = signature reads writes right) :
    signature reads writes (execute writes operation left) =
      signature reads writes (execute writes operation right) := by
  have values : ∀ r : Fin reads.length, read left reads[r] = read right reads[r] :=
    fun r => congrFun (congrArg Prod.fst same) r
  have aliases : ∀ (w : Fin writes.length) (r : Fin reads.length), incidence left writes[w] reads[r] = incidence right writes[w] reads[r] :=
    fun w r => congrFun (congrFun (congrArg Prod.snd same) w) r
  apply Prod.ext
  · funext r
    change read (execute writes operation left) reads[r] = read (execute writes operation right) reads[r]
    rw [read_after_execute, read_after_execute, values r, aliases operation.1 r]
  · funext w r
    exact (incidence_after_execute writes operation left _ _).trans
      ((aliases w r).trans (incidence_after_execute writes operation right _ _).symm)

/-- Sufficiency follows from the concrete update law and the greatest
operation-stable relation in the shared context-closure owner. -/
theorem equivalent_of_signature (reads writes : List (List Nat)) (left right : Client A V)
    (same : signature reads writes left = signature reads writes right) :
    (observations reads writes).PolicyEquivalent left right := by
  apply PolicyFamily.ContextClosure.greatest (execute writes) (base reads writes)
    (fun _ l r => signature reads writes l = signature reads writes r) ?_ ?_ same
  · intro scope l r related coordinate
    exact congrFun (congrArg Prod.fst related) coordinate
  · intro a b operation l r related
    exact signature_stable reads writes operation l r related

/-- Two actual distinguishable writes recover each observable incidence
bit. No raw endpoint names or globally available anchors are required. -/
theorem signature_of_equivalent [Nontrivial V] (reads writes : List (List Nat))
    (left right : Client A V) (same : (observations reads writes).PolicyEquivalent left right) :
    signature reads writes left = signature reads writes right := by
  have values : ∀ r : Fin reads.length, read left reads[r] = read right reads[r] := by
    intro r
    exact same ⟨.heap, .nil, r⟩
  apply Prod.ext
  · exact funext values
  · funext w r
    change incidence left writes[w] reads[r] = incidence right writes[w] reads[r]
    have probe (value : V) :
        (if incidence left writes[w] reads[r] then some value else read left reads[r]) =
          (if incidence right writes[w] reads[r] then some value else read right reads[r]) := by
      have after := PolicyFamily.ContextClosure.operation_stable (execute writes) (base reads writes)
        (a := (.heap : Scope V writes)) (b := .heap) (w, value) same
      have observed := after ⟨.heap, .nil, r⟩
      change read (execute writes (a := (.heap : Scope V writes)) (b := .heap) (w, value) left) reads[r] =
        read (execute writes (a := (.heap : Scope V writes)) (b := .heap) (w, value) right) reads[r] at observed
      simpa only [read_after_execute] using observed
    obtain ⟨zero, one, different⟩ := exists_pair_ne V
    have first := probe zero
    have second := probe one
    cases l : incidence left writes[w] reads[r] <;>
      cases r' : incidence right writes[w] reads[r] <;> simp only [l, r', Bool.false_eq_true,
        ↓reduceIte] at first second ⊢
    · exact False.elim (different (Option.some.inj (first.symm.trans second)))
    · exact False.elim (different (Option.some.inj (first.trans second.symm)))

theorem contextual_equivalent_iff [Nontrivial V] (reads writes : List (List Nat))
    (left right : Client A V) :
    (observations reads writes).PolicyEquivalent left right ↔
      signature reads writes left = signature reads writes right :=
  ⟨signature_of_equivalent reads writes left right, equivalent_of_signature reads writes left right⟩

section Indexed

variable [DecidableEq V] {Row Binding : Type}

/-- Admission checks path depth before executing its query. Outer absence
means unknown; an admitted inner `none` is an actual negative lookup. This
allowance counts path depth, not native instructions or allocation work. -/
def preview (allowance : Nat) (client : Client A V) (path : List Nat) : Option (Option V) :=
  if path.length + 1 ≤ allowance then some (read client path) else none

def accept (reads writes : List (List Nat)) (query : Client A V)
    (view : Row → Client A V) (row : Row) : Bool :=
  decide (signature reads writes (view row) = signature reads writes query)

/-- Filter only on an actually admitted scalar coordinate. Raw row and
resource representatives remain unchanged for downstream bindings. -/
def possible (reads : List (List Nat)) (coordinate : Fin reads.length)
    (allowance : Nat) (query : Client A V) (view : Row → Client A V) (row : Row) : Bool :=
  match preview allowance (view row) reads[coordinate] with
  | none => true
  | some answer => decide (answer = read query reads[coordinate])

theorem accept_iff_contextual [Nontrivial V] (reads writes : List (List Nat))
    (query : Client A V) (view : Row → Client A V) (row : Row) :
    accept reads writes query view row = true ↔
      (observations reads writes).PolicyEquivalent (view row) query := by
  simp only [accept, decide_eq_true_eq, contextual_equivalent_iff]

/-- Completeness is derived from the constructed observation, not supplied
as an unexplained candidate-soundness assumption. -/
theorem candidate_complete (reads writes : List (List Nat)) (coordinate : Fin reads.length)
    (allowance : Nat) (query : Client A V) (view : Row → Client A V) (row : Row)
    (accepted : accept reads writes query view row = true) :
    possible reads coordinate allowance query view row = true := by
  have same := of_decide_eq_true accepted
  have scalar := congrFun (congrArg Prod.fst same) coordinate
  simp only [signature] at scalar
  by_cases admitted : reads[coordinate].length + 1 ≤ allowance
  · simp only [possible, preview, if_pos admitted]
    exact decide_eq_true scalar
  · simp only [possible, preview, if_neg admitted]

theorem filter_exact (reads writes : List (List Nat)) (coordinate : Fin reads.length)
    (allowance : Nat) (query : Client A V) (view : Row → Client A V) (rows : List Row) :
    (rows.filter (possible reads coordinate allowance query view)).filter
        (accept reads writes query view) = rows.filter (accept reads writes query view) :=
  Mettapedia.Machines.MatchIndexProjection.filter_candidates _ _
    (candidate_complete reads writes coordinate allowance query view) rows

/-- Original occurrence coordinates and duplicate rows survive the filter;
candidate-list positions are never substituted for source positions. -/
theorem original_coordinates_exact (reads writes : List (List Nat))
    (coordinate : Fin reads.length) (allowance : Nat) (query : Client A V)
    (view : Row → Client A V) (rows : List Row) :
    ((Mettapedia.Machines.MatchIndexProjection.Ordered.localIndex
        (possible reads coordinate allowance query view) rows).rows.filter
          (fun entry => accept reads writes query view entry.1)) =
      rows.zipIdx.filter (fun entry => accept reads writes query view entry.1) := by
  apply Mettapedia.Machines.MatchIndexProjection.filter_candidates
  intro entry accepted
  exact candidate_complete reads writes coordinate allowance query view entry.1 accepted

theorem original_bindings_exact (reads writes : List (List Nat))
    (coordinate : Fin reads.length) (allowance : Nat) (query : Client A V)
    (view : Row → Client A V) (rows : List Row) (bindings : Row → List Binding) :
    (((rows.filter (possible reads coordinate allowance query view)).filter
      (accept reads writes query view)).flatMap bindings) =
      (rows.filter (accept reads writes query view)).flatMap bindings := by
  rw [filter_exact]

end Indexed

namespace Controls

open DescriptorAdmission

def row (address : Fin 5) (value : Nat) (slots : List (Fin 5)) :
    Fin 5 × Descriptor (Fin 5) Nat :=
  (address, (some ⟨value, slots.toFinset, 1⟩, slots))

/-- Both graphs contain actual headers and ordered slots. The shared graph
has a spare unreachable cell; its diamond still has one shared descendant. -/
def diamondRows (shared : Bool) : Rows (Fin 5) Nat :=
  [row 0 0 [1, 2], row 1 1 [3], row 2 2 [if shared then 3 else 4],
    row 3 7 [], row 4 7 []]

def diamondChecked (shared : Bool) : Checked (Fin 5) Nat :=
  ⟨diamondRows shared, [0], by cases shared <;> decide⟩

def diamond (shared : Bool) : Client (Fin 5) Nat :=
  (SourceAdapter.source (diamondChecked shared), 0)

def leftPath : List Nat := [0, 0]
def rightPath : List Nat := [1, 0]

theorem diamond_has_equal_scalars_but_different_sharing :
    read (diamond true) leftPath = some 7 ∧ read (diamond true) rightPath = some 7 ∧
      read (diamond false) leftPath = some 7 ∧ read (diamond false) rightPath = some 7 ∧
      incidence (diamond true) leftPath rightPath = true ∧
      incidence (diamond false) leftPath rightPath = false := by decide

theorem read_only_diamond_forgets_shared_descendant :
    (observations [leftPath, rightPath] []).PolicyEquivalent (diamond true) (diamond false) := by
  apply equivalent_of_signature
  decide

theorem selected_descendant_mutable_profile_forgets_sharing :
    (observations [leftPath] [leftPath]).PolicyEquivalent (diamond true) (diamond false) := by
  apply equivalent_of_signature
  decide

theorem alternate_path_observes_actual_write :
    read (execute [leftPath] (a := (.heap : Scope Nat [leftPath])) (b := .heap)
      (0, (9 : Nat)) (diamond true)) rightPath = some 9 ∧
    read (execute [leftPath] (a := (.heap : Scope Nat [leftPath])) (b := .heap)
      (0, (9 : Nat)) (diamond false)) rightPath = some 7 := by decide

theorem mutation_closed_diamond_profile_separates_sharing :
    ¬ (observations [rightPath] [leftPath]).PolicyEquivalent (diamond true) (diamond false) := by
  rw [contextual_equivalent_iff]
  decide

theorem raw_alias_rejection_loses_a_read_only_match :
    accept [rightPath] [] (diamond true) id (diamond false) = true ∧
      incidence (diamond true) leftPath rightPath ≠ incidence (diamond false) leftPath rightPath := by
  decide

def cycleRows : Rows (Fin 5) Nat :=
  [row 0 7 [1, 1], row 1 7 [0]]

def cycleChecked : Checked (Fin 5) Nat := ⟨cycleRows, [0], by decide⟩
def cycle : Client (Fin 5) Nat := (SourceAdapter.source cycleChecked, 0)

def selfChecked : Checked (Fin 5) Nat := ⟨[row 0 7 [0, 0]], [0], by decide⟩
def selfCycle : Client (Fin 5) Nat := (SourceAdapter.source selfChecked, 0)

def isolatedChecked : Checked (Fin 5) Nat := ⟨[row 0 7 []], [0], by decide⟩
def isolated : Client (Fin 5) Nat := (SourceAdapter.source isolatedChecked, 0)

theorem mutual_cycle_is_read_and_written_without_unfolding_a_tree :
    read cycle [0, 0] = some 7 ∧ incidence cycle [] [0, 0] = true ∧
      OrderedObservation.target cycle.1.heap cycle.1.slots cycle.2 [0, 0, 0] = some 1 ∧
      read (execute [[]] (a := (.heap : Scope Nat [[]])) (b := .heap)
        (0, (9 : Nat)) cycle) [0, 0] = some 9 := by decide

theorem self_cycle_keeps_repeated_read_occurrences_and_duplicate_slots :
    (OrderedObservation.observe selfCycle.1.heap selfCycle.1.slots selfCycle.2 [0, 1]).reads.map
      Prod.fst = [0, 0, 0] ∧
      selfCycle.1.slots 0 = [0, 0] ∧ read selfCycle [0, 1] = some 7 := by decide

theorem arbitrary_finite_self_cycle_keeps_all_read_occurrences (length : Nat) :
    (OrderedObservation.observe selfCycle.1.heap selfCycle.1.slots selfCycle.2
      (List.replicate length 0)).reads.map Prod.fst = List.replicate (length + 1) 0 := by
  have actual := OrderedObservation.self_cycle_reads selfCycle.1.heap selfCycle.1.slots
    selfCycle.2 ⟨7, {0}, 1⟩ (by decide) (by decide) length
  have logged := congrArg (fun observed => observed.reads.map Prod.fst) actual
  simpa only [List.map_replicate, selfCycle] using logged

theorem absence_is_not_aliasing :
    read cycle [2] = none ∧ incidence cycle [2] [3] = false ∧
      read (execute [[2]] (a := (.heap : Scope Nat [[2]])) (b := .heap)
        (0, (9 : Nat)) cycle) [] = some 7 := by decide

/-- A valid unobserved write and an invalid no-op are equivalent for this
profile; an extra validity bit would make the claimed exact signature false. -/
theorem invalid_and_unobserved_write_are_equivalent :
    (observations [[]] [[0]]).PolicyEquivalent isolated cycle := by
  apply equivalent_of_signature
  decide

theorem known_absence_and_unknown_preview_differ :
    preview 0 cycle [2] = none ∧ preview 2 cycle [2] = some none ∧
      possible [[]] 0 0 (diamond true) id cycle = true ∧
      possible [[]] 0 1 (diamond true) id cycle = false := by decide

theorem filtering_keeps_raw_rows_duplicates_and_coordinates :
    ((Mettapedia.Machines.MatchIndexProjection.Ordered.localIndex
      (possible [rightPath] 0 3 (diamond true) id)
      [diamond false, diamond false, isolated]).rows.filter
        (fun entry => accept [rightPath] [] (diamond true) id entry.1)).map Prod.snd = [0, 1] := by decide

def reorderedChecked : Checked (Fin 5) Nat :=
  ⟨[row 0 0 [2, 1], row 1 1 [3], row 2 2 [3], row 3 7 [], row 4 7 []], [0], by decide⟩
def reordered : Client (Fin 5) Nat := (SourceAdapter.source reorderedChecked, 0)

def duplicateChecked : Checked (Fin 5) Nat :=
  ⟨[row 0 0 [1, 1, 2], row 1 1 [3], row 2 2 [3], row 3 7 [], row 4 7 []], [0], by decide⟩
def duplicate : Client (Fin 5) Nat := (SourceAdapter.source duplicateChecked, 0)

theorem header_and_reference_set_equality_do_not_preserve_ordinal_observations :
    (diamond true).1.heap.lookup 0 = reordered.1.heap.lookup 0 ∧
      (diamond true).1.heap.lookup 0 = duplicate.1.heap.lookup 0 ∧
      read (diamond true) [0] = some 1 ∧ read reordered [0] = some 2 ∧
      read (diamond true) [1] = some 2 ∧ read duplicate [1] = some 1 := by
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide⟩
  · change some (⟨0, ([1, 2] : List (Fin 5)).toFinset, 1⟩ : Cell (Fin 5) Nat) =
      some ⟨0, ([2, 1] : List (Fin 5)).toFinset, 1⟩
    have unordered : ([1, 2] : List (Fin 5)).toFinset = [2, 1].toFinset := by
      ext address
      simp [or_comm]
    exact congrArg (fun refs => some (⟨0, refs, 1⟩ : Cell (Fin 5) Nat)) unordered
  · change some (⟨0, ([1, 2] : List (Fin 5)).toFinset, 1⟩ : Cell (Fin 5) Nat) =
      some ⟨0, ([1, 1, 2] : List (Fin 5)).toFinset, 1⟩
    simp

theorem complete_descriptor_agreement_preserves_actual_ordered_query
    (path : List Nat) :
    ReadOnlyQuery.Agrees
      (OrderedObservation.provider (diamond true).1.heap (diamond true).1.slots)
      (OrderedObservation.observe (diamond true).1.heap (diamond true).1.slots 0 path).reads :=
  ReadOnlyQuery.run_agrees _ _

theorem unconsulted_scalar_write_preserves_complete_actual_certificate :
    OrderedObservation.observe ((diamond true).1.heap.writePayload 4 9) (diamond true).1.slots 0 leftPath =
      OrderedObservation.observe (diamond true).1.heap (diamond true).1.slots 0 leftPath := by
  apply OrderedObservation.write_outside_reads
  decide

theorem consulted_scalar_write_changes_actual_certificate :
    OrderedObservation.observe ((diamond true).1.heap.writePayload 3 9) (diamond true).1.slots 0 leftPath ≠
      OrderedObservation.observe (diamond true).1.heap (diamond true).1.slots 0 leftPath := by
  intro same
  have observed := congrArg (fun observation => observation.answer.map (fun p => p.2.value)) same
  exact (by decide : (some 9 : Option Nat) ≠ some 7) observed

end Controls

end Mettapedia.Machines.ResourceOwnership.TraceWork.NestedProfiles

/-!
## Retained copy phase invoices

The following annotations read the existing step's actual cases: ordered
root consumption, fresh private reservation, indexed slot write, node
completion, and refused lookup. Independent state-coordinate balances derive
an exact phase census for every actual cursor prefix. Completed counts are
computed from source root occurrences, reachable nodes and ordered slots.
The existing run-account construction projects declared prices over typed
paths of that same step, and the existing cursor retains exact charge words.

These are mathematical action prices. A constant number of model events does
not establish bounded native work: descriptor lookup, shell storage, allocation,
validation, callbacks, cancellation disposal and finalizers require separately
justified prices and progress. Cancellation here retains private writes and its
paid prefix; it does not run disposal. Native source/event/scope decoding,
current-view and lifetime admission, and compiled-C refinement remain open.
-/

namespace Mettapedia.Machines.ResourceOwnership.TraceWork.RetainedCopy.Invoice

open Mettapedia.TypeTheory

variable {A V : Type} [LinearOrder A]

inductive Kind where
  | root | reserve | slot | finish | refused
  deriving DecidableEq, Repr

/-- Source coordinates are retained; slot indices are the actual saved
written-prefix position. These are model actions, not C instruction events. -/
inductive Event (A : Type) where
  | root (address : A)
  | reserve (address : A)
  | slot (source : A) (ordinal : Nat) (target : A)
  | finish (address : A)
  | refused (address : A)
  deriving DecidableEq, Repr

def Event.kind : Event A → Kind
  | .root _ => .root
  | .reserve _ => .reserve
  | .slot _ _ _ => .slot
  | .finish _ => .finish
  | .refused _ => .refused

/-- Exhaustive annotation of the existing step. No transition, discovery,
allocation or evaluator is defined by this observation. -/
def events (source : Source A V) (state : State A V) : List (Event A) :=
  if state.refused then [] else
  match state.frames with
  | frame :: _ => match frame.remaining with
    | [] => [.finish frame.source]
    | child :: _ =>
      if child ∈ state.reserved then [.slot frame.source (state.count frame.source) child]
      else match source.heap.lookup child with
        | none => [.refused child]
        | some _ => [.reserve child, .slot frame.source (state.count frame.source) child]
  | [] => match state.roots with
    | [] => []
    | root :: _ =>
      if root ∈ state.reserved then [.root root]
      else match source.heap.lookup root with
        | none => [.refused root]
        | some _ => [.root root, .reserve root]

def count (kind : Kind) (word : List (Event A)) : Nat :=
  word.countP (fun event => event.kind == kind)

def writtenTally (state : State A V) : Nat := state.reserved.sum state.count

theorem tally_pushFresh (source : Source A V) (state : State A V) (a : A)
    (fresh : a ∉ state.reserved) :
    writtenTally (pushFresh source a state) = writtenTally state := by
  simp only [writtenTally, pushFresh, reserve]
  rw [Finset.sum_insert fresh, Function.update_self,
    Finset.sum_update_of_notMem fresh]
  simp only [zero_add]

theorem tally_writeSlot (state : State A V) (a b : A) (seen : a ∈ state.reserved) :
    writtenTally (writeSlot a b state) = writtenTally state + 1 := by
  simp only [writtenTally, writeSlot]
  rw [Finset.sum_update_of_mem seen]
  have partition := Finset.sum_erase_add state.reserved state.count seen
  simp only [Finset.sdiff_singleton_eq_erase] at *
  convert congrArg (· + 1) partition using 1
  ac_rfl

theorem events_length (source : Source A V) (state : State A V) :
    (events source state).length ≤ 2 := by
  unfold events
  split
  · simp
  · split
    · split
      · simp
      · split
        · simp
        · split <;> simp
    · split
      · simp
      · split
        · simp
        · split <;> simp

/-- Every actual provider request has one charged primary action. A refused
lookup is paid; already terminal client inspections are not requests. -/
theorem primary_coverage (source : Source A V) (state : State A V)
    (clear : state.refused = false) (running : ready state = false) :
    count .root (events source state) + count .slot (events source state) +
      count .finish (events source state) + count .refused (events source state) = 1 := by
  cases frames : state.frames with
  | nil =>
      cases roots : state.roots with
      | nil => simp [ready, clear, frames, roots] at running
      | cons root rest =>
          unfold events
          simp only [clear, Bool.false_eq_true, ↓reduceIte, frames, roots]
          split
          · rfl
          · split <;> rfl
  | cons frame rest =>
      unfold events
      simp only [clear, Bool.false_eq_true, ↓reduceIte, frames]
      split
      · rfl
      · split
        · rfl
        · split <;> rfl


/-- Actual valid steps conserve each independently read state coordinate.
The premises are the existing buffer invariant and actual readiness status. -/
theorem step_balance (source : Source A V) (roots : List A) (state : State A V)
    (valid : Invariant source roots state) (running : ready state = false) :
    count .root (events source state) + (step source state).roots.length = state.roots.length ∧
    count .reserve (events source state) + state.reserved.card = (step source state).reserved.card ∧
    count .slot (events source state) + writtenTally state = writtenTally (step source state) ∧
    count .finish (events source state) + state.complete.card = (step source state).complete.card ∧
    count .refused (events source state) = 0 := by
  have clear := valid.not_refused
  cases stack : state.frames with
  | nil =>
      cases pending : state.roots with
      | nil => simp [ready, clear, stack, pending] at running
      | cons a rest =>
          by_cases seen : a ∈ state.reserved
          · simp [events, step, clear, stack, pending, seen, count, Event.kind, writtenTally, Nat.add_comm]
          · have live := valid.root_live a (pending ▸ List.mem_cons_self)
            have allocated := live_allocated source.heap _ live
            obtain ⟨cell, found⟩ := (source.heap.allocated_iff a).mp allocated
            have tally := tally_pushFresh source state a seen
            simp only [events, step, clear, Bool.false_eq_true, ↓reduceIte, stack,
              pending, seen, found]
            simpa [count, Event.kind, pushFresh, reserve, writtenTally,
              Finset.card_insert_of_notMem seen, pending, Nat.add_comm] using
              (show 1 + rest.length = state.roots.length ∧
                1 + state.reserved.card = (insert a state.reserved).card ∧
                writtenTally state = writtenTally (pushFresh source a state) ∧
                state.complete.card = state.complete.card ∧ (0 : Nat) = 0 from
                ⟨by simp [pending, Nat.add_comm], by simp [seen, Nat.add_comm], tally.symm, rfl, rfl⟩)
  | cons frame rest =>
      have member : frame ∈ state.frames := stack ▸ List.mem_cons_self
      have seenSource := valid.frames_reserved frame member
      have unfinished := valid.frames_incomplete frame member
      cases remaining : frame.remaining with
      | nil =>
          simp [events, step, clear, stack, remaining, count, Event.kind, writtenTally,
            unfinished, Nat.add_comm]
      | cons child tail =>
          have slot : child ∈ source.slots frame.source := by
            have original := (valid.frames_remaining frame member).symm.trans remaining
            exact List.mem_of_mem_drop (original ▸ List.mem_cons_self)
          by_cases seen : child ∈ state.reserved
          · have tally := tally_writeSlot state frame.source child seenSource
            simpa [events, step, clear, stack, remaining, seen, count, Event.kind,
              writeSlot, writtenTally, Nat.add_comm] using tally.symm
          · have live := slot_live source roots (valid.reserved_live _ seenSource) slot
            have allocated := live_allocated source.heap _ live
            obtain ⟨cell, found⟩ := (source.heap.allocated_iff child).mp allocated
            have still : frame.source ∈ (pushFresh source child state).reserved :=
              Finset.mem_insert_of_mem seenSource
            have tally := (tally_writeSlot (pushFresh source child state) frame.source child still).trans
              (congrArg (· + 1) (tally_pushFresh source state child seen))
            simp only [events, step, clear, Bool.false_eq_true, ↓reduceIte, stack,
              remaining, seen, found]
            simpa [count, Event.kind, pushFresh, reserve, writeSlot, writtenTally,
              Finset.card_insert_of_notMem seen, Nat.add_comm] using tally.symm

def meter (source : Source A V) (kind : Kind) : Cursor.Charge (provider source) :=
  fun _ request => count kind (events source request)

/-- The existing cursor executes the original client/provider. Only its
declared charge coordinate is selected. No reference traversal is run here. -/
def prefixBill (source : Source A V) (kind : Kind) (fuel : Nat) (state : State A V) : Nat :=
  (Cursor.advance (provider source) client (meter source kind) fuel (packet source state)).1

@[simp] theorem prefix_zero (source : Source A V) (kind : Kind) (state : State A V) :
    prefixBill source kind 0 state = 0 := rfl

theorem prefix_ready (source : Source A V) (kind : Kind) (state : State A V)
    (clear : state.refused = false) (finished : ready state = true) (fuel : Nat) :
    prefixBill source kind (fuel + 1) state = 0 := by
  simp only [prefixBill, Cursor.advance, packet]
  rw [client_ready state clear finished]

theorem prefix_step (source : Source A V) (kind : Kind) (state : State A V)
    (clear : state.refused = false) (running : ready state = false) (fuel : Nat) :
    prefixBill source kind (fuel + 1) state =
      count kind (events source state) + prefixBill source kind fuel (step source state) := by
  simp only [prefixBill, Cursor.advance, packet]
  rw [client_running state clear running]
  rfl

theorem prefix_balance (source : Source A V) (roots : List A) (state : State A V)
    (valid : Invariant source roots state) (fuel : Nat) :
    prefixBill source .root fuel state + (stateOf source (run source fuel state).2).roots.length =
        state.roots.length ∧
    prefixBill source .reserve fuel state + state.reserved.card =
        (stateOf source (run source fuel state).2).reserved.card ∧
    prefixBill source .slot fuel state + writtenTally state =
        writtenTally (stateOf source (run source fuel state).2) ∧
    prefixBill source .finish fuel state + state.complete.card =
        (stateOf source (run source fuel state).2).complete.card ∧
    prefixBill source .refused fuel state = 0 := by
  induction fuel generalizing state with
  | zero => simp [run_zero, stateOf, packet]
  | succ fuel ih =>
      by_cases finished : ready state = true
      · rw [run_ready source state valid.not_refused finished]
        simp only [prefix_ready source _ state valid.not_refused finished, stateOf,
          zero_add, and_self]
      · have running := Bool.eq_false_iff.mpr finished
        obtain ⟨rootStep, reserveStep, slotStep, finishStep, faultStep⟩ :=
          step_balance source roots state valid running
        obtain ⟨rootPrefix, reservePrefix, slotPrefix, finishPrefix, faultPrefix⟩ :=
          ih (step source state) (step_invariant source roots state valid)
        rw [run_step source state valid.not_refused running]
        simp only [prefix_step source _ state valid.not_refused running]
        exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Each coordinate is determined by the independent initial ordered roots
and reachable source graph, rather than by a postulated complete invoice. -/
theorem completed_counts (source : Source A V) (roots : List A) (owner fuel spent : Nat)
    (validRoots : ∀ a ∈ roots, a ∈ source.heap.allocated) (final : State A V)
    (done : run source fuel (initial owner roots) = (spent, .done ⟨(), .ok final, ()⟩)) :
    prefixBill source .root fuel (initial owner roots) = roots.length ∧
    prefixBill source .reserve fuel (initial owner roots) = (footprint source.heap (rootsOf roots)).card ∧
    prefixBill source .slot fuel (initial owner roots) =
      (footprint source.heap (rootsOf roots)).sum (fun a => (source.slots a).length) ∧
    prefixBill source .finish fuel (initial owner roots) = (footprint source.heap (rootsOf roots)).card ∧
    prefixBill source .refused fuel (initial owner roots) = 0 := by
  have valid := initial_invariant source roots owner validRoots
  have sound := prefix_sound source roots (initial owner roots) valid fuel
  have balances := prefix_balance source roots (initial owner roots) valid fuel
  rw [done] at sound balances
  simp only [stateOf, published] at sound balances
  have finished : ready final = true := sound.2.2.2 final rfl
  have complete := ready_complete source roots final sound.1 finished
  have reached := ready_footprint source roots final sound.1 finished
  have lists := ready_lists final finished
  have tally : writtenTally final =
      (footprint source.heap (rootsOf roots)).sum (fun a => (source.slots a).length) := by
    unfold writtenTally
    rw [reached]
    apply Finset.sum_congr rfl
    intro a member
    apply sound.1.complete_count
    rw [complete, reached]
    exact member
  simpa only [initial, Finset.card_empty, Finset.sum_empty, writtenTally,
    List.length_nil, lists.1, Nat.add_zero, complete, reached] using
      (show prefixBill source .root fuel (initial owner roots) + final.roots.length = roots.length ∧
        prefixBill source .reserve fuel (initial owner roots) + 0 = final.reserved.card ∧
        prefixBill source .slot fuel (initial owner roots) + 0 =
          (footprint source.heap (rootsOf roots)).sum (fun a => (source.slots a).length) ∧
        prefixBill source .finish fuel (initial owner roots) + 0 = final.complete.card ∧
        prefixBill source .refused fuel (initial owner roots) = 0 from
      ⟨balances.1, balances.2.1, balances.2.2.1.trans tally,
        balances.2.2.2.1, balances.2.2.2.2⟩)

def weighted (prices : Kind → Nat) (word : List (Event A)) : Nat :=
  (word.map (fun event => prices event.kind)).sum

omit [LinearOrder A] in
theorem weighted_counts (prices : Kind → Nat) (word : List (Event A)) :
    weighted prices word = prices .root * count .root word +
      prices .reserve * count .reserve word + prices .slot * count .slot word +
      prices .finish * count .finish word + prices .refused * count .refused word := by
  induction word with
  | nil => simp [weighted, count]
  | cons event rest ih =>
      cases event <;> simp [weighted, count, Event.kind, Nat.mul_add] at ih ⊢ <;> omega

def price (source : Source A V) (prices : Kind → Nat) : Cursor.Charge (provider source) :=
  fun _ request => weighted prices (events source request)

/-- The full selected price is projected over all actual phase coordinates.
Linearity is inherited from the existing arbitrary-client cursor theorems. -/
theorem price_projection (source : Source A V) (prices : Kind → Nat) (fuel : Nat)
    (state : State A V) :
    (Cursor.advance (provider source) client (price source prices) fuel (packet source state)).1 =
      prices .root * prefixBill source .root fuel state +
      prices .reserve * prefixBill source .reserve fuel state +
      prices .slot * prefixBill source .slot fuel state +
      prices .finish * prefixBill source .finish fuel state +
      prices .refused * prefixBill source .refused fuel state := by
  let linear : Cursor.Charge (provider source) := fun {base index} world request =>
    prices .root * meter source .root (base := base) (index := index) world request +
    prices .reserve * meter source .reserve (base := base) (index := index) world request +
    prices .slot * meter source .slot (base := base) (index := index) world request +
    prices .finish * meter source .finish (base := base) (index := index) world request +
    prices .refused * meter source .refused (base := base) (index := index) world request
  have exactPrice : @price A V _ source prices = @linear := by
    funext base index world request
    exact weighted_counts prices (events source request)
  change (Cursor.advance (provider source) client (@price A V _ source prices) fuel (packet source state)).1 = _
  rw [exactPrice]
  dsimp only [linear]
  simp only [Cursor.advance_charge_add, Cursor.advance_charge_scale, prefixBill]

open _root_.CategoryTheory Mettapedia.Effects

/-- The graph is the actual existing transition on retained states. Its
arrows carry no assumed account equality or correctness of a destination. -/
abbrev stepGraph (source : Source A V) : Quiver (State A V) where
  Hom before after := PLift (before.refused = false ∧ ready before = false ∧ step source before = after)

def actionAccount (source : Source A V) :
    letI := stepGraph source
    RunAccount (Paths (State A V)) (FreeMonoid (Event A)) := by
  letI := stepGraph source
  exact Mettapedia.GSLT.Contracts.Accounts.pathAccount
    (fun {before} {_after} _ => FreeMonoid.ofList (events source before))

def priceHom (prices : Kind → Nat) : FreeMonoid (Event A) →* Multiplicative Nat :=
  FreeMonoid.lift fun event => Multiplicative.ofAdd (prices event.kind)

omit [LinearOrder A] in
theorem priceHom_word (prices : Kind → Nat) (word : List (Event A)) :
    Multiplicative.toAdd (priceHom prices (FreeMonoid.ofList word)) = weighted prices word := by
  induction word with
  | nil => simp [priceHom, weighted]
  | cons event rest ih =>
      simp only [FreeMonoid.ofList_cons, map_mul]
      simpa [priceHom, weighted] using congrArg (prices event.kind + ·) ih

def priceAccount (source : Source A V) (prices : Kind → Nat) :
    letI := stepGraph source
    RunAccount (Paths (State A V)) (Multiplicative Nat) :=
  letI := stepGraph source
  (actionAccount source).map (priceHom prices)

def priced (source : Source A V) (prices : Kind → Nat) (fuel : Nat) (state : State A V) :=
  Cursor.advance (provider source) client (price source prices) fuel (packet source state)

def resumePriced (source : Source A V) (prices : Kind → Nat) (fuel : Nat)
    (previous : Nat × Cursor.Outcome (provider source) client ()) :=
  Cursor.resume (provider source) client (price source prices) fuel previous

theorem priced_zero (source : Source A V) (prices : Kind → Nat) (state : State A V) :
    priced source prices 0 state = (0, .paused (packet source state)) := rfl

theorem priced_split (source : Source A V) (prices : Kind → Nat) (first second : Nat)
    (state : State A V) :
    priced source prices (first + second) state =
      resumePriced source prices second (priced source prices first state) := Cursor.advance_add ..

theorem resumePriced_zero (source : Source A V) (prices : Kind → Nat)
    (previous : Nat × Cursor.Outcome (provider source) client ()) :
    resumePriced source prices 0 previous = previous := Cursor.resume_zero ..

theorem resumePriced_add (source : Source A V) (prices : Kind → Nat) (first second : Nat)
    (previous : Nat × Cursor.Outcome (provider source) client ()) :
    resumePriced source prices (first + second) previous =
      resumePriced source prices second (resumePriced source prices first previous) := Cursor.resume_add ..

/-- This word is the existing observer of actual reply-selected requests.
It is not an invoice supplied after a completed traversal. -/
def chargeWord (source : Source A V) (prices : Kind → Nat) (fuel : Nat) (state : State A V) : List Nat :=
  Cursor.Lease.charges client (provider source) (price source prices) fuel (packet source state)

theorem chargeWord_sum (source : Source A V) (prices : Kind → Nat) (fuel : Nat) (state : State A V) :
    (chargeWord source prices fuel state).sum = (priced source prices fuel state).1 :=
  Cursor.Lease.charges_sum ..

theorem chargeWord_split (source : Source A V) (prices : Kind → Nat) (first second : Nat)
    (state : State A V) :
    chargeWord source prices (first + second) state = chargeWord source prices first state ++
      Cursor.Lease.suffixCharges client (provider source) (price source prices) second
        (priced source prices first state).2 := Cursor.Lease.charges_split ..

theorem resume_priced_actual_word (source : Source A V) (prices : Kind → Nat) (fuel : Nat)
    (previous : Nat × Cursor.Outcome (provider source) client ()) :
    (resumePriced source prices fuel previous).1 = previous.1 +
      (Cursor.Lease.suffixCharges client (provider source) (price source prices) fuel previous.2).sum :=
  Cursor.Lease.resume_paid ..

theorem priced_outcome (source : Source A V) (prices : Kind → Nat) (fuel : Nat)
    (state : State A V) :
    (priced source prices fuel state).2 = (run source fuel state).2 := by
  have identity (outcome : Cursor.Outcome (provider source) client ()) :
      (Cursor.Hom.id (provider source)).outcome client outcome = outcome := by
    cases outcome <;> rfl
  have transported := Cursor.Hom.advance client (Cursor.Hom.id (provider source))
    (price source prices) (charge source) fuel (packet source state)
  rw [identity] at transported
  exact transported

theorem priced_ready (source : Source A V) (prices : Kind → Nat) (state : State A V)
    (clear : state.refused = false) (finished : ready state = true) (fuel : Nat) :
    priced source prices (fuel + 1) state = (0, .done ⟨(), .ok state, ()⟩) := by
  simp only [priced, Cursor.advance, packet]
  rw [client_ready state clear finished]

theorem priced_step (source : Source A V) (prices : Kind → Nat) (state : State A V)
    (clear : state.refused = false) (running : ready state = false) (fuel : Nat) :
    priced source prices (fuel + 1) state =
      (weighted prices (events source state) + (priced source prices fuel (step source state)).1,
        (priced source prices fuel (step source state)).2) := by
  simp only [priced, Cursor.advance, packet]
  rw [client_running state clear running]
  rfl

/-- A typed path and its price account are derived from each actual cursor
prefix. This is an execution witness, not another traversal evaluator. -/
theorem actual_path_account (source : Source A V) (prices : Kind → Nat) (roots : List A)
    (state : State A V) (valid : Invariant source roots state) (fuel : Nat) :
    letI := stepGraph source
    ∃ path : Quiver.Path state (stateOf source (run source fuel state).2),
      (priceAccount source prices).of path = Multiplicative.ofAdd (priced source prices fuel state).1 := by
  let _ := stepGraph source
  induction fuel generalizing state with
  | zero => exact ⟨.nil, rfl⟩
  | succ fuel ih =>
      by_cases finished : ready state = true
      · rw [run_ready source state valid.not_refused finished,
          priced_ready source prices state valid.not_refused finished]
        exact ⟨.nil, rfl⟩
      · have running := Bool.eq_false_iff.mpr finished
        obtain ⟨path, accounted⟩ := ih (step source state) (step_invariant source roots state valid)
        let edge : state ⟶ step source state := ⟨valid.not_refused, running, rfl⟩
        have head : (priceAccount source prices).of edge.toPath =
            Multiplicative.ofAdd (weighted prices (events source state)) := by
          apply Multiplicative.toAdd.injective
          exact priceHom_word prices (events source state)
        rw [run_step source state valid.not_refused running,
          priced_step source prices state valid.not_refused running]
        refine ⟨edge.toPath.comp path, ?_⟩
        change (priceAccount source prices).of (edge.toPath ≫ path) = _
        exact ((priceAccount source prices).of_comp edge.toPath path).trans
          ((congrArg₂ (fun x y : Multiplicative Nat => x * y) head accounted).trans rfl)

noncomputable def referencePrice (source : Source A V) (roots : List A) (prices : Kind → Nat) : Nat :=
  prices .root * roots.length +
    (prices .reserve + prices .finish) * (footprint source.heap (rootsOf roots)).card +
    prices .slot * (footprint source.heap (rootsOf roots)).sum (fun a => (source.slots a).length)

theorem completed_price (source : Source A V) (roots : List A) (owner fuel spent : Nat)
    (prices : Kind → Nat) (validRoots : ∀ a ∈ roots, a ∈ source.heap.allocated) (final : State A V)
    (done : run source fuel (initial owner roots) = (spent, .done ⟨(), .ok final, ()⟩)) :
    (priced source prices fuel (initial owner roots)).1 = referencePrice source roots prices := by
  obtain ⟨rootCount, reserveCount, slotCount, finishCount, refusedCount⟩ :=
    completed_counts source roots owner fuel spent validRoots final done
  unfold priced
  rw [price_projection, rootCount, reserveCount, slotCount, finishCount, refusedCount]
  simp only [referencePrice, Nat.mul_zero, Nat.add_zero, Nat.add_mul]
  omega

/-- Finite completion and the full declared price are obtained together
from the existing actual cursor, without a correct destination or invoice premise. -/
theorem initial_completes_priced (source : Source A V) (roots : List A) (owner : Nat)
    (prices : Kind → Nat) (validRoots : ∀ a ∈ roots, a ∈ source.heap.allocated) :
    ∃ final, priced source prices (referenceWork source roots + 1) (initial owner roots) =
        (referencePrice source roots prices, .done ⟨(), .ok final, ()⟩) ∧
      Invariant source roots final ∧ ready final = true := by
  obtain ⟨final, done, valid, finished⟩ := initial_completes_exact source roots owner validRoots
  have cost := completed_price source roots owner (referenceWork source roots + 1)
    (referenceWork source roots) prices validRoots final done
  have outcome := priced_outcome source prices (referenceWork source roots + 1) (initial owner roots)
  rw [done] at outcome
  exact ⟨final, Prod.ext cost outcome, valid, finished⟩

/-- Cancellation retains the actually paid invoice and private buffers.
No disposal work or finalizer price is inferred from this operation. -/
theorem cancel_priced_prefix (source : Source A V) (prices : Kind → Nat) (fuel : Nat)
    (state : State A V) :
    (cancel source (priced source prices fuel state)).1 = (priced source prices fuel state).1 ∧
      published source (cancel source (priced source prices fuel state)).2 = none ∧
      (stateOf source (cancel source (priced source prices fuel state)).2).written =
        (stateOf source (priced source prices fuel state).2).written :=
  ⟨cancel_paid .., cancel_unpublished .., (cancel_keeps_private_writes ..).1⟩

theorem cancelled_priced_resume_is_inert (source : Source A V) (prices : Kind → Nat)
    (fuel : Nat) (previous : Nat × Cursor.Outcome (provider source) client ()) :
    resumePriced source prices fuel (cancel source previous) = cancel source previous := rfl

namespace Controls

open NestedProfiles.Controls (cycle diamond selfCycle)

def cyclicSource : Source (Fin 5) Nat := cycle.1
def sharedSource : Source (Fin 5) Nat := (diamond true).1
def duplicateSource : Source (Fin 5) Nat := (diamond false).1
def selfSource : Source (Fin 5) Nat := selfCycle.1

def prices : Kind → Nat
  | .root => 2
  | .reserve => 3
  | .slot => 5
  | .finish => 7
  | .refused => 11

theorem actual_fresh_and_backedge_actions_keep_source_coordinates :
    events cyclicSource (initial 77 [0, 0]) = [.root 0, .reserve 0] ∧
      events cyclicSource (step cyclicSource (initial 77 [0, 0])) =
        [.reserve 1, .slot 0 0 1] ∧
      events cyclicSource (step cyclicSource (step cyclicSource (initial 77 [0, 0]))) =
        [.slot 1 0 0] := by decide

theorem cyclic_duplicate_root_and_slot_counts :
    prefixBill cyclicSource .root 8 (initial 77 [0, 0]) = 2 ∧
      prefixBill cyclicSource .reserve 8 (initial 77 [0, 0]) = 2 ∧
      prefixBill cyclicSource .slot 8 (initial 77 [0, 0]) = 3 ∧
      prefixBill cyclicSource .finish 8 (initial 77 [0, 0]) = 2 ∧
      prefixBill cyclicSource .refused 8 (initial 77 [0, 0]) = 0 ∧
      (priced cyclicSource prices 8 (initial 77 [0, 0])).1 = 39 := by decide

theorem self_cycle_and_shared_descendant_keep_distinct_invoices :
    (priced selfSource prices 5 (initial 77 [0])).1 = 22 ∧
      (priced sharedSource prices 10 (initial 77 [0])).1 = 62 ∧
      (priced duplicateSource prices 11 (initial 77 [0])).1 = 72 ∧
      prefixBill sharedSource .reserve 10 (initial 77 [0]) = 4 ∧
      prefixBill duplicateSource .reserve 11 (initial 77 [0]) = 5 := by decide

theorem unit_poll_count_does_not_equal_complete_selected_price :
    (run cyclicSource 8 (initial 77 [0, 0])).1 = 7 ∧
      (priced cyclicSource prices 8 (initial 77 [0, 0])).1 = 39 := by decide

def omitReservations : Kind → Nat
  | .reserve => 0
  | kind => prices kind

theorem dropping_reservation_lines_changes_the_actual_invoice :
    (priced cyclicSource omitReservations 8 (initial 77 [0, 0])).1 = 33 ∧
      (priced cyclicSource prices 8 (initial 77 [0, 0])).1 ≠
        (priced cyclicSource omitReservations 8 (initial 77 [0, 0])).1 := by decide

theorem readiness_before_client_return_does_not_publish :
    ready (stateOf cyclicSource (priced cyclicSource prices 7 (initial 77 [0, 0])).2) = true ∧
      published cyclicSource (priced cyclicSource prices 7 (initial 77 [0, 0])).2 = none ∧
      (published cyclicSource (priced cyclicSource prices 8 (initial 77 [0, 0])).2).map
        State.originals = some [0, 0] := by decide

theorem cancelling_a_real_backedge_prefix_retains_paid_private_writes :
    (cancel cyclicSource (priced cyclicSource prices 3 (initial 77 [0, 0]))).1 = 18 ∧
      published cyclicSource (cancel cyclicSource (priced cyclicSource prices 3 (initial 77 [0, 0]))).2 = none ∧
      (stateOf cyclicSource (cancel cyclicSource (priced cyclicSource prices 3 (initial 77 [0, 0]))).2).written
        0 0 = some (77, 1) ∧
      (stateOf cyclicSource (cancel cyclicSource (priced cyclicSource prices 3 (initial 77 [0, 0]))).2).written
        1 0 = some (77, 0) ∧
      (stateOf cyclicSource (cancel cyclicSource (priced cyclicSource prices 3 (initial 77 [0, 0]))).2).written
        0 1 = none := by decide

def emptyChecked : DescriptorAdmission.Checked (Fin 5) Nat := ⟨[], [], by decide⟩
def emptySource : Source (Fin 5) Nat := DescriptorAdmission.SourceAdapter.source emptyChecked

theorem refused_source_lookup_is_paid_and_unpublished :
    events emptySource (initial 77 [0]) = [.refused 0] ∧
      (priced emptySource prices 2 (initial 77 [0])).1 = 11 ∧
      (stateOf emptySource (priced emptySource prices 2 (initial 77 [0])).2).refused = true ∧
      published emptySource (priced emptySource prices 2 (initial 77 [0])).2 = none := by decide

def widePrice (width : Nat) : Kind → Nat
  | .reserve => width
  | _ => 1

/-- Two model events do not bound their declared primitive prices. A native
bound needs a separately justified price for each admitted service. -/
theorem bounded_event_count_allows_unbounded_declared_price (width : Nat) :
    (events selfSource (initial 77 [0])).length = 2 ∧
      (priced selfSource (widePrice width) 1 (initial 77 [0])).1 = width + 1 := by
  constructor
  · decide
  · rw [priced_step selfSource (widePrice width) (initial 77 [0]) (by rfl) (by decide) 0]
    change weighted (widePrice width) [.root 0, .reserve 0] + 0 = width + 1
    simp [weighted, widePrice, Event.kind, Nat.add_comm]

/-- An existing independently implemented array-copy provider has the same
one-pull semantic observation, yet visits an arbitrarily wide copied tail. -/
theorem one_fold_pull_can_hide_input_sized_array_copy (width : Nat) :
    (Cursor.advance (Cursor.SequenceCost.copying Nat) (Cursor.Fold.client Nat.add)
      (Cursor.SequenceCost.copyingVisits Nat) 1
      (Cursor.Fold.start _ Nat.add (List.replicate (width + 1) 7).toArray 0)).1 = width + 1 ∧
    (Cursor.advance (Cursor.Sequence.tails Nat) (Cursor.Fold.client Nat.add)
      (Cursor.Sequence.requested Nat) 1
      (Cursor.Fold.start _ Nat.add (List.replicate (width + 1) 7) 0)).1 = 1 := by
  constructor
  · have actual := Cursor.SequenceCost.copying_prefix_visits Nat.add
      (List.replicate (width + 1) 7).toArray 0 1 (by simp)
    simpa [Cursor.SequenceCost.prefixVisits] using actual
  · exact Cursor.SequenceCost.fold_prefix_requested Nat.add
      (List.replicate (width + 1) 7) 0 1 (by simp)

end Controls

end Mettapedia.Machines.ResourceOwnership.TraceWork.RetainedCopy.Invoice
