import Mettapedia.GSLT.Parsing.PlainBnfGraphNameTrie
import Mathlib.Data.List.Sort

/-!
# Exact finite-trie and deterministic-automaton product traversal

The traversal advances a deterministic state once per stored edge, not once
per complete name. It returns precisely the independent flat-entry filter.
Terminal payloads are not sets: repeated values and empty names survive.
This reuses the generic scalar trie used by the authored BNF name index.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.TrieAutomatonProduct

open PlainBnfGraphNameTrie (Trie)

universe v w

variable {Scalar : Type} {Payload : Type v} {State : Type w}

/-- A total deterministic recognizer. Failure states may be ordinary states. -/
structure Automaton (Scalar : Type) (State : Type w) where
  step : State → Scalar → State
  accept : State → Bool

def run (machine : Automaton Scalar State) : State → List Scalar → State
  | state, [] => state
  | state, scalar :: rest => run machine (machine.step state scalar) rest

theorem run_append (machine : Automaton Scalar State) (state : State)
    (first second : List Scalar) :
    run machine state (first ++ second) = run machine (run machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons scalar rest ih => exact ih _

mutual
  def entries : Trie Payload Scalar → List (List Scalar × Payload)
    | .empty => []
    | .node value edges =>
        (match value with | none => [] | some payload => [([], payload)]) ++ entriesEdges edges

  def entriesEdges : List (Scalar × Trie Payload Scalar) → List (List Scalar × Payload)
    | [] => []
    | (scalar, child) :: rest =>
        (entries child).map (fun entry => (scalar :: entry.1, entry.2)) ++ entriesEdges rest
end

mutual
  def query (machine : Automaton Scalar State) (state : State) :
      Trie Payload Scalar → List (List Scalar × Payload)
    | .empty => []
    | .node value edges =>
        (match value with
          | none => []
          | some payload => if machine.accept state then [([], payload)] else []) ++
        queryEdges machine state edges

  def queryEdges (machine : Automaton Scalar State) (state : State) :
      List (Scalar × Trie Payload Scalar) → List (List Scalar × Payload)
    | [] => []
    | (scalar, child) :: rest =>
        (query machine (machine.step state scalar) child).map
          (fun entry => (scalar :: entry.1, entry.2)) ++ queryEdges machine state rest
end

private theorem filter_prepend (machine : Automaton Scalar State) (state : State)
    (scalar : Scalar) (values : List (List Scalar × Payload)) :
    ((values.filter (fun entry => machine.accept (run machine (machine.step state scalar) entry.1))).map
      (fun entry => (scalar :: entry.1, entry.2))) =
      ((values.map (fun entry => (scalar :: entry.1, entry.2))).filter
        (fun entry => machine.accept (run machine state entry.1))) := by
  induction values with
  | nil => rfl
  | cons entry rest ih =>
      cases accepted : machine.accept (run machine (machine.step state scalar) entry.1) <;>
        simp [run, accepted, ih]

mutual
  /-- Exact ordered-list equality, not merely preservation of membership. -/
  theorem query_eq_filter (machine : Automaton Scalar State) (state : State)
      (trie : Trie Payload Scalar) :
      query machine state trie =
        (entries trie).filter (fun entry => machine.accept (run machine state entry.1)) := by
    cases trie with
    | empty => rfl
    | node value edges =>
        cases value with
        | none => simpa [query, entries] using queryEdges_eq_filter machine state edges
        | some payload =>
            cases accepted : machine.accept state <;>
              simp [query, entries, accepted, run, queryEdges_eq_filter machine state edges]

  theorem queryEdges_eq_filter (machine : Automaton Scalar State) (state : State)
      (edges : List (Scalar × Trie Payload Scalar)) :
      queryEdges machine state edges =
        (entriesEdges edges).filter (fun entry => machine.accept (run machine state entry.1)) := by
    cases edges with
    | nil => rfl
    | cons edge rest =>
        rcases edge with ⟨scalar, child⟩
        simp only [queryEdges, entriesEdges, List.filter_append,
          query_eq_filter machine (machine.step state scalar) child,
          queryEdges_eq_filter machine state rest]
        rw [filter_prepend]
end

/-- The two directions exclude both omitted names and invented names. -/
theorem query_mem_iff (machine : Automaton Scalar State) (state : State)
    (trie : Trie Payload Scalar) (word : List Scalar) (payload : Payload) :
    (word, payload) ∈ query machine state trie ↔
      (word, payload) ∈ entries trie ∧ machine.accept (run machine state word) = true := by
  rw [query_eq_filter]
  exact List.mem_filter

/-- Binding the trie entries to a finite authorized snapshot yields an exact
query over that snapshot. The snapshot need not be a set of unique payloads. -/
theorem snapshot_query_exact (machine : Automaton Scalar State) (state : State)
    (trie : Trie Payload Scalar) (snapshot : List (List Scalar × Payload))
    (represented : entries trie = snapshot) :
    query machine state trie =
      snapshot.filter (fun entry => machine.accept (run machine state entry.1)) := by
  rw [query_eq_filter, represented]

/-- Native stores may choose a different edge order. A finite-snapshot
permutation is enough for exact occurrence multiplicity before sorting. -/
theorem snapshot_query_perm (machine : Automaton Scalar State) (state : State)
    (trie : Trie Payload Scalar) (snapshot : List (List Scalar × Payload))
    (represented : (entries trie).Perm snapshot) :
    (query machine state trie).Perm
      (snapshot.filter (fun entry => machine.accept (run machine state entry.1))) := by
  rw [query_eq_filter]
  exact represented.filter _

/-- Sorting returned stable symbol IDs removes implementation edge order,
without deduplicating or changing the authorized finite snapshot. -/
theorem stable_ids_exact (machine : Automaton Scalar State) (state : State)
    (trie : Trie Nat Scalar) (snapshot : List (List Scalar × Nat))
    (represented : (entries trie).Perm snapshot) :
    ((query machine state trie).map Prod.snd).mergeSort (· ≤ ·) =
      ((snapshot.filter (fun entry => machine.accept (run machine state entry.1))).map Prod.snd).mergeSort
        (· ≤ ·) := by
  have permutation := (snapshot_query_perm machine state trie snapshot represented).map Prod.snd
  have sortedPermutation := (List.mergeSort_perm _ (· ≤ ·)).trans
    (permutation.trans (List.mergeSort_perm _ (· ≤ ·)).symm)
  exact sortedPermutation.eq_of_pairwise' (List.pairwise_mergeSort' (· ≤ ·) _)
    (List.pairwise_mergeSort' (· ≤ ·) _)

namespace Controls

private def containsA : Automaton Nat Bool :=
  ⟨fun seen scalar => seen || scalar == 97, id⟩

private def names : Trie (List Nat) Nat :=
  .node (some [0]) [(97, .node (some [1, 2]) [(955, .node (some [3]) [])]),
    (98, .node (some [4]) [])]

theorem prefix_shared_names_preserve_terminal_occurrences :
    query containsA false names = [([97], [1, 2]), ([97, 955], [3])] := by decide

theorem accepting_initial_state_retains_empty_name :
    query containsA true names =
      [([], [0]), ([97], [1, 2]), ([97, 955], [3]), ([98], [4])] := by decide

theorem absent_name_cannot_be_invented :
    ([955], [3]) ∉ query containsA false names := by decide

end Controls

end Mettapedia.GSLT.Parsing.TrieAutomatonProduct
