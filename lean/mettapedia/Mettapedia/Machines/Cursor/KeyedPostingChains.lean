import Mettapedia.Machines.Cursor.TermPathPosting
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Posting chains keyed by a projection

A store keeps rows in arrival order and threads each row onto the chain of its
key: a chain records its first and last row, and every row its successor.
Reading a chain from its first row yields exactly the rows with that key, in
arrival order, and appending a row extends one chain by one link.

A lookup that answers by exact equality reads one chain: equal payloads have
equal keys, so no answer is lost or reordered. Declarations keyed by their
subject's head symbol and the term-path postings of `TermPathPosting` are
instances of the same store.

The model fixes the row order and the links; hash placement of the key map
and native memory ownership are the adapter's obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.KeyedPostingChains

variable {κ : Type*} [DecidableEq κ]

/-- Each row of a chain points at its successor; the last row points nowhere. -/
def Linked (next : Nat → Option Nat) : List Nat → Prop
  | [] => True
  | [row] => next row = none
  | row :: following :: rest => next row = some following ∧ Linked next (following :: rest)

/-- Follow the successor links from a row, at most `fuel` rows. -/
def walk (next : Nat → Option Nat) : Option Nat → Nat → List Nat
  | none, _ => []
  | some _, 0 => []
  | some row, fuel + 1 => row :: walk next (next row) fuel

theorem walk_linked (next : Nat → Option Nat) :
    ∀ chain : List Nat, Linked next chain → walk next chain.head? chain.length = chain
  | [], _ => rfl
  | [row], linked => by
    simp only [Linked] at linked
    simp [walk, linked]
  | row :: following :: rest, linked => by
    obtain ⟨link, tail⟩ := linked
    have := walk_linked next (following :: rest) tail
    simp only [List.head?_cons, List.length_cons] at this ⊢
    simp [walk, link, this]

/-- The rows whose key is `key`, in arrival order: the specification of a chain. -/
def rowsOf (keys : List κ) (key : κ) : List Nat :=
  (List.range keys.length).filter fun row => keys[row]? = some key

theorem rowsOf_append (keys : List κ) (added key : κ) :
    rowsOf (keys ++ [added]) key =
      rowsOf keys key ++ if added = key then [keys.length] else [] := by
  unfold rowsOf
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro row member
    rw [List.mem_range] at member
    simp [List.getElem?_append_left member]
  · by_cases same : added = key <;> simp [same]

theorem rowsOf_lt (keys : List κ) (key : κ) (row : Nat) (member : row ∈ rowsOf keys key) :
    row < keys.length := by
  simpa [rowsOf] using (List.mem_filter.mp member).1

theorem rowsOf_key (keys : List κ) (key : κ) (row : Nat) (member : row ∈ rowsOf keys key) :
    keys[row]? = some key := by
  simpa using (List.mem_filter.mp member).2

/-- A chain store: the key of each arrived row, the successor links, and the
first and last row of each chain. -/
structure Store (κ : Type*) where
  keys : List κ
  next : Nat → Option Nat
  first : κ → Option Nat
  last : κ → Option Nat

/-- The store's links describe every key's rows. -/
def Describes (store : Store κ) : Prop :=
  ∀ key, Linked store.next (rowsOf store.keys key) ∧
    store.first key = (rowsOf store.keys key).head? ∧
    store.last key = (rowsOf store.keys key).getLast?

/-- An empty store. -/
def empty : Store κ where
  keys := []
  next := fun _ => none
  first := fun _ => none
  last := fun _ => none

theorem empty_describes : Describes (empty : Store κ) := by
  intro key
  simp [empty, rowsOf, Linked]

/-- A row arrives with `key`: it becomes the last row of that chain. -/
def append (store : Store κ) (key : κ) : Store κ where
  keys := store.keys ++ [key]
  next := fun row =>
    if store.last key = some row then some store.keys.length
    else if row = store.keys.length then none
    else store.next row
  first := fun other => if other = key then (store.first key).or (some store.keys.length)
    else store.first other
  last := fun other => if other = key then some store.keys.length else store.last other

/-- Links among rows that are neither the old last row of the appended key nor
the new row are unchanged. -/
theorem linked_append_other (store : Store κ) (key : κ) (chain : List Nat)
    (linked : Linked store.next chain)
    (notLast : ∀ row ∈ chain, store.last key ≠ some row)
    (old : ∀ row ∈ chain, row < store.keys.length) :
    Linked (append store key).next chain := by
  induction chain with
  | nil => trivial
  | cons row rest inductionHypothesis =>
    cases rest with
    | nil =>
      have rowOld := old row (by simp)
      simp only [Linked] at linked ⊢
      simp [append, notLast row (by simp), Nat.ne_of_lt rowOld, linked]
    | cons following rest =>
      obtain ⟨link, tail⟩ := linked
      have rowOld := old row (by simp)
      refine ⟨?_, inductionHypothesis tail
        (fun r member => notLast r (List.mem_cons_of_mem _ member))
        (fun r member => old r (List.mem_cons_of_mem _ member))⟩
      simp [append, notLast row (by simp), Nat.ne_of_lt rowOld, link]

/-- Extending a linked chain by the new row. -/
theorem linked_append_self (store : Store κ) (key : κ) (chain : List Nat)
    (linked : Linked store.next chain)
    (lastRow : store.last key = chain.getLast?)
    (old : ∀ row ∈ chain, row < store.keys.length)
    (distinct : chain.Nodup) :
    Linked (append store key).next (chain ++ [store.keys.length]) := by
  induction chain generalizing store with
  | nil => simp [Linked, append, lastRow]
  | cons row rest inductionHypothesis =>
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton] at lastRow
      have rowOld := old row (by simp)
      simp [Linked, append, lastRow, Nat.ne_of_lt rowOld]
    | cons following rest =>
      obtain ⟨link, tail⟩ := linked
      have rowOld := old row (by simp)
      have rowNotLast : store.last key ≠ some row := by
        rw [lastRow, List.getLast?_cons_cons]
        intro equal
        exact (List.nodup_cons.mp distinct).1 (List.mem_of_getLast? equal)
      refine ⟨?_, ?_⟩
      · simp [append, rowNotLast, Nat.ne_of_lt rowOld, link]
      · have := inductionHypothesis store tail
          (by simpa using lastRow)
          (fun r member => old r (List.mem_cons_of_mem _ member))
          (List.nodup_cons.mp distinct).2
        simpa using this

theorem rowsOf_nodup (keys : List κ) (key : κ) : (rowsOf keys key).Nodup :=
  (List.nodup_range).filter _

/-- Appending a row keeps every chain described. -/
theorem append_describes (store : Store κ) (key : κ) (describes : Describes store) :
    Describes (append store key) := by
  intro other
  obtain ⟨linked, firstRow, lastRow⟩ := describes other
  have old : ∀ row ∈ rowsOf store.keys other, row < store.keys.length :=
    fun row member => rowsOf_lt store.keys other row member
  by_cases same : other = key
  · subst same
    have rows : rowsOf (append store other).keys other =
        rowsOf store.keys other ++ [store.keys.length] := by
      simp [append, rowsOf_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [rows]
      exact linked_append_self store other _ linked lastRow old (rowsOf_nodup _ _)
    · rw [rows]
      cases chain : rowsOf store.keys other with
      | nil => simp [append, firstRow, chain]
      | cons row rest => simp [append, firstRow, chain]
    · rw [rows]
      simp [append]
  · have rows : rowsOf (append store key).keys other = rowsOf store.keys other := by
      simp [append, rowsOf_append, Ne.symm same]
    refine ⟨?_, ?_, ?_⟩
    · rw [rows]
      apply linked_append_other store key _ linked _ old
      intro row member equal
      obtain ⟨_, _, keyLast⟩ := describes key
      rw [keyLast] at equal
      have keyMember := List.mem_of_getLast? equal
      have keyIs := rowsOf_key store.keys key row keyMember
      have otherIs := rowsOf_key store.keys other row member
      rw [keyIs] at otherIs
      exact same (Option.some.inj otherIs).symm
    · rw [rows]
      simp [append, same, firstRow]
    · rw [rows]
      simp [append, same, lastRow]

/-- Reading a chain from its first row returns exactly the key's rows. -/
theorem read_chain (store : Store κ) (describes : Describes store) (key : κ) :
    walk store.next (store.first key) (rowsOf store.keys key).length =
      rowsOf store.keys key := by
  obtain ⟨linked, firstRow, _⟩ := describes key
  rw [firstRow]
  exact walk_linked store.next _ linked

/-- The store built by appending each key in arrival order. -/
def build (keys : List κ) : Store κ := keys.foldl append empty

theorem foldl_append_keys (keys : List κ) :
    ∀ store : Store κ, (keys.foldl append store).keys = store.keys ++ keys := by
  induction keys with
  | nil => intro store; simp
  | cons key rest inductionHypothesis =>
    intro store
    simp [inductionHypothesis, append]

theorem foldl_append_describes (keys : List κ) :
    ∀ store : Store κ, Describes store → Describes (keys.foldl append store) := by
  induction keys with
  | nil => intro store describes; simpa using describes
  | cons key rest inductionHypothesis =>
    intro store describes
    exact inductionHypothesis _ (append_describes store key describes)

theorem build_keys (keys : List κ) : (build keys).keys = keys := by
  simp [build, foldl_append_keys, empty]

theorem build_describes (keys : List κ) : Describes (build keys) :=
  foldl_append_describes keys empty empty_describes

/-! ## Lookups by exact equality -/

/-- The rows whose payload equals the query: what the lookup must answer. -/
def answers {α : Type*} [DecidableEq α] (payloads : List α) (query : α) : List Nat :=
  (List.range payloads.length).filter fun row => payloads[row]? = some query

/-- Exact-equality lookups read one chain: equal payloads share a key, so the
chain of the query's key holds every answer, in arrival order. -/
theorem lookup_reads_one_chain {α : Type*} [DecidableEq α] (key : α → κ)
    (payloads : List α) (query : α) :
    (rowsOf (payloads.map key) (key query)).filter
        (fun row => payloads[row]? = some query) =
      answers payloads query := by
  unfold rowsOf answers
  rw [List.length_map, List.filter_filter]
  apply List.filter_congr
  intro row member
  rw [List.mem_range] at member
  by_cases equal : payloads[row]? = some query
  · simp [equal, List.getElem?_map]
  · simp [equal]

/-- The space's own rows precede imported ones: two passes over one chain
partition it by position and keep arrival order within each part. -/
theorem own_then_imported (chain : List Nat) (position : Nat → Nat) (imported : Nat) :
    List.Perm ((chain.filter fun row => imported ≤ position row) ++
        chain.filter (fun row => position row < imported)) chain := by
  have split := List.filter_append_perm (fun row => decide (imported ≤ position row)) chain
  have same : (chain.filter fun row => !decide (imported ≤ position row)) =
      chain.filter fun row => position row < imported := by
    apply List.filter_congr
    intro row _
    rcases Nat.lt_or_ge (position row) imported with order | order <;>
      simp [order, Nat.not_le.mpr, Nat.not_lt.mpr]
  rwa [same] at split

/-! ## Instances -/

/-- A declaration's subject: a symbol, an expression with a head, or neither. -/
inductive Subject
  | symbol (name : Nat)
  | headed (head : Nat) (arguments : List Nat)
  | headless (value : Nat)
  deriving DecidableEq, Repr

/-- Declarations are chained by their subject's head. -/
def subjectHead : Subject → Option Nat
  | .symbol name => some name
  | .headed head _ => some head
  | .headless _ => none

/-- Declarations of `foo` and of `(foo x)` share a chain; others do not. -/
example : rowsOf ([.symbol 1, .headed 2 [5], .headed 1 [3], .headless 7] |>.map subjectHead)
    (subjectHead (.symbol 1)) = [0, 2] := by decide

/-- Exact equality still separates `foo` from `(foo 3)` within the chain. -/
example : answers [Subject.symbol 1, .headed 2 [5], .headed 1 [3], .headless 7]
    (.symbol 1) = [0] := by decide

/-- A key that keeps distinct subjects apart is still required: reading only
the chain of a wrong key loses the answer. -/
example : (rowsOf ([Subject.symbol 1, .symbol 2].map subjectHead) (some 2)).filter
    (fun row => [Subject.symbol 1, .symbol 2][row]? = some (.symbol 1)) = [] := by decide

/-- Selecting positions by a projected key is the same list whether the
positions index the projections or travel with the payloads. -/
theorem select_positions {α β : Type*} [DecidableEq β] (project : α → β) (key : β) :
    ∀ payloads : List α,
      (List.range payloads.length).filter
          (fun row => (payloads.map project)[row]? = some key) =
        ((List.range payloads.length).zip payloads).filterMap
          (fun occurrence => if project occurrence.2 = key then some occurrence.1 else none) := by
  intro payloads
  induction payloads using List.reverseRecOn with
  | nil => rfl
  | append_singleton payloads payload inductionHypothesis =>
    have lengths : (List.range payloads.length).length = payloads.length := List.length_range
    rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
      List.zip_append lengths, List.filterMap_append]
    congr 1
    · rw [← inductionHypothesis]
      apply List.filter_congr
      intro row member
      rw [List.mem_range] at member
      have inside : row < (payloads.map project).length := by simpa using member
      rw [List.map_append, List.getElem?_append_left inside]
    · by_cases selected : project payload = key <;> simp [selected]

open TermPathPosting in
/-- Term-path postings are the chains keyed by a path projection. -/
theorem postings_are_chains (path : List Nat) (key : Nat) (terms : List Term) :
    rowsOf (terms.map fun term => project term path) (.key key) =
      postings path key ((List.range terms.length).zip terms) := by
  unfold rowsOf postings
  rw [List.length_map]
  exact select_positions (fun term => project term path) (.key key) terms

end Mettapedia.Machines.Cursor.KeyedPostingChains
