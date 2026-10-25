import Mettapedia.Languages.MeTTa.SpaceKinds
import Mettapedia.Languages.MeTTa.HE.SpaceAlgebra
import Mathlib.Data.List.MinMax
import Mathlib.Logic.Function.Iterate

/-!
# Each kind's own interface, and its laws against the space view

A space has two faces. The common interface (`match`, `get-atoms`,
`add-atom`, `remove-atom`) reads the space view, a bag
(`SpaceKinds.Kind.contents`). A kind's own interface may read more: the order
of a history, the keys of a dict, a priority order on the atoms. This module
states, kind by kind, which operations of a kind's own interface are queries on
the space view, which are not, and the laws tying each to the view.

**Ordered spaces.** A history is read at one end (`peekAt`, `popAt`): the
oldest element for a queue, the newest for a stack. CeTTa stores both in
insertion order; `space-get` indexes that order and `space-truncate` keeps a
prefix of it (`getAt`, `truncate`). The stack laws: a pushed atom is on top,
and popping it restores the history (`peekAt_back_push`, `popAt_back_push`).
The queue laws: pushing changes the front only of an empty queue, and pushing
commutes with popping a nonempty queue (`peekAt_front_push`,
`popAt_front_push`). Draining gives a queue back in insertion order and a stack
in reverse (`drain_front`, `drain_back`, `drain_thaw_queue`,
`drain_thaw_stack`). Popping takes the occurrence it read off the view
(`contents_popAt`). Truncating is popping the newest elements
(`iterate_pop_back`), a stack's pop and never a queue's
(`iterate_pop_front`, `Controls.truncate_not_queue_pop`).

**What the space view does not see.** Neither the next element nor an indexed
element is a function of the view (`Controls.peek_not_unordered`,
`Controls.get_not_unordered`), and a stack and a queue holding the very same
history answer differently (`Controls.stack_queue_same_history`).

**Removal against popping.** When `remove-atom` takes from the end the
interface reads, removing the atom read next is popping (`eraseAt_eq_popAt`,
`Ordered.remove_eq_pop`). CeTTa's stack removes the oldest occurrence and pops
the newest, so removing the atom on top and popping leave different stacks,
with different tops (`Controls.stack_remove_ne_pop`); a stack that removes the
newest occurrence does not have this split (`Controls.lifoStack_remove_eq_pop`).

**Order from content.** A priority space reads its least atom (`peekMin`), a
function of the view characterized by membership and minimality
(`peekMin_eq_some_iff`); draining it sorts the view, whatever the insertion
history (`drainMin_eq_sort`). Breaking ties of a priority key by insertion
order is not a function of the view (`Controls.tie_by_history_not_unordered`).

**The storage algebra.** Read through its view, every kind that adds one
occurrence and removes one satisfies the counted-bag laws of the abstract
storage algebra (`countedBagLaws`; `atom_countedBagLaws`,
`history_countedBagLaws`). The set kind satisfies neither of that algebra's
law bundles, since their shared core has insertion add an occurrence
(`Controls.set_not_storageLaws`): the set discipline is outside it. LeaTTa's
named spaces are a concrete instance of the counted-bag bundle
(`HE.SpaceAlgebraLeaTTa.leattaSpaceOps_countedBagLaws`).

**Membership.** CeTTa's hash space is the atom kind with exact membership:
membership is presence of the answer of the ground query
(`mem_iff_query_ne_zero`), and `add-atom-nodup` acts on the view as the set
discipline (`SpaceKinds.toFinsupp_ndinsert`). Dict lookup is the `match` query
of `(k, $v)` (`SpaceKinds.dict_lookup_eq_query`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceKindContracts

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.Languages.MeTTa.SpaceQueryPolicy
open Mettapedia.Languages.MeTTa.SpaceKinds

universe u

variable {α : Type u}

/-! ## Reading a history at one end -/

/-- The element an ordered space reads next: its oldest (`front`) or its
newest (`back`). -/
def peekAt : End → List α → Option α
  | .front, stored => stored.head?
  | .back, stored => stored.getLast?

/-- Take the element read next off the history. -/
def popAt : End → List α → List α
  | .front, stored => stored.tail
  | .back, stored => stored.dropLast

/-- `space-get`: the element at an index of the insertion order. -/
def getAt (stored : List α) (index : ℕ) : Option α := stored[index]?

/-- `space-truncate`: keep the first `length` elements inserted. -/
def truncate (length : ℕ) (stored : List α) : List α := stored.take length

/-- An ordered space: the end `remove-atom` takes from, and the end the
space's own interface reads. -/
structure Ordered where
  removal : End
  access : End
  deriving DecidableEq, Repr

/-- CeTTa's queue space. -/
def queue : Ordered := ⟨.front, .front⟩

/-- CeTTa's stack space: `remove-atom` takes the oldest occurrence, the
interface reads the newest. -/
def stack : Ordered := ⟨.front, .back⟩

/-- A stack whose `remove-atom` takes the newest occurrence. -/
def lifoStack : Ordered := ⟨.back, .back⟩

/-- The kind of an ordered space. -/
abbrev Ordered.kind [DecidableEq α] (ordered : Ordered) : Kind.{u, u} α :=
  historyKind ordered.removal

/-! ## Stack and queue laws -/

@[simp] theorem peekAt_back_push (stored : List α) (atom : α) :
    peekAt .back (stored ++ [atom]) = some atom := by
  simp [peekAt]

@[simp] theorem popAt_back_push (stored : List α) (atom : α) :
    popAt .back (stored ++ [atom]) = stored := by
  simp [popAt]

theorem peekAt_front_push (stored : List α) (atom : α) :
    peekAt .front (stored ++ [atom]) = (peekAt .front stored).or (some atom) := by
  simp [peekAt, List.head?_append]

theorem popAt_front_push {stored : List α} (nonempty : stored ≠ []) (atom : α) :
    popAt .front (stored ++ [atom]) = popAt .front stored ++ [atom] :=
  List.tail_append_of_ne_nil nonempty

theorem mem_of_peekAt {e : End} {stored : List α} {atom : α}
    (peeked : peekAt e stored = some atom) : atom ∈ stored := by
  cases e with
  | front =>
      obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp peeked
      exact List.mem_cons_self
  | back =>
      obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.mp peeked
      simp

/-- **Popping takes the occurrence it read off the view.** -/
theorem contents_popAt [DecidableEq α] {e : End} {stored : List α} {atom : α}
    (peeked : peekAt e stored = some atom) :
    ((popAt e stored : List α) : Multiset α) = (stored : Multiset α).erase atom := by
  cases e with
  | front =>
      obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp peeked
      rw [← Multiset.cons_coe, Multiset.erase_cons_head]
      rfl
  | back =>
      obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.mp peeked
      rw [Multiset.coe_eq_coe.mpr (List.perm_append_singleton atom init), ← Multiset.cons_coe,
        Multiset.erase_cons_head]
      simp [popAt]

theorem peekAt_front_eq_getAt (stored : List α) : peekAt .front stored = getAt stored 0 := by
  cases stored <;> rfl

theorem peekAt_back_eq_getAt (stored : List α) :
    peekAt .back stored = getAt stored (stored.length - 1) :=
  List.getLast?_eq_getElem?

@[simp] theorem getAt_push_length (stored : List α) (atom : α) :
    getAt (stored ++ [atom]) stored.length = some atom := by
  simp [getAt]

theorem getAt_push_lt {stored : List α} {index : ℕ} (below : index < stored.length) (atom : α) :
    getAt (stored ++ [atom]) index = getAt stored index := by
  simp [getAt, List.getElem?_append_left below]

/-- Popping a stack `steps` times keeps the oldest elements: it is
`space-truncate`. -/
theorem iterate_pop_back (stored : List α) (steps : ℕ) :
    (popAt .back)^[steps] stored = truncate (stored.length - steps) stored := by
  change (List.dropLast)^[steps] stored = stored.take (stored.length - steps)
  induction steps generalizing stored with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih, List.dropLast_eq_take, List.length_take,
        List.take_take]
      congr 1
      omega

/-- Popping a queue `steps` times drops the oldest elements. -/
theorem iterate_pop_front (stored : List α) (steps : ℕ) :
    (popAt .front)^[steps] stored = stored.drop steps := by
  change (List.tail)^[steps] stored = stored.drop steps
  induction steps generalizing stored with
  | zero => simp
  | succ steps ih => rw [Function.iterate_succ_apply', ih, List.tail_drop]

/-! ## Draining -/

/-- Read and pop `steps` times, collecting what was read. -/
def drain (e : End) : ℕ → List α → List α
  | 0, _ => []
  | steps + 1, stored =>
      match peekAt e stored with
      | none => []
      | some atom => atom :: drain e steps (popAt e stored)

/-- Draining a queue gives its history in insertion order. -/
theorem drain_front (stored : List α) : drain .front stored.length stored = stored := by
  induction stored with
  | nil => rfl
  | cons head tail ih => simp [drain, peekAt, popAt, ih]

/-- Draining a stack gives its history in reverse. -/
theorem drain_back (stored : List α) : drain .back stored.length stored = stored.reverse := by
  induction stored using List.reverseRecOn with
  | nil => rfl
  | append_singleton init last ih => simp [drain, ih]

/-- **First in, first out.** -/
theorem drain_thaw_queue [DecidableEq α] (values : List α) :
    drain queue.access values.length (thaw queue.kind values) = values := by
  show drain .front values.length (thaw (historyKind .front) values) = values
  rw [thaw_history]
  exact drain_front values

/-- **Last in, first out.** -/
theorem drain_thaw_stack [DecidableEq α] (values : List α) :
    drain stack.access values.length (thaw stack.kind values) = values.reverse := by
  show drain .back values.length (thaw (historyKind .front) values) = values.reverse
  rw [thaw_history]
  exact drain_back values

/-! ## Removal against popping -/

/-- Removing the element read next from the end it is read at is popping. -/
theorem eraseAt_eq_popAt [DecidableEq α] {e : End} {stored : List α} {atom : α}
    (peeked : peekAt e stored = some atom) : eraseAt e stored atom = popAt e stored := by
  cases e with
  | front =>
      obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp peeked
      simp [eraseAt, popAt]
  | back =>
      obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.mp peeked
      simp [eraseAt, popAt]

/-- When `remove-atom` takes from the end the interface reads, removing the
atom read next is popping. -/
theorem Ordered.remove_eq_pop [DecidableEq α] (ordered : Ordered)
    (consistent : ordered.removal = ordered.access) {stored : List α} {atom : α}
    (peeked : peekAt ordered.access stored = some atom) :
    ordered.kind.remove stored atom = popAt ordered.access stored := by
  show eraseAt ordered.removal stored atom = popAt ordered.access stored
  rw [consistent]
  exact eraseAt_eq_popAt peeked

/-! ## Order from content: priority spaces -/

section Priority

variable [LinearOrder α]

/-- The least stored atom. -/
def peekMin (view : Multiset α) : Option α := (view.sort (· ≤ ·)).head?

/-- Read and remove the least atom `steps` times. -/
def drainMin : ℕ → Multiset α → List α
  | 0, _ => []
  | steps + 1, view =>
      match peekMin view with
      | none => []
      | some atom => atom :: drainMin steps (view.erase atom)

/-- The least atom is a stored atom below every stored atom. -/
theorem peekMin_eq_some_iff (view : Multiset α) (atom : α) :
    peekMin view = some atom ↔ atom ∈ view ∧ ∀ other ∈ view, atom ≤ other := by
  have sorted := Multiset.pairwise_sort view (· ≤ ·)
  constructor
  · intro least
    obtain ⟨rest, split⟩ := List.head?_eq_some_iff.mp least
    have inSorted : ∀ other, other ∈ view ↔ other = atom ∨ other ∈ rest := by
      intro other
      rw [← Multiset.mem_sort (· ≤ ·), split, List.mem_cons]
    refine ⟨(inSorted atom).mpr (Or.inl rfl), fun other member => ?_⟩
    rcases (inSorted other).mp member with same | later
    · exact same ▸ le_refl atom
    · rw [split] at sorted
      exact List.rel_of_pairwise_cons sorted later
  · rintro ⟨member, least⟩
    have nonempty : view.sort (· ≤ ·) ≠ [] := by
      intro empty
      have := (Multiset.mem_sort (· ≤ ·)).mpr member
      rw [empty] at this
      cases this
    obtain ⟨first, rest, split⟩ := List.exists_cons_of_ne_nil nonempty
    have firstMember : first ∈ view := by
      rw [← Multiset.mem_sort (· ≤ ·), split]
      exact List.mem_cons_self
    have firstLeast : ∀ other ∈ view, first ≤ other := by
      intro other otherMember
      rw [← Multiset.mem_sort (· ≤ ·), split, List.mem_cons] at otherMember
      rcases otherMember with same | later
      · exact same ▸ le_refl first
      · rw [split] at sorted
        exact List.rel_of_pairwise_cons sorted later
    rw [peekMin, split, List.head?_cons,
      le_antisymm (firstLeast atom member) (least first firstMember)]

/-- **Draining a priority space sorts its view**, whatever order the atoms
were inserted in. -/
theorem drainMin_eq_sort (view : Multiset α) :
    drainMin (Multiset.card view) view = view.sort (· ≤ ·) := by
  induction h : Multiset.card view generalizing view with
  | zero =>
      rw [Multiset.card_eq_zero.mp h]
      simp [drainMin]
  | succ steps ih =>
      have nonempty : view ≠ 0 := by
        intro empty
        rw [empty, Multiset.card_zero] at h
        cases h
      obtain ⟨least, member, below⟩ : ∃ least ∈ view, ∀ other ∈ view, least ≤ other := by
        obtain ⟨first, firstMember⟩ := Multiset.exists_mem_of_ne_zero nonempty
        have sortedNonempty : view.sort (· ≤ ·) ≠ [] := by
          intro empty
          have := (Multiset.mem_sort (· ≤ ·)).mpr firstMember
          rw [empty] at this
          cases this
        obtain ⟨head, rest, split⟩ := List.exists_cons_of_ne_nil sortedNonempty
        have peeked : peekMin view = some head := by rw [peekMin, split, List.head?_cons]
        exact ⟨head, ((peekMin_eq_some_iff view head).mp peeked).1,
          ((peekMin_eq_some_iff view head).mp peeked).2⟩
      have peeked : peekMin view = some least := (peekMin_eq_some_iff view least).mpr ⟨member, below⟩
      have smaller : Multiset.card (view.erase least) = steps := by
        rw [Multiset.card_erase_of_mem member, h]
        rfl
      show (match peekMin view with
        | none => []
        | some atom => atom :: drainMin steps (view.erase atom)) = view.sort (· ≤ ·)
      rw [peeked]
      simp only
      rw [ih (view.erase least) smaller]
      apply List.Perm.eq_of_sortedLE
      · rw [List.sortedLE_iff_pairwise, List.pairwise_cons]
        refine ⟨fun other otherMember => ?_, Multiset.pairwise_sort _ _⟩
        rw [Multiset.mem_sort] at otherMember
        exact below other (Multiset.mem_of_mem_erase otherMember)
      · rw [List.sortedLE_iff_pairwise]
        exact Multiset.pairwise_sort _ _
      · rw [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.sort_eq, Multiset.sort_eq,
          Multiset.cons_erase member]

/-- A sorted list of the view's atoms is the view in canonical order. -/
theorem sort_eq_of_pairwise {view : Multiset α} {values : List α}
    (sorted : values.Pairwise (· ≤ ·)) (same : (values : Multiset α) = view) :
    view.sort (· ≤ ·) = values := by
  apply List.Perm.eq_of_sortedLE
  · rw [List.sortedLE_iff_pairwise]
    exact Multiset.pairwise_sort _ _
  · rw [List.sortedLE_iff_pairwise]
    exact sorted
  · rw [← Multiset.coe_eq_coe, Multiset.sort_eq, same]

end Priority

/-- The first stored atom of least key: ties of the key broken by insertion
order. -/
def firstMin (key : α → ℕ) (stored : List α) : Option α := stored.argmin key

/-! ## Membership -/

/-- **Membership is presence of the answer of the ground query.** -/
theorem mem_iff_query_ne_zero [DecidableEq α] (view : Multiset α) (atom : α) :
    atom ∈ view ↔ query groundMatcher (Multiset.toFinsupp view) atom ≠ 0 := by
  rw [count_eq_query, Ne, Finsupp.single_eq_zero, ← Ne, Multiset.count_ne_zero]

/-! ## The counted-bag laws of the storage algebra -/

section StorageAlgebra

open Mettapedia.Languages.MeTTa.HE.SpaceAlgebra

variable [DecidableEq α]

/-- A kind as storage operations, counting occurrences through its view. -/
def storageOps (κ : Kind.{u, u} α) : StorageOps κ.State α where
  empty := κ.empty
  add atom state := κ.add state atom
  remove atom state := κ.remove state atom
  multiplicity state atom := (κ.contents state).count atom

/-- **A kind that adds one occurrence and removes one satisfies the
counted-bag laws.** -/
theorem countedBagLaws (κ : Kind.{u, u} α) (bag : BagDiscipline κ)
    (empty : κ.contents κ.empty = 0)
    (removal : ∀ state atom, κ.contents (κ.remove state atom) = (κ.contents state).erase atom) :
    CountedBagLaws (storageOps κ) where
  multiplicity_empty atom := by
    show (κ.contents κ.empty).count atom = 0
    rw [empty, Multiset.count_zero]
  multiplicity_add_self atom state := by
    show (κ.contents (κ.add state atom)).count atom = (κ.contents state).count atom + 1
    rw [bag, Multiset.count_cons_self]
  multiplicity_add_other first second state different := by
    show (κ.contents (κ.add state first)).count second = (κ.contents state).count second
    rw [bag, Multiset.count_cons_of_ne (Ne.symm different)]
  multiplicity_remove_self atom state := by
    show (κ.contents (κ.remove state atom)).count atom = (κ.contents state).count atom - 1
    rw [removal, Multiset.count_erase_self]
  multiplicity_remove_other first second state different := by
    show (κ.contents (κ.remove state first)).count second = (κ.contents state).count second
    rw [removal, Multiset.count_erase_of_ne (Ne.symm different)]

theorem atom_countedBagLaws : CountedBagLaws (storageOps (atomKind (α := α))) :=
  countedBagLaws atomKind atom_bag rfl atom_remove

theorem history_countedBagLaws (removal : End) :
    CountedBagLaws (storageOps (historyKind (α := α) removal)) :=
  countedBagLaws (historyKind removal) (history_bag removal) rfl (history_remove removal)

end StorageAlgebra

/-! ## Controls -/

namespace Controls

/-- **The element read next is not a function of the view**, at either end
and for either removal: two histories with the same atoms read differently. -/
theorem peek_not_unordered (removal access : End) :
    ¬ Unordered (historyKind (α := ℕ) removal) (peekAt access) := by
  rw [history_unordered_iff]
  intro invariant
  have := invariant [1, 2] [2, 1] (List.Perm.swap 2 1 [])
  cases access <;> simp [peekAt] at this

/-- An indexed element is not a function of the view. -/
theorem get_not_unordered (removal : End) :
    ¬ Unordered (historyKind (α := ℕ) removal) (fun stored : List ℕ => getAt stored 0) := by
  rw [history_unordered_iff]
  intro invariant
  have := invariant [1, 2] [2, 1] (List.Perm.swap 2 1 [])
  simp [getAt] at this

/-- **A stack and a queue holding the same history read different atoms
next.** -/
theorem stack_queue_same_history :
    peekAt queue.access ([1, 2] : List ℕ) = some 1 ∧ peekAt stack.access ([1, 2] : List ℕ) = some 2 :=
  ⟨rfl, rfl⟩

/-- **CeTTa's stack: removing the atom on top is not popping.** The history
`[1, 2, 1]` (oldest first) reads `1` on top; `remove-atom 1` takes the oldest
`1` and leaves `1` on top, popping leaves `2` on top. -/
theorem stack_remove_ne_pop :
    peekAt stack.access ([1, 2, 1] : List ℕ) = some 1 ∧
      stack.kind.remove ([1, 2, 1] : List ℕ) 1 = [2, 1] ∧
      popAt stack.access ([1, 2, 1] : List ℕ) = [1, 2] ∧
      peekAt stack.access (stack.kind.remove ([1, 2, 1] : List ℕ) 1) = some 1 ∧
      peekAt stack.access (popAt stack.access ([1, 2, 1] : List ℕ)) = some 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A stack that removes the newest occurrence: removing the atom on top is
popping. -/
theorem lifoStack_remove_eq_pop :
    lifoStack.kind.remove ([1, 2, 1] : List ℕ) 1 = popAt lifoStack.access [1, 2, 1] :=
  lifoStack.remove_eq_pop rfl rfl

/-- `space-truncate` on a queue is not popping it: it drops the newest
element, popping drops the oldest. -/
theorem truncate_not_queue_pop :
    truncate 1 ([1, 2] : List ℕ) = [1] ∧ popAt queue.access ([1, 2] : List ℕ) = [2] :=
  ⟨rfl, rfl⟩

/-- **Ties broken by insertion order are not a function of the view**: with a
key that ties `1` and `2`, the histories `[1, 2]` and `[2, 1]` read different
atoms first. -/
theorem tie_by_history_not_unordered :
    ¬ Unordered (historyKind (α := ℕ) .front) (firstMin fun _ => 0) := by
  rw [history_unordered_iff]
  intro invariant
  have := invariant [1, 2] [2, 1] (List.Perm.swap 2 1 [])
  revert this
  decide

/-- **The set kind is outside the storage algebra's core**: inserting a
stored atom leaves its count at one. -/
theorem set_not_storageLaws :
    ¬ Mettapedia.Languages.MeTTa.HE.SpaceAlgebra.StorageLaws (storageOps (setKind (α := ℕ))) := by
  intro laws
  have := laws.multiplicity_add_self 1 ({1} : Finset ℕ)
  revert this
  decide

/-- A priority space drains `{3, 1, 2, 1}` as `[1, 1, 2, 3]`. -/
theorem drainMin_example :
    drainMin 4 (({3, 1, 2, 1} : Multiset ℕ)) = [1, 1, 2, 3] := by
  rw [show (4 : ℕ) = Multiset.card ({3, 1, 2, 1} : Multiset ℕ) from rfl, drainMin_eq_sort]
  exact sort_eq_of_pairwise (by decide) (by decide)

end Controls

end Mettapedia.Languages.MeTTa.SpaceKindContracts
