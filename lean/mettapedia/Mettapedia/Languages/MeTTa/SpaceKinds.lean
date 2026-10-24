import Mettapedia.Languages.MeTTa.SpaceQueryPolicy
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Sort

/-!
# Space kinds: one space view, several insertion disciplines

Every space offers the common interface whatever its kind: `match` and
`get-atoms` read its **space view**, the bag of stored atoms
(`Kind.contents`), and a mutable space takes `add-atom` and `remove-atom`. A
kind fixes what its state is and how insertion and removal act on it. The
interface of its own (front, top, index, lookup, minimum) and the laws tying
that interface to the space view are in `SpaceKindContracts`.

| kind | state | `add-atom` | `remove-atom` | the space view after `add-atom` |
|---|---|---|---|---|
| atom | bag | add an occurrence | one occurrence | `x ::ₘ view` |
| history | list in insertion order | append | one occurrence, from a chosen end | `x ::ₘ view` |
| set | finite set | insert unless present | the atom | `ndinsert x view` |
| ordered set | duplicate-free list | append unless present | the atom | `ndinsert x view` |
| dict | functional set of pairs | by its update policy | the pair | the old pairs of other keys, and the new pair |

In CeTTa, `atom` and `hash` spaces both add an occurrence on `add-atom`; a
hash space adds exact membership and a fast `add-atom-nodup`, so its contract
is the atom kind's together with a membership facility. Stack and queue spaces
are both history spaces whose `remove-atom` takes the oldest occurrence; they
differ only in the end their own interface reads. The set, ordered-set and dict
kinds are candidates with no CeTTa counterpart yet. LeaTTa's named spaces append
on the right and erase the first occurrence (`HE.SpaceAlgebraLeaTTa`): the
history kind with removal from the front. HE's `BagSpace` inserts as the atom
kind does (`SpaceKindSupportBridge.bagSpace_add`).

**Disciplines** (`BagDiscipline`, `SetDiscipline`). The atom and history kinds
add one occurrence to the view (`atom_bag`, `history_bag`); the set and
ordered-set kinds insert unless present (`setKind_set`, `orderedSet_set`),
which on the view is `add-atom-nodup` (`toFinsupp_ndinsert`). Through any
query, a bag discipline adds the new atom's contribution and a set discipline
adds it only for a new atom (`matchView_add_bag`, `matchView_add_set`).
Removal takes one occurrence off the view for every kind (`atom_remove`,
`history_remove`, `set_remove`), whichever end a history removes from
(`Controls.removal_end_invisible`).

**Unordered observations.** An observation is unordered when it is a function
of the view (`Unordered`). Counting is unordered for every kind
(`count_unordered`), and is the query of a ground pattern (`count_eq_query`);
set membership is presence in the view, with at most one copy
(`set_member_iff`, `set_count_le_one`). Every observation of the atom and set
kinds is unordered, since their state is their view (`unordered_of_injective`);
an observation of a history is unordered exactly when permutations of the
history leave it unchanged (`history_unordered_iff`).

**Update policies of a dict** (`UpdatePolicy`): replace, keep the first value,
reject a second value, or merge with an operation. Each keeps the dict
functional (`functional_put`) and has its own lookup law
(`lookup_put_replace`, `lookup_put_keepFirst`, `put_reject_eq_none_iff`,
`lookup_put_merge`); other keys are unchanged (`lookup_put_other`). Lookup is
the `match` query of `(k, $v)` (`dict_lookup_eq_query`). Neither `add-atom`
nor `add-atom-nodup` keeps a dict functional
(`Controls.nodup_insert_breaks_functional`): `nodup` is about whole atoms, not
keys.

**Thawing and freezing.** Thawing a list into a kind inserts its elements in
order (`thaw`). A history gives the list back (`thaw_history`). The view of a
thawed list is its bag for bag disciplines and its support for set
disciplines (`contents_thaw_bag`, `contents_thaw_set`). Freezing back in
canonical order gives the list exactly when it is strictly increasing, for the
set kind (`set_roundtrip_iff`), and nondecreasing, for the atom kind
(`atom_roundtrip_iff`). An ordered set keeps first-insertion order
(`orderedSet_thaw_toFinset`, `Controls.orderedSet_order_observable`) and
gives the list back exactly when it has no repetition
(`orderedSet_thaw_eq_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceKinds

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.Languages.MeTTa.SpaceQueryPolicy

universe u v

/-- A space kind: a state, the space view the common interface reads, and the
kind's insertion and removal disciplines. -/
structure Kind (Atom : Type u) where
  State : Type v
  empty : State
  contents : State → Multiset Atom
  add : State → Atom → State
  remove : State → Atom → State

variable {α : Type u}

/-- An end of an insertion-ordered list: the oldest element (`front`) or the
newest (`back`). -/
inductive End where
  | front
  | back
  deriving DecidableEq, Repr

/-! ## The kinds -/

section Kinds

variable [DecidableEq α]

/-- The atom kind: a bag of atoms. -/
def atomKind : Kind.{u, u} α where
  State := Multiset α
  empty := 0
  contents := id
  add stored atom := atom ::ₘ stored
  remove stored atom := stored.erase atom

/-- The set kind: exact membership, insertion unless present. -/
def setKind : Kind.{u, u} α where
  State := Finset α
  empty := ∅
  contents stored := stored.val
  add stored atom := insert atom stored
  remove stored atom := stored.erase atom

/-- Remove one occurrence of an atom from an insertion-ordered list: the
oldest (`front`) or the newest (`back`). -/
def eraseAt : End → List α → α → List α
  | .front, stored, atom => stored.erase atom
  | .back, stored, atom => (stored.reverse.erase atom).reverse

/-- The history kind: atoms in insertion order. `add-atom` appends, and
`remove-atom` takes one occurrence from the chosen end. -/
def historyKind (removal : End) : Kind.{u, u} α where
  State := List α
  empty := []
  contents stored := stored
  add stored atom := stored ++ [atom]
  remove := eraseAt removal

/-- Insert at the back unless already present. -/
def orderedInsert (stored : List α) (atom : α) : List α :=
  if atom ∈ stored then stored else stored ++ [atom]

theorem nodup_orderedInsert {stored : List α} (nodup : stored.Nodup) (atom : α) :
    (orderedInsert stored atom).Nodup := by
  unfold orderedInsert
  split_ifs with present
  · exact nodup
  · exact nodup.append (List.nodup_singleton atom)
      (List.disjoint_singleton.mpr present)

/-- The ordered set kind: a set that remembers first-insertion order. -/
def orderedSetKind : Kind.{u, u} α where
  State := {stored : List α // stored.Nodup}
  empty := ⟨[], List.nodup_nil⟩
  contents stored := stored.1
  add stored atom := ⟨orderedInsert stored.1 atom, nodup_orderedInsert stored.2 atom⟩
  remove stored atom := ⟨stored.1.erase atom, stored.2.erase atom⟩

end Kinds

/-! ## Disciplines -/

/-- Insertion adds one occurrence to the space view. -/
def BagDiscipline (κ : Kind.{u, v} α) : Prop :=
  ∀ stored atom, κ.contents (κ.add stored atom) = atom ::ₘ κ.contents stored

/-- Insertion adds an atom to the space view unless it is already there. -/
def SetDiscipline [DecidableEq α] (κ : Kind.{u, v} α) : Prop :=
  ∀ stored atom, κ.contents (κ.add stored atom) = Multiset.ndinsert atom (κ.contents stored)

section Disciplines

variable [DecidableEq α]

theorem atom_bag : BagDiscipline (atomKind (α := α)) := fun _ _ => rfl

theorem history_bag (removal : End) : BagDiscipline (historyKind (α := α) removal) :=
  fun stored atom => Multiset.coe_eq_coe.mpr (List.perm_append_singleton atom stored)

theorem setKind_set : SetDiscipline (setKind (α := α)) := fun stored atom =>
  Finset.insert_val atom stored

theorem orderedSet_set : SetDiscipline (orderedSetKind (α := α)) := by
  intro stored atom
  show ((orderedInsert stored.1 atom : List α) : Multiset α) =
    Multiset.ndinsert atom (stored.1 : Multiset α)
  unfold orderedInsert
  split_ifs with present
  · rw [Multiset.ndinsert_of_mem (Multiset.mem_coe.mpr present)]
  · rw [Multiset.ndinsert_of_notMem (by simpa using present)]
    exact Multiset.coe_eq_coe.mpr (List.perm_append_singleton atom stored.1)

/-- On the space view, the set discipline is `add-atom-nodup`. -/
theorem toFinsupp_ndinsert (view : Multiset α) (atom : α) :
    Multiset.toFinsupp (Multiset.ndinsert atom view) = addNodup (Multiset.toFinsupp view) atom := by
  unfold addNodup
  rw [Multiset.toFinsupp_apply]
  split_ifs with absent
  · rw [Multiset.ndinsert_of_notMem (Multiset.count_eq_zero.mp absent), ← Multiset.singleton_add,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, add_comm]
  · rw [Multiset.ndinsert_of_mem (Multiset.count_ne_zero.mp absent)]

/-- What `match` returns on a space of kind `κ`: the query of its view, each
answer counted once per stored occurrence that gives it. -/
noncomputable def matchView {Pat Res : Type*} (κ : Kind.{u, v} α)
    (matcher : Pat → α → Option Res) (stored : κ.State) (pattern : Pat) : Ans ℕ Res :=
  query matcher (Multiset.toFinsupp (κ.contents stored)) pattern

/-- Under a bag discipline, `add-atom` adds the new atom's contribution to
every query. -/
theorem matchView_add_bag {Pat Res : Type*} {κ : Kind.{u, v} α} (bag : BagDiscipline κ)
    (matcher : Pat → α → Option Res) (stored : κ.State) (atom : α) (pattern : Pat) :
    matchView κ matcher (κ.add stored atom) pattern =
      matchView κ matcher stored pattern + contribution matcher pattern atom := by
  unfold matchView
  rw [bag, ← Multiset.singleton_add, Multiset.toFinsupp_add, query_add, add_comm,
    Multiset.toFinsupp_singleton, query_single, one_smul]

/-- Under a set discipline, `add-atom` adds the contribution only for an atom
not yet stored. -/
theorem matchView_add_set {Pat Res : Type*} {κ : Kind.{u, v} α} (set : SetDiscipline κ)
    (matcher : Pat → α → Option Res) (stored : κ.State) (atom : α) (pattern : Pat) :
    matchView κ matcher (κ.add stored atom) pattern =
      if atom ∈ κ.contents stored then matchView κ matcher stored pattern
      else matchView κ matcher stored pattern + contribution matcher pattern atom := by
  unfold matchView
  rw [set]
  split_ifs with present
  · rw [Multiset.ndinsert_of_mem present]
  · rw [Multiset.ndinsert_of_notMem present, ← Multiset.singleton_add, Multiset.toFinsupp_add,
      query_add, add_comm, Multiset.toFinsupp_singleton, query_single, one_smul]

theorem atom_remove (stored : Multiset α) (atom : α) :
    (atomKind (α := α)).contents ((atomKind (α := α)).remove stored atom) =
      ((atomKind (α := α)).contents stored).erase atom := rfl

/-- Removing from either end of a history takes one occurrence off the
view. -/
theorem history_remove (removal : End) (stored : List α) (atom : α) :
    (historyKind (α := α) removal).contents ((historyKind (α := α) removal).remove stored atom) =
      ((historyKind (α := α) removal).contents stored).erase atom := by
  cases removal with
  | front => exact (Multiset.coe_erase stored atom).symm
  | back =>
      show (((stored.reverse.erase atom).reverse : List α) : Multiset α) =
        (stored : Multiset α).erase atom
      rw [Multiset.coe_reverse, ← Multiset.coe_erase, Multiset.coe_reverse]

theorem set_remove (stored : Finset α) (atom : α) :
    (setKind (α := α)).contents ((setKind (α := α)).remove stored atom) =
      ((setKind (α := α)).contents stored).erase atom :=
  Finset.erase_val stored atom

end Disciplines

/-! ## Observations that do not see order -/

section Interfaces

variable [DecidableEq α]

/-- The matcher of a ground pattern. -/
def groundMatcher (pattern atom : α) : Option α := if atom = pattern then some atom else none

/-- **Counting is the query of a ground pattern** on the view. -/
theorem count_eq_query (view : Multiset α) (atom : α) :
    query groundMatcher (Multiset.toFinsupp view) atom = Finsupp.single atom (view.count atom) := by
  classical
  ext answer
  unfold query
  rw [Ans.bind_apply, Finsupp.sum, Finset.sum_eq_single atom]
  · simp [contribution, groundMatcher, Ans.pure, Finsupp.single_apply, Multiset.toFinsupp_apply]
  · intro other _ different
    simp [contribution, groundMatcher, different]
  · intro absent
    rw [Finsupp.notMem_support_iff.mp absent, zero_mul]

/-- Set membership is presence in the view. -/
theorem set_member_iff (stored : Finset α) (atom : α) :
    atom ∈ stored ↔ atom ∈ (setKind (α := α)).contents stored := by
  simp [setKind]

/-- A set space stores each atom at most once. -/
theorem set_count_le_one (stored : Finset α) (atom : α) :
    ((setKind (α := α)).contents stored).count atom ≤ 1 :=
  Multiset.nodup_iff_count_le_one.mp stored.nodup atom

end Interfaces

/-- An observation is unordered when it is a function of the space view. -/
def Unordered {β : Type*} (κ : Kind.{u, v} α) (observe : κ.State → β) : Prop :=
  ∃ through : Multiset α → β, ∀ stored, observe stored = through (κ.contents stored)

/-- Counting is unordered for every kind. -/
theorem count_unordered [DecidableEq α] (κ : Kind.{u, v} α) (atom : α) :
    Unordered κ fun stored => (κ.contents stored).count atom :=
  ⟨fun view => view.count atom, fun _ => rfl⟩

/-- When the state is its view, every observation is unordered. -/
theorem unordered_of_injective {β : Type*} (κ : Kind.{u, v} α)
    (injective : Function.Injective κ.contents) (observe : κ.State → β) :
    Unordered κ observe := by
  classical
  refine ⟨fun view => if found : ∃ stored, κ.contents stored = view
    then observe found.choose else observe κ.empty, fun stored => ?_⟩
  have found : ∃ other, κ.contents other = κ.contents stored := ⟨stored, rfl⟩
  simp only [found, dite_true]
  exact congrArg observe (injective found.choose_spec).symm

theorem atom_injective [DecidableEq α] : Function.Injective (atomKind (α := α)).contents :=
  fun _ _ same => same

theorem set_injective [DecidableEq α] : Function.Injective (setKind (α := α)).contents :=
  fun _ _ same => Finset.val_injective same

/-- An observation of a history is unordered exactly when permuting the
history leaves it unchanged. -/
theorem history_unordered_iff [DecidableEq α] {β : Type*} (removal : End)
    (observe : List α → β) :
    Unordered (historyKind (α := α) removal) observe ↔
      ∀ first second : List α, first.Perm second → observe first = observe second := by
  constructor
  · rintro ⟨through, factors⟩ first second permuted
    exact (factors first).trans
      ((congrArg through (Multiset.coe_eq_coe.mpr permuted)).trans (factors second).symm)
  · intro invariant
    exact ⟨Quot.lift observe invariant, fun _ => rfl⟩

/-! ## Dictionaries and their update policies -/

section Dict

variable {Key Val : Type*} [DecidableEq Key] [DecidableEq Val]

/-- Each key has at most one stored value. -/
def FunctionalSet (stored : Finset (Key × Val)) : Prop :=
  ∀ key first second, (key, first) ∈ stored → (key, second) ∈ stored → first = second

/-- The value stored under a key. -/
noncomputable def lookup (stored : Finset (Key × Val)) (key : Key) : Option Val := by
  classical
  exact if found : ∃ value, (key, value) ∈ stored then some found.choose else none

omit [DecidableEq Key] [DecidableEq Val] in
theorem lookup_eq_some_iff {stored : Finset (Key × Val)} (functional : FunctionalSet stored)
    (key : Key) (value : Val) : lookup stored key = some value ↔ (key, value) ∈ stored := by
  unfold lookup
  split_ifs with found
  · constructor
    · rintro ⟨⟩
      exact found.choose_spec
    · intro member
      exact congrArg some (functional key _ _ found.choose_spec member)
  · constructor
    · intro impossible
      cases impossible
    · intro member
      exact absurd ⟨value, member⟩ found

omit [DecidableEq Key] [DecidableEq Val] in
theorem lookup_eq_none_iff (stored : Finset (Key × Val)) (key : Key) :
    lookup stored key = none ↔ ∀ value, (key, value) ∉ stored := by
  unfold lookup
  split_ifs with found
  · simp only [false_iff, not_forall, not_not]
    exact found
  · simp only [true_iff]
    intro value member
    exact found ⟨value, member⟩

/-- The view of a dict as a bag space of pairs. -/
noncomputable def dictView (stored : Finset (Key × Val)) : Space ℕ (Key × Val) :=
  Multiset.toFinsupp stored.val

theorem dictView_ne_zero (stored : Finset (Key × Val)) (pair : Key × Val) :
    dictView stored pair ≠ 0 ↔ pair ∈ stored := by
  rw [dictView, Multiset.toFinsupp_apply, Multiset.count_ne_zero, Finset.mem_val]

/-- A functional dict is described by its lookup. -/
theorem dict_describes {stored : Finset (Key × Val)} (functional : FunctionalSet stored) :
    Describes (lookup stored) (dictView stored) := fun key value => by
  rw [lookup_eq_some_iff functional, dictView_ne_zero]

/-- **Dict lookup is the `match` query of `(k, $v)`**: one answer, of weight
one, exactly when the key is stored. -/
theorem dict_lookup_eq_query {stored : Finset (Key × Val)} (functional : FunctionalSet stored)
    (key : Key) :
    getValue (dictView stored) key = match lookup stored key with
      | some value => Finsupp.single value 1
      | none => 0 := by
  rw [getValue_eq_index (dictView stored) (lookup stored) (dict_describes functional) key]
  cases found : lookup stored key with
  | none => rfl
  | some value =>
      have member := (lookup_eq_some_iff functional key value).mp found
      simp only [dictView, Multiset.toFinsupp_apply]
      rw [Multiset.count_eq_one_of_mem stored.nodup member]

/-- How a dict answers a second value under a stored key. -/
inductive UpdatePolicy (Val : Type*) where
  /-- The new value replaces the old one. -/
  | replace
  /-- The old value stays. -/
  | keepFirst
  /-- A second value is refused. -/
  | reject
  /-- The two values are combined. -/
  | merge (combine : Val → Val → Val)

/-- Store a value under a key, removing the key's old pairs. -/
def replaceValue (stored : Finset (Key × Val)) (key : Key) (value : Val) : Finset (Key × Val) :=
  insert (key, value) (stored.filter fun pair => pair.1 ≠ key)

/-- Store a value under a key according to a policy; `none` is a refusal. -/
noncomputable def put : UpdatePolicy Val → Finset (Key × Val) → Key → Val →
    Option (Finset (Key × Val))
  | .replace, stored, key, value => some (replaceValue stored key value)
  | .keepFirst, stored, key, value =>
      some (match lookup stored key with
        | some _ => stored
        | none => replaceValue stored key value)
  | .reject, stored, key, value =>
      match lookup stored key with
      | some _ => none
      | none => some (replaceValue stored key value)
  | .merge combine, stored, key, value =>
      some (replaceValue stored key (match lookup stored key with
        | some old => combine old value
        | none => value))

theorem mem_replaceValue (stored : Finset (Key × Val)) (key : Key) (value : Val)
    (pair : Key × Val) :
    pair ∈ replaceValue stored key value ↔ pair = (key, value) ∨ (pair ∈ stored ∧ pair.1 ≠ key) := by
  simp [replaceValue, Finset.mem_insert, Finset.mem_filter]

theorem functional_replaceValue {stored : Finset (Key × Val)} (functional : FunctionalSet stored)
    (key : Key) (value : Val) : FunctionalSet (replaceValue stored key value) := by
  intro stored' first second firstMember secondMember
  rw [mem_replaceValue] at firstMember secondMember
  rcases firstMember with same | ⟨firstStored, firstOther⟩ <;>
    rcases secondMember with same' | ⟨secondStored, secondOther⟩
  · simp only [Prod.mk.injEq] at same same'
    rw [same.2, same'.2]
  · simp only [Prod.mk.injEq] at same
    exact absurd same.1 secondOther
  · simp only [Prod.mk.injEq] at same'
    exact absurd same'.1 firstOther
  · exact functional stored' first second firstStored secondStored

/-- Every policy keeps a dict functional. -/
theorem functional_put {stored : Finset (Key × Val)} (functional : FunctionalSet stored)
    (policy : UpdatePolicy Val) (key : Key) (value : Val) (updated : Finset (Key × Val))
    (stores : put policy stored key value = some updated) : FunctionalSet updated := by
  cases policy with
  | replace =>
      simp only [put, Option.some.injEq] at stores
      exact stores ▸ functional_replaceValue functional key value
  | keepFirst =>
      simp only [put, Option.some.injEq] at stores
      cases found : lookup stored key with
      | some _ => rw [found] at stores; exact stores ▸ functional
      | none => rw [found] at stores; exact stores ▸ functional_replaceValue functional key value
  | reject =>
      simp only [put] at stores
      cases found : lookup stored key with
      | some _ => rw [found] at stores; cases stores
      | none =>
          rw [found, Option.some.injEq] at stores
          exact stores ▸ functional_replaceValue functional key value
  | merge combine =>
      simp only [put, Option.some.injEq] at stores
      exact stores ▸ functional_replaceValue functional key _

theorem lookup_replaceValue {stored : Finset (Key × Val)} (functional : FunctionalSet stored)
    (key : Key) (value : Val) : lookup (replaceValue stored key value) key = some value :=
  (lookup_eq_some_iff (functional_replaceValue functional key value) key value).mpr
    ((mem_replaceValue stored key value _).mpr (Or.inl rfl))

theorem lookup_replaceValue_other {stored : Finset (Key × Val)} (functional : FunctionalSet stored)
    (key other : Key) (different : other ≠ key) (value : Val) :
    lookup (replaceValue stored key value) other = lookup stored other := by
  cases found : lookup stored other with
  | some old =>
      rw [lookup_eq_some_iff (functional_replaceValue functional key value), mem_replaceValue]
      exact Or.inr ⟨(lookup_eq_some_iff functional other old).mp found, different⟩
  | none =>
      rw [lookup_eq_none_iff] at found ⊢
      intro candidate member
      rw [mem_replaceValue] at member
      rcases member with same | ⟨stored', _⟩
      · simp only [Prod.mk.injEq] at same
        exact different same.1
      · exact found candidate stored'

/-- Replace: the new value is found. -/
theorem lookup_put_replace {stored : Finset (Key × Val)} (functional : FunctionalSet stored)
    (key : Key) (value : Val) :
    (put .replace stored key value).map (lookup · key) = some (some value) := by
  simp [put, lookup_replaceValue functional]

/-- Keep the first: an old value stays, otherwise the new one is stored. -/
theorem lookup_put_keepFirst {stored : Finset (Key × Val)} (functional : FunctionalSet stored)
    (key : Key) (value : Val) :
    (put .keepFirst stored key value).map (lookup · key) =
      some ((lookup stored key).or (some value)) := by
  simp only [put, Option.map_some]
  cases found : lookup stored key with
  | some old => simp [found]
  | none => simp [lookup_replaceValue functional]

/-- Reject: a second value is refused exactly when the key is stored. -/
theorem put_reject_eq_none_iff (stored : Finset (Key × Val)) (key : Key) (value : Val) :
    put .reject stored key value = none ↔ (lookup stored key).isSome := by
  simp only [put]
  cases lookup stored key <;> simp

/-- Merge: an old value is combined with the new one. -/
theorem lookup_put_merge {stored : Finset (Key × Val)} (functional : FunctionalSet stored)
    (combine : Val → Val → Val) (key : Key) (value : Val) :
    (put (.merge combine) stored key value).map (lookup · key) =
      some (some (match lookup stored key with
        | some old => combine old value
        | none => value)) := by
  simp [put, lookup_replaceValue functional]

/-- Every policy leaves the other keys unchanged. -/
theorem lookup_put_other {stored : Finset (Key × Val)} (functional : FunctionalSet stored)
    (policy : UpdatePolicy Val) (key other : Key) (different : other ≠ key) (value : Val)
    (updated : Finset (Key × Val)) (stores : put policy stored key value = some updated) :
    lookup updated other = lookup stored other := by
  cases policy with
  | replace =>
      simp only [put, Option.some.injEq] at stores
      exact stores ▸ lookup_replaceValue_other functional key other different value
  | keepFirst =>
      simp only [put, Option.some.injEq] at stores
      cases found : lookup stored key with
      | some _ => rw [found] at stores; rw [← stores]
      | none =>
          rw [found] at stores
          exact stores ▸ lookup_replaceValue_other functional key other different value
  | reject =>
      simp only [put] at stores
      cases found : lookup stored key with
      | some _ => rw [found] at stores; cases stores
      | none =>
          rw [found, Option.some.injEq] at stores
          exact stores ▸ lookup_replaceValue_other functional key other different value
  | merge combine =>
      simp only [put, Option.some.injEq] at stores
      exact stores ▸ lookup_replaceValue_other functional key other different _

/-- On the view, replacing is `SpaceQueryPolicy.setValue`. -/
theorem dictView_replaceValue (stored : Finset (Key × Val)) (key : Key) (value : Val) :
    dictView (replaceValue stored key value) = setValue (dictView stored) key value := by
  ext pair
  have fresh : (key, value) ∉ stored.filter fun stored => stored.1 ≠ key := by simp
  rw [dictView, replaceValue, Finset.insert_val_of_notMem fresh, Finset.filter_val,
    ← Multiset.singleton_add, Multiset.toFinsupp_add, add_comm]
  simp only [setValue, dictView, Finsupp.add_apply, Finsupp.filter_apply, Multiset.toFinsupp_apply,
    Multiset.count_filter, Multiset.toFinsupp_singleton]

/-- The dict kind under an update policy: `add-atom` of a pair stores it by
the policy, a refused pair leaves the dict as it was, and `remove-atom` removes
the pair. -/
noncomputable def dictKind (policy : UpdatePolicy Val) : Kind (Key × Val) where
  State := {stored : Finset (Key × Val) // FunctionalSet stored}
  empty := ⟨∅, fun _ _ _ member => absurd member (Finset.notMem_empty _)⟩
  contents stored := stored.1.val
  add stored pair :=
    match stores : put policy stored.1 pair.1 pair.2 with
    | some updated => ⟨updated, functional_put stored.2 policy pair.1 pair.2 updated stores⟩
    | none => stored
  remove stored pair := ⟨stored.1.erase pair, fun key first second firstMember secondMember =>
    stored.2 key first second (Finset.mem_of_mem_erase firstMember)
      (Finset.mem_of_mem_erase secondMember)⟩

/-- Under the replace policy, `add-atom` on a dict is `setValue` on its view. -/
theorem dictKind_replace_view (stored : (dictKind (Key := Key) (Val := Val) .replace).State)
    (key : Key) (value : Val) :
    Multiset.toFinsupp ((dictKind .replace).contents ((dictKind .replace).add stored (key, value))) =
      setValue (Multiset.toFinsupp ((dictKind .replace).contents stored)) key value :=
  dictView_replaceValue stored.1 key value

end Dict

/-! ## Thawing and freezing -/

section Thaw

variable [DecidableEq α]

/-- Thaw a list into a kind: insert its elements in order. -/
def thaw (κ : Kind.{u, v} α) (values : List α) : κ.State := values.foldl κ.add κ.empty

/-- A history gives the list back. -/
theorem thaw_history (removal : End) (values : List α) :
    thaw (historyKind (α := α) removal) values = values := by
  suffices ∀ prefix' : List α, values.foldl (fun stored atom => stored ++ [atom]) prefix' =
      prefix' ++ values from (this []).trans (List.nil_append values)
  induction values with
  | nil => intro prefix'; simp
  | cons head tail ih => intro prefix'; simp [ih]

omit [DecidableEq α] in
/-- Under a bag discipline the view of a thawed list is its bag. -/
theorem contents_thaw_bag (κ : Kind.{u, v} α) (bag : BagDiscipline κ)
    (empty : κ.contents κ.empty = 0) (values : List α) :
    κ.contents (thaw κ values) = (values : Multiset α) := by
  suffices ∀ start : κ.State, κ.contents (values.foldl κ.add start) =
      κ.contents start + (values : Multiset α) by
    rw [thaw, this, empty, zero_add]
  induction values with
  | nil => intro start; simp
  | cons head tail ih =>
      intro start
      rw [List.foldl_cons, ih, bag, ← Multiset.cons_coe, Multiset.add_cons, Multiset.cons_add]

/-- Under a set discipline the view of a thawed list is its support. -/
theorem contents_thaw_set (κ : Kind.{u, v} α) (set : SetDiscipline κ)
    (empty : κ.contents κ.empty = 0) (values : List α) :
    κ.contents (thaw κ values) = (values.toFinset).val := by
  have step : ∀ start : κ.State, (κ.contents start).Nodup →
      (κ.contents (values.foldl κ.add start)).Nodup ∧
        ∀ atom, atom ∈ κ.contents (values.foldl κ.add start) ↔
          atom ∈ κ.contents start ∨ atom ∈ values := by
    induction values with
    | nil => intro start nodup; exact ⟨nodup, fun atom => by simp⟩
    | cons head tail ih =>
        intro start nodup
        have nodup' : (κ.contents (κ.add start head)).Nodup := by
          rw [set]
          exact nodup.ndinsert head
        obtain ⟨resultNodup, members⟩ := ih (κ.add start head) nodup'
        refine ⟨resultNodup, fun atom => ?_⟩
        rw [List.foldl_cons, members, set, Multiset.mem_ndinsert, List.mem_cons]
        tauto
  obtain ⟨nodup, members⟩ := step κ.empty (by rw [empty]; exact Multiset.nodup_zero)
  apply (Multiset.Nodup.ext nodup values.toFinset.nodup).mpr
  intro atom
  rw [members, empty, Finset.mem_val, List.mem_toFinset]
  simp

/-- A list thawed into a set space is its finite set. -/
theorem thaw_set (values : List α) : thaw (setKind (α := α)) values = values.toFinset := by
  apply Finset.val_injective
  exact contents_thaw_set setKind setKind_set rfl values

/-- **A list thawed into a set space and frozen in canonical order is that
list exactly when it is strictly increasing.** -/
theorem set_roundtrip_iff [LinearOrder α] (values : List α) :
    (thaw (setKind (α := α)) values).sort (· ≤ ·) = values ↔
      values.Pairwise (· < ·) := by
  rw [thaw_set]
  constructor
  · intro same
    rw [← same]
    have := Finset.sortedLT_sort values.toFinset
    exact this.pairwise
  · intro increasing
    exact (List.toFinset_sort (· ≤ ·) (increasing.nodup)).mpr
      (increasing.imp le_of_lt)

/-- A list thawed into an atom space and frozen in canonical order is that
list exactly when it is nondecreasing. -/
theorem atom_roundtrip_iff [LinearOrder α] (values : List α) :
    (thaw (atomKind (α := α)) values).sort (· ≤ ·) = values ↔ values.Pairwise (· ≤ ·) := by
  have thawed : thaw (atomKind (α := α)) values = (values : Multiset α) :=
    contents_thaw_bag atomKind atom_bag rfl values
  rw [thawed]
  constructor
  · intro same
    rw [← same]
    exact Multiset.pairwise_sort _ _
  · intro sorted
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self (· ≤ ·) sorted

/-- The ordered set kind keeps the support of what was inserted. -/
theorem orderedSet_thaw_toFinset (values : List α) :
    (thaw (orderedSetKind (α := α)) values).1.toFinset = values.toFinset := by
  apply Finset.val_injective
  rw [List.toFinset_val, ← Multiset.coe_dedup,
    show ((thaw (orderedSetKind (α := α)) values).1 : Multiset α).dedup =
      ((thaw (orderedSetKind (α := α)) values).1 : Multiset α) from
      Multiset.dedup_eq_self.mpr (thaw (orderedSetKind (α := α)) values).2]
  exact contents_thaw_set orderedSetKind orderedSet_set rfl values

/-- The list an ordered set holds after thawing: the elements inserted one by
one unless present. -/
theorem thaw_orderedSet_val (values : List α) :
    (thaw (orderedSetKind (α := α)) values).1 = values.foldl orderedInsert [] := by
  suffices ∀ start : (orderedSetKind (α := α)).State,
      (values.foldl (orderedSetKind (α := α)).add start).1 = values.foldl orderedInsert start.1 from
    this _
  induction values with
  | nil => intro start; rfl
  | cons head tail ih => intro start; exact ih _

theorem foldl_orderedInsert_of_nodup (values : List α) :
    ∀ start : List α, (start ++ values).Nodup →
      values.foldl orderedInsert start = start ++ values := by
  induction values with
  | nil => intro start _; simp
  | cons head tail ih =>
      intro start nodup
      have fresh : head ∉ start := fun member =>
        (List.nodup_append.mp nodup).2.2 _ member _ List.mem_cons_self rfl
      rw [List.foldl_cons, show orderedInsert start head = start ++ [head] by
        simp [orderedInsert, fresh], ih _ (by simpa using nodup)]
      simp

/-- **A list thawed into an ordered set comes back exactly when it has no
repetition.** -/
theorem orderedSet_thaw_eq_iff (values : List α) :
    (thaw (orderedSetKind (α := α)) values).1 = values ↔ values.Nodup := by
  constructor
  · intro same
    rw [← same]
    exact (thaw (orderedSetKind (α := α)) values).2
  · intro nodup
    rw [thaw_orderedSet_val, foldl_orderedInsert_of_nodup values [] (by simpa using nodup)]
    rfl

end Thaw

/-! ## Controls -/

namespace Controls

/-- Removing the oldest or the newest occurrence leaves different histories and
the same view: the space view does not see which end a removal takes. -/
theorem removal_end_invisible :
    eraseAt .front ([1, 2, 1] : List ℕ) 1 ≠ eraseAt .back [1, 2, 1] 1 ∧
      ((eraseAt .front ([1, 2, 1] : List ℕ) 1 : List ℕ) : Multiset ℕ) =
        ((eraseAt .back ([1, 2, 1] : List ℕ) 1 : List ℕ) : Multiset ℕ) := by
  decide

/-- The set kind is not a bag discipline: adding a stored atom leaves the view
unchanged. -/
theorem set_not_bag : ¬ BagDiscipline (setKind (α := ℕ)) := by
  intro bag
  have := congrArg Multiset.card (bag ({1} : Finset ℕ) 1)
  simp [setKind] at this

/-- The atom kind is not a set discipline: adding a stored atom adds an
occurrence. -/
theorem atom_not_set : ¬ SetDiscipline (atomKind (α := ℕ)) := by
  intro set
  have := congrArg Multiset.card (set ({1} : Multiset ℕ) 1)
  simp only [atomKind] at this
  rw [Multiset.ndinsert_of_mem (by simp)] at this
  simp at this

/-- `add-atom-nodup` keeps whole atoms unique, not keys: a second value under
a key is stored beside the first. -/
theorem nodup_insert_breaks_functional :
    ¬ FunctionalSet (insert ((0 : ℕ), (2 : ℕ)) {((0 : ℕ), (1 : ℕ))}) := by
  intro functional
  have := functional 0 1 2 (by simp) (by simp)
  omega

/-- Two insertion histories with the same set: the ordered set kind tells
them apart, the set kind does not. -/
theorem orderedSet_order_observable :
    ((thaw (orderedSetKind (α := ℕ)) [1, 2]).1 : List ℕ) ≠
        ((thaw (orderedSetKind (α := ℕ)) [2, 1]).1 : List ℕ) ∧
      (thaw (setKind (α := ℕ)) [1, 2] : Finset ℕ) = (thaw (setKind (α := ℕ)) [2, 1] : Finset ℕ) := by
  have first : ((thaw (orderedSetKind (α := ℕ)) [1, 2]).1 : List ℕ) = [1, 2] := by
    simp [thaw, orderedSetKind, orderedInsert]
  have second : ((thaw (orderedSetKind (α := ℕ)) [2, 1]).1 : List ℕ) = [2, 1] := by
    simp [thaw, orderedSetKind, orderedInsert]
  rw [first, second, thaw_set, thaw_set]
  refine ⟨by simp, ?_⟩
  show ([1, 2] : List ℕ).toFinset = ([2, 1] : List ℕ).toFinset
  decide

/-- A repetition is merged by the ordered set: `[1, 2, 1]` comes back as
`[1, 2]`. -/
theorem orderedSet_merges_repetition :
    ((thaw (orderedSetKind (α := ℕ)) [1, 2, 1]).1 : List ℕ) = [1, 2] := by
  simp [thaw, orderedSetKind, orderedInsert]

end Controls

end Mettapedia.Languages.MeTTa.SpaceKinds
