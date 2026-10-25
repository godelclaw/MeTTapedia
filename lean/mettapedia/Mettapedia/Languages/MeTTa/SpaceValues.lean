import Mettapedia.Languages.MeTTa.SpaceKindContracts

/-!
# Collection values and spaces: reading values as spaces, reifying answers

Values are immutable (a list, a bag, a set); spaces hold atoms under a kind's
discipline; answers are what a query returns, a bag of results. Three bridges
connect them.

* **A value read as a read-only space.** A bag value is the space
  `Multiset.toFinsupp b` (`spaceOf`). `match` over a list value, listing the
  answers in the value's order (`matchList`), has exactly the answers of the
  query of that space as its bag (`matchList_bag`): the order of a value's
  answers is the value's order, and the bag is order-free
  (`Controls.match_order_follows_value`). `superpose` of a bag is `match $x`
  over the bag read as a space (`superpose_eq_query`).
* **`superpose` and `collapse` are reflection and reification.** A bag value
  becomes answers (`superpose`) and answers become a bag value
  (`collapseBag`); the two are inverse (`collapseBag_superpose`,
  `superpose_collapseBag`), and reifying a bound computation is binding the
  reified bags (`collapseBag_bind`). Reifying as a set keeps the support
  (`collapseSet_eq`), and the support of a bound computation is the union of
  the supports (`collapseSet_bind`).
* **An ordered `collapse` is not a function of the answers.** An evaluation
  lists its answers in some order (`Enumerates`); two listings of the same
  answers can differ (`Controls.collapse_order_not_function`), and sorting a
  listing gives the canonical bag, the same for every listing
  (`sort_enumeration`). This is how a canonical `collapse-bag` is obtained from
  an ordered `collapse`.
* **`unique-atom` is thawing into an ordered set.** It keeps the first
  occurrence of each element (`uniqueAtom`): the result has no repetition,
  holds exactly the input's elements, and is the input exactly when the input
  has no repetition (`uniqueAtom_nodup`, `uniqueAtom_toFinset`,
  `uniqueAtom_eq_iff`). Thawing a list into the set kind and freezing it back
  gives the list's bag exactly when the list has no repetition
  (`thaw_set_val_eq_iff`).

The values side connects these to canonical collection literals:
`CollectionValueBridges.uniqueAtom_eq_dedupFirst` (`unique-atom` is the normal
form of the insertion-ordered set), and `CollectionValueBridges.canonical_enumeration`
with `CollectionValueBridges.conv_enumerations_iff` (every enumeration of one bag
of answers, written as a bag literal, has the canonical form of the sorted
answers).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceValues

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.Languages.MeTTa.SpaceQueryPolicy
open Mettapedia.Languages.MeTTa.SpaceKinds
open Mettapedia.Languages.MeTTa.SpaceKindContracts

universe u

variable {α X Y : Type*}

/-! ## A value read as a space -/

section ReadOnly

variable [DecidableEq α]

/-- A bag value read as a read-only space. -/
noncomputable def spaceOf (value : Multiset α) : Space ℕ α := Multiset.toFinsupp value

/-- The answers of `match` over a list value, in the list's order. -/
def matchList {Pat Res : Type*} (matcher : Pat → α → Option Res) (pattern : Pat)
    (values : List α) : List Res :=
  values.filterMap (matcher pattern)

theorem toFinsupp_cons (value : Multiset α) (atom : α) :
    Multiset.toFinsupp (atom ::ₘ value) = Finsupp.single atom 1 + Multiset.toFinsupp value := by
  rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

/-- **The answers of `match` over a list value are, as a bag, the query of the
value read as a space.** -/
theorem matchList_bag {Pat Res : Type*} [DecidableEq Res] (matcher : Pat → α → Option Res)
    (pattern : Pat) (values : List α) :
    Multiset.toFinsupp (matchList matcher pattern values : Multiset Res) =
      query matcher (spaceOf (values : Multiset α)) pattern := by
  induction values with
  | nil => simp [matchList, spaceOf, query_zero]
  | cons head tail ih =>
      have space : spaceOf ((head :: tail : List α) : Multiset α) =
          Finsupp.single head 1 + spaceOf (tail : Multiset α) := by
        rw [spaceOf, spaceOf, ← Multiset.cons_coe, toFinsupp_cons]
      rw [space, query_add, query_single, one_smul, ← ih]
      cases matched : matcher pattern head with
      | none => simp [matchList, matched, contribution]
      | some result =>
          simp only [matchList, List.filterMap_cons, matched]
          rw [← Multiset.cons_coe, toFinsupp_cons]
          simp [contribution, matched, Ans.pure]

/-- **`superpose` of a bag is `match $x` over the bag read as a space.** -/
theorem superpose_eq_query (value : Multiset α) :
    Multiset.toFinsupp value = query (fun (_ : Unit) (atom : α) => some atom) (spaceOf value) () := by
  rw [query_identity (fun (_ : Unit) (atom : α) => some atom) () id (fun _ => rfl),
    Finsupp.mapDomain_id]
  rfl

end ReadOnly

/-! ## Reflection and reification -/

section Reify

variable [DecidableEq X]

/-- `superpose`: a bag value becomes answers, each element as often as it
occurs. -/
noncomputable def superpose (value : Multiset X) : Ans ℕ X := Multiset.toFinsupp value

/-- `collapse`, reified as a bag. -/
noncomputable def collapseBag (answers : Ans ℕ X) : Multiset X := Finsupp.toMultiset answers

/-- `collapse`, reified as a set. -/
def collapseSet (answers : Ans ℕ X) : Finset X := answers.support

@[simp] theorem collapseBag_superpose (value : Multiset X) : collapseBag (superpose value) = value :=
  Multiset.toFinsupp_toMultiset value

@[simp] theorem superpose_collapseBag (answers : Ans ℕ X) : superpose (collapseBag answers) = answers :=
  Finsupp.toMultiset_toFinsupp answers

/-- **Reifying a bound computation binds the reified bags.** -/
theorem collapseBag_bind [DecidableEq Y] (answers : Ans ℕ X) (continuation : X → Ans ℕ Y) :
    collapseBag (Ans.bind answers continuation) =
      (collapseBag answers).bind fun x => collapseBag (continuation x) := by
  apply (Multiset.toFinsupp (α := Y)).injective
  show superpose (collapseBag (Ans.bind answers continuation)) =
    Multiset.toFinsupp ((collapseBag answers).bind fun x => collapseBag (continuation x))
  rw [superpose_collapseBag, toFinsupp_bind]
  congr 1
  · exact (superpose_collapseBag answers).symm
  · funext x
    exact (superpose_collapseBag (continuation x)).symm

/-- Reifying as a set keeps the support of the reified bag. -/
theorem collapseSet_eq (answers : Ans ℕ X) : collapseSet answers = (collapseBag answers).toFinset :=
  (Finsupp.toFinset_toMultiset answers).symm

theorem collapseSet_superpose (value : Multiset X) : collapseSet (superpose value) = value.toFinset :=
  Multiset.toFinsupp_support value

omit [DecidableEq X] in
/-- **The set of answers of a bound computation is the union of the sets.** -/
theorem collapseSet_bind [DecidableEq Y] (answers : Ans ℕ X) (continuation : X → Ans ℕ Y) :
    collapseSet (Ans.bind answers continuation) =
      (collapseSet answers).biUnion fun x => collapseSet (continuation x) :=
  Ans.support_bind answers continuation

/-! ## Ordered `collapse` -/

/-- A list enumerates answers when its bag is those answers: what an
evaluation strategy that lists answers one by one produces. -/
def Enumerates (listed : List X) (answers : Ans ℕ X) : Prop :=
  Multiset.toFinsupp (listed : Multiset X) = answers

theorem enumerates_iff (listed : List X) (answers : Ans ℕ X) :
    Enumerates listed answers ↔ (listed : Multiset X) = collapseBag answers := by
  constructor
  · intro enumerates
    rw [← enumerates, collapseBag, Multiset.toFinsupp_toMultiset]
  · intro same
    rw [Enumerates, same, collapseBag, Finsupp.toMultiset_toFinsupp]

/-- **Sorting an ordered `collapse` gives the canonical bag**, the same for
every enumeration of the answers. -/
theorem sort_enumeration [LinearOrder X] {listed : List X} {answers : Ans ℕ X}
    (enumerates : Enumerates listed answers) :
    listed.mergeSort (fun first second => decide (first ≤ second)) =
      (collapseBag answers).sort (· ≤ ·) := by
  rw [← (enumerates_iff listed answers).mp enumerates, Multiset.coe_sort]

end Reify

/-! ## `unique-atom` -/

section Unique

variable [DecidableEq α]

/-- `unique-atom`: the first occurrence of each element, in order: the list
thawed into an ordered set. -/
def uniqueAtom (values : List α) : List α := (thaw (orderedSetKind (α := α)) values).1

theorem uniqueAtom_nodup (values : List α) : (uniqueAtom values).Nodup :=
  (thaw (orderedSetKind (α := α)) values).2

/-- `unique-atom` keeps exactly the input's elements. -/
theorem uniqueAtom_toFinset (values : List α) : (uniqueAtom values).toFinset = values.toFinset :=
  orderedSet_thaw_toFinset values

/-- As a value, `unique-atom` returns the input's set. -/
theorem uniqueAtom_bag (values : List α) :
    (uniqueAtom values : Multiset α) = (values : Multiset α).dedup := by
  rw [← Multiset.dedup_eq_self.mpr (Multiset.coe_nodup.mpr (uniqueAtom_nodup values)),
    Multiset.coe_dedup, Multiset.coe_dedup, ← List.toFinset_val, ← List.toFinset_val,
    uniqueAtom_toFinset]

/-- `unique-atom` returns its input exactly when the input has no
repetition. -/
theorem uniqueAtom_eq_iff (values : List α) : uniqueAtom values = values ↔ values.Nodup :=
  orderedSet_thaw_eq_iff values

/-- Thawing a list into the set kind and freezing it back gives the list's
bag exactly when the list has no repetition. -/
theorem thaw_set_val_eq_iff (values : List α) :
    (thaw (setKind (α := α)) values).val = (values : Multiset α) ↔ values.Nodup := by
  rw [thaw_set, List.toFinset_val, Multiset.coe_eq_coe]
  constructor
  · intro same
    exact same.nodup_iff.mp (List.nodup_dedup values)
  · intro nodup
    rw [List.dedup_eq_self.mpr nodup]

end Unique

/-! ## Controls -/

namespace Controls

/-- **The order of a value's answers is the value's order**: matching `$x`
over `[1, 2]` and `[2, 1]` lists different answers with the same bag. -/
theorem match_order_follows_value :
    matchList (fun (_ : Unit) (atom : ℕ) => some atom) () [1, 2] = [1, 2] ∧
      matchList (fun (_ : Unit) (atom : ℕ) => some atom) () [2, 1] = [2, 1] ∧
      ((matchList (fun (_ : Unit) (atom : ℕ) => some atom) () [1, 2] : List ℕ) : Multiset ℕ) =
        ((matchList (fun (_ : Unit) (atom : ℕ) => some atom) () [2, 1] : List ℕ) : Multiset ℕ) := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- **An ordered `collapse` is not a function of the answers**: `[1, 2]` and
`[2, 1]` enumerate the same answers. -/
theorem collapse_order_not_function :
    Enumerates [1, 2] (superpose ({1, 2} : Multiset ℕ)) ∧
      Enumerates [2, 1] (superpose ({1, 2} : Multiset ℕ)) ∧ ([1, 2] : List ℕ) ≠ [2, 1] := by
  refine ⟨?_, ?_, by decide⟩
  · rw [enumerates_iff, collapseBag_superpose]
    rfl
  · rw [enumerates_iff, collapseBag_superpose]
    exact Multiset.coe_eq_coe.mpr (List.Perm.swap 1 2 [])

/-- `unique-atom` keeps first occurrences: `[1, 2, 1, 3, 2]` gives
`[1, 2, 3]`. -/
theorem uniqueAtom_example : uniqueAtom ([1, 2, 1, 3, 2] : List ℕ) = [1, 2, 3] := by
  simp [uniqueAtom, thaw, orderedSetKind, orderedInsert]

/-- Reifying as a set forgets counts: `{1, 1, 2}` and `{1, 2}` reify to the
same set and to different bags. -/
theorem collapseSet_forgets_counts :
    collapseSet (superpose ({1, 1, 2} : Multiset ℕ)) = collapseSet (superpose ({1, 2} : Multiset ℕ)) ∧
      collapseBag (superpose ({1, 1, 2} : Multiset ℕ)) ≠ collapseBag (superpose ({1, 2} : Multiset ℕ)) := by
  rw [collapseSet_superpose, collapseSet_superpose, collapseBag_superpose, collapseBag_superpose]
  decide

end Controls

end Mettapedia.Languages.MeTTa.SpaceValues
