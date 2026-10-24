import Mettapedia.Languages.MeTTa.SpaceQueryPolicy
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Containers: shapes, positions, and the two views of a data structure

A container (Abbott, Altenkirch and Ghani; Mathlib's `PFunctor`) describes a
data structure by its shapes and the positions of each shape; a value is a
shape with an element at each position. Lists have a length as shape and its
indices as positions; tensors have dimensions and coordinates; dicts have a
finite key set and its keys. A value has two views.

* **The content view** (`contents`): the bag of its elements, forgetting
  positions. This is what `match` reads in a list-like space: the space view.
* **The graph view** (`graph`): each position's key with its element. When
  positions carry distinct keys (`Keyed`), the graph view is a functional
  space of key-element pairs (`graphSpace_functional`), and **positional
  access is the `match` query of `(k, $v)` on it** (`getValue_graphSpace_key`,
  `getValue_graphSpace_absent`; for lists, `getValue_listGraph`). The content
  view is the graph view with keys forgotten (`graph_map_snd`). A dict's atoms
  are its graph view; a list's atoms are its content view, which is why list
  indexing is not a query on a list space's view.

**Quotient containers.** Identifying values whose elements differ by a group
of position permutations keeps the content view (`bagOf_perm`). The content
view is a complete invariant for the full permutation group: two element
families have the same bag exactly when a permutation relates them
(`bagOf_eq_iff_perm`). Conversely, when the elements can be told apart, the
content view is complete for a group of permutations only if the group is all
of them (`complete_iff_top`): bags are exactly the full symmetric quotient, and
any smaller symmetry (rotations, say) leaves information that the bag view
loses (`Controls.rotation_not_complete`).

**Sets are not a quotient by positions.** Every identification of list values
by position permutations keeps both the length and the bag
(`PositionalRel.length_eq`, `PositionalRel.bag_eq`); deduplication identifies
lists of different lengths, so no family of position permutations produces it
(`Controls.dedup_not_positional`). A set is reached by a different insertion
discipline, not by forgetting positions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceContainers

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.Languages.MeTTa.SpaceQueryPolicy

universe u v w

/-! ## The bag of a finite family -/

section Bag

variable {ι : Type u} [Fintype ι] {X : Type w}

/-- The bag of the elements of a finite family. -/
def bagOf (elements : ι → X) : Multiset X := Finset.univ.val.map elements

/-- **Permuting positions keeps the bag.** -/
theorem bagOf_perm (elements : ι → X) (σ : Equiv.Perm ι) :
    bagOf (elements ∘ σ) = bagOf elements := by
  rw [bagOf, bagOf, ← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem bagOf_equiv {κ : Type v} [Fintype κ] (elements : ι → X) (e : κ ≃ ι) :
    bagOf (elements ∘ e) = bagOf elements := by
  rw [bagOf, bagOf, ← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem count_bagOf [DecidableEq X] (elements : ι → X) (element : X) :
    (bagOf elements).count element = Fintype.card {position // elements position = element} := by
  rw [bagOf, Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro position _
  exact eq_comm

/-- **The bag is a complete invariant for permutations of positions**: two
families have the same bag exactly when a permutation relates them. -/
theorem bagOf_eq_iff_perm [DecidableEq X] (first second : ι → X) :
    bagOf first = bagOf second ↔ ∃ σ : Equiv.Perm ι, second = first ∘ σ := by
  constructor
  · intro same
    have fibers : ∀ element : X,
        Fintype.card {position // second position = element} =
          Fintype.card {position // first position = element} := by
      intro element
      rw [← count_bagOf, ← count_bagOf, same]
    let matching : ∀ element : X,
        {position // second position = element} ≃ {position // first position = element} :=
      fun element => Fintype.equivOfCardEq (fibers element)
    exact ⟨Equiv.ofFiberEquiv matching, funext fun position =>
      (Equiv.ofFiberEquiv_map matching position).symm⟩
  · rintro ⟨σ, rfl⟩
    exact (bagOf_perm first σ).symm

/-- A group of position permutations for which the bag is a complete
invariant. -/
def BagComplete (X : Type w) (G : Subgroup (Equiv.Perm ι)) : Prop :=
  ∀ first second : ι → X, bagOf first = bagOf second → ∃ σ ∈ G, second = first ∘ σ

/-- **Bags are exactly the full symmetric quotient**: when the elements can
tell positions apart, the bag is a complete invariant for a group of
permutations exactly when the group is all of them. -/
theorem complete_iff_top [DecidableEq X] (G : Subgroup (Equiv.Perm ι)) (embed : ι ↪ X) :
    BagComplete X G ↔ G = ⊤ := by
  constructor
  · intro complete
    rw [Subgroup.eq_top_iff']
    intro τ
    obtain ⟨σ, member, same⟩ := complete embed (embed ∘ τ) (bagOf_perm embed τ).symm
    have : τ = σ := Equiv.ext fun position => embed.injective (congrFun same position)
    exact this ▸ member
  · rintro rfl first second same
    obtain ⟨σ, related⟩ := (bagOf_eq_iff_perm first second).mp same
    exact ⟨σ, Subgroup.mem_top σ, related⟩

end Bag

/-! ## Containers and their views -/

section Container

variable (P : PFunctor.{u, v}) [∀ shape, Fintype (P.B shape)] {X : Type w}

/-- The content view of a container value: the bag of its elements. -/
def contents (value : P X) : Multiset X := bagOf value.2

/-- Positions carry keys, distinct within a shape: list indices, dict keys,
tensor coordinates. -/
structure Keyed (Key : Type*) where
  key : ∀ shape, P.B shape ↪ Key

variable {P} {Key : Type*}

/-- The graph view: each position's key with its element. -/
def graph (keyed : Keyed P Key) (value : P X) : Multiset (Key × X) :=
  Finset.univ.val.map fun position => (keyed.key value.1 position, value.2 position)

/-- The content view is the graph view with keys forgotten. -/
theorem graph_map_snd (keyed : Keyed P Key) (value : P X) :
    (graph keyed value).map Prod.snd = contents P value := by
  rw [graph, Multiset.map_map]
  rfl

theorem graph_nodup (keyed : Keyed P Key) (value : P X) : (graph keyed value).Nodup :=
  Finset.univ.nodup.map fun _ _ same =>
    (keyed.key value.1).injective (congrArg Prod.fst same)

theorem mem_graph (keyed : Keyed P Key) (value : P X) (key : Key) (element : X) :
    (key, element) ∈ graph keyed value ↔
      ∃ position, keyed.key value.1 position = key ∧ value.2 position = element := by
  simp [graph]

/-- The graph view as a space of key-element pairs. -/
noncomputable def graphSpace [DecidableEq Key] [DecidableEq X] (keyed : Keyed P Key)
    (value : P X) : Space ℕ (Key × X) :=
  Multiset.toFinsupp (graph keyed value)

theorem graphSpace_apply [DecidableEq Key] [DecidableEq X] (keyed : Keyed P Key) (value : P X)
    (pair : Key × X) :
    graphSpace keyed value pair = if pair ∈ graph keyed value then 1 else 0 := by
  rw [graphSpace, Multiset.toFinsupp_apply]
  split_ifs with member
  · exact Multiset.count_eq_one_of_mem (graph_nodup keyed value) member
  · exact Multiset.count_eq_zero.mpr member

/-- **The graph view is functional**: a key has at most one element. -/
theorem graphSpace_functional [DecidableEq Key] [DecidableEq X] (keyed : Keyed P Key)
    (value : P X) : Functional (graphSpace keyed value) := by
  intro key first second firstStored secondStored
  rw [graphSpace_apply] at firstStored secondStored
  split_ifs at firstStored secondStored with firstMember secondMember
  · obtain ⟨p, pKey, pElement⟩ := (mem_graph keyed value key first).mp firstMember
    obtain ⟨q, qKey, qElement⟩ := (mem_graph keyed value key second).mp secondMember
    have : p = q := (keyed.key value.1).injective (pKey.trans qKey.symm)
    rw [← pElement, ← qElement, this]
  all_goals exact absurd rfl ‹(0 : ℕ) ≠ 0›

/-- **Positional access is the `match` query of `(k, $v)` on the graph
view**: at a position's key it answers that position's element, once. -/
theorem getValue_graphSpace_key [DecidableEq Key] [DecidableEq X] (keyed : Keyed P Key)
    (value : P X) (position : P.B value.1) :
    getValue (graphSpace keyed value) (keyed.key value.1 position) =
      Finsupp.single (value.2 position) 1 := by
  ext element
  rw [getValue_apply, graphSpace_apply, Finsupp.single_apply]
  by_cases same : value.2 position = element
  · rw [if_pos same, if_pos ((mem_graph keyed value _ _).mpr ⟨position, rfl, same⟩)]
  · rw [if_neg same, if_neg]
    rintro member
    obtain ⟨other, otherKey, otherElement⟩ := (mem_graph keyed value _ _).mp member
    have : other = position := (keyed.key value.1).injective otherKey
    exact same (this ▸ otherElement)

/-- At a key no position carries, positional access answers nothing. -/
theorem getValue_graphSpace_absent [DecidableEq Key] [DecidableEq X] (keyed : Keyed P Key)
    (value : P X) (key : Key) (absent : ∀ position, keyed.key value.1 position ≠ key) :
    getValue (graphSpace keyed value) key = 0 := by
  ext element
  rw [getValue_apply, graphSpace_apply, if_neg]
  · rfl
  · rintro member
    obtain ⟨position, positionKey, _⟩ := (mem_graph keyed value _ _).mp member
    exact absent position positionKey

end Container

/-! ## Lists -/

/-- Lists as a container: a length, and the indices below it. -/
abbrev listContainer : PFunctor.{0, 0} := ⟨ℕ, Fin⟩

/-- A list as a container value. -/
def ofList {X : Type} (values : List X) : listContainer X := ⟨values.length, values.get⟩

/-- List positions keyed by their index. -/
def listKeys : Keyed listContainer ℕ := ⟨fun _ => Fin.valEmbedding⟩

/-- The content view of a list is its bag. -/
theorem contents_ofList {X : Type} (values : List X) :
    contents listContainer (ofList values) = (values : Multiset X) := by
  show Finset.univ.val.map values.get = (values : Multiset X)
  rw [Fin.univ_val_map, List.ofFn_get]

/-- **Indexing a list is the `match` query of `(i, $v)` on its graph
view.** -/
theorem getValue_listGraph {X : Type} [DecidableEq X] (values : List X) (index : ℕ) :
    getValue (graphSpace listKeys (ofList values)) index = match values[index]? with
      | some element => Finsupp.single element 1
      | none => 0 := by
  by_cases below : index < values.length
  · rw [List.getElem?_eq_getElem below]
    exact getValue_graphSpace_key listKeys (ofList values) ⟨index, below⟩
  · rw [List.getElem?_eq_none (Nat.le_of_not_lt below)]
    apply getValue_graphSpace_absent
    intro position same
    exact below (same ▸ position.2)

/-- List values related by a permutation of positions drawn from a family of
groups. -/
def PositionalRel {X : Type} (G : ∀ length, Subgroup (Equiv.Perm (Fin length)))
    (first second : List X) : Prop :=
  ∃ same : first.length = second.length, ∃ σ ∈ G first.length,
    ∀ position, second.get (Fin.cast same position) = first.get (σ position)

theorem PositionalRel.length_eq {X : Type} {G : ∀ length, Subgroup (Equiv.Perm (Fin length))}
    {first second : List X} (related : PositionalRel G first second) :
    first.length = second.length :=
  related.1

/-- **A positional identification keeps the bag.** -/
theorem PositionalRel.bag_eq {X : Type} {G : ∀ length, Subgroup (Equiv.Perm (Fin length))}
    {first second : List X} (related : PositionalRel G first second) :
    (first : Multiset X) = (second : Multiset X) := by
  obtain ⟨same, σ, _, agrees⟩ := related
  have secondBag : bagOf (second.get ∘ finCongr same) = (second : Multiset X) := by
    rw [bagOf_equiv, bagOf, Fin.univ_val_map, List.ofFn_get]
  have firstBag : bagOf (first.get ∘ σ) = (first : Multiset X) := by
    rw [bagOf_perm, bagOf, Fin.univ_val_map, List.ofFn_get]
  rw [← secondBag, ← firstBag]
  congr 1
  funext position
  exact (agrees position).symm

/-! ## Controls -/

namespace Controls

/-- **Deduplication is not a positional identification**: no family of
groups of position permutations identifies exactly the lists with the same
elements, since `[0, 0]` and `[0]` have the same elements and different
lengths. -/
theorem dedup_not_positional :
    ¬ ∃ G : ∀ length, Subgroup (Equiv.Perm (Fin length)),
      ∀ first second : List ℕ, PositionalRel G first second ↔ first.toFinset = second.toFinset := by
  rintro ⟨G, characterizes⟩
  have related := (characterizes [0, 0] [0]).mpr (by decide)
  have := related.length_eq
  simp at this

/-- The content view does not see positions: `[1, 2]` and `[2, 1]` have the
same bag and different elements at index `0`. -/
theorem contents_forgets_positions :
    contents listContainer (ofList ([1, 2] : List ℕ)) = contents listContainer (ofList [2, 1]) ∧
      ([1, 2] : List ℕ)[0]? ≠ ([2, 1] : List ℕ)[0]? := by
  rw [contents_ofList, contents_ofList]
  decide

/-- The rotations of three positions. -/
def rotations : Subgroup (Equiv.Perm (Fin 3)) := Subgroup.zpowers (finRotate 3)

/-- **A smaller symmetry is not complete**: the rotations of three positions
are not all permutations, so some bag-equal families are not rotations of each
other. -/
theorem rotation_not_complete : ¬ BagComplete ℕ rotations := by
  rw [complete_iff_top rotations Fin.valEmbedding]
  intro everything
  have swapped : Equiv.swap (0 : Fin 3) 1 ∈ rotations := everything ▸ Subgroup.mem_top _
  obtain ⟨power, equal⟩ := Subgroup.mem_zpowers_iff.mp swapped
  have three : (finRotate 3) ^ (3 : ℤ) = 1 := by decide
  rw [show (finRotate 3) ^ power = (finRotate 3) ^ (power % 3) by
    conv_lhs => rw [← Int.mul_ediv_add_emod power 3, zpow_add, zpow_mul, three, one_zpow,
      one_mul]] at equal
  have cases : power % 3 = 0 ∨ power % 3 = 1 ∨ power % 3 = 2 := by omega
  rcases cases with zero | one | two
  · rw [zero] at equal
    exact absurd (congrArg (· (0 : Fin 3)) equal) (by decide)
  · rw [one] at equal
    exact absurd (congrArg (· (1 : Fin 3)) equal) (by decide)
  · rw [two] at equal
    exact absurd (congrArg (· (0 : Fin 3)) equal) (by decide)

end Controls

end Mettapedia.Languages.MeTTa.SpaceContainers
