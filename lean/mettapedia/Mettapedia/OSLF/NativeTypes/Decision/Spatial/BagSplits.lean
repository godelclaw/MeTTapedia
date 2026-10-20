import Mathlib.Data.Multiset.Antidiagonal
import Mathlib.Data.Finset.Dedup

/-!
# Finite bag decompositions

`enumerate` allocates each occurrence to exactly one side. Its list output is
convenient for interpreters; `candidates` removes duplicate value pairs for
consumers that work directly with multisets. Neither operation identifies two
occurrences inside a bag. The existence theorem is exact modulo permutation of
the two component lists and includes the empty components.

The list implementation enumerates occurrence choices, so equal occurrences can
produce duplicate pairs. No grouped-multiplicity complexity bound is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagSplits

universe u
variable {α : Type u}

/-- Allocate each occurrence to the left or the right component. -/
def enumerate : List α → List (List α × List α)
  | [] => [([], [])]
  | item :: rest =>
      (enumerate rest).map (fun pair => (item :: pair.1, pair.2)) ++
        (enumerate rest).map (fun pair => (pair.1, item :: pair.2))

/-- Interpret an enumerated pair as bags, retaining all multiplicities. -/
def bags (pair : List α × List α) : Multiset α × Multiset α :=
  (pair.1, pair.2)

theorem enumerate_antidiagonal (items : List α) :
    (((enumerate items).map bags : List (Multiset α × Multiset α)) :
      Multiset (Multiset α × Multiset α)) = (items : Multiset α).antidiagonal := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [enumerate, List.map_append, List.map_map, ← Multiset.coe_add,
      ← Multiset.cons_coe, Multiset.antidiagonal_cons]
    rw [← ih]
    simp only [Multiset.map_coe, List.map_map, Function.comp_def, bags,
      Prod.map_apply, id_eq, Multiset.cons_coe]
    exact add_comm _ _

/-- Every listed split partitions the input, up to permutation. -/
theorem enumerate_sound {items left right : List α}
    (member : (left, right) ∈ enumerate items) :
    (left : Multiset α) + (right : Multiset α) = (items : Multiset α) := by
  apply (Multiset.mem_antidiagonal (x := ((left : Multiset α), (right : Multiset α)))).mp
  rw [← enumerate_antidiagonal]
  exact List.mem_map.mpr ⟨(left, right), member, rfl⟩

/-- Every bag decomposition has a listed pair of representatives. -/
theorem enumerate_complete {items : List α} {left right : Multiset α}
    (partition : left + right = (items : Multiset α)) :
    ∃ pair ∈ enumerate items,
      (pair.1 : Multiset α) = left ∧ (pair.2 : Multiset α) = right := by
  have member : (left, right) ∈ (items : Multiset α).antidiagonal :=
    Multiset.mem_antidiagonal.mpr partition
  rw [← enumerate_antidiagonal] at member
  obtain ⟨pair, listed, same⟩ := List.mem_map.mp member
  exact ⟨pair, listed, congrArg Prod.fst same, congrArg Prod.snd same⟩

theorem enumerate_iff (items : List α) (left right : Multiset α) :
    (∃ pair ∈ enumerate items,
      (pair.1 : Multiset α) = left ∧ (pair.2 : Multiset α) = right) ↔
      left + right = (items : Multiset α) := by
  constructor
  · rintro ⟨⟨first, second⟩, member, rfl, rfl⟩
    exact enumerate_sound member
  · exact enumerate_complete

/-- A list predicate that respects permutation can use the finite catalogue
without choosing a canonical representative of each component bag. -/
theorem exists_enumerate_iff
    (left right : List α → Prop)
    (leftInvariant : ∀ {first second}, List.Perm first second → (left first ↔ left second))
    (rightInvariant : ∀ {first second}, List.Perm first second → (right first ↔ right second))
    (items : List α) :
    (∃ pair ∈ enumerate items, left pair.1 ∧ right pair.2) ↔
      ∃ first second : List α, (first ++ second).Perm items ∧ left first ∧ right second := by
  constructor
  · rintro ⟨⟨first, second⟩, member, acceptsLeft, acceptsRight⟩
    exact ⟨first, second, Multiset.coe_eq_coe.mp (enumerate_sound member),
      acceptsLeft, acceptsRight⟩
  · rintro ⟨first, second, partition, acceptsLeft, acceptsRight⟩
    obtain ⟨pair, member, firstEq, secondEq⟩ :=
      enumerate_complete (left := (first : Multiset α)) (right := (second : Multiset α))
        (Multiset.coe_eq_coe.mpr partition)
    exact ⟨pair, member,
      (leftInvariant (Multiset.coe_eq_coe.mp firstEq)).mpr acceptsLeft,
      (rightInvariant (Multiset.coe_eq_coe.mp secondEq)).mpr acceptsRight⟩

/-- The finite catalogue of distinct bag pairs. -/
def candidates [DecidableEq α] (input : Multiset α) :
    Finset (Multiset α × Multiset α) := input.antidiagonal.toFinset

@[simp]
theorem mem_candidates [DecidableEq α] (input left right : Multiset α) :
    (left, right) ∈ candidates input ↔ left + right = input := by
  simp [candidates]

/-- Evaluate separating conjunction for executable predicates on bags. -/
def check (left right : Multiset α → Bool) (items : List α) : Bool :=
  (enumerate items).any fun pair => left pair.1 && right pair.2

theorem check_iff (left right : Multiset α → Bool) (items : List α) :
    check left right items = true ↔
      ∃ first second : Multiset α,
        first + second = (items : Multiset α) ∧ left first = true ∧ right second = true := by
  simp only [check, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨first, second⟩, member, acceptsLeft, acceptsRight⟩
    exact ⟨first, second, enumerate_sound member, acceptsLeft, acceptsRight⟩
  · rintro ⟨first, second, partition, acceptsLeft, acceptsRight⟩
    obtain ⟨pair, member, firstEq, secondEq⟩ := enumerate_complete partition
    exact ⟨pair, member, firstEq ▸ acceptsLeft, secondEq ▸ acceptsRight⟩

theorem check_permutation (left right : Multiset α → Bool) {first second : List α}
    (same : first.Perm second) : check left right first = check left right second := by
  apply Bool.eq_iff_iff.mpr
  rw [check_iff, check_iff, Multiset.coe_eq_coe.mpr same]

/-- The reference enumeration counts occurrence allocations, before removing
duplicate value pairs. -/
theorem enumerate_length (items : List α) : (enumerate items).length = 2 ^ items.length := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [enumerate, List.length_append, List.length_map, List.length_cons, ih,
      Nat.pow_succ, Nat.mul_two]

end Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagSplits
