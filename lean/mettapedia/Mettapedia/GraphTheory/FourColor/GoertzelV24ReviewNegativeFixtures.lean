import Mathlib.Tactic
import Mettapedia.GraphTheory.FourColor.GoertzelV24CurvatureScope

/-!
# Finite negative fixtures for the compositional route

These regressions record four false shortcuts exposed by mathematical review:
unrestricted capped subtraction, a polynomial subset-orbit inference from
monotonicity, erasure of ordered boundary data, and a general twelve-pentagon
bound.  Each refutation is paired with the strongest elementary replacement
needed by the source route.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ReviewNegativeFixtures

open GoertzelV24CurvatureScope

/-! ## Capped arithmetic -/

/-- Truncated natural subtraction refutes the unrestricted capped update. -/
theorem cappedAddSub_unrestricted_counterexample :
    Nat.min 1 (2 + 0 - 1) ≠ Nat.min 1 (Nat.min 1 2 + 0 - 1) := by
  norm_num

/-- Capping the predecessor first is sound when the removed overlap belongs
to the new contribution.  Both literal source cap cases satisfy `d ≤ b`. -/
theorem min_add_sub_eq_min_min_add_sub_of_le
    (k a b d : Nat) (hdb : d ≤ b) :
    Nat.min k (a + b - d) = Nat.min k (Nat.min k a + b - d) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hdb
  have hcancel (x : Nat) : x + (d + c) - d = x + c := by omega
  rw [hcancel a, hcancel (Nat.min k a)]
  by_cases hak : a ≤ k
  · simp [Nat.min_eq_right hak]
  · have hka : k ≤ a := Nat.le_of_not_ge hak
    simp [Nat.min_eq_left hka,
      Nat.min_eq_left (by omega : k ≤ a + c)]

/-- The first literal source update removes one edge from a five-edge new
contribution, so the corrected capped law applies without an extra premise at
its use site. -/
theorem min_add_five_sub_one_eq_min_min_add_five_sub_one (k a : Nat) :
    Nat.min k (a + 5 - 1) = Nat.min k (Nat.min k a + 5 - 1) :=
  min_add_sub_eq_min_min_add_sub_of_le k a 5 1 (by omega)

/-- The second literal source update has zero overlap with its one-edge new
contribution, so it also satisfies the corrected capped law. -/
theorem min_add_one_sub_zero_eq_min_min_add_one_sub_zero (k a : Nat) :
    Nat.min k (a + 1 - 0) = Nat.min k (Nat.min k a + 1 - 0) :=
  min_add_sub_eq_min_min_add_sub_of_le k a 1 0 (by omega)

/-! ## Exponential subset orbit -/

/-- One delete letter removes one chosen state from a finite subset. -/
def DeleteLetterStep {α : Type*} [DecidableEq α]
    (source target : Finset α) : Prop :=
  ∃ item, target = source.erase item

/-- Execute a heterogeneous word of delete letters. -/
def applyDeleteWord {α : Type*} [DecidableEq α] :
    List α → Finset α → Finset α
  | [], source => source
  | item :: rest, source => applyDeleteWord rest (source.erase item)

theorem reachable_applyDeleteWord {α : Type*} [DecidableEq α]
    (word : List α) (source : Finset α) :
    Relation.ReflTransGen DeleteLetterStep source
      (applyDeleteWord word source) := by
  induction word generalizing source with
  | nil => exact Relation.ReflTransGen.refl
  | cons item rest ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single ⟨item, rfl⟩)
        (ih (source.erase item))

theorem mem_applyDeleteWord_iff {α : Type*} [DecidableEq α]
    (word : List α) (source : Finset α) (item : α) :
    item ∈ applyDeleteWord word source ↔ item ∈ source ∧ item ∉ word := by
  induction word generalizing source with
  | nil => simp [applyDeleteWord]
  | cons head rest ih =>
      rw [applyDeleteWord, ih]
      simp only [Finset.mem_erase, List.mem_cons]
      aesop

/-- Starting from the full set, delete letters reach every subset.  Hence no
polynomial subset-orbit bound follows from monotonicity alone. -/
theorem every_subset_reachable_by_deleteLetters
    {α : Type*} [Fintype α] [DecidableEq α] (target : Finset α) :
    Relation.ReflTransGen DeleteLetterStep Finset.univ target := by
  let word := targetᶜ.toList
  have hreach := reachable_applyDeleteWord word (Finset.univ : Finset α)
  convert hreach using 1
  ext item
  rw [mem_applyDeleteWord_iff]
  simp [word]

/-! ## Ordered boundary data -/

def standardOrder : Fin 4 → Fin 4 := ![0, 1, 2, 3]

def crossedOrder : Fin 4 → Fin 4 := ![0, 2, 1, 3]

/-- Rotation or reversal is the allowed dihedral ambiguity of an ordered
four-port boundary. -/
def DihedrallyEquivalent (first second : Fin 4 → Fin 4) : Prop :=
  ∃ shift : Fin 4,
    (∀ index, second index = first (shift + index)) ∨
    (∀ index, second index = first (shift - index))

/-- Equal underlying port sets do not determine the sewing order. -/
theorem standardOrder_not_dihedrallyEquivalent_crossedOrder :
    ¬ DihedrallyEquivalent standardOrder crossedOrder := by
  rintro ⟨shift, hforward | hreverse⟩
  · fin_cases shift
    · exact (by decide : crossedOrder 1 ≠ standardOrder ((0 : Fin 4) + 1))
        (hforward 1)
    · exact (by decide : crossedOrder 0 ≠ standardOrder ((1 : Fin 4) + 0))
        (hforward 0)
    · exact (by decide : crossedOrder 0 ≠ standardOrder ((2 : Fin 4) + 0))
        (hforward 0)
    · exact (by decide : crossedOrder 0 ≠ standardOrder ((3 : Fin 4) + 0))
        (hforward 0)
  · fin_cases shift
    · exact (by decide : crossedOrder 1 ≠ standardOrder ((0 : Fin 4) - 1))
        (hreverse 1)
    · exact (by decide : crossedOrder 0 ≠ standardOrder ((1 : Fin 4) - 0))
        (hreverse 0)
    · exact (by decide : crossedOrder 0 ≠ standardOrder ((2 : Fin 4) - 0))
        (hreverse 0)
    · exact (by decide : crossedOrder 0 ≠ standardOrder ((3 : Fin 4) - 0))
        (hreverse 0)

/-! ## Curvature scope -/

def thirteenPentagonsOneHeptagon : Multiset Nat :=
  Multiset.replicate 13 5 + {7}

theorem thirteenPentagonsOneHeptagon_minimumFive :
    FaceCycleMinimumFive thirteenPentagonsOneHeptagon := by
  intro n hn
  simp [thirteenPentagonsOneHeptagon] at hn
  rcases hn with rfl | rfl <;> omega

/-- Thirteen pentagons and one heptagon satisfy curvature sum `12`. -/
theorem thirteenPentagonsOneHeptagon_curvature_eq_twelve :
    (thirteenPentagonsOneHeptagon.map faceLengthCurvature).sum = 12 := by
  norm_num [thirteenPentagonsOneHeptagon, faceLengthCurvature]

theorem thirteenPentagonsOneHeptagon_pentagon_count_eq_thirteen :
    thirteenPentagonsOneHeptagon.count 5 = 13 := by
  norm_num [thirteenPentagonsOneHeptagon]

theorem thirteenPentagonsOneHeptagon_negativeWeight_eq_one :
    faceCycleNegativeCurvatureWeight thirteenPentagonsOneHeptagon = 1 := by
  norm_num [thirteenPentagonsOneHeptagon,
    faceCycleNegativeCurvatureWeight]

/-- Curvature `12` and minimum face size five do not imply at most twelve
pentagons.  The valid identity is `p5 = 12 + negativeWeight`. -/
theorem thirteenPentagonsOneHeptagon_not_pentagon_count_le_twelve :
    ¬ thirteenPentagonsOneHeptagon.count 5 ≤ 12 := by
  rw [thirteenPentagonsOneHeptagon_pentagon_count_eq_thirteen]
  omega

end GoertzelV24ReviewNegativeFixtures

end Mettapedia.GraphTheory.FourColor
