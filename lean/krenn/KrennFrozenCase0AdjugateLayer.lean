import KrennAdjugateDichotomy
import KrennFrozenCase0System
import Mathlib

/-!
Exact case-0 C6 connector for the non-collapse split.

This file is generated only after term-for-term reconstruction of the
canonical 747-generator frozen system.  Each of the eighteen slots has
two actual one-defect equations in that system.  Lean expands those
source equations and checks their adjugate decompositions with `ring`.
The base system is the same frozen source with exactly those eighteen
determinant positions omitted; adding every determinant back recovers
the all-collapse system consumed by the certificate corpus.
-/

namespace Krenn.FrozenCase0AdjugateLayer

open MvPolynomial
open Krenn.SparseCertificate

noncomputable def sourceValue {R : Type*} [CommRing R]
    (values : Fin 75 → R) (source : Fin 747) : R :=
  eval₂Hom (Int.castRingHom R) values
    (Krenn.FrozenCase0System.equations source).toPoly

/-- Two one-defect source equations for every `(vertex, colour)` slot. -/
def l1SourceIndex : Fin 18 → Fin 2 → Fin 747 := ![
  ![716, 718],
  ![647, 719],
  ![715, 717],
  ![686, 688],
  ![646, 695],
  ![702, 704],
  ![658, 659],
  ![645, 671],
  ![678, 679],
  ![655, 656],
  ![644, 669],
  ![682, 683],
  ![642, 654],
  ![667, 668],
  ![684, 685],
  ![643, 657],
  ![666, 670],
  ![680, 681]
]

/-- The actual frozen source position of the corresponding determinant. -/
def determinantSourceIndex : Fin 18 → Fin 747 := ![
  6,
  1,
  4,
  37,
  3,
  35,
  36,
  38,
  39,
  41,
  42,
  43,
  0,
  7,
  21,
  2,
  33,
  34
]

/-- The original, pre-all-collapse C6 equations: all frozen source rows
except the eighteen recorded determinant rows. -/
noncomputable def BaseCommonZero {R : Type*} [CommRing R]
    (values : Fin 75 → R) : Prop :=
  ∀ source, (∀ slot, determinantSourceIndex slot ≠ source) →
    sourceValue values source = 0

/-- First left-neighbour coefficient. -/
def slotA1 {R : Type*} [CommRing R] (values : Fin 75 → R) : Fin 18 → R := ![
  (values 11),
  (1),
  (values 10),
  (values 27),
  (1),
  (values 26),
  (1),
  (values 27),
  (values 30),
  (1),
  (values 35),
  (values 38),
  (1),
  (values 11),
  (values 14),
  (1),
  (values 19),
  (values 22)
]

/-- First right-neighbour coefficient. -/
def slotB1 {R : Type*} [CommRing R] (values : Fin 75 → R) : Fin 18 → R := ![
  (values 19),
  (1),
  (values 18),
  (values 35),
  (1),
  (values 34),
  (values 55),
  (1),
  (values 54),
  (values 63),
  (1),
  (values 62),
  (1),
  (values 63),
  (values 66),
  (1),
  (values 55),
  (values 58)
]

/-- Second left-neighbour coefficient. -/
def slotA2 {R : Type*} [CommRing R] (values : Fin 75 → R) : Fin 18 → R := ![
  (values 14),
  (values 15),
  (values 13),
  (values 30),
  (values 31),
  (values 29),
  (values 26),
  (values 29),
  (values 31),
  (values 34),
  (values 37),
  (values 39),
  (values 10),
  (values 13),
  (values 15),
  (values 18),
  (values 21),
  (values 23)
]

/-- Second right-neighbour coefficient. -/
def slotB2 {R : Type*} [CommRing R] (values : Fin 75 → R) : Fin 18 → R := ![
  (values 22),
  (values 23),
  (values 21),
  (values 38),
  (values 39),
  (values 37),
  (values 58),
  (values 59),
  (values 57),
  (values 66),
  (values 67),
  (values 65),
  (values 62),
  (values 65),
  (values 67),
  (values 54),
  (values 57),
  (values 59)
]

/-- First deflated amplitude. -/
def slotLeft {R : Type*} [CommRing R] (values : Fin 75 → R) : Fin 18 → R := ![
  (values 25 * values 69) + (values 33 * values 53) + (values 44 * values 47),
  (values 28 * values 70) + (values 36 * values 56) + (values 45 * values 48),
  (values 32 * values 71) + (values 40 * values 60) + (values 46 * values 49),
  (values 6 * values 72) + (values 9 * values 69) + (values 17 * values 61),
  (values 7 * values 73) + (values 12 * values 70) + (values 20 * values 64),
  (values 8 * values 74) + (values 16 * values 71) + (values 24 * values 68),
  (values 6 * values 72) + (values 9 * values 69) + (values 17 * values 61),
  (values 7 * values 73) + (values 12 * values 70) + (values 20 * values 64),
  (values 8 * values 74) + (values 16 * values 71) + (values 24 * values 68),
  (values 3 * values 72) + (values 9 * values 53) + (values 17 * values 50),
  (values 4 * values 73) + (values 12 * values 56) + (values 20 * values 51),
  (values 5 * values 74) + (values 16 * values 60) + (values 24 * values 52),
  (values 25 * values 69) + (values 33 * values 53) + (values 44 * values 47),
  (values 28 * values 70) + (values 36 * values 56) + (values 45 * values 48),
  (values 32 * values 71) + (values 40 * values 60) + (values 46 * values 49),
  (values 25 * values 61) + (values 33 * values 50) + (values 41 * values 47),
  (values 28 * values 64) + (values 36 * values 51) + (values 42 * values 48),
  (values 32 * values 68) + (values 40 * values 52) + (values 43 * values 49)
]

/-- Second deflated amplitude. -/
def slotRight {R : Type*} [CommRing R] (values : Fin 75 → R) : Fin 18 → R := ![
  (values 25 * values 61) + (values 33 * values 50) + (values 41 * values 47),
  (values 28 * values 64) + (values 36 * values 51) + (values 42 * values 48),
  (values 32 * values 68) + (values 40 * values 52) + (values 43 * values 49),
  (values 3 * values 72) + (values 9 * values 53) + (values 17 * values 50),
  (values 4 * values 73) + (values 12 * values 56) + (values 20 * values 51),
  (values 5 * values 74) + (values 16 * values 60) + (values 24 * values 52),
  (values 0 * values 61) + (values 6 * values 41) + (values 9 * values 33),
  (values 1 * values 64) + (values 7 * values 42) + (values 12 * values 36),
  (values 2 * values 68) + (values 8 * values 43) + (values 16 * values 40),
  (values 0 * values 53) + (values 3 * values 44) + (values 17 * values 25),
  (values 1 * values 56) + (values 4 * values 45) + (values 20 * values 28),
  (values 2 * values 60) + (values 5 * values 46) + (values 24 * values 32),
  (values 0 * values 53) + (values 3 * values 44) + (values 17 * values 25),
  (values 1 * values 56) + (values 4 * values 45) + (values 20 * values 28),
  (values 2 * values 60) + (values 5 * values 46) + (values 24 * values 32),
  (values 0 * values 61) + (values 6 * values 41) + (values 9 * values 33),
  (values 1 * values 64) + (values 7 * values 42) + (values 12 * values 36),
  (values 2 * values 68) + (values 8 * values 43) + (values 16 * values 40)
]

/-- The literal two-by-two determinant in each frozen slot. -/
def slotDeterminant {R : Type*} [CommRing R] (values : Fin 75 → R)
    (slot : Fin 18) : R :=
  slotA1 values slot * slotB2 values slot -
    slotA2 values slot * slotB1 values slot

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem first_l1_source_eq {R : Type*} [CommRing R]
    (values : Fin 75 → R) (slot : Fin 18) :
    sourceValue values (l1SourceIndex slot 0) =
      slotA1 values slot * slotLeft values slot +
        slotB1 values slot * slotRight values slot := by
  fin_cases slot <;> simp [sourceValue, l1SourceIndex, slotA1, slotB1, slotLeft, slotRight, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly] <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem second_l1_source_eq {R : Type*} [CommRing R]
    (values : Fin 75 → R) (slot : Fin 18) :
    sourceValue values (l1SourceIndex slot 1) =
      slotA2 values slot * slotLeft values slot +
        slotB2 values slot * slotRight values slot := by
  fin_cases slot <;> simp [sourceValue, l1SourceIndex, slotA2, slotB2, slotLeft, slotRight, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly] <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem determinant_source_eq {R : Type*} [CommRing R]
    (values : Fin 75 → R) (slot : Fin 18) :
    sourceValue values (determinantSourceIndex slot) =
      slotDeterminant values slot := by
  fin_cases slot <;> simp [sourceValue, determinantSourceIndex, slotA1, slotB1, slotA2, slotB2, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant] <;> ring

/-- A one-defect row is never mistaken for one of the added collapse
determinants.  This finite disjointness check is part of the bridge. -/
theorem l1_source_not_determinant (slot : Fin 18) (row : Fin 2)
    (determinant : Fin 18) :
    determinantSourceIndex determinant ≠ l1SourceIndex slot row := by
  fin_cases slot <;> fin_cases row <;> fin_cases determinant <;> decide

/-- Every common zero of the original pre-collapse case-0 system lies on
the all-collapse locus or has a concrete left deflated-amplitude kill. -/
theorem left_kill_or_collapse {R : Type*} [CommRing R] [NoZeroDivisors R]
    (values : Fin 75 → R)
    (base : BaseCommonZero values) (slot : Fin 18) :
    slotDeterminant values slot = 0 ∨ slotLeft values slot = 0 := by
  change slotA1 values slot * slotB2 values slot -
      slotA2 values slot * slotB1 values slot = 0 ∨
        slotLeft values slot = 0
  refine Krenn.AdjugateDichotomy.left_kill_or_collapse
    (slotA1 values slot) (slotB1 values slot)
    (slotA2 values slot) (slotB2 values slot)
    (slotLeft values slot) (slotRight values slot) ?_ ?_
  · have h := base (l1SourceIndex slot 0)
      (fun determinant => l1_source_not_determinant slot 0 determinant)
    rw [first_l1_source_eq] at h
    exact h
  · have h := base (l1SourceIndex slot 1)
      (fun determinant => l1_source_not_determinant slot 1 determinant)
    rw [second_l1_source_eq] at h
    exact h

/-- The symmetric right deflated-amplitude alternative. -/
theorem right_kill_or_collapse {R : Type*} [CommRing R] [NoZeroDivisors R]
    (values : Fin 75 → R)
    (base : BaseCommonZero values) (slot : Fin 18) :
    slotDeterminant values slot = 0 ∨ slotRight values slot = 0 := by
  change slotA1 values slot * slotB2 values slot -
      slotA2 values slot * slotB1 values slot = 0 ∨
        slotRight values slot = 0
  refine Krenn.AdjugateDichotomy.right_kill_or_collapse
    (slotA1 values slot) (slotB1 values slot)
    (slotA2 values slot) (slotB2 values slot)
    (slotLeft values slot) (slotRight values slot) ?_ ?_
  · have h := base (l1SourceIndex slot 0)
      (fun determinant => l1_source_not_determinant slot 0 determinant)
    rw [first_l1_source_eq] at h
    exact h
  · have h := base (l1SourceIndex slot 1)
      (fun determinant => l1_source_not_determinant slot 1 determinant)
    rw [second_l1_source_eq] at h
    exact h

/-- Adding every slot determinant to a base common zero recovers the
complete frozen all-collapse system. -/
theorem full_common_zero_of_base_and_all_collapse
    {R : Type*} [CommRing R] (values : Fin 75 → R)
    (base : BaseCommonZero values)
    (collapse : ∀ slot, slotDeterminant values slot = 0) :
    Krenn.FrozenCase0System.CommonZero values := by
  intro source
  by_cases hdet : ∃ slot, determinantSourceIndex slot = source
  · rcases hdet with ⟨slot, hslot⟩
    rw [← hslot]
    change sourceValue values (determinantSourceIndex slot) = 0
    rw [determinant_source_eq]
    exact collapse slot
  · exact base source (fun slot equal => hdet ⟨slot, equal⟩)

/-- The full exact split of the original case-0 C6 system: either it
enters the already-certified all-collapse system, or an explicit left
deflated amplitude is zero. -/
theorem base_all_collapse_or_exists_left_kill
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (values : Fin 75 → R) (base : BaseCommonZero values) :
    Krenn.FrozenCase0System.CommonZero values ∨
      ∃ slot, slotLeft values slot = 0 := by
  rcases Krenn.AdjugateDichotomy.all_collapse_or_exists_kill
      (slotDeterminant values) (slotLeft values)
      (left_kill_or_collapse values base) with collapse | kill
  · exact Or.inl (full_common_zero_of_base_and_all_collapse values base collapse)
  · exact Or.inr kill

#print axioms Krenn.FrozenCase0AdjugateLayer.left_kill_or_collapse
#print axioms Krenn.FrozenCase0AdjugateLayer.right_kill_or_collapse
#print axioms Krenn.FrozenCase0AdjugateLayer.base_all_collapse_or_exists_left_kill

end Krenn.FrozenCase0AdjugateLayer
