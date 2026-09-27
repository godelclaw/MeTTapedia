import Mettapedia.GraphTheory.FourColor.EdgeColouringGluing
import Mathlib.Data.Fin.VecNotation

/-!
# A three/two pair can require revising the original colouring

This eighteen-edge incidence patch retains the labels of five faces in
the dodecahedral graph. The first new path is 9--13--14--7, and the
second is 13--12--11. One proper original colouring extends to the first
path but to no colouring of the whole pair. Revising four original edge
colours gives an explicit final colouring.

The kernel certifies incidence, properness, missing colours and
nonextension. A spherical rotation-system instance is not constructed
in this example.
-/

namespace Mettapedia.GraphTheory.FourColor.ThreeTwoChoiceExample

open GoertzelV24ForkInterfaceSupport

def incidence : Fin 18 → Finset (Fin 20) :=
  ![{0, 1}, {0, 10}, {0, 19}, {1, 2}, {1, 8}, {2, 6}, {6, 7}, {7, 8},
    {7, 14}, {8, 9}, {9, 10}, {9, 13}, {10, 11}, {11, 12}, {11, 18},
    {12, 13}, {13, 14}, {18, 19}]

def original : Finset (Fin 18) := {0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 17}
def intermediate : Finset (Fin 18) := original ∪ {8, 11, 16}
def finalEdges : Finset (Fin 18) := Finset.univ

def firstChoice : Fin 18 → Fin 3 :=
  ![2, 1, 0, 1, 0, 2, 0, 2, 1, 1, 2, 0, 0, 0, 2, 0, 2, 1]

def revisedChoice : Fin 18 → Fin 3 :=
  ![2, 0, 1, 1, 0, 2, 0, 2, 1, 1, 2, 0, 1, 0, 2, 1, 2, 0]

theorem edge_counts : original.card = 13 ∧
    (intermediate \ original).card = 3 ∧ (finalEdges \ intermediate).card = 2 := by decide

theorem first_proper : Proper incidence intermediate firstChoice := by decide

theorem original_proper : Proper incidence original firstChoice :=
  proper_of_subset (by decide : original ⊆ intermediate) first_proper

theorem original_missing (q : Fin 3) :
    (q ∉ profile incidence original firstChoice 9 ↔ q = 0) ∧
    (q ∉ profile incidence original firstChoice 7 ↔ q = 1) ∧
    (q ∉ profile incidence original firstChoice 11 ↔ q = 1) := by
  revert q
  decide

/-- The original colours force all three first-path colours. Both new
edges of the second path are then forced to one, despite meeting. -/
theorem original_cannot_extend : ¬ ∃ c : Fin 18 → Fin 3,
    Proper incidence finalEdges c ∧ ∀ x ∈ original, c x = firstChoice x := by
  rintro ⟨c, hc, hfix⟩
  have h6 : c 6 = 0 := hfix 6 (by decide)
  have h7 : c 7 = 2 := hfix 7 (by decide)
  have h9 : c 9 = 1 := hfix 9 (by decide)
  have h10 : c 10 = 2 := hfix 10 (by decide)
  have h12 : c 12 = 0 := hfix 12 (by decide)
  have h14 : c 14 = 2 := hfix 14 (by decide)
  have h119 := hc 11 (by decide) 9 (by decide) (by decide) (by decide)
  have h1110 := hc 11 (by decide) 10 (by decide) (by decide) (by decide)
  have h86 := hc 8 (by decide) 6 (by decide) (by decide) (by decide)
  have h87 := hc 8 (by decide) 7 (by decide) (by decide) (by decide)
  rw [h9] at h119
  rw [h10] at h1110
  rw [h6] at h86
  rw [h7] at h87
  have h11 : c 11 = 0 := by have := (c 11).isLt; omega
  have h8 : c 8 = 1 := by have := (c 8).isLt; omega
  have h1611 := hc 16 (by decide) 11 (by decide) (by decide) (by decide)
  have h168 := hc 16 (by decide) 8 (by decide) (by decide) (by decide)
  rw [h11] at h1611
  rw [h8] at h168
  have h16 : c 16 = 2 := by have := (c 16).isLt; omega
  have h1511 := hc 15 (by decide) 11 (by decide) (by decide) (by decide)
  have h1516 := hc 15 (by decide) 16 (by decide) (by decide) (by decide)
  have h1312 := hc 13 (by decide) 12 (by decide) (by decide) (by decide)
  have h1314 := hc 13 (by decide) 14 (by decide) (by decide) (by decide)
  rw [h11] at h1511
  rw [h16] at h1516
  rw [h12] at h1312
  rw [h14] at h1314
  have h15 : c 15 = 1 := by have := (c 15).isLt; omega
  have h13 : c 13 = 1 := by have := (c 13).isLt; omega
  exact hc 13 (by decide) 15 (by decide) (by decide) (by decide) (h13.trans h15.symm)

theorem revised_proper : Proper incidence finalEdges revisedChoice := by decide

theorem revised_missing (q : Fin 3) :
    (q ∉ profile incidence original revisedChoice 9 ↔ q = 0) ∧
    (q ∉ profile incidence original revisedChoice 7 ↔ q = 1) ∧
    (q ∉ profile incidence original revisedChoice 11 ↔ q = 0) := by
  revert q
  decide

/-- Exactly four original edges have changed; the three first-path
colours are retained. The second path now has colours one and zero. -/
theorem revised_changes :
    (original.filter fun x => revisedChoice x ≠ firstChoice x) = {1, 2, 12, 17} ∧
    (∀ x ∈ intermediate \ original, revisedChoice x = firstChoice x) ∧
    revisedChoice 15 = 1 ∧ revisedChoice 13 = 0 := by decide

/-- This obstruction concerns keeping the original choice. The same
incidence patch has a proper colouring after the original choice changes. -/
theorem original_choice_matters :
    Proper incidence original firstChoice ∧
    (∃ b : Fin 18 → Fin 3, Proper incidence intermediate b ∧
      ∀ x ∈ original, b x = firstChoice x) ∧
    (¬ ∃ c : Fin 18 → Fin 3, Proper incidence finalEdges c ∧
      ∀ x ∈ original, c x = firstChoice x) ∧
    (∃ c : Fin 18 → Fin 3, Proper incidence finalEdges c) :=
  ⟨original_proper, ⟨firstChoice, first_proper, fun _ _ => rfl⟩,
    original_cannot_extend, ⟨revisedChoice, revised_proper⟩⟩

end Mettapedia.GraphTheory.FourColor.ThreeTwoChoiceExample
