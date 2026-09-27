import Mettapedia.GraphTheory.FourColor.EdgeColouringGluing
import Mathlib.Data.Fin.VecNotation

/-!
# A first extension can fail although a joint choice succeeds

This fifteen-edge incidence patch consists of four pentagonal faces of
the dodecahedral graph, with the original vertex labels retained. The
first two faces supply nine edges. The next face adds the path
`1--2--6--7--8`; the last adds `2--3--19`.

The example certifies the edge incidences, proper colourings and failure
of the fixed intermediate choice. It does not construct a spherical
rotation system or instantiate the geometric face-pair theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.DeferredFaceChoiceExample

open GoertzelV24ForkInterfaceSupport

def incidence : Fin 15 → Finset (Fin 20) :=
  ![{0, 1}, {0, 10}, {0, 19}, {1, 2}, {1, 8}, {2, 3}, {2, 6}, {3, 19},
    {6, 7}, {7, 8}, {8, 9}, {9, 10}, {10, 11}, {11, 18}, {18, 19}]

def original : Finset (Fin 15) := {0, 1, 2, 4, 10, 11, 12, 13, 14}

def intermediate : Finset (Fin 15) := original ∪ {3, 6, 8, 9}

def finalEdges : Finset (Fin 15) := Finset.univ

def badChoice : Fin 15 → Fin 3 := ![0, 1, 2, 1, 2, 0, 2, 0, 0, 1, 0, 2, 0, 2, 1]

def jointChoice : Fin 15 → Fin 3 := ![0, 1, 2, 1, 2, 2, 0, 0, 2, 1, 0, 2, 0, 2, 1]

theorem edge_counts : original.card = 9 ∧
    (intermediate \ original).card = 4 ∧ (finalEdges \ intermediate).card = 2 := by
  decide

theorem bad_proper : Proper incidence intermediate badChoice := by decide

theorem joint_proper : Proper incidence finalEdges jointChoice := by decide

theorem original_preserved : ∀ x ∈ original, jointChoice x = badChoice x := by decide

/-- The two new end edges are forced to colour zero by the intermediate
choice, but they meet at vertex three and must have different colours. -/
theorem bad_cannot_extend : ¬ ∃ c : Fin 15 → Fin 3,
    Proper incidence finalEdges c ∧ ∀ x ∈ intermediate, c x = badChoice x := by
  rintro ⟨c, hc, hfix⟩
  have h3 : c 3 = 1 := hfix 3 (by decide)
  have h6 : c 6 = 2 := hfix 6 (by decide)
  have h2 : c 2 = 2 := hfix 2 (by decide)
  have h14 : c 14 = 1 := hfix 14 (by decide)
  have h53 : c 5 ≠ c 3 := hc 5 (by decide) 3 (by decide) (by decide) (by decide)
  have h56 : c 5 ≠ c 6 := hc 5 (by decide) 6 (by decide) (by decide) (by decide)
  have h72 : c 7 ≠ c 2 := hc 7 (by decide) 2 (by decide) (by decide) (by decide)
  have h714 : c 7 ≠ c 14 := hc 7 (by decide) 14 (by decide) (by decide) (by decide)
  rw [h3] at h53
  rw [h6] at h56
  rw [h2] at h72
  rw [h14] at h714
  have h5 : c 5 = 0 := by have := (c 5).isLt; omega
  have h7 : c 7 = 0 := by have := (c 7).isLt; omega
  exact hc 5 (by decide) 7 (by decide) (by decide) (by decide) (h5.trans h7.symm)

/-- A successful choice exists for the pair, although one valid first
choice cannot be kept. This distinguishes existential composition from
preserving every possible intermediate witness. -/
theorem joint_choice_exists_but_not_every_first_choice :
    (∃ c : Fin 15 → Fin 3,
      Proper incidence finalEdges c ∧ ∀ x ∈ original, c x = badChoice x) ∧
    Proper incidence intermediate badChoice ∧
    ¬ (∃ c : Fin 15 → Fin 3,
      Proper incidence finalEdges c ∧ ∀ x ∈ intermediate, c x = badChoice x) :=
  ⟨⟨jointChoice, joint_proper, original_preserved⟩, bad_proper, bad_cannot_extend⟩

end Mettapedia.GraphTheory.FourColor.DeferredFaceChoiceExample
