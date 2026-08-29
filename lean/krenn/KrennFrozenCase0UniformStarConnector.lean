import KrennDoilyVertexStars
import KrennFrozenCase0AdjugateLayer
import Mathlib

/-!
Uniform C6 non-collapse connector from every adjugate slot to a K6 vertex
star.

For each of the eighteen `(vertex, colour)` slots in the frozen case-0
system, the two adjugate kills are exactly the two cycle-edge diagonal
co-sums incident to that vertex.  Three additional chord-side co-sum kills
complete its vertex star.  The final theorem is deliberately conditional on
those three kills: deriving them from the balanced layers is the remaining
mathematical harvest obligation.

All finite maps below were checked against the canonical frozen system and
the C6 support before being serialized here.
-/

namespace Krenn.FrozenCase0UniformStarConnector

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.DoilyPotential
open Krenn.DoilyVertexStars
open Krenn.FrozenCase0AdjugateLayer

/-- The three diagonal colour slices of the 75-coordinate frozen C6 system,
in the lexicographic K6 edge order. -/
def diagonal {R : Type*} [CommRing R] (values : Fin 75 → R) : Fin 3 → Fin 15 → R := ![
  ![values 0, values 3, values 6, values 9, values 17,
    values 25, values 33, values 41, values 44, values 47,
    values 50, values 53, values 61, values 69, values 72],
  ![values 1, values 4, values 7, values 12, values 20,
    values 28, values 36, values 42, values 45, values 48,
    values 51, values 56, values 64, values 70, values 73],
  ![values 2, values 5, values 8, values 16, values 24,
    values 32, values 40, values 43, values 46, values 49,
    values 52, values 60, values 68, values 71, values 74]
]

/-- The vertex and colour represented by each frozen adjugate slot. -/
def slotVertex : Fin 18 → Fin 6 := ![
  0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5
]

def slotColour : Fin 18 → Fin 3 := ![
  0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2
]

/-- The two C6-side co-sum edges furnished by the left and right adjugate
identities for each slot. -/
def slotLeftEdge : Fin 18 → Fin 15 := ![
  3, 3, 3, 5, 5, 5, 5, 5, 5, 6, 6, 6, 3, 3, 3, 4, 4, 4
]

def slotRightEdge : Fin 18 → Fin 15 := ![
  4, 4, 4, 6, 6, 6, 11, 11, 11, 12, 12, 12, 12, 12, 12, 11, 11, 11
]

/-- The remaining three chord-side edges in the corresponding K6 vertex
star. -/
def slotChordEdge : Fin 18 → Fin 3 → Fin 15 := ![
  ![0, 1, 2], ![0, 1, 2], ![0, 1, 2],
  ![0, 7, 8], ![0, 7, 8], ![0, 7, 8],
  ![1, 9, 10], ![1, 9, 10], ![1, 9, 10],
  ![2, 9, 13], ![2, 9, 13], ![2, 9, 13],
  ![7, 10, 14], ![7, 10, 14], ![7, 10, 14],
  ![8, 13, 14], ![8, 13, 14], ![8, 13, 14]
]

/-- The three frozen monochromatic source rows, one per colour. -/
def monoSourceIndex : Fin 3 → Fin 747 := ![744, 745, 746]

/-- Every left deflated amplitude is literally the diagonal co-sum of its
recorded cycle edge and colour. -/
theorem slotLeft_eq_coSum {R : Type*} [CommRing R]
    (values : Fin 75 → R) (slot : Fin 18) :
    slotLeft values slot =
      coSum (diagonal values (slotColour slot)) (slotLeftEdge slot) := by
  fin_cases slot <;>
    simp [slotLeft, diagonal, slotColour, slotLeftEdge, coSum]

/-- The same exact identification for the right adjugate amplitude. -/
theorem slotRight_eq_coSum {R : Type*} [CommRing R]
    (values : Fin 75 → R) (slot : Fin 18) :
    slotRight values slot =
      coSum (diagonal values (slotColour slot)) (slotRightEdge slot) := by
  fin_cases slot <;>
    simp [slotRight, diagonal, slotColour, slotRightEdge, coSum]

/- Each frozen monochromatic source row is the normalized total matching
sum of its corresponding diagonal colour slice. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem monoSource_eq {R : Type*} [CommRing R]
    (values : Fin 75 → R) (colour : Fin 3) :
    sourceValue values (monoSourceIndex colour) =
      totalMatching (matchingProduct (diagonal values colour)) - 1 := by
  fin_cases colour <;>
    simp [sourceValue, monoSourceIndex, diagonal, totalMatching,
      matchingProduct, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly] <;> ring

/-- A monochromatic row is retained by the pre-collapse base system. -/
theorem monoSource_not_determinant (colour : Fin 3) (slot : Fin 18) :
    determinantSourceIndex slot ≠ monoSourceIndex colour := by
  fin_cases colour <;> fin_cases slot <;> decide

/-- The original C6 case-0 system has an exact top-level split: either all
eighteen determinants vanish and it enters the all-collapse system, or one
concrete determinant is nonzero. -/
theorem base_allCollapse_or_exists_noncollapse_slot
    {R : Type*} [CommRing R] (values : Fin 75 → R)
    (base : BaseCommonZero values) :
    Krenn.FrozenCase0System.CommonZero values ∨
      ∃ slot, slotDeterminant values slot ≠ 0 := by
  classical
  by_cases hcollapse : ∀ slot, slotDeterminant values slot = 0
  · exact Or.inl (full_common_zero_of_base_and_all_collapse values base hcollapse)
  · right
    push Not at hcollapse
    exact hcollapse

/-- On the non-collapse side of the top-level split, the two incident C6
co-sums are already killed by the two one-defect adjugate identities. -/
theorem base_allCollapse_or_exists_two_cycle_kills
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (values : Fin 75 → R) (base : BaseCommonZero values) :
    Krenn.FrozenCase0System.CommonZero values ∨
      ∃ slot, slotDeterminant values slot ≠ 0 ∧
        coSum (diagonal values (slotColour slot)) (slotLeftEdge slot) = 0 ∧
        coSum (diagonal values (slotColour slot)) (slotRightEdge slot) = 0 := by
  rcases base_allCollapse_or_exists_noncollapse_slot values base with full | ⟨slot, hdet⟩
  · exact Or.inl full
  · right
    refine ⟨slot, hdet, ?_, ?_⟩
    · rw [← slotLeft_eq_coSum]
      exact (left_kill_or_collapse values base slot).resolve_left hdet
    · rw [← slotRight_eq_coSum]
      exact (right_kill_or_collapse values base slot).resolve_left hdet

/- The two adjugate edges and three chord edges are exactly the five edges
of the associated vertex star. -/
set_option maxHeartbeats 5000000 in
theorem vertexStar_edge_cases (slot : Fin 18) (edge : Fin 15)
    (hstar : edge ∈ vertexStarEdges (slotVertex slot)) :
    edge = slotLeftEdge slot ∨ edge = slotRightEdge slot ∨
      ∃ chord, edge = slotChordEdge slot chord := by
  fin_cases slot <;> fin_cases edge <;>
    simp_all [slotVertex, slotLeftEdge, slotRightEdge, slotChordEdge,
      vertexStarEdges] <;>
    first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩

/-- A non-collapse slot plus the three balanced-layer chord kills at its
vertex is incompatible with the original pre-collapse frozen system. -/
theorem no_base_witness_of_noncollapse_and_star_chord_kills
    {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values) (slot : Fin 18)
    (hdet : slotDeterminant values slot ≠ 0)
    (hchord : ∀ chord,
      coSum (diagonal values (slotColour slot)) (slotChordEdge slot chord) = 0) :
    False := by
  have hleft : coSum (diagonal values (slotColour slot)) (slotLeftEdge slot) = 0 := by
    rw [← slotLeft_eq_coSum]
    exact (left_kill_or_collapse values base slot).resolve_left hdet
  have hright : coSum (diagonal values (slotColour slot)) (slotRightEdge slot) = 0 := by
    rw [← slotRight_eq_coSum]
    exact (right_kill_or_collapse values base slot).resolve_left hdet
  have hsource := base (monoSourceIndex (slotColour slot))
    (fun determinant => monoSource_not_determinant (slotColour slot) determinant)
  rw [monoSource_eq] at hsource
  have hmono : totalMatching (matchingProduct (diagonal values (slotColour slot))) = 1 := by
    linear_combination hsource
  exact no_normalized_diagonal_witness_of_vertex_star_kills
    (slotVertex slot) (diagonal values (slotColour slot))
    (fun edge hstar => by
      rcases vertexStar_edge_cases slot edge hstar with hleftEdge | hrightEdge | ⟨chord, hchordEdge⟩
      · simpa [hleftEdge] using hleft
      · simpa [hrightEdge] using hright
      · simpa [hchordEdge] using hchord chord)
    hmono

#print axioms Krenn.FrozenCase0UniformStarConnector.slotLeft_eq_coSum
#print axioms Krenn.FrozenCase0UniformStarConnector.slotRight_eq_coSum
#print axioms Krenn.FrozenCase0UniformStarConnector.monoSource_eq
#print axioms Krenn.FrozenCase0UniformStarConnector.base_allCollapse_or_exists_noncollapse_slot
#print axioms Krenn.FrozenCase0UniformStarConnector.base_allCollapse_or_exists_two_cycle_kills
#print axioms Krenn.FrozenCase0UniformStarConnector.no_base_witness_of_noncollapse_and_star_chord_kills

end Krenn.FrozenCase0UniformStarConnector
