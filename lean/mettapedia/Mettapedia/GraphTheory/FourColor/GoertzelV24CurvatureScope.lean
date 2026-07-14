import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mettapedia.GraphTheory.FourColor.RotationSystem

namespace Mettapedia.GraphTheory.FourColor

open scoped BigOperators

namespace GoertzelV24CurvatureScope

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Distinct face edge-sets represented by the face orbits of a rotation
system. This legacy encoding deduplicates equal face boundaries and repeated
edges within a facial walk; use `faceCycleLengths` for all-face counting. -/
def allFaces (RS : RotationSystem V E) : Finset (Finset E) :=
  Finset.univ.image RS.faceEdges

/-- Legacy encoded arithmetic package retained for compatibility. Its
`faceEdgeIncidence` field is assumed over deduplicated face edge-sets, so it is
not the structural all-face theorem; `SphericalCubicMapData` supersedes it. -/
structure CubicSphericalRotationData (RS : RotationSystem V E) where
  cubicIncidence :
    (3 : Int) * Fintype.card V = 2 * Fintype.card E
  faceEdgeIncidence :
    (allFaces RS).sum (fun f => (f.card : Int)) = 2 * Fintype.card E
  euler :
    (Fintype.card V : Int) - Fintype.card E + (allFaces RS).card = 2

/-- Combinatorial face curvature in a cubic spherical map. -/
def faceCurvature (f : Finset E) : Int :=
  6 - f.card

/-- The total combinatorial face curvature over every face orbit. -/
def totalFaceCurvature (RS : RotationSystem V E) : Int :=
  (allFaces RS).sum faceCurvature

/-- Arithmetic consequence of the legacy encoded package. This does not prove
that `allFaces` faithfully enumerates facial walks; the structural replacement
is `faceCycleTotalCurvature_eq_twelve`. -/
theorem totalFaceCurvature_eq_twelve
    (RS : RotationSystem V E) (h : CubicSphericalRotationData RS) :
    totalFaceCurvature RS = 12 := by
  unfold totalFaceCurvature faceCurvature
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [h.faceEdgeIncidence]
  have hcubic := h.cubicIncidence
  have heuler := h.euler
  omega

/-- Face lengths, with one entry for every cycle of the face permutation.
Unlike `allFaces`, this representation retains repeated face boundaries and
counts repeated darts in a facial walk. -/
def faceCycleLengths (RS : RotationSystem V E) : Multiset Nat :=
  RS.phi.partition.parts

/-- Curvature of a face represented by its facial-walk length. -/
def faceLengthCurvature (n : Nat) : Int :=
  6 - n

/-- Total all-face curvature computed from the cycles of the face permutation. -/
def faceCycleTotalCurvature (RS : RotationSystem V E) : Int :=
  (faceCycleLengths RS).map faceLengthCurvature |>.sum

/-- The face permutation partitions all darts, including any fixed darts, so
the sum of its facial-walk lengths is the number of darts. -/
theorem sum_faceCycleLengths_eq_card_darts (RS : RotationSystem V E) :
    (faceCycleLengths RS).sum = Fintype.card RS.D := by
  exact RS.phi.partition.parts_sum

/-- The genuine remaining global geometric input for the curvature theorem.
Cubicity is a predicate computed from the stored dart incidence; the Euler
identity asserts that the rotation system is a cellular sphere map. -/
structure SphericalCubicMapData (RS : RotationSystem V E) where
  cubic : RS.IsCubic
  euler :
    (Fintype.card V : Int) - Fintype.card E +
      (faceCycleLengths RS).card = 2

/-- Cubic incidence is derived from the vertex and edge fibers rather than
stored as an equation in the spherical-map package. -/
theorem cubic_incidence_of_sphericalCubicMapData
    (RS : RotationSystem V E) (h : SphericalCubicMapData RS) :
    (3 : Int) * Fintype.card V = 2 * Fintype.card E := by
  have hvertices := RS.card_darts_eq_three_times_card_vertices h.cubic
  have hedges := RS.card_darts_eq_twice_card_edges
  exact_mod_cast hvertices.symm.trans hedges

/-- Face-edge incidence is derived from the face-cycle partition and the
two-darts-per-edge law. -/
theorem faceCycleLengths_sum_eq_twice_card_edges
    (RS : RotationSystem V E) :
    (faceCycleLengths RS).sum = 2 * Fintype.card E := by
  rw [sum_faceCycleLengths_eq_card_darts]
  exact RS.card_darts_eq_twice_card_edges

/-- Summing `6 - n` over a multiset records six units per face and subtracts
the total facial-walk length. -/
theorem sum_faceLengthCurvature (lengths : Multiset Nat) :
    (lengths.map faceLengthCurvature).sum =
      6 * (lengths.card : Int) - lengths.sum := by
  induction lengths using Multiset.induction_on with
  | empty => simp [faceLengthCurvature]
  | cons n lengths ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      rw [ih]
      unfold faceLengthCurvature
      push_cast
      ring

/-- All-face discrete Gauss--Bonnet for a cellular cubic sphere map. Every
facial cycle occurs with its multiplicity, and faces longer than six contribute
negative curvature. -/
theorem faceCycleTotalCurvature_eq_twelve
    (RS : RotationSystem V E) (h : SphericalCubicMapData RS) :
    faceCycleTotalCurvature RS = 12 := by
  unfold faceCycleTotalCurvature
  rw [sum_faceLengthCurvature]
  rw [faceCycleLengths_sum_eq_twice_card_edges]
  have hcubic := cubic_incidence_of_sphericalCubicMapData RS h
  have heuler := h.euler
  omega

/-- The face-size consequences used by the v24 normal-form budget argument,
separated from any claim that the list is realized by a graph. -/
def NormalFormFaceSizeConsequences (faceSizes : List Nat) : Prop :=
  ∀ n ∈ faceSizes, 5 <= n

/-- The numerical curvature sum of a list of face sizes. -/
def faceSizeCurvatureSum (faceSizes : List Nat) : Int :=
  (faceSizes.map fun n : Nat => (6 : Int) - Int.ofNat n).sum

/-- Thirteen pentagons and one heptagon: a numerical witness that negative face
curvature permits more than twelve pentagons while preserving total curvature
twelve and minimum face size five. This is an arithmetic witness, not a graph
realization. -/
def thirteenPentagonsOneHeptagon : List Nat :=
  List.replicate 13 5 ++ [7]

theorem thirteenPentagonsOneHeptagon_minFaceSize :
    NormalFormFaceSizeConsequences thirteenPentagonsOneHeptagon := by
  simp [NormalFormFaceSizeConsequences, thirteenPentagonsOneHeptagon]

theorem thirteenPentagonsOneHeptagon_curvature :
    faceSizeCurvatureSum thirteenPentagonsOneHeptagon = 12 := by
  decide

theorem thirteenPentagonsOneHeptagon_pentagonCount :
    thirteenPentagonsOneHeptagon.count 5 = 13 := by
  decide

/-- Minimum face size five and total curvature twelve do not imply a cap of
twelve pentagons. -/
theorem normalFormFaceSizeConsequences_do_not_imply_pentagonCount_le_twelve :
    ∃ faceSizes : List Nat,
      NormalFormFaceSizeConsequences faceSizes ∧
      faceSizeCurvatureSum faceSizes = 12 ∧
      ¬ faceSizes.count 5 <= 12 := by
  refine ⟨thirteenPentagonsOneHeptagon,
    thirteenPentagonsOneHeptagon_minFaceSize,
    thirteenPentagonsOneHeptagon_curvature, ?_⟩
  rw [thirteenPentagonsOneHeptagon_pentagonCount]
  omega

/-- The fullerene face restriction: every face has size five or six. -/
def FullereneFaceRestriction (faceSizes : List Nat) : Prop :=
  ∀ n ∈ faceSizes, n = 5 ∨ n = 6

/-- The total magnitude of negative curvature contributed by faces longer
than six. -/
def negativeCurvatureWeight (faceSizes : List Nat) : Nat :=
  (faceSizes.map fun n => n - 6).sum

/-- An explicit weighted-curvature hypothesis ruling out negative curvature. -/
def ZeroNegativeCurvatureWeight (faceSizes : List Nat) : Prop :=
  negativeCurvatureWeight faceSizes = 0

end GoertzelV24CurvatureScope

end Mettapedia.GraphTheory.FourColor
