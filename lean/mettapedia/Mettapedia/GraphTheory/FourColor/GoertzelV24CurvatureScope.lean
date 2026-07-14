import Mathlib.Tactic
import Mettapedia.GraphTheory.FourColor.RotationSystem

namespace Mettapedia.GraphTheory.FourColor

open scoped BigOperators

namespace GoertzelV24CurvatureScope

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- All face edge-sets represented by the face orbits of a rotation system. -/
def allFaces (RS : RotationSystem V E) : Finset (Finset E) :=
  Finset.univ.image RS.faceEdges

/-- The three global counting identities needed for the spherical cubic
curvature calculation. The bare `RotationSystem` API does not yet derive these
incidence and Euler identities, so this structure records the strengthened
geometric input explicitly. -/
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

/-- Discrete Gauss--Bonnet for a cubic spherical rotation package: every face,
including faces of length at least seven with negative contribution, occurs in
the sum. -/
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
