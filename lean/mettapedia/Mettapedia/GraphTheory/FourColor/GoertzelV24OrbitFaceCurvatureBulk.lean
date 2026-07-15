import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexPathExtraction

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrbitFaceCurvatureBulk

open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexPathExtraction
open GoertzelV24BulkCorridor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Structural sphere data stated on the actual quotient of facial cycles.
The Euler field is the cellular-sphere input; cubicity is computed from the
stored dart incidence. -/
structure OrbitSphericalCubicMapData (RS : RotationSystem V E) where
  cubic : RS.IsCubic
  euler :
    (Fintype.card V : Int) - Fintype.card E +
      Fintype.card (OrbitFace RS) = 2

/-- No facial cycle repeats an underlying edge. This is the exact local
simplicity fact needed to identify facial-walk length with boundary-support
size. -/
def OrbitFaceBoundarySimple (RS : RotationSystem V E) : Prop :=
  ∀ face : OrbitFace RS,
    (orbitFaceBoundary RS face).card = (orbitFaceDarts RS face).card

/-- Fullerene scope on actual facial cycles. -/
def OrbitFaceFullerene (RS : RotationSystem V E) : Prop :=
  ∀ face : OrbitFace RS,
    (orbitFaceBoundary RS face).card = 5 ∨
      (orbitFaceBoundary RS face).card = 6

/-- Total combinatorial curvature over every quotient facial cycle. -/
noncomputable def orbitFaceTotalCurvature (RS : RotationSystem V E) : Int :=
  ∑ face : OrbitFace RS,
    ((6 : Int) - ((orbitFaceBoundary RS face).card : Int))

theorem sum_card_orbitFaceBoundary_eq_card_darts
    (RS : RotationSystem V E) (hsimple : OrbitFaceBoundarySimple RS) :
    ∑ face : OrbitFace RS, (orbitFaceBoundary RS face).card =
      Fintype.card RS.D := by
  calc
    ∑ face : OrbitFace RS, (orbitFaceBoundary RS face).card =
        ∑ face : OrbitFace RS, (orbitFaceDarts RS face).card := by
      apply Finset.sum_congr rfl
      intro face _
      exact hsimple face
    _ = Fintype.card RS.D := sum_card_orbitFaceDarts_eq_card_darts RS

/-- All-face discrete Gauss--Bonnet on the quotient-face rotation model. -/
theorem orbitFaceTotalCurvature_eq_twelve
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (hsimple : OrbitFaceBoundarySimple RS) :
    orbitFaceTotalCurvature RS = 12 := by
  have hvertices := RS.card_darts_eq_three_times_card_vertices hsphere.cubic
  have hedges := RS.card_darts_eq_twice_card_edges
  have hboundaries := sum_card_orbitFaceBoundary_eq_card_darts RS hsimple
  have hverticesInt : (Fintype.card RS.D : Int) =
      3 * Fintype.card V := by
    exact_mod_cast hvertices
  have hedgesInt : (Fintype.card RS.D : Int) =
      2 * Fintype.card E := by
    exact_mod_cast hedges
  have hboundariesInt :
      (∑ face : OrbitFace RS,
        ((orbitFaceBoundary RS face).card : Int)) =
          Fintype.card RS.D := by
    exact_mod_cast hboundaries
  unfold orbitFaceTotalCurvature
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith [hsphere.euler, hverticesInt, hedgesInt, hboundariesInt]

theorem orbitFace_curvature_eq_defectIndicator_of_fullerene
    (RS : RotationSystem V E) (hfullerene : OrbitFaceFullerene RS)
    (face : OrbitFace RS) :
    (6 : Int) - (orbitFaceBoundary RS face).card =
      if (orbitFaceBoundary RS face).card ≠ 6 then 1 else 0 := by
  rcases hfullerene face with hfive | hsix
  · rw [hfive]
    norm_num
  · rw [hsix]
    norm_num

/-- In fullerene scope, total curvature is exactly the number of
nonhexagonal quotient faces. -/
theorem orbitFaceTotalCurvature_eq_faceDefectSet_card_of_fullerene
    (RS : RotationSystem V E) (hfullerene : OrbitFaceFullerene RS) :
    orbitFaceTotalCurvature RS =
      (faceDefectSet (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).card := by
  classical
  calc
    orbitFaceTotalCurvature RS =
        ∑ face : OrbitFace RS,
          if (orbitFaceBoundary RS face).card ≠ 6
          then (1 : Int) else 0 := by
      unfold orbitFaceTotalCurvature
      apply Finset.sum_congr rfl
      intro face _
      exact orbitFace_curvature_eq_defectIndicator_of_fullerene
        RS hfullerene face
    _ = (faceDefectSet (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))).card := by
      simpa [faceDefectSet] using
        (Finset.sum_boole (R := Int)
          (fun face : OrbitFace RS =>
            (orbitFaceBoundary RS face).card ≠ 6) Finset.univ)

/-- A cellular cubic fullerene sphere has exactly twelve quotient facial
cycles that are not hexagons. -/
theorem orbitFaceDefectSet_card_eq_twelve_of_fullerene
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (hsimple : OrbitFaceBoundarySimple RS)
    (hfullerene : OrbitFaceFullerene RS) :
    (faceDefectSet (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).card = 12 := by
  have hdefectCurvature :=
    orbitFaceTotalCurvature_eq_faceDefectSet_card_of_fullerene
      RS hfullerene
  have hcurvature := orbitFaceTotalCurvature_eq_twelve RS hsphere hsimple
  have : ((faceDefectSet (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).card : Int) = 12 :=
    hdefectCurvature.symm.trans hcurvature
  exact_mod_cast this

/-- Structural fullerene L1 theorem on a rotation system. Once the quotient
facial dual is connected, more than `7^(13L-1)` faces force a geodesic dual
path carrying `L` consecutive hexagons. The remaining geometry is to expose
the corresponding primal ladder patch. -/
theorem orbitFaceFullerene_exists_allHexagonalGeodesicBlock
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (hsimple : OrbitFaceBoundarySimple RS)
    (hfullerene : OrbitFaceFullerene RS)
    (hconnected :
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Connected)
    (blockLength : Nat) (hblockLength : 0 < blockLength)
    (hlarge : 7 ^ (13 * blockLength - 1) < Fintype.card (OrbitFace RS)) :
    ∃ start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS)),
      ∃ path :
        (interiorDualGraph (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))).Walk start finish,
        path.IsPath ∧
          path.length =
            (interiorDualGraph (orbitFaceBoundary RS)
              (Finset.univ : Finset (OrbitFace RS))).dist start finish ∧
          ∃ block : Fin 13,
            ∀ offset : Fin blockLength,
              (orbitFaceBoundary RS
                (path.getVert
                  (corridorBlockIndex
                    (defectBudget := 12) block offset).val).1).card = 6 := by
  have hfaceSize : ∀ face ∈ (Finset.univ : Finset (OrbitFace RS)),
      (orbitFaceBoundary RS face).card ≤ 6 := by
    intro face _
    rcases hfullerene face with hfive | hsix <;> omega
  have hdefects :
      (faceDefectSet (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).card ≤ 12 := by
    rw [orbitFaceDefectSet_card_eq_twelve_of_fullerene
      RS hsphere hsimple hfullerene]
  simpa using
    connectedSixFaceDual_exists_allHexagonalGeodesicBlock
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS) hfaceSize hconnected
      12 blockLength hblockLength hdefects hlarge

end GoertzelV24OrbitFaceCurvatureBulk

end Mettapedia.GraphTheory.FourColor
