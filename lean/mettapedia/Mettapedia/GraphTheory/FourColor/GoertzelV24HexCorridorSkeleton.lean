import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexCorridorSkeleton

open GoertzelV24BulkCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24CurvatureScope

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The incidence-level corridor delivered before L1's finite local primal
classification: a sequence of distinct hexagonal quotient faces with every
consecutive pair adjacent in the full facial dual. -/
structure OrbitHexCorridorSkeleton (RS : RotationSystem V E)
    (corridorLength : Nat) where
  faceAt : Fin corridorLength →
    AmbientFace (Finset.univ : Finset (OrbitFace RS))
  faceAt_injective : Function.Injective faceAt
  hexagonal : ∀ offset,
    (orbitFaceBoundary RS (faceAt offset).1).card = 6
  consecutive_adjacent : ∀ left right,
    right.val = left.val + 1 →
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Adj
          (faceAt left) (faceAt right)

/-- An index of a genuine consecutive step in a corridor. -/
structure CorridorStep (corridorLength : Nat) where
  left : Fin corridorLength
  right_in_range : left.val + 1 < corridorLength

namespace CorridorStep

/-- The face index immediately following a corridor step's left endpoint. -/
def right {corridorLength : Nat} (step : CorridorStep corridorLength) :
    Fin corridorLength :=
  ⟨step.left.val + 1, step.right_in_range⟩

@[simp]
theorem right_val {corridorLength : Nat} (step : CorridorStep corridorLength) :
    step.right.val = step.left.val + 1 :=
  rfl

end CorridorStep

theorem OrbitHexCorridorSkeleton.faceAt_ne
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    {left right : Fin corridorLength} (hne : left ≠ right) :
    corridor.faceAt left ≠ corridor.faceAt right :=
  fun heq => hne (corridor.faceAt_injective heq)

/-- Every consecutive corridor pair has a concrete primal rung edge shared by
the two hexagonal facial boundaries. -/
theorem OrbitHexCorridorSkeleton.exists_consecutive_rungEdge
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    {left right : Fin corridorLength}
    (hsuccessor : right.val = left.val + 1) :
    ∃ edge,
      edge ∈ interiorEdgeSupport (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) ∧
      edge ∈ orbitFaceBoundary RS (corridor.faceAt left).1 ∧
      edge ∈ orbitFaceBoundary RS (corridor.faceAt right).1 := by
  exact (interiorDualGraph_adj_iff (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).1
      (corridor.consecutive_adjacent left right hsuccessor) |>.2

/-- Once distinct quotient faces share at most one edge, every corridor step
has a unique primal rung. -/
theorem OrbitHexCorridorSkeleton.existsUnique_rungEdge
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : CorridorStep corridorLength) :
    ∃! edge,
      edge ∈ sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))
        (corridor.faceAt step.left).1 (corridor.faceAt step.right).1 := by
  exact existsUnique_sharedInteriorEdge_of_adj_of_pairwiseUnique
    (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS)) hunique
      (corridor.consecutive_adjacent step.left step.right rfl)

/-- The canonical primal rung of a corridor step when facial intersections
are pairwise edge-simple. -/
noncomputable def OrbitHexCorridorSkeleton.rungEdge
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : CorridorStep corridorLength) : E :=
  sharedInteriorEdgeOfAdjOfPairwiseUnique
    (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS)) hunique
      (corridor.consecutive_adjacent step.left step.right rfl)

theorem OrbitHexCorridorSkeleton.rungEdge_mem_left
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : CorridorStep corridorLength) :
    corridor.rungEdge hunique step ∈
      orbitFaceBoundary RS (corridor.faceAt step.left).1 := by
  exact sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_left
    (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS)) hunique
      (corridor.consecutive_adjacent step.left step.right rfl)

theorem OrbitHexCorridorSkeleton.rungEdge_mem_right
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : CorridorStep corridorLength) :
    corridor.rungEdge hunique step ∈
      orbitFaceBoundary RS (corridor.faceAt step.right).1 := by
  exact sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
    (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS)) hunique
      (corridor.consecutive_adjacent step.left step.right rfl)

theorem OrbitHexCorridorSkeleton.rungEdge_eq_of_shared
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : CorridorStep corridorLength) {edge : E}
    (hshared : edge ∈ sharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (corridor.faceAt step.left).1 (corridor.faceAt step.right).1) :
    corridor.rungEdge hunique step = edge := by
  exact sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
    (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS)) hunique
      (corridor.consecutive_adjacent step.left step.right rfl) hshared

/-- An all-hex block whose exported index bound lies on a simple dual path
gives a genuine corridor skeleton rather than a clamped `getVert` sample. -/
def OrbitHexCorridorSkeleton.ofPathBlock
    (RS : RotationSystem V E) {start finish :
      AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (path : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (hpath : path.IsPath) (corridorLength : Nat)
    (hpositionBound : 13 * corridorLength ≤ path.length + 1)
    (block : Fin 13)
    (hhexagonal : ∀ offset : Fin corridorLength,
      (orbitFaceBoundary RS
        (path.getVert
          (corridorBlockIndex
            (defectBudget := 12) block offset).val).1).card = 6) :
    OrbitHexCorridorSkeleton RS corridorLength where
  faceAt := fun offset =>
    path.getVert
      (corridorBlockIndex (defectBudget := 12) block offset).val
  faceAt_injective := by
    intro left right hfaces
    have hleftBound :
        (corridorBlockIndex (defectBudget := 12) block left).val ≤
          path.length := by
      have hindex := (corridorBlockIndex
        (defectBudget := 12) block left).isLt
      omega
    have hrightBound :
        (corridorBlockIndex (defectBudget := 12) block right).val ≤
          path.length := by
      have hindex := (corridorBlockIndex
        (defectBudget := 12) block right).isLt
      omega
    have hindices := hpath.getVert_injOn
      (by simpa using hleftBound) (by simpa using hrightBound) hfaces
    apply Fin.ext
    change block.val * corridorLength + left.val =
      block.val * corridorLength + right.val at hindices
    omega
  hexagonal := hhexagonal
  consecutive_adjacent := by
    intro left right hsuccessor
    have hrightBound :
        (corridorBlockIndex (defectBudget := 12) block right).val ≤
          path.length := by
      have hindex := (corridorBlockIndex
        (defectBudget := 12) block right).isLt
      omega
    have hleftStrict :
        (corridorBlockIndex (defectBudget := 12) block left).val <
          path.length := by
      change block.val * corridorLength + left.val < path.length
      change block.val * corridorLength + right.val ≤ path.length at hrightBound
      omega
    have hadj := path.adj_getVert_succ hleftStrict
    change (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (path.getVert (block.val * corridorLength + left.val))
        (path.getVert (block.val * corridorLength + right.val))
    change (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (path.getVert (block.val * corridorLength + left.val))
        (path.getVert ((block.val * corridorLength + left.val) + 1)) at hadj
    simpa only [hsuccessor, Nat.add_assoc] using hadj

/-- Structural fullerene L1 up to its explicitly separated finite local
classification: sufficiently many quotient faces force an incidence-level
hexagonal corridor of the requested length. -/
theorem orbitFaceFullerene_exists_hexCorridorSkeleton
    (RS : RotationSystem V E) (hsphere : SphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hfullerene : OrbitFaceFullerene RS)
    (hprimal : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS)
    (corridorLength : Nat) (hpositive : 0 < corridorLength)
    (hlarge : 7 ^ (13 * corridorLength - 1) <
      Fintype.card (OrbitFace RS)) :
    Nonempty (OrbitHexCorridorSkeleton RS corridorLength) := by
  obtain ⟨start, finish, path, hpath, _hgeodesic, hpositionBound,
      block, hhexagonal⟩ :=
    orbitFaceFullerene_exists_allHexagonalGeodesicBlock
      RS hsphere htwoSided hfullerene hprimal hrotation
        corridorLength hpositive hlarge
  exact ⟨OrbitHexCorridorSkeleton.ofPathBlock RS path hpath
    corridorLength hpositionBound block hhexagonal⟩

end

end GoertzelV24HexCorridorSkeleton

end Mettapedia.GraphTheory.FourColor
