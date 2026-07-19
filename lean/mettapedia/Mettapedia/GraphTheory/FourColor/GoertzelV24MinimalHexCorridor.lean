import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorSlab
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceIntersections
import Mettapedia.GraphTheory.FourColor.GoertzelV24WeightedOrbitFaceCorridor

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalHexCorridor

open GoertzelV24CleanHexCorridor
open GoertzelV24CurvatureScope
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WeightedOrbitFaceCorridor
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The quotient-face and face-cycle spherical Euler packages are equivalent:
the two face carriers count the same permutation orbits. -/
def sphericalCubicMapData_of_orbitSphericalCubicMapData
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS) :
    SphericalCubicMapData RS where
  cubic := hsphere.cubic
  euler := by
    rw [← GoertzelV24FaceOrbitPartitionBridge.card_orbitFace_eq_faceCycleLengths_card]
    exact hsphere.euler

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Structural L1 corridor slab for a graph-backed vertex-minimal Tait
counterexample. Minimality supplies canonical rung uniqueness directly, so no
cyclic-five normal-form assumption is present. -/
theorem orbitFaceFullerene_exists_widthFourCleanHexCorridorSlab
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hfullerene : OrbitFaceFullerene graphData.toRotationSystem)
    (corridorLength : Nat) (hpositive : 0 < corridorLength)
    (hlarge : 7 ^ (85 * corridorLength - 1) <
      Fintype.card (OrbitFace graphData.toRotationSystem)) :
    ∃ clean : CleanOrbitHexCorridorSkeleton
        graphData.toRotationSystem corridorLength,
      ∃ hunique : PairwiseUniqueSharedInteriorEdges
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset (OrbitFace graphData.toRotationSystem)),
        Function.Injective
            (clean.toOrbitHexCorridorSkeleton.rungEdge hunique) ∧
        (∀ interior : CorridorInterior corridorLength,
          (internalSideEdges clean.toOrbitHexCorridorSkeleton
              hunique interior).card = 4 ∧
          Function.Injective
            (internalSideNeighbor clean minimal.facesTwoSided hunique interior) ∧
          ∀ side : {edge // edge ∈ internalSideEdges
              clean.toOrbitHexCorridorSkeleton hunique interior},
            (orbitFaceBoundary graphData.toRotationSystem
              (internalSideNeighbor clean minimal.facesTwoSided hunique
                interior side).1).card = 6 ∧
            ∀ index : Fin corridorLength,
              internalSideNeighbor clean minimal.facesTwoSided hunique
                  interior side ≠
                clean.toOrbitHexCorridorSkeleton.faceAt index) ∧
        ∀ offset : Fin (corridorLength - 2),
          (internalHexRungTypeWord clean.toOrbitHexCorridorSkeleton
            minimal.facesTwoSided hunique offset) ≠
              HexRungType.adjacent := by
  let hsphere := sphericalCubicMapData_of_orbitSphericalCubicMapData
    graphData.toRotationSystem minimal.spherical
  obtain ⟨clean⟩ := orbitFaceFullerene_exists_cleanHexCorridorSkeleton
    graphData.toRotationSystem hsphere minimal.facesTwoSided hfullerene
      minimal.primalConnected minimal.vertexRotationCyclic corridorLength
        hpositive hlarge
  let hunique := pairwiseUniqueSharedInteriorEdges graphData minimal
  let corridor := clean.toOrbitHexCorridorSkeleton
  exact ⟨clean, hunique,
    corridor.rungEdge_injective minimal.facesTwoSided hunique,
    fun interior =>
      ⟨card_internalSideEdges_eq_four corridor minimal.facesTwoSided
          hunique interior,
        internalSideNeighbor_injective clean minimal.facesTwoSided
          hunique interior,
        fun side =>
          ⟨internalSideNeighbor_hexagonal clean minimal.facesTwoSided
              hunique interior side,
            internalSideNeighbor_ne_faceAt clean minimal.facesTwoSided
              hunique interior side⟩⟩,
    fun offset =>
      GoertzelV24InducedHexCorridorTypes.InternalHexRungPlacement.rungType_ne_adjacent
        (internalHexRungPlacement corridor minimal.facesTwoSided hunique offset)
          hsphere.cubic minimal.vertexRotationCyclic
            minimal.facesTwoSided⟩

/-- Weighted all-face replacement for the fullerene corridor entry. For a
vertex-minimal counterexample whose actual face boundaries have length at
least five, either its number of faces is explicitly bounded in terms of
negative curvature or it contains the complete width-four clean slab used
by the corridor transfer system. -/
theorem orbitFace_card_le_weightedThreshold_or_exists_widthFourCleanHexCorridorSlab
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hminimum : OrbitFaceMinimumFive graphData.toRotationSystem)
    (corridorLength : Nat) (hpositive : 0 < corridorLength) :
    Fintype.card (OrbitFace graphData.toRotationSystem) ≤
        weightedCleanHexCorridorFaceThreshold
          graphData.toRotationSystem corridorLength ∨
      ∃ clean : CleanOrbitHexCorridorSkeleton
          graphData.toRotationSystem corridorLength,
        ∃ hunique : PairwiseUniqueSharedInteriorEdges
            (orbitFaceBoundary graphData.toRotationSystem)
            (Finset.univ : Finset (OrbitFace graphData.toRotationSystem)),
          Function.Injective
              (clean.toOrbitHexCorridorSkeleton.rungEdge hunique) ∧
          (∀ interior : CorridorInterior corridorLength,
            (internalSideEdges clean.toOrbitHexCorridorSkeleton
                hunique interior).card = 4 ∧
            Function.Injective
              (internalSideNeighbor clean minimal.facesTwoSided
                hunique interior) ∧
            ∀ side : {edge // edge ∈ internalSideEdges
                clean.toOrbitHexCorridorSkeleton hunique interior},
              (orbitFaceBoundary graphData.toRotationSystem
                (internalSideNeighbor clean minimal.facesTwoSided hunique
                  interior side).1).card = 6 ∧
              ∀ index : Fin corridorLength,
                internalSideNeighbor clean minimal.facesTwoSided hunique
                    interior side ≠
                  clean.toOrbitHexCorridorSkeleton.faceAt index) ∧
          ∀ offset : Fin (corridorLength - 2),
            (internalHexRungTypeWord clean.toOrbitHexCorridorSkeleton
              minimal.facesTwoSided hunique offset) ≠
                HexRungType.adjacent := by
  rcases orbitFace_card_le_weightedThreshold_or_exists_cleanHexCorridor
      graphData.toRotationSystem minimal.spherical minimal.facesTwoSided
      hminimum minimal.primalConnected minimal.vertexRotationCyclic
      corridorLength hpositive with hbounded | hclean
  · exact Or.inl hbounded
  · right
    obtain ⟨clean⟩ := hclean
    let hunique := pairwiseUniqueSharedInteriorEdges graphData minimal
    let corridor := clean.toOrbitHexCorridorSkeleton
    exact ⟨clean, hunique,
      corridor.rungEdge_injective minimal.facesTwoSided hunique,
      fun interior =>
        ⟨card_internalSideEdges_eq_four corridor minimal.facesTwoSided
            hunique interior,
          internalSideNeighbor_injective clean minimal.facesTwoSided
            hunique interior,
          fun side =>
            ⟨internalSideNeighbor_hexagonal clean minimal.facesTwoSided
                hunique interior side,
              internalSideNeighbor_ne_faceAt clean minimal.facesTwoSided
                hunique interior side⟩⟩,
      fun offset =>
        GoertzelV24InducedHexCorridorTypes.InternalHexRungPlacement.rungType_ne_adjacent
          (internalHexRungPlacement corridor minimal.facesTwoSided hunique
            offset)
          minimal.spherical.cubic minimal.vertexRotationCyclic
            minimal.facesTwoSided⟩

end

end GoertzelV24MinimalHexCorridor

end Mettapedia.GraphTheory.FourColor
