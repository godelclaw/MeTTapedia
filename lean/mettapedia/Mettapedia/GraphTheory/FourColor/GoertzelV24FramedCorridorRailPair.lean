import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorRailStep
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceProfileWord

/-!
# Concrete paired rails between consecutive source interfaces

The three finite source slab words produce different local geometry, but they
all provide the same compositional datum: two actual short facial-dual paths
between the corresponding endpoints of consecutive source interfaces.  This
module packages that common datum without claiming global noncrossing; a later
corridor assembly must establish that for a sequence of these local steps.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- Keep the edge carrier's equality instance aligned with the source-corridor
   geometry, whose finite facial boundaries use the ordinary subtype instance. -/
local instance corridorRailPairGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The two exterior rails between a pair of consecutive source interfaces.
Each rail is retained as a genuine simple walk, with its local length bound,
so corridor composition can append checked paths rather than reconstructing
them from a finite profile code. -/
structure SourceCornerAlignedRailPair
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext) where
  firstRail :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      first.toInterface.firstLayerFace second.toInterface.firstLayerFace
  secondRail :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      first.toInterface.secondLayerFace second.toInterface.secondLayerFace
  firstRail_isPath : firstRail.IsPath
  secondRail_isPath : secondRail.IsPath
  firstRail_length_le_two : firstRail.length ≤ 2
  secondRail_length_le_two : secondRail.length ≤ 2
  /-- Every face on a local rail is an actual side neighbor of one of the
  two source cells that the rail joins.  Retaining this provenance lets the
  global construction exclude remote rail collisions from the L1 geodesic,
  rather than treating rail simplicity as a bare local fact. -/
  firstRail_support_adjacent_to_source :
    ∀ face ∈ firstRail.support,
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          first.toInterface.centerLayerFace face ∨
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          second.toInterface.centerLayerFace face
  secondRail_support_adjacent_to_source :
    ∀ face ∈ secondRail.support,
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          first.toInterface.centerLayerFace face ∨
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          second.toInterface.centerLayerFace face

/-- Restate the retained first-rail provenance directly in terms of the
realized source axis.  This is the form consumed by the geodesic
noncollision theorem when a long corridor is assembled. -/
theorem SourceCornerAlignedRailPair.firstRail_support_adjacent_to_axis
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext}
    (pair : SourceCornerAlignedRailPair first second)
    (face : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hface : face ∈ pair.firstRail.support) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        (realization.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton.faceAt leftInterior.center) face ∨
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        (realization.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior leftInterior hnext).center) face := by
  rcases pair.firstRail_support_adjacent_to_source face hface with hfirst | hsecond
  · exact Or.inl (by
      simpa [SourceConsecutiveSlabInterface.centerLayerFace] using hfirst)
  · exact Or.inr (by
      simpa [SourceConsecutiveSlabInterface.centerLayerFace] using hsecond)

/-- The analogous source-axis provenance of the second local rail. -/
theorem SourceCornerAlignedRailPair.secondRail_support_adjacent_to_axis
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext}
    (pair : SourceCornerAlignedRailPair first second)
    (face : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hface : face ∈ pair.secondRail.support) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        (realization.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton.faceAt leftInterior.center) face ∨
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        (realization.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior leftInterior hnext).center) face := by
  rcases pair.secondRail_support_adjacent_to_source face hface with hfirst | hsecond
  · exact Or.inl (by
      simpa [SourceConsecutiveSlabInterface.centerLayerFace] using hfirst)
  · exact Or.inr (by
      simpa [SourceConsecutiveSlabInterface.centerLayerFace] using hsecond)

/-- First rails from two source cells separated by a three-cell gap cannot
meet.  This instantiates the L1 geodesic noncollision theorem with the
concrete provenance retained by the source rail construction. -/
theorem sourceCornerAlignedRailPair_firstRail_support_disjoint_of_add_three_lt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior rightInterior : CorridorInterior blockLength}
    {hleftNext : leftInterior.center.val + 2 < blockLength}
    {hleftNextNext :
      (nextCorridorInterior leftInterior hleftNext).center.val + 2 < blockLength}
    {hrightNext : rightInterior.center.val + 2 < blockLength}
    {hrightNextNext :
      (nextCorridorInterior rightInterior hrightNext).center.val + 2 < blockLength}
    (leftFirst : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hleftNext)
    (leftSecond : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hleftNext) hleftNextNext)
    (rightFirst : SourceCornerAlignedSlabInterface realization htwoSided hunique
      rightInterior hrightNext)
    (rightSecond : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior rightInterior hrightNext) hrightNextNext)
    (leftPair : SourceCornerAlignedRailPair leftFirst leftSecond)
    (rightPair : SourceCornerAlignedRailPair rightFirst rightSecond)
    (hseparated : leftInterior.center.val + 3 < rightInterior.center.val) :
    leftPair.firstRail.support.Disjoint rightPair.firstRail.support := by
  apply realization.walkSupports_disjoint_of_two_source_anchor_pairs_of_add_three_lt
    hleftNext hrightNext leftPair.firstRail rightPair.firstRail
  · intro face hface
    exact leftPair.firstRail_support_adjacent_to_axis face hface
  · intro face hface
    exact rightPair.firstRail_support_adjacent_to_axis face hface
  · exact hseparated

/-- A `forwardTwo` source word gives a shared first rail endpoint and a
two-edge second rail through its certified exterior middle face. -/
theorem sourceCornerAlignedRailPair_of_forwardTwo
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hdistance : hexForwardDistance
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).incomingPosition6
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition6 = 2) :
    Nonempty (SourceCornerAlignedRailPair first second) := by
  rcases sourceCornerAlignedBentRailStep_of_forwardTwo hcubic hrotation
      first second hdistance with ⟨rail⟩
  rcases sourceCornerAlignedExteriorFaces_pairwise_ne_of_forwardTwo first second
      rail hdistance with ⟨hAB, hAM, hAD, hBM, hBD, hMD⟩
  refine ⟨{
    firstRail := SimpleGraph.Walk.nil.copy rfl rail.sharedFirst
    secondRail := SimpleGraph.Walk.cons rail.middleToFirst.symm
      (SimpleGraph.Walk.cons rail.secondToMiddle.symm SimpleGraph.Walk.nil)
    firstRail_isPath := by simp
    secondRail_isPath := by
      apply SimpleGraph.Walk.IsPath.cons
      · apply SimpleGraph.Walk.IsPath.cons
        · exact SimpleGraph.Walk.IsPath.nil
        · simpa [SourceCornerAlignedForwardTwoRailWitness.middleFace] using hMD
      · have hBM' : first.toInterface.secondLayerFace ≠
            placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
              hunique
              (realization.slabPlacementAt htwoSided hunique
                (nextCorridorInterior leftInterior hnext)) rail.middlePosition := by
          simpa only [SourceCornerAlignedForwardTwoRailWitness.middleFace] using hBM
        simpa only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false, not_or] using And.intro hBM' hBD
    firstRail_length_le_two := by simp
    secondRail_length_le_two := by simp
    firstRail_support_adjacent_to_source := by
      intro face hface
      have hfaceEq : face = first.toInterface.firstLayerFace := by
        simpa only [SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false] using hface
      subst face
      exact Or.inl first.toInterface.firstLayerFace_adjacent_centerLayerFace.symm
    secondRail_support_adjacent_to_source := by
      have hmiddle :
          (interiorDualGraph
            (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
            second.toInterface.centerLayerFace rail.middleFace := by
        simpa [SourceConsecutiveSlabInterface.centerLayerFace,
          SourceCornerAlignedForwardTwoRailWitness.middleFace,
          placementSideNeighbor] using
          (internalSideNeighbor_adjacent realization.toCleanOrbitHexCorridorSkeleton
            htwoSided hunique (nextCorridorInterior leftInterior hnext)
            (placementSideEdge htwoSided
              (realization.slabPlacementAt htwoSided hunique
                (nextCorridorInterior leftInterior hnext)) rail.middlePosition))
      intro face hface
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hface
      rcases hface with hface | hface | hface
      · subst face
        exact Or.inl first.toInterface.centerLayerFace_adjacent_secondLayerFace
      · subst face
        exact Or.inr hmiddle
      · subst face
        exact Or.inr second.toInterface.centerLayerFace_adjacent_secondLayerFace
  }⟩

/-- The numerical middle source word is the opposite-rung case. -/
private theorem outgoing_modEq_of_hexForwardDistance_three
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 3) :
    outgoing.val ≡ incoming.val + 3 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexForwardDistance, Nat.ModEq] at *

/-- A `forwardThree` source word gives one actual exterior edge on each rail. -/
theorem sourceCornerAlignedRailPair_of_forwardThree
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hdistance : hexForwardDistance
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).incomingPosition6
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition6 = 3) :
    Nonempty (SourceCornerAlignedRailPair first second) := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hopposite6 : sharedPlacement.outgoingPosition6.val ≡
      sharedPlacement.incomingPosition6.val + 3 [MOD 6] :=
    outgoing_modEq_of_hexForwardDistance_three _ _ (by
      simpa [sharedPlacement] using hdistance)
  have hopposite : sharedPlacement.outgoingPosition.val ≡
      sharedPlacement.incomingPosition.val + 3 [MOD 6] := by
    simpa [InternalHexRungPlacement.incomingPosition6,
      InternalHexRungPlacement.outgoingPosition6] using hopposite6
  let rails := sourceCornerAlignedRailStep_of_oppositeRungs hcubic hrotation
    first second (by simpa [sharedPlacement] using hopposite)
  exact ⟨{
    firstRail := rails.1.toWalk
    secondRail := rails.2.toWalk
    firstRail_isPath := SimpleGraph.Walk.IsPath.of_adj rails.1
    secondRail_isPath := SimpleGraph.Walk.IsPath.of_adj rails.2
    firstRail_length_le_two := by simp
    secondRail_length_le_two := by simp
    firstRail_support_adjacent_to_source := by
      intro face hface
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hface
      rcases hface with hface | hface
      · subst face
        exact Or.inl first.toInterface.firstLayerFace_adjacent_centerLayerFace.symm
      · subst face
        exact Or.inr second.toInterface.firstLayerFace_adjacent_centerLayerFace.symm
    secondRail_support_adjacent_to_source := by
      intro face hface
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hface
      rcases hface with hface | hface
      · subst face
        exact Or.inl first.toInterface.centerLayerFace_adjacent_secondLayerFace
      · subst face
        exact Or.inr second.toInterface.centerLayerFace_adjacent_secondLayerFace
  }⟩

/-- A `forwardFour` source word gives a two-edge first rail through its
certified exterior middle face and a shared second rail endpoint. -/
theorem sourceCornerAlignedRailPair_of_forwardFour
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hdistance : hexForwardDistance
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).incomingPosition6
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition6 = 4) :
    Nonempty (SourceCornerAlignedRailPair first second) := by
  rcases sourceCornerAlignedBentRailStep_of_forwardFour hcubic hrotation
      first second hdistance with ⟨rail⟩
  rcases sourceCornerAlignedExteriorFaces_pairwise_ne_of_forwardFour first second
      rail hdistance with ⟨hAB, hAM, hAC, hBM, hBC, hMC⟩
  refine ⟨{
    firstRail := SimpleGraph.Walk.cons rail.firstToMiddle
      (SimpleGraph.Walk.cons rail.middleToSecond SimpleGraph.Walk.nil)
    secondRail := SimpleGraph.Walk.nil.copy rfl rail.sharedSecond
    firstRail_isPath := by
      apply SimpleGraph.Walk.IsPath.cons
      · apply SimpleGraph.Walk.IsPath.cons
        · exact SimpleGraph.Walk.IsPath.nil
        · simpa [SourceCornerAlignedForwardFourRailWitness.middleFace] using hMC
      · have hAM' : first.toInterface.firstLayerFace ≠
            placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
              hunique
              (realization.slabPlacementAt htwoSided hunique
                (nextCorridorInterior leftInterior hnext)) rail.middlePosition := by
          simpa only [SourceCornerAlignedForwardFourRailWitness.middleFace] using hAM
        simpa only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false, not_or] using And.intro hAM' hAC
    secondRail_isPath := by simp
    firstRail_length_le_two := by simp
    secondRail_length_le_two := by simp
    firstRail_support_adjacent_to_source := by
      have hmiddle :
          (interiorDualGraph
            (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
            second.toInterface.centerLayerFace rail.middleFace := by
        simpa [SourceConsecutiveSlabInterface.centerLayerFace,
          SourceCornerAlignedForwardFourRailWitness.middleFace,
          placementSideNeighbor] using
          (internalSideNeighbor_adjacent realization.toCleanOrbitHexCorridorSkeleton
            htwoSided hunique (nextCorridorInterior leftInterior hnext)
            (placementSideEdge htwoSided
              (realization.slabPlacementAt htwoSided hunique
                (nextCorridorInterior leftInterior hnext)) rail.middlePosition))
      intro face hface
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hface
      rcases hface with hface | hface | hface
      · subst face
        exact Or.inl first.toInterface.firstLayerFace_adjacent_centerLayerFace.symm
      · subst face
        exact Or.inr hmiddle
      · subst face
        exact Or.inr second.toInterface.firstLayerFace_adjacent_centerLayerFace.symm
    secondRail_support_adjacent_to_source := by
      intro face hface
      have hfaceEq : face = first.toInterface.secondLayerFace := by
        simpa only [SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false] using hface
      subst face
      exact Or.inl first.toInterface.centerLayerFace_adjacent_secondLayerFace
  }⟩

/-- Every non-adjacent source tile yields one bounded pair of concrete local
rails.  The finite three-way case split is performed here, so subsequent
corridor composition cannot accidentally retain only the straight case. -/
theorem exists_sourceCornerAlignedRailPair
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext) :
    Nonempty (SourceCornerAlignedRailPair first second) := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hnonadjacent : sharedPlacement.rungType ≠ HexRungType.adjacent := by
    simpa [sharedPlacement] using
      realization.slabPlacementAt_rungType_ne_adjacent hcubic hrotation htwoSided
        hunique (nextCorridorInterior leftInterior hnext)
  rcases hexForwardDistance_eq_two_or_three_or_four
      sharedPlacement.incomingPosition6 sharedPlacement.outgoingPosition6
      sharedPlacement.positions6_ne hnonadjacent with htwo | hthree | hfour
  · exact sourceCornerAlignedRailPair_of_forwardTwo hcubic hrotation first second
      (by simpa [sharedPlacement] using htwo)
  · exact sourceCornerAlignedRailPair_of_forwardThree hcubic hrotation first second
      (by simpa [sharedPlacement] using hthree)
  · exact sourceCornerAlignedRailPair_of_forwardFour hcubic hrotation first second
      (by simpa [sharedPlacement] using hfour)

/-- The left endpoint of an indexed rail step is an actual source-profile
position; one slot remains available for its successor interface. -/
def sourceSlabRailStartOffset {blockLength : Nat}
    (offset : Fin (blockLength - 4)) : Fin (blockLength - 3) :=
  ⟨offset.val, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    apply (Nat.lt_sub_iff_add_lt).2
    omega⟩

/-- The second source-profile position adjacent to a rail-step start. -/
def sourceSlabRailFinishOffset {blockLength : Nat}
    (offset : Fin (blockLength - 4)) : Fin (blockLength - 3) :=
  ⟨offset.val + 1, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    apply (Nat.lt_sub_iff_add_lt).2
    omega⟩

/-- The adjacent source-profile index names exactly the next corridor
interior used by the rail construction. -/
theorem sourceSlabLeftInterior_railFinish_eq_next {blockLength : Nat}
    (offset : Fin (blockLength - 4)) :
    sourceSlabLeftInterior (sourceSlabRailFinishOffset offset) =
      nextCorridorInterior
        (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
        (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset)) := by
  have hcenter :
      (sourceSlabLeftInterior (sourceSlabRailFinishOffset offset)).center =
        (nextCorridorInterior
          (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
          (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset))).center := by
    apply Fin.ext
    rfl
  cases hleft : sourceSlabLeftInterior (sourceSlabRailFinishOffset offset) with
  | mk leftCenter leftPositive leftSuccessor =>
    cases hright : nextCorridorInterior
        (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
        (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset)) with
    | mk rightCenter rightPositive rightSuccessor =>
      simp only [hleft, hright, CorridorInterior.mk.injEq] at hcenter ⊢
      exact hcenter

/-- A rail-step start has a second successor corridor face, so the next
corner-aligned source interface is a real object rather than a profile-only
index. -/
theorem sourceSlabRailStart_hasNextNext {blockLength : Nat}
    (offset : Fin (blockLength - 4)) :
    (nextCorridorInterior
      (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
      (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset))).center.val + 2 <
      blockLength := by
  have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
  change offset.val + 2 + 2 < blockLength
  omega

/-- The next concrete corner-aligned interface along the source-profile
word.  Its underlying corridor interior is definitionally the successor of
the first one, which is the endpoint required by a rail pair. -/
noncomputable def sourceSlabRailNextCornerInterfaceAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :
    SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
        (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset)))
      (sourceSlabRailStart_hasNextNext offset) :=
  realization.sourceCornerAlignedSlabInterface hcubic hrotation htwoSided hunique
    (nextCorridorInterior
      (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
      (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset)))
    (sourceSlabRailStart_hasNextNext offset)

/-- At every source-profile position with one following position, the two
literal interfaces carry an actual bounded rail pair.  This is the direct
link from the finite profile word to the geometry that a later splice
formation appends. -/
theorem sourceSlabCornerInterfaceAt_hasRailPair
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :
    Nonempty (SourceCornerAlignedRailPair
      (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailStartOffset offset))
      (sourceSlabRailNextCornerInterfaceAt realization hcubic hrotation htwoSided hunique
        offset)) := by
  exact exists_sourceCornerAlignedRailPair hcubic hrotation
    (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
      (sourceSlabRailStartOffset offset))
    (sourceSlabRailNextCornerInterfaceAt realization hcubic hrotation htwoSided hunique
      offset)

/-- The preceding rail pair is indexed by two genuinely consecutive entries
of the source profile word, not merely by an isomorphic successor interior. -/
theorem sourceSlabCornerInterfaces_adjacent_hasRailPair
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :
    Nonempty (SourceCornerAlignedRailPair
      (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailStartOffset offset))
      (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailFinishOffset offset))) := by
  have hinterior := sourceSlabLeftInterior_railFinish_eq_next offset
  cases hinterior
  exact exists_sourceCornerAlignedRailPair hcubic hrotation
    (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
      (sourceSlabRailStartOffset offset))
    (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
      (sourceSlabRailFinishOffset offset))

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
