import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileEnclosedProfileTransition

/-!
# Finite full-profile support of an enclosed aligned source slab

The physical aligned slab is an actual open morphism with four transverse
boundary crossings and two local rail ports.  This module packages the full
profile of its *enclosed* literal tangle into one finite carrier and records
the corresponding realizability-witnessed support relation between its two
transverse endpoint views.

The six-port carrier belongs to a generator, not to the moving corridor state:
the two rails stay local to this slab.  In particular, this file neither
asserts serial gluing of consecutive slabs nor identifies either endpoint view
with a cumulative prefix profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfileRestriction
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileEnclosedBoundedSupportEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- One common finite carrier for the complete `4 + 2` profile of an
enclosed aligned slab.  The twelve-fragment bound comes from the literal
six-edge vertex-side boundary, including dart occurrences. -/
abbrev AlignedTwoTileEnclosedBoundedFullProfile :=
  BoundedCorridorCutProfile 4 2 12

/-- The finite endpoint carrier obtained by selecting either transverse
two-edge block of that same slab while retaining its two local rail ports. -/
abbrev AlignedTwoTileEnclosedBoundedEndpointProfile :=
  BoundedCorridorCutProfile 2 2 12

/-- The enclosed aligned slab has at most twelve occurrence-sensitive
boundary face fragments: at most two per one of its six actual crossing
edges. -/
theorem sourceTwoTileAlignedEnclosed_faceFragmentCount_le_twelve
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
    Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique offset).componentSideᶜ)
      (vertexSetRegionEdges embedded.cellulation.rotation.toRotationSystem
        (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique offset).componentSideᶜ)) ≤ 12 := by
  let boundary := sourceTwoTileAlignedLayerBoundaryAt realization hcubic
    hrotation htwoSided hunique offset
  let inside := boundary.componentSideᶜ
  have hcrossingCard :
      Fintype.card (VertexSetCrossingEdge
        embedded.cellulation.rotation.toRotationSystem inside) = 6 := by
    calc
      Fintype.card (VertexSetCrossingEdge
          embedded.cellulation.rotation.toRotationSystem inside) =
          Fintype.card (CorridorPort 4 2) := by
        simpa only [inside, boundary] using
          (Fintype.card_congr
            (sourceTwoTileAlignedEnclosedPortCrossingEquiv realization hcubic
              hrotation htwoSided hunique offset)).symm
      _ = 6 := by simp
  calc
    Fintype.card (BoundaryRegionalFragment
        embedded.cellulation.rotation.toRotationSystem
        (vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
          inside)
        (vertexSetRegionEdges embedded.cellulation.rotation.toRotationSystem
          inside)) ≤
        2 * Fintype.card (VertexSetCrossingEdge
          embedded.cellulation.rotation.toRotationSystem inside) :=
      vertexSetBoundaryGraphCutData_fragmentCount_le_two_mul_crossingPortCount_of_dartOccurrences
        embedded.cellulation.rotation.toRotationSystem inside
    _ = 12 := by omega

/-- Package the full profile calculated from one literal enclosed-slab Tait
coloring in the common finite carrier.  No coordinate is discarded. -/
noncomputable def sourceTwoTileAlignedEnclosedLiteralBoundedFullProfile
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
    (offset : Fin (blockLength - 4))
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring) :
    AlignedTwoTileEnclosedBoundedFullProfile := by
  refine {
    faceFragmentCount := ⟨_, Nat.lt_succ_of_le
      (sourceTwoTileAlignedEnclosed_faceFragmentCount_le_twelve realization
        hcubic hrotation htwoSided hunique offset)⟩
    profile := ?_ }
  exact sourceTwoTileAlignedEnclosedLiteralOpenProfile realization hcubic
    hrotation htwoSided hunique offset coloring hcoloring

/-- The input endpoint of the literal enclosed slab, packaged on the same
finite fragment bound and retaining its local rail observations. -/
noncomputable def sourceTwoTileAlignedEnclosedLiteralBoundedInputProfile
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
    (offset : Fin (blockLength - 4))
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring) :
    AlignedTwoTileEnclosedBoundedEndpointProfile :=
  restrictBoundedCrossings
    (sourceTwoTileAlignedEnclosedLiteralBoundedFullProfile realization hcubic
      hrotation htwoSided hunique offset coloring hcoloring)
    sourceTwoTileAlignedFirstTerminalCrossingIndex

/-- The output endpoint of the same literal enclosed slab.  It has the same
local rail observations but the second transverse crossing block. -/
noncomputable def sourceTwoTileAlignedEnclosedLiteralBoundedOutputProfile
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
    (offset : Fin (blockLength - 4))
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring) :
    AlignedTwoTileEnclosedBoundedEndpointProfile :=
  restrictBoundedCrossings
    (sourceTwoTileAlignedEnclosedLiteralBoundedFullProfile realization hcubic
      hrotation htwoSided hunique offset coloring hcoloring)
    sourceTwoTileAlignedSecondTerminalCrossingIndex

/-- A bounded full profile is realizable precisely when it is produced by an
actual Tait coloring of this literal enclosed source slab. -/
def SourceTwoTileAlignedEnclosedBoundedProfileRealizable
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
    (offset : Fin (blockLength - 4))
    (profile : AlignedTwoTileEnclosedBoundedFullProfile) : Prop :=
  ∃ coloring : { coloring :
      (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic hrotation
        htwoSided hunique offset).EdgeColoring Color //
      (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic hrotation
        htwoSided hunique offset).IsTaitEdgeColoring coloring },
    sourceTwoTileAlignedEnclosedLiteralBoundedFullProfile realization hcubic
      hrotation htwoSided hunique offset coloring.1 coloring.2 = profile

/-- The actual literal profile of a Tait coloring is realizable by that
coloring. -/
theorem sourceTwoTileAlignedEnclosedLiteralBoundedFullProfile_realizable
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
    (offset : Fin (blockLength - 4))
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring) :
    SourceTwoTileAlignedEnclosedBoundedProfileRealizable realization hcubic
      hrotation htwoSided hunique offset
      (sourceTwoTileAlignedEnclosedLiteralBoundedFullProfile realization
        hcubic hrotation htwoSided hunique offset coloring hcoloring) :=
  ⟨⟨coloring, hcoloring⟩, rfl⟩

/-- The realizability-witnessed finite support relation of one literal
enclosed aligned slab.  This is the support-level precursor to its `Count`
matrix: arbitrary encodings outside the realized image receive no transition.
-/
def sourceTwoTileAlignedEnclosedBoundedProfileTransfer
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
    (offset : Fin (blockLength - 4))
    (input output : AlignedTwoTileEnclosedBoundedEndpointProfile) : Prop :=
  ∃ common : AlignedTwoTileEnclosedBoundedFullProfile,
    SourceTwoTileAlignedEnclosedBoundedProfileRealizable realization hcubic
      hrotation htwoSided hunique offset common ∧
      restrictBoundedCrossings common
          sourceTwoTileAlignedFirstTerminalCrossingIndex = input ∧
      restrictBoundedCrossings common
          sourceTwoTileAlignedSecondTerminalCrossingIndex = output

/-- The bounded support relation is finite and decidable; its semantic
restriction is that the common witness must come from a literal tangle
coloring. -/
noncomputable instance instDecidableRelSourceTwoTileAlignedEnclosedBoundedProfileTransfer
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
    DecidableRel (sourceTwoTileAlignedEnclosedBoundedProfileTransfer
      realization hcubic hrotation htwoSided hunique offset) := by
  classical
  intro input output
  unfold sourceTwoTileAlignedEnclosedBoundedProfileTransfer
  infer_instance

/-- Every literal enclosed-slab Tait coloring supplies a transition in the
finite support relation between its two actual transverse endpoint views. -/
theorem sourceTwoTileAlignedEnclosedLiteralBoundedProfiles_transfer
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
    (offset : Fin (blockLength - 4))
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring) :
    sourceTwoTileAlignedEnclosedBoundedProfileTransfer realization hcubic
      hrotation htwoSided hunique offset
      (sourceTwoTileAlignedEnclosedLiteralBoundedInputProfile realization
        hcubic hrotation htwoSided hunique offset coloring hcoloring)
      (sourceTwoTileAlignedEnclosedLiteralBoundedOutputProfile realization
        hcubic hrotation htwoSided hunique offset coloring hcoloring) := by
  refine ⟨sourceTwoTileAlignedEnclosedLiteralBoundedFullProfile realization
    hcubic hrotation htwoSided hunique offset coloring hcoloring, ?_, rfl, rfl⟩
  exact sourceTwoTileAlignedEnclosedLiteralBoundedFullProfile_realizable
    realization hcubic hrotation htwoSided hunique offset coloring hcoloring

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
