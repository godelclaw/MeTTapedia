import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileFactorCoordinates

/-!
# Source prefix factor caps at finite coordinates

An old-prefix factor that meets the incoming source cut has already been
assigned an exact finite-profile coordinate.  This file shows that the
`faceLengthCap` stored at that coordinate is precisely the factor's
occurrence-sensitive cap at five.

The shared-rung residue is deliberately absent from this statement.  It is
the other branch of factor coverage and requires its own local arithmetic.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceCapUpdate
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileFactorCapsEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedSlabInterface

variable {source : SourceTrail G}
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

/-- Occurrence-sensitive cap-at-five of one old-prefix factor. -/
def localLayerLeftFactorPositionCap
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment) : Nat :=
  min
    (faceRegionalFragmentPositions
      embedded.cellulation.rotation.toRotationSystem
      (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        fragment.1.1)
      aligned.toInterface.localLayerLeftPrefixRegion factor).card
    5

/-- At a genuine incoming profile coordinate, the stored edge cap is exactly
the edge-support cap of the corresponding old-prefix factor. -/
theorem exists_localLayerLeftPrefixProfileFaceLengthCap_eq_factorEdgeCap
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment)
    (hcoordinate :
      aligned.LocalLayerLeftFactorHasProfileCoordinate fragment factor) :
    ∃ index : aligned.LocalLayerLeftBoundaryIndex,
      (((aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor)
          |>.profile.faceLengthCap index).val) =
        min (aligned.localLayerLeftFactorEdges fragment factor).card 5 := by
  rcases hcoordinate with ⟨index, hindex⟩
  refine ⟨index, ?_⟩
  let interface := aligned.toInterface
  let RS := embedded.cellulation.rotation.toRotationSystem
  have hfragmentEdges :
      interface.localLayerLeftPrefixGraphCutData.regionalFragmentEdges index =
        aligned.localLayerLeftBoundaryFragmentEdgesAt index := by
    rw [interface.localLayerLeftPrefixGraphCutData
      |>.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
        (regionalBoundaryGraphCutData_fragmentsOnFaceInRegion RS
          interface.localLayerLeftPrefixRegion
          interface.localLayerPrefixCrossing)]
    rfl
  change min
      (interface.localLayerLeftPrefixGraphCutData.regionalFragmentEdges
        index).card 5 = _
  rw [hfragmentEdges, hindex]

/-- On a two-sided source face, the same finite coordinate stores the
occurrence-sensitive cap used by the relational face update. -/
theorem exists_localLayerLeftPrefixProfileFaceLengthCap_eq_factorPositionCap
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment)
    (hcoordinate :
      aligned.LocalLayerLeftFactorHasProfileCoordinate fragment factor) :
    ∃ index : aligned.LocalLayerLeftBoundaryIndex,
      (((aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor)
          |>.profile.faceLengthCap index).val) =
        aligned.localLayerLeftFactorPositionCap fragment factor := by
  rcases aligned
      |>.exists_localLayerLeftPrefixProfileFaceLengthCap_eq_factorEdgeCap
        color hcolor fragment factor hcoordinate with ⟨index, hindex⟩
  refine ⟨index, hindex.trans ?_⟩
  simpa [localLayerLeftFactorEdges, localLayerLeftFactorPositionCap] using
    (min_card_faceRegionalFragmentEdges_eq_positions
      embedded.cellulation.rotation.toRotationSystem htwoSided
      (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        fragment.1.1)
      aligned.toInterface.localLayerLeftPrefixRegion factor 5)

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
