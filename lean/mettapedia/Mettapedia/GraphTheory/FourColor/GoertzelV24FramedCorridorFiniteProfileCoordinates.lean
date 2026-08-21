import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorRightThreeFaceBound
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorThreeFacePrefixProfileRepeat

/-!
# Fixed profile coordinates across one literal source Cell

The terminal-aware cumulative profile entering one source Cell was originally
packaged with a four-fragment outer bound, as was the terminal-free profile
leaving it.  The literal left and right two-edge cross-sections are now both
proved to have at most three occurrence-sensitive face fragments.

This module narrows the two actual profiles losslessly to the fixed types
`BoundedCorridorCutProfile 2 1 3` and
`BoundedCorridorCutProfile 2 0 3`.  Narrowing changes only the proof-carrying
outer bound; none of the five semantic profile coordinates is quotiented or
recomputed.  These are the input and output types for the finite one-Cell
support relation.  The relation itself is intentionally not asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedCorridorThreeFacePrefixProfileRepeat
open GoertzelV24CorridorProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorFiniteProfileCoordinatesEdgeSetDecidableEq :
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

/-- The complete terminal-aware profile entering a literal Cell, narrowed
losslessly to the proved three-fragment carrier. -/
noncomputable def localLayerFiniteInputProfile
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0) :
    BoundedCorridorCutProfile 2 1 3 :=
  narrowFaceFragmentBound
    (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor)
    (aligned.localLayerLeftPrefixSharedRungBoundedProfile_faceFragmentCount_le_three
      color hcolor)

@[simp]
theorem localLayerFiniteInputProfile_faceFragmentCount_val
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0) :
    (aligned.localLayerFiniteInputProfile color hcolor).faceFragmentCount.val =
      (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor
        ).faceFragmentCount.val :=
  rfl

@[simp]
theorem localLayerFiniteInputProfile_profile
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0) :
    (aligned.localLayerFiniteInputProfile color hcolor).profile =
      (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor
        ).profile :=
  rfl

/-- Equality of narrowed incoming profiles reflects equality of the complete
four-bound profiles from which they were obtained. -/
theorem localLayerFiniteInputProfile_eq_reflects
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (leftColor rightColor : G.edgeSet → Color)
    (hleft : ∀ step,
      leftColor (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (hright : ∀ step,
      rightColor (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (heq : aligned.localLayerFiniteInputProfile leftColor hleft =
      aligned.localLayerFiniteInputProfile rightColor hright) :
    aligned.localLayerLeftPrefixSharedRungBoundedProfile leftColor hleft =
      aligned.localLayerLeftPrefixSharedRungBoundedProfile rightColor hright := by
  exact narrowFaceFragmentBound_injective
    (aligned.localLayerLeftPrefixSharedRungBoundedProfile_faceFragmentCount_le_three
      leftColor hleft)
    (aligned.localLayerLeftPrefixSharedRungBoundedProfile_faceFragmentCount_le_three
      rightColor hright) heq

/-- The complete profile leaving a literal Cell, narrowed losslessly to the
same proved three-fragment face carrier. -/
noncomputable def localLayerFiniteOutputProfile
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    BoundedCorridorCutProfile 2 0 3 :=
  narrowFaceFragmentBound
    (aligned.toInterface.localLayerRightPrefixBoundedProfile color hcolor)
    (aligned.toInterface
      |>.localLayerRightPrefixBoundedProfile_faceFragmentCount_le_three
        color hcolor)

@[simp]
theorem localLayerFiniteOutputProfile_faceFragmentCount_val
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    (aligned.localLayerFiniteOutputProfile color hcolor).faceFragmentCount.val =
      (aligned.toInterface.localLayerRightPrefixBoundedProfile color hcolor
        ).faceFragmentCount.val :=
  rfl

@[simp]
theorem localLayerFiniteOutputProfile_profile
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    (aligned.localLayerFiniteOutputProfile color hcolor).profile =
      (aligned.toInterface.localLayerRightPrefixBoundedProfile color hcolor
        ).profile :=
  rfl

/-- Equality of narrowed outgoing profiles reflects equality of the complete
four-bound profiles from which they were obtained. -/
theorem localLayerFiniteOutputProfile_eq_reflects
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (leftColor rightColor : G.edgeSet → Color)
    (hleft : ∀ step,
      leftColor (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (hright : ∀ step,
      rightColor (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (heq : aligned.localLayerFiniteOutputProfile leftColor hleft =
      aligned.localLayerFiniteOutputProfile rightColor hright) :
    aligned.toInterface.localLayerRightPrefixBoundedProfile leftColor hleft =
      aligned.toInterface.localLayerRightPrefixBoundedProfile rightColor hright := by
  exact narrowFaceFragmentBound_injective
    (aligned.toInterface
      |>.localLayerRightPrefixBoundedProfile_faceFragmentCount_le_three
        leftColor hleft)
    (aligned.toInterface
      |>.localLayerRightPrefixBoundedProfile_faceFragmentCount_le_three
        rightColor hright) heq

/-- The finite input/output state pair realized by one literal source Cell.
The relation generated by all such pairs remains heterogeneous in the literal
Cell; no quotient to the three geometric orientation labels is assumed. -/
noncomputable def localLayerFiniteProfilePair
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hleftColor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (hrightColor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    BoundedCorridorCutProfile 2 1 3 ×
      BoundedCorridorCutProfile 2 0 3 :=
  (aligned.localLayerFiniteInputProfile color hleftColor,
    aligned.localLayerFiniteOutputProfile color hrightColor)

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
