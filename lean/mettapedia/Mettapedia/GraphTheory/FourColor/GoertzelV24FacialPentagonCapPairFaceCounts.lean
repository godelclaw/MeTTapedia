import Mettapedia.GraphTheory.FourColor.GoertzelV24CutTransitionFaceCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairBoundaryFaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionSlitOpenRegionComparison

/-!
# Ambient face counts at a separated facial-cap pair

The literal two-cap cut has ten retained boundary darts.  Under the remote
facial-separation condition already isolated for C-4, the two one-cap bond
theorems make those darts unique on their ambient faces.  The generic cut
count then proves that exactly ten ambient faces are touched.

This is one term of the C-3 face census.  It does not count the two pure
deleted cap faces, the untouched retained faces, or the opened face orbits.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapPairFaceCounts

open SimpleGraphDartRotation
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24CutTransitionFaceCount
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24DeletedRegionSlitGraph
open GoertzelV24DeletedRegionSlitOpenRegionComparison
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapPairBoundaryFaces
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

namespace OrientedFacialPentagonCapPair

variable {data : Data G}

private abbrev pair (caps : OrientedFacialPentagonCapPair data) :
    PentagonCapPair G := caps.toFacialPentagonCapPair.toPentagonCapPair

/-- Manuscript boundary ports and literal rotation-system boundary darts are
the same carrier. -/
def boundaryPortEquivBoundaryDart
    (data : Data G) (deleted : Finset V) :
    DeletedRegionBoundaryPort G deleted ≃
      BoundaryDart data.toRotationSystem (deletedRegionKeep deleted) where
  toFun := portToBoundaryDart data
  invFun := boundaryDartToPort data
  left_inv := by intro port; rfl
  right_inv := by intro boundary; rfl

/-- The simultaneous facial-cap boundary has the literal ten coordinates
`inner 0..4` and `outer 0..4`. -/
def boundaryCoordinateEquiv
    (caps : OrientedFacialPentagonCapPair data) :
    Fin 5 ⊕ Fin 5 ≃
      BoundaryDart data.toRotationSystem
        (deletedRegionKeep (pair caps).deletedVertexSupport) :=
  (pair caps).boundaryPortEquiv.trans
    (boundaryPortEquivBoundaryDart data (pair caps).deletedVertexSupport)

/-- The literal simultaneous vertex cut has ten retained boundary darts. -/
theorem card_boundaryDart_eq_ten
    (caps : OrientedFacialPentagonCapPair data) :
    Fintype.card
        (BoundaryDart data.toRotationSystem
          (deletedRegionKeep (pair caps).deletedVertexSupport)) = 10 := by
  rw [← Fintype.card_congr (boundaryCoordinateEquiv caps)]
  simp

/-- Equivalently, the endpoint-computed crossing-edge set has cardinality
ten. -/
theorem card_vertexSetCrossingEdges_eq_ten
    (caps : OrientedFacialPentagonCapPair data) :
    (vertexSetCrossingEdges data.toRotationSystem
      (pair caps).deletedVertexSupport).card = 10 := by
  rw [← card_boundaryDart_deletedRegionKeep]
  exact card_boundaryDart_eq_ten caps

/-- Remote facial separation makes the ten boundary darts lie on ten distinct
touched ambient faces. -/
theorem card_cutSideTransitionFaces_eq_ten
    (caps : OrientedFacialPentagonCapPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data caps) :
    (cutSideTransitionFaces data.toRotationSystem
      (pair caps).deletedVertexSupport).card = 10 := by
  rw [card_cutSideTransitionFaces_eq_crossingEdges_of_unique]
  · exact card_vertexSetCrossingEdges_eq_ten caps
  · exact
      GoertzelV24FacialPentagonCapPairBoundaryFaces.OrientedFacialPentagonCapPair.cutFacesHaveUniqueRetainedBoundaryDart_of_remoteBoundaryFacesSeparated
        caps minimal hremote

end OrientedFacialPentagonCapPair

end

end GoertzelV24FacialPentagonCapPairFaceCounts

end Mettapedia.GraphTheory.FourColor
