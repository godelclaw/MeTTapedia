import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusBoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusDecomposition

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Source-side package for the boundary-walk interface of the annulus route: a concrete
shared-endpoint boundary-component witness, honest facial closed walks for every ambient face,
and the facewise fact that the selected-boundary edges form one contiguous arc on the boundary
run induced by those walks. This keeps the closed-walk source explicit instead of deriving it
from unordered incidence or from the weaker cyclic selected-boundary shells. -/
structure PlanarBoundaryClosedWalkAnnulusBoundarySource {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  boundaryReachability : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  closedWalks : PlanarBoundaryClosedWalkEmbeddingData emb
  selectedBoundaryArc :
    (f : AmbientFace emb.faces) ->
      (closedWalks.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/-- Build the source package from its three independent same-embedding fields. This is the
intended constructor: the honest closed walks are supplied explicitly, not reconstructed from
the boundary reachability or selected-arc layers. -/
def ofFields
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryReachability : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (closedWalks : PlanarBoundaryClosedWalkEmbeddingData emb)
    (selectedBoundaryArc :
      (f : AmbientFace emb.faces) ->
        (closedWalks.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    PlanarBoundaryClosedWalkAnnulusBoundarySource emb where
  boundaryReachability := boundaryReachability
  closedWalks := closedWalks
  selectedBoundaryArc := selectedBoundaryArc

/-- Build the annulus boundary-walk source from successor-based facial dart cycles. The selected
arc hypothesis is still stated on the face-boundary runs induced by the mechanically constructed
closed walks, so this is a lowering from a stronger rotation-side source rather than a new
closed-walk wrapper. -/
def ofDartSuccessorCycleFields
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryReachability : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (selectedBoundaryArc :
      (f : AmbientFace emb.faces) ->
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
  ofFields boundaryReachability
    dartCycles.toPlanarBoundaryClosedWalkEmbeddingData selectedBoundaryArc

/-- The honest facial closed-walk field is the strengthened source field required by the
boundary-walk blocker. -/
def toPlanarBoundaryClosedWalkEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    PlanarBoundaryClosedWalkEmbeddingData emb :=
  source.closedWalks

/-- The honest facial closed walks canonically provide one fallback boundary edge on every
ambient face.  This is the local geometric datum consumed by the one-collar witness-choice
constructor when the face has no interior boundary edge. -/
noncomputable def fallbackEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (f : AmbientFace emb.faces) : G.edgeSet :=
  Classical.choose (source.closedWalks.faceBoundaryClosedWalk f).faceBoundary_nonempty

theorem fallbackEdge_mem_faceBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (f : AmbientFace emb.faces) :
    source.fallbackEdge f ∈ emb.faceBoundary f.1 :=
  Classical.choose_spec (source.closedWalks.faceBoundaryClosedWalk f).faceBoundary_nonempty

/-- The same source lowers to the existing selected-boundary arc geometry used by the
boundary-component reductions. -/
def toPlanarBoundarySelectedBoundaryArcGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    PlanarBoundarySelectedBoundaryArcGeometry emb :=
  source.closedWalks.toPlanarBoundaryFaceBoundaryRunGeometry.toSelectedBoundaryArcGeometry
    source.selectedBoundaryArc

/-- The same source also lowers to the cyclic ordered face-arc shell: the honest facial closed
walks supply the cyclic boundary order, while the bundled selected-boundary contiguity is carried
over on the induced face-boundary runs. -/
noncomputable def toPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb :=
  source.closedWalks.toPlanarBoundaryCyclicOrderedFaceArcEmbeddingData source.selectedBoundaryArc

/-- The boundary reachability field lowers mechanically to the abstract annulus-boundary split
already consumed downstream. -/
noncomputable def toPlanarBoundaryAnnulusBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    PlanarBoundaryAnnulusBoundaryData emb :=
  source.boundaryReachability.toPlanarBoundaryAnnulusBoundaryData

/-- Closed-walk source data gives the facewise boundary-component constancy needed when the
annulus-boundary split is extracted from shared-endpoint reachability. -/
theorem boundaryComponentConstantOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    {f : AmbientFace emb.faces} :
    source.boundaryReachability.BoundaryComponentConstantOnFace f := by
  exact
    source.boundaryReachability
      |>.boundaryComponentConstantOnFace_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
        source.closedWalks source.selectedBoundaryArc

/-- The closed-walk source plus selected-arc contiguity gives the disjointness of the outer and
inner boundary-face layers extracted from the shared-endpoint annulus-boundary split. -/
theorem outerBoundaryFaces_disjoint_innerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    Disjoint
      source.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  simpa [toPlanarBoundaryAnnulusBoundaryData] using
    source.boundaryReachability
      |>.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
        source.closedWalks source.selectedBoundaryArc

end PlanarBoundaryClosedWalkAnnulusBoundarySource

end Mettapedia.GraphTheory.FourColor
