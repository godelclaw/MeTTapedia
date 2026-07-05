import Mettapedia.GraphTheory.FourColor.CAP5Reducibility
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryRotationSystem
import Mettapedia.GraphTheory.FourColor.PlanarFaceIncidence

namespace Mettapedia.GraphTheory.FourColor

open Mettapedia.GraphTheory

variable {V : Type*} [DecidableEq V]

/--
Graph-facing normal-form interface for the minimal-counterexample regime used
by the collar route.  The connectivity datum is the internal one supplied by
the ambient minimal counterexample: no cyclic edge cut of size at most four in
the ambient cubic graph.  It is deliberately not a cyclic-connectivity field
for any peeled collar.

The remaining fields name the planar/dual/CAP5 normal-form facts that the
regime route consumes before a concrete collar extraction is selected.
-/
structure MinimalCounterexampleCAP5FreeNormalForm (G : SimpleGraph V) where
  planeEmbedding : Nonempty (PlaneEmbedding G)
  globalFaceSuccessorBoundaryData :
    AdmitsPlanarBoundaryGlobalFaceSuccessorEmbeddingData G
  dualMinimumDegreeAtLeastFive : Prop
  noSeparatingDualTriangle : Prop
  noSeparatingDualQuadrilateral : Prop
  cap5FreeNormalForm : Prop
  noSmallCyclicEdgeCuts : NoCyclicEdgeCutOfSizeAtMostFour G
  hdualMinimumDegreeAtLeastFive : dualMinimumDegreeAtLeastFive
  hnoSeparatingDualTriangle : noSeparatingDualTriangle
  hnoSeparatingDualQuadrilateral : noSeparatingDualQuadrilateral
  hcap5FreeNormalForm : cap5FreeNormalForm

namespace MinimalCounterexampleCAP5FreeNormalForm

/-- The ambient normal form immediately supplies the graph-facing
no-small-cyclic-cut obstruction used by CAP5 and collar separator arguments. -/
theorem ambientNoSmallCyclicEdgeCuts
    {G : SimpleGraph V} (regime : MinimalCounterexampleCAP5FreeNormalForm G) :
    NoCyclicEdgeCutOfSizeAtMostFour G :=
  regime.noSmallCyclicEdgeCuts

/-- Equivalent named cyclic-connectivity form for the ambient graph only.  This
is often useful for existing APIs, but it is not an inherited collar fact. -/
theorem ambientCyclicallyFiveEdgeConnected
    {G : SimpleGraph V} (regime : MinimalCounterexampleCAP5FreeNormalForm G) :
    CyclicallyFiveEdgeConnected G :=
  regime.noSmallCyclicEdgeCuts.cyclicallyFiveEdgeConnected

end MinimalCounterexampleCAP5FreeNormalForm

/--
The rotation/embedding data available for a graph that is being used as a
peeled collar.  This is just the local surface; it intentionally carries no
connectivity conclusion.
-/
structure PeeledCollarPlanarNormalForm (H : SimpleGraph V) where
  boundaryEmbedding : Nonempty (PlaneEmbeddingWithBoundary H)
  globalFaceSuccessorBoundaryData :
    AdmitsPlanarBoundaryGlobalFaceSuccessorEmbeddingData H
  cap5FreeLocalNormalForm : Prop
  inheritedDualCellNormalForm : Prop
  hcap5FreeLocalNormalForm : cap5FreeLocalNormalForm
  hinheritedDualCellNormalForm : inheritedDualCellNormalForm

/--
Reusable two-graph package for a collar peeled from an ambient normal-form
graph.  The structural theorem connecting small collar cuts back to ambient
cuts is named separately in the bridge module.
-/
structure MinimalCounterexamplePeeledCollarRegime
    (G : SimpleGraph V) (W : Type*) [DecidableEq W] (H : SimpleGraph W) where
  ambient : MinimalCounterexampleCAP5FreeNormalForm G
  collar : PeeledCollarPlanarNormalForm H

end Mettapedia.GraphTheory.FourColor
