import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceCore
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices
import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundarySeed

/-!
# Core bundled hypothesis shells for the Theorem 4.9 route

This module contains the exact geometric/v23 shell data used by the live goal
surface.  Detector and cancellation certificates live in `Shells`.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Exact one-collar current-boundary data whose underlying annulus boundary
split is a prescribed one.  This is the strongest current-boundary repair that
honest sources are known to supply for free
(`exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource`). -/
structure ExactOneCollarOn (emb : PlaneEmbeddingWithBoundary G)
    (boundary : PlanarBoundaryAnnulusBoundaryData emb) where
  current : PlanarBoundaryAnnulusCurrentBoundaryData emb
  numCollars_eq_one : current.numCollars = 1
  boundary_eq : current.toPlanarBoundaryAnnulusBoundaryData = boundary

/-- A real Tait coloring together with an exact v23 residual boundary initial
state for a chosen color pair and face boundary.  The residual state is
unconditionally constructible (see `TaitV23Data.ofTait`), so the genuine
content of this bundle is the Tait coloring itself; the seed fields are kept
because the manuscript's Step 2 statements quantify over them. -/
structure TaitV23Data (G : SimpleGraph V) where
  coloring : G.EdgeColoring Color
  isTait : IsTaitEdgeColoring G coloring
  a : Color
  b : Color
  faceBoundary : Finset G.edgeSet
  v23 : Nonempty (V23ResidualBoundaryInitialState coloring a b faceBoundary)

/-- Any Tait coloring yields the full v23 bundle for any color pair and face
boundary, because the exact v23 Step 2 purification is already proved. -/
def TaitV23Data.ofTait (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (a b : Color) (faceBoundary : Finset G.edgeSet) : TaitV23Data G :=
  ⟨C, hC, a, b, faceBoundary,
    ⟨residualBoundaryInitialState_of_sum_v23_single_component_purifications_eq_boundaryOnlyGenerator
      C a b faceBoundary⟩⟩

/-- The endpoint-bearing exact one-collar/v23 shell over the honest closed-walk
source presentation.  This is the strongest hypothesis package on the
closed-walk branch that is currently known *not* to force the missing
same-embedding geometry. -/
structure ClosedWalkExactShell (emb : PlaneEmbeddingWithBoundary G) where
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  oneCollar : ExactOneCollarOn emb source.toPlanarBoundaryAnnulusBoundaryData
  tait : TaitV23Data G
  endpoint : HasUnblockedInteriorEndpoint emb

/-- The selected-boundary-arc payload carried by the successor-cycle shell.  Naming this
dependent projection keeps the live shell interface compact while preserving the exact
successor-cycle geometry required by the closed-walk lowering. -/
abbrev SuccessorCycleSelectedBoundaryArcData {emb : PlaneEmbeddingWithBoundary G}
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb) : Sort _ :=
  (f : AmbientFace emb.faces) →
    (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
      |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f

/-- The endpoint-bearing exact one-collar/v23 shell over the successor-cycle
boundary-order presentation. -/
structure SuccessorCycleExactShell (emb : PlaneEmbeddingWithBoundary G) where
  boundaryReachability : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb
  selectedBoundaryArc : SuccessorCycleSelectedBoundaryArcData dartCycles
  oneCollar : ExactOneCollarOn emb boundaryReachability.toPlanarBoundaryAnnulusBoundaryData
  tait : TaitV23Data G
  endpoint : HasUnblockedInteriorEndpoint emb

namespace ClosedWalkExactShell

/-- Build the exact shell from the finite no-selected-boundary-chord repair. -/
def ofInteriorEdgesNotSelectedBoundaryChords
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (oneCollar : ExactOneCollarOn emb source.toPlanarBoundaryAnnulusBoundaryData)
    (tait : TaitV23Data G)
    (hChordFree : InteriorEdgesNotSelectedBoundaryChords emb)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    ClosedWalkExactShell emb where
  source := source
  oneCollar := oneCollar
  tait := tait
  endpoint :=
    hasUnblockedInteriorEndpoint_of_interiorEdgesNotSelectedBoundaryChords_and_nonempty
      hChordFree hInterior

/-- Build the exact shell from selected-boundary inducedness, the endpoint repair that survives
the validation-lab stress suite. -/
def ofSelectedBoundaryInducedSubgraph
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (oneCollar : ExactOneCollarOn emb source.toPlanarBoundaryAnnulusBoundaryData)
    (tait : TaitV23Data G)
    (hInduced : SelectedBoundaryInducedSubgraph emb)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    ClosedWalkExactShell emb where
  source := source
  oneCollar := oneCollar
  tait := tait
  endpoint :=
    hasUnblockedInteriorEndpoint_of_selectedBoundaryInducedSubgraph_and_nonempty
      hInduced hInterior

/-- Build the exact shell from the split-boundary finite repair: each component boundary is
induced and the two endpoint supports are cross-component chord-free. -/
def ofBoundarySplitInducedCrossComponentChordFree
    {emb : PlaneEmbeddingWithBoundary G} {outer inner : Finset G.edgeSet}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (oneCollar : ExactOneCollarOn emb source.toPlanarBoundaryAnnulusBoundaryData)
    (tait : TaitV23Data G)
    (hSelected :
      selectedBoundarySupport emb.faceBoundary emb.faces emb.faces = outer ∪ inner)
    (hOuter : BoundaryEdgeSetInducedSubgraph outer)
    (hInner : BoundaryEdgeSetInducedSubgraph inner)
    (hCross : BoundaryEdgeSetCrossComponentChordFree outer inner)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    ClosedWalkExactShell emb where
  source := source
  oneCollar := oneCollar
  tait := tait
  endpoint :=
    hasUnblockedInteriorEndpoint_of_selectedBoundarySupport_eq_union_of_induced_of_crossComponentChordFree_and_nonempty
      hSelected hOuter hInner hCross hInterior

end ClosedWalkExactShell

namespace SuccessorCycleExactShell

/-- Build the successor-cycle exact shell from the finite no-selected-boundary-chord repair. -/
def ofInteriorEdgesNotSelectedBoundaryChords
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryReachability : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (selectedBoundaryArc : SuccessorCycleSelectedBoundaryArcData dartCycles)
    (oneCollar : ExactOneCollarOn emb
      boundaryReachability.toPlanarBoundaryAnnulusBoundaryData)
    (tait : TaitV23Data G)
    (hChordFree : InteriorEdgesNotSelectedBoundaryChords emb)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    SuccessorCycleExactShell emb where
  boundaryReachability := boundaryReachability
  dartCycles := dartCycles
  selectedBoundaryArc := selectedBoundaryArc
  oneCollar := oneCollar
  tait := tait
  endpoint :=
    hasUnblockedInteriorEndpoint_of_interiorEdgesNotSelectedBoundaryChords_and_nonempty
      hChordFree hInterior

/-- Build the successor-cycle exact shell from selected-boundary inducedness. -/
def ofSelectedBoundaryInducedSubgraph
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryReachability : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (selectedBoundaryArc : SuccessorCycleSelectedBoundaryArcData dartCycles)
    (oneCollar : ExactOneCollarOn emb
      boundaryReachability.toPlanarBoundaryAnnulusBoundaryData)
    (tait : TaitV23Data G)
    (hInduced : SelectedBoundaryInducedSubgraph emb)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    SuccessorCycleExactShell emb where
  boundaryReachability := boundaryReachability
  dartCycles := dartCycles
  selectedBoundaryArc := selectedBoundaryArc
  oneCollar := oneCollar
  tait := tait
  endpoint :=
    hasUnblockedInteriorEndpoint_of_selectedBoundaryInducedSubgraph_and_nonempty
      hInduced hInterior

/-- Build the successor-cycle exact shell from the split-boundary finite repair. -/
def ofBoundarySplitInducedCrossComponentChordFree
    {emb : PlaneEmbeddingWithBoundary G} {outer inner : Finset G.edgeSet}
    (boundaryReachability : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (selectedBoundaryArc : SuccessorCycleSelectedBoundaryArcData dartCycles)
    (oneCollar : ExactOneCollarOn emb
      boundaryReachability.toPlanarBoundaryAnnulusBoundaryData)
    (tait : TaitV23Data G)
    (hSelected :
      selectedBoundarySupport emb.faceBoundary emb.faces emb.faces = outer ∪ inner)
    (hOuter : BoundaryEdgeSetInducedSubgraph outer)
    (hInner : BoundaryEdgeSetInducedSubgraph inner)
    (hCross : BoundaryEdgeSetCrossComponentChordFree outer inner)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    SuccessorCycleExactShell emb where
  boundaryReachability := boundaryReachability
  dartCycles := dartCycles
  selectedBoundaryArc := selectedBoundaryArc
  oneCollar := oneCollar
  tait := tait
  endpoint :=
    hasUnblockedInteriorEndpoint_of_selectedBoundarySupport_eq_union_of_induced_of_crossComponentChordFree_and_nonempty
      hSelected hOuter hInner hCross hInterior

end SuccessorCycleExactShell

/-- Lower the successor-cycle shell to the honest closed-walk shell.  The
boundary split of the lowered source is definitionally the reachability
split, so the exact one-collar data transports unchanged. -/
def SuccessorCycleExactShell.toClosedWalkExactShell
    {emb : PlaneEmbeddingWithBoundary G} (shell : SuccessorCycleExactShell emb) :
    ClosedWalkExactShell emb where
  source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      shell.boundaryReachability shell.dartCycles shell.selectedBoundaryArc
  oneCollar := shell.oneCollar
  tait := shell.tait
  endpoint := shell.endpoint

/-- Generic refutation schema: one explicit witness of a shell that fails a
target refutes every universal derivation of that target from that shell.
All of the route-audit converse failures are instances of this lemma applied to
a bundled shell. -/
theorem not_forall_target_of_exists_shell_witness {ι : Sort*}
    {Shell Target : ι → Prop} (h : ∃ i, Shell i ∧ ¬ Target i) :
    ¬ ∀ i, Shell i → Target i := by
  rcases h with ⟨i, hShell, hNotTarget⟩
  exact fun hAll => hNotTarget (hAll i hShell)

end Mettapedia.GraphTheory.FourColor
