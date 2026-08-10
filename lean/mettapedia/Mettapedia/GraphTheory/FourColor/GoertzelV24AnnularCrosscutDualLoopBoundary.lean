import Mettapedia.GraphTheory.FourColor.GoertzelV24DualCycleDeletedBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualCycleBoundaryFaceOrientation
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversalAppend

/-!
# Concrete deleted-boundary coordinates for a source crosscut loop

The paired source transversals already give an exact finite cut and a chosen
outward dart at every cut edge.  Their facial-dual composite is a simple
cycle.  This module puts those two finite descriptions in the same
coordinates: left forward, then right backward.  The remaining face-side
incidence is deliberately kept as a concrete theorem target; it is supplied
by the corridor-layer construction, not by a profile assumption.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24DualCycleBoundaryFaceOrientation
open GoertzelV24DualCycleDeletedBoundaryOrder
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The source dual loop has twice the common transversal width. -/
theorem dualLoop_length_eq_double
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    pair.dualLoop.length = pair.left.walk.length + pair.left.walk.length := by
  rw [pair.dualLoop_length, pair.length_eq]

/-- The source's two interface lists, in the cyclic order of the facial-dual
loop: the left list forward and the right list backward. -/
noncomputable def sourceCrosscutDualLoopPositionEquiv
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    Fin pair.dualLoop.length ≃ OrderedSeamPosition pair.left.walk.length :=
  (finCongr (pair.dualLoop_length_eq_double data)).trans
    (oppositeBoundaryPositionEquiv pair.left.walk.length).symm

/-- The actual retained-side boundary dart at each facial-dual loop step.
This is a fully concrete enumeration: no arbitrary `Fintype` choice is used. -/
noncomputable def sourceCrosscutDualLoopBoundaryEquiv
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    Fin pair.dualLoop.length ≃
      BoundaryDart data.toRotationSystem
        (deletedRegionKeep (boundary.deletedVertices data pair)) :=
  (pair.sourceCrosscutDualLoopPositionEquiv data).trans
    (orderedBoundaryPositionEquiv data.toRotationSystem
      (boundary.deletedVertices data pair)
      (pair.left.crossingEdge hunique)
      (fun step : Fin pair.left.walk.length =>
        pair.right.crossingEdge hunique (Fin.cast pair.length_eq step))
      (boundary.orderedCut_boundary_eq data pair)
      boundary.leftInjective
      (pair.sourceCrosscutOrderedCutSidesData data boundary).rightInjective
      (pair.sourceCrosscutOrderedCutSidesData data boundary).disjoint)

/-- The concrete loop-boundary enumeration is exhaustive and duplication-free
by construction. -/
theorem sourceCrosscutDualLoopBoundaryEquiv_bijective
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    Function.Bijective (pair.sourceCrosscutDualLoopBoundaryEquiv data boundary) :=
  (pair.sourceCrosscutDualLoopBoundaryEquiv data boundary).bijective

/-- The loop step occupying one of the source boundary coordinates.  Keeping
this inverse map named lets the edge calculation split on the two real source
transversals instead of on an arbitrary natural-number offset. -/
noncomputable def sourceCrosscutDualLoopStepAt
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (position : OrderedSeamPosition pair.left.walk.length) :
    Fin pair.dualLoop.length :=
  (pair.sourceCrosscutDualLoopPositionEquiv data).symm position

/-- Evaluating the concrete boundary enumeration at the loop step for a
source coordinate returns the corresponding source-ordered boundary dart. -/
theorem sourceCrosscutDualLoopBoundaryEquiv_at_coordinate
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (position : OrderedSeamPosition pair.left.walk.length) :
    (pair.sourceCrosscutDualLoopBoundaryEquiv data boundary)
        (pair.sourceCrosscutDualLoopStepAt data position) =
      orderedBoundaryPositionEquiv data.toRotationSystem
        (boundary.deletedVertices data pair)
        (pair.left.crossingEdge hunique)
        (fun step : Fin pair.left.walk.length =>
          pair.right.crossingEdge hunique (Fin.cast pair.length_eq step))
        (boundary.orderedCut_boundary_eq data pair)
        boundary.leftInjective
        (pair.sourceCrosscutOrderedCutSidesData data boundary).rightInjective
        (pair.sourceCrosscutOrderedCutSidesData data boundary).disjoint
        position := by
  simp [sourceCrosscutDualLoopBoundaryEquiv,
    sourceCrosscutDualLoopStepAt]

/-- The left source coordinate is the corresponding initial step of the
facial-dual loop. -/
theorem sourceCrosscutDualLoopStepAt_left
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (step : Fin pair.left.walk.length) :
    pair.sourceCrosscutDualLoopStepAt data (Sum.inl step) =
      ⟨step.val, by
        rw [pair.dualLoop_length]
        omega⟩ := by
  apply Fin.ext
  simp [sourceCrosscutDualLoopStepAt,
    sourceCrosscutDualLoopPositionEquiv,
    oppositeBoundaryPositionEquiv]

/-- The right source coordinate is traversed in reverse after the left
transversal in the facial-dual loop. -/
theorem sourceCrosscutDualLoopStepAt_right
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (step : Fin pair.left.walk.length) :
    pair.sourceCrosscutDualLoopStepAt data (Sum.inr step) =
      ⟨pair.left.walk.length + (Fin.cast pair.length_eq step).rev.val, by
        rw [pair.dualLoop_length]
        exact Nat.add_lt_add_left
          (Fin.cast pair.length_eq step).rev.isLt _⟩ := by
  have hlength : pair.left.walk.length = pair.right.walk.length :=
    pair.length_eq
  apply Fin.ext
  simp [sourceCrosscutDualLoopStepAt,
    sourceCrosscutDualLoopPositionEquiv,
    oppositeBoundaryPositionEquiv, Fin.revPerm, Fin.rev]
  omega

/-- The dual-loop crossing at a left source coordinate is the left
transversal crossing itself. -/
theorem dualWalkCrossingEdge_sourceCrosscutDualLoop_left
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (step : Fin pair.left.walk.length) :
    dualWalkCrossingEdge (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
        pair.dualLoop (pair.sourceCrosscutDualLoopStepAt data (Sum.inl step)) =
      pair.left.crossingEdge hunique step := by
  rw [pair.sourceCrosscutDualLoopStepAt_left data step]
  simpa [dualLoop, SimpleDualCrosscut.crossingEdge] using
    (dualWalkCrossingEdge_append_left
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
      pair.left.walk pair.right.walk.reverse step)

/-- The dual-loop crossing at a right source coordinate is the aligned right
transversal crossing, with its traversal direction reversed. -/
theorem dualWalkCrossingEdge_sourceCrosscutDualLoop_right
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (step : Fin pair.left.walk.length) :
    dualWalkCrossingEdge (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
        pair.dualLoop (pair.sourceCrosscutDualLoopStepAt data (Sum.inr step)) =
      pair.right.crossingEdge hunique (Fin.cast pair.length_eq step) := by
  let rightStep : Fin pair.right.walk.length := Fin.cast pair.length_eq step
  let reverseStep : Fin pair.right.walk.reverse.length :=
    ⟨rightStep.rev.val, by simpa using rightStep.rev.isLt⟩
  have hreverseStep :
      reverseStep =
        ⟨pair.right.walk.length - (rightStep.val + 1), by
          rw [SimpleGraph.Walk.length_reverse]
          omega⟩ := by
    apply Fin.ext
    simp [reverseStep, Fin.rev]
  rw [pair.sourceCrosscutDualLoopStepAt_right data step]
  change dualWalkCrossingEdge (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
      pair.dualLoop
      ⟨pair.left.walk.length + rightStep.rev.val, by
        rw [pair.dualLoop_length]
        exact Nat.add_lt_add_left rightStep.rev.isLt _⟩ =
    pair.right.crossingEdge hunique rightStep
  calc
    dualWalkCrossingEdge (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
        pair.dualLoop
        ⟨pair.left.walk.length + rightStep.rev.val, by
          rw [pair.dualLoop_length]
          exact Nat.add_lt_add_left rightStep.rev.isLt _⟩ =
      dualWalkCrossingEdge (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
        pair.right.walk.reverse reverseStep := by
          simpa [dualLoop, reverseStep] using
            (dualWalkCrossingEdge_append_right
              (orbitFaceBoundary data.toRotationSystem)
              (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
              pair.left.walk pair.right.walk.reverse reverseStep)
    _ = pair.right.crossingEdge hunique rightStep := by
      rw [hreverseStep]
      simpa [SimpleDualCrosscut.crossingEdge] using
        (dualWalkCrossingEdge_reverse
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
          pair.right.walk rightStep)

/-- At a left source coordinate, the concrete deleted-boundary enumeration
crosses the left source transversal's literal edge. -/
theorem sourceCrosscutDualLoopBoundaryEquiv_edge_left
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (step : Fin pair.left.walk.length) :
    data.toRotationSystem.edgeOf
        ((pair.sourceCrosscutDualLoopBoundaryEquiv data boundary)
          (pair.sourceCrosscutDualLoopStepAt data (Sum.inl step))).1.1 =
      pair.left.crossingEdge hunique step := by
  rw [pair.sourceCrosscutDualLoopBoundaryEquiv_at_coordinate data boundary]
  exact orderedBoundaryDart_edgeOf data.toRotationSystem _ _ _ step

/-- At a right source coordinate, the concrete deleted-boundary enumeration
crosses the aligned right source transversal's literal edge. -/
theorem sourceCrosscutDualLoopBoundaryEquiv_edge_right
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (step : Fin pair.left.walk.length) :
    data.toRotationSystem.edgeOf
        ((pair.sourceCrosscutDualLoopBoundaryEquiv data boundary)
          (pair.sourceCrosscutDualLoopStepAt data (Sum.inr step))).1.1 =
      pair.right.crossingEdge hunique (Fin.cast pair.length_eq step) := by
  rw [pair.sourceCrosscutDualLoopBoundaryEquiv_at_coordinate data boundary]
  exact orderedBoundaryDart_edgeOf data.toRotationSystem _ _ _ step

/-- The concrete retained-side boundary enumeration and the simple facial-dual
loop cross exactly the same primal edge at every position.  This turns the
source's two open transversals into the pointwise edge premise consumed by
the generic deleted-boundary successor theorem. -/
theorem sourceCrosscutDualLoopBoundaryEquiv_edge_eq_dualLoopCrossing
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (step : Fin pair.dualLoop.length) :
    data.toRotationSystem.edgeOf
        ((pair.sourceCrosscutDualLoopBoundaryEquiv data boundary) step).1.1 =
      dualWalkCrossingEdge (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
        pair.dualLoop step := by
  let position := pair.sourceCrosscutDualLoopPositionEquiv data step
  have hstep : pair.sourceCrosscutDualLoopStepAt data position = step := by
    exact (pair.sourceCrosscutDualLoopPositionEquiv data).symm_apply_apply step
  rw [← hstep]
  rcases position with left | right
  · exact (sourceCrosscutDualLoopBoundaryEquiv_edge_left
      data pair boundary left).trans
        (dualWalkCrossingEdge_sourceCrosscutDualLoop_left data pair left).symm
  · exact (sourceCrosscutDualLoopBoundaryEquiv_edge_right
      data pair boundary right).trans
        (dualWalkCrossingEdge_sourceCrosscutDualLoop_right data pair right).symm

/-- The exact finite boundary of the source deletion is the crossing support
of its closed facial-dual loop. -/
theorem sourceCrosscut_vertexSetCrossingEdges_eq_dualLoopCrossingEdges
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    vertexSetCrossingEdges data.toRotationSystem
        (boundary.deletedVertices data pair) =
      dualWalkCrossingEdges (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
        pair.dualLoop := by
  calc
    vertexSetCrossingEdges data.toRotationSystem
        (boundary.deletedVertices data pair) =
        orderedCut (pair.left.crossingEdge hunique) ∪
          orderedCut (fun step : Fin pair.left.walk.length =>
            pair.right.crossingEdge hunique (Fin.cast pair.length_eq step)) :=
      (boundary.orderedCut_boundary_eq data pair).symm
    _ = pair.left.crossingEdges hunique ∪ pair.right.crossingEdges hunique := by
      rw [orderedCut_crossingEdge_eq_crossingEdges pair.left hunique,
        pair.orderedCut_sourceCrosscutRight_eq data,
        orderedCut_crossingEdge_eq_crossingEdges pair.right hunique]
    _ = pair.primalCutEdges data :=
      (pair.primalCutEdges_eq_sourceCrossingSupport data).symm
    _ = dualWalkCrossingEdges (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
        pair.dualLoop := rfl

/-- The one remaining local geometric fact needed to read the source
transversal loop as the actual deleted-boundary order.  It is deliberately
about concrete darts and concrete target faces, rather than a profile or a
semantic extension assumption. -/
def SourceCrosscutBoundaryData.DualLoopBoundaryFacesTarget
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) : Prop :=
  BoundaryDartsUseDualCycleTargetFaces data pair.dualLoop
    (boundary.deletedVertices data pair)
    (pair.sourceCrosscutDualLoopBoundaryEquiv data boundary)

/-- The target-face condition for the source crosscut is reduced all the way
to a concrete retained-side check on the literal target darts of its facial
dual loop.  The loop, the cut equality, and the boundary enumeration are
already constructed; a corridor formation need only prove that its selected
side contains these displayed darts. -/
theorem SourceCrosscutBoundaryData.dualLoopBoundaryFacesTarget_of_targetFaceDarts_kept
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hkept : ∀ step,
      deletedRegionKeep (boundary.deletedVertices data pair)
        (data.toRotationSystem.vertOf
          (dualWalkTargetFaceDart hunique pair.dualLoop step))) :
    boundary.DualLoopBoundaryFacesTarget data pair := by
  exact boundaryDartsUseDualCycleTargetFaces_of_targetFaceDarts_kept
    data pair.dualLoop (boundary.deletedVertices data pair)
    (pair.sourceCrosscut_vertexSetCrossingEdges_eq_dualLoopCrossingEdges
      data boundary)
    (pair.sourceCrosscutDualLoopBoundaryEquiv data boundary)
    (pair.sourceCrosscutDualLoopBoundaryEquiv_edge_eq_dualLoopCrossing
      data boundary)
    hkept

/-- Once the source layer formation supplies its target-face incidence, the
actual deleted boundary advances exactly one step around the source's simple
facial-dual loop.  All cut, coverage, and edge-alignment facts are now
constructed above. -/
theorem sourceCrosscut_deletedBoundarySuccessor_eq_dualLoopBoundaryOrder
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hfaces : boundary.DualLoopBoundaryFacesTarget data pair) :
    deletedRegionBoundarySuccessor data.toRotationSystem
        (boundary.deletedVertices data pair) =
      (pair.sourceCrosscutDualLoopBoundaryEquiv data boundary).permCongr
        (finRotate pair.dualLoop.length) := by
  let boundaryEquiv := pair.sourceCrosscutDualLoopBoundaryEquiv data boundary
  have hchosen : Equiv.ofBijective (boundaryEquiv : Fin pair.dualLoop.length →
      BoundaryDart data.toRotationSystem
        (deletedRegionKeep (boundary.deletedVertices data pair)))
      boundaryEquiv.bijective = boundaryEquiv := by
    apply Equiv.ext
    intro step
    rfl
  have hgeneric := deletedBoundarySuccessor_eq_dualCycleBoundaryOrder data htwoSided
    pair.dualLoop pair.dualLoop_isCycle
    (boundary.deletedVertices data pair)
    (pair.sourceCrosscut_vertexSetCrossingEdges_eq_dualLoopCrossingEdges
      data boundary)
    boundaryEquiv
    boundaryEquiv.bijective
    (pair.sourceCrosscutDualLoopBoundaryEquiv_edge_eq_dualLoopCrossing
      data boundary)
    hfaces
  rw [hchosen] at hgeneric
  exact hgeneric

/-- Reindexing `Fin` along an equality commutes with its positive cyclic
successor. -/
private theorem finCongr_permCongr_finRotate {m n : Nat} (h : m = n) :
    (finCongr h).permCongr (finRotate m) = finRotate n := by
  subst n
  rfl

/-- Conjugation along a composite coordinate map factors through its two
coordinate changes. -/
private theorem permCongr_trans_eq
    {A B C : Type*} (first : A ≃ B) (second : B ≃ C)
    (perm : Equiv.Perm A) :
    (first.trans second).permCongr perm =
      second.permCongr (first.permCongr perm) := by
  rfl

/-- In the source loop coordinates, one dual-loop step is exactly the
opposite-order boundary cycle: left forward and right backward. -/
theorem sourceCrosscutDualLoopPosition_rotate_eq_oppositeBoundaryCycle
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    (pair.sourceCrosscutDualLoopPositionEquiv data).permCongr
        (finRotate pair.dualLoop.length) =
      oppositeBoundaryCycle pair.left.walk.length := by
  unfold sourceCrosscutDualLoopPositionEquiv
  change
    ((finCongr (pair.dualLoop_length_eq_double data)).trans
      (oppositeBoundaryPositionEquiv pair.left.walk.length).symm).permCongr
        (finRotate pair.dualLoop.length) =
      (oppositeBoundaryPositionEquiv pair.left.walk.length).symm.permCongr
        (finRotate (pair.left.walk.length + pair.left.walk.length))
  rw [permCongr_trans_eq, finCongr_permCongr_finRotate]

/-- The source target-face incidence turns the computed deleted boundary into
the exact opposite order on the two original transverse interfaces.  This is
the geometric order premise required by the planar splice, now derived from
the concrete dual loop rather than supplied by a caller. -/
theorem sourceCrosscut_deletedBoundarySuccessor_eq_oppositeBoundaryOrder
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hfaces : boundary.DualLoopBoundaryFacesTarget data pair) :
    deletedRegionBoundarySuccessor data.toRotationSystem
        (boundary.deletedVertices data pair) =
      (orderedBoundaryPositionEquiv data.toRotationSystem
        (boundary.deletedVertices data pair)
        (pair.left.crossingEdge hunique)
        (fun step : Fin pair.left.walk.length =>
          pair.right.crossingEdge hunique (Fin.cast pair.length_eq step))
        (boundary.orderedCut_boundary_eq data pair)
        boundary.leftInjective
        (pair.sourceCrosscutOrderedCutSidesData data boundary).rightInjective
        (pair.sourceCrosscutOrderedCutSidesData data boundary).disjoint).permCongr
          (oppositeBoundaryCycle pair.left.walk.length) := by
  rw [pair.sourceCrosscut_deletedBoundarySuccessor_eq_dualLoopBoundaryOrder
    data htwoSided boundary hfaces]
  let loopPositionEquiv := pair.sourceCrosscutDualLoopPositionEquiv data
  let boundaryPositionEquiv := orderedBoundaryPositionEquiv
    data.toRotationSystem (boundary.deletedVertices data pair)
    (pair.left.crossingEdge hunique)
    (fun step : Fin pair.left.walk.length =>
      pair.right.crossingEdge hunique (Fin.cast pair.length_eq step))
    (boundary.orderedCut_boundary_eq data pair)
    boundary.leftInjective
    (pair.sourceCrosscutOrderedCutSidesData data boundary).rightInjective
    (pair.sourceCrosscutOrderedCutSidesData data boundary).disjoint
  change (loopPositionEquiv.trans boundaryPositionEquiv).permCongr
      (finRotate pair.dualLoop.length) =
    boundaryPositionEquiv.permCongr
      (oppositeBoundaryCycle pair.left.walk.length)
  apply Equiv.ext
  intro dart
  obtain ⟨position, rfl⟩ := boundaryPositionEquiv.surjective dart
  have hsymm :
      (loopPositionEquiv.trans boundaryPositionEquiv).symm
          (boundaryPositionEquiv position) =
        loopPositionEquiv.symm position := by
    simp [loopPositionEquiv, boundaryPositionEquiv]
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [hsymm]
  rw [← (pair.sourceCrosscutDualLoopPosition_rotate_eq_oppositeBoundaryCycle
    data)]
  change boundaryPositionEquiv
      (loopPositionEquiv
        (finRotate pair.dualLoop.length (loopPositionEquiv.symm position))) =
    boundaryPositionEquiv
      ((loopPositionEquiv.permCongr
        (finRotate pair.dualLoop.length)) position)
  rfl

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
