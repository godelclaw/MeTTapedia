import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLiteralProfileCount

/-!
# Literal boundary-color `Count` matrix for source crosscuts

For the open component between two source transversals, the color-coordinate
of the compositional `Count` functor is an actual finite matrix: an entry
counts the open Tait colorings whose left and right literal boundary words are
the selected pair.  This is generated from the source crosscut construction,
not imported from a configuration catalogue.  The full transfer state further
refines these entries by connectivity and capped face-progress.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionRotation
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SpliceUnification.OrderedCutSpliceData
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The left literal boundary word of an open source component. -/
noncomputable def sourceCrosscutLiteralOpenLeftBoundaryWord
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color) :
    Fin pair.left.walk.length → Color :=
  fun step => pair.sourceCrosscutInsideBoundaryWord data boundary coloring (.inl step)

/-- The right literal boundary word of an open source component. -/
noncomputable def sourceCrosscutLiteralOpenRightBoundaryWord
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color) :
    Fin pair.right.walk.length → Color :=
  fun step => pair.sourceCrosscutInsideBoundaryWord data boundary coloring (.inr step)

/-- The finite fiber of literal open Tait colorings at a pair of actual source
boundary words. -/
noncomputable def sourceCrosscutLiteralOpenTaitColoringFiber
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
    (left : Fin pair.left.walk.length → Color)
    (right : Fin pair.right.walk.length → Color) :
    Finset ((pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color) := by
  classical
  exact Finset.univ.filter fun coloring =>
    (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring coloring ∧
      pair.sourceCrosscutLiteralOpenLeftBoundaryWord data boundary coloring = left ∧
      pair.sourceCrosscutLiteralOpenRightBoundaryWord data boundary coloring = right

/-- The color-coordinate matrix of the source's `Count` functor for the
literal crosscut component.  It counts open Tait colorings by their two
actual boundary words. -/
noncomputable def sourceCrosscutLiteralOpenBoundaryColorCount
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
    Matrix (Fin pair.left.walk.length → Color)
      (Fin pair.right.walk.length → Color) Nat :=
  fun left right => (pair.sourceCrosscutLiteralOpenTaitColoringFiber
    data boundary left right).card

@[simp]
theorem sourceCrosscutLiteralOpenBoundaryColorCount_apply
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
    (left : Fin pair.left.walk.length → Color)
    (right : Fin pair.right.walk.length → Color) :
    pair.sourceCrosscutLiteralOpenBoundaryColorCount data boundary left right =
      (pair.sourceCrosscutLiteralOpenTaitColoringFiber data boundary left right).card :=
  rfl

/-- Membership in a literal matrix fiber is exactly the intended open Tait
condition together with the two source boundary-word equations. -/
theorem mem_sourceCrosscutLiteralOpenTaitColoringFiber_iff
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
    (left : Fin pair.left.walk.length → Color)
    (right : Fin pair.right.walk.length → Color)
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color) :
    coloring ∈ pair.sourceCrosscutLiteralOpenTaitColoringFiber data boundary left right ↔
      (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring coloring ∧
        pair.sourceCrosscutLiteralOpenLeftBoundaryWord data boundary coloring = left ∧
        pair.sourceCrosscutLiteralOpenRightBoundaryWord data boundary coloring = right := by
  classical
  simp [sourceCrosscutLiteralOpenTaitColoringFiber]

/-- A Tait coloring of the shortened splice realizes the diagonal boundary
entry selected by its sewn seam word.  This connects the actual output
coloring to a positive entry of the literal source `Count` matrix. -/
theorem sourceCrosscutSpliceOutputOpenColoring_mem_literalBoundaryFiber
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
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1)
    (output :
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output.EdgeColoring
        Color)
    (houtput : RotationSystem.IsTaitEdgeColoring
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output output) :
    pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output ∈
      pair.sourceCrosscutLiteralOpenTaitColoringFiber data boundary
        (seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints) output)
        (fun step => seamColorWord
          (pair.sourceCrosscutSpliceData data boundary seamEndpoints) output
          (Fin.cast pair.length_eq.symm step)) := by
  apply (pair.mem_sourceCrosscutLiteralOpenTaitColoringFiber_iff data boundary _ _ _).2
  refine ⟨pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary
    seamEndpoints output houtput, ?_, ?_⟩
  · funext step
    exact pair.sourceCrosscutOutputInsideBoundaryWord_left_eq_seamColorWord
      data boundary seamEndpoints output step
  · funext step
    exact pair.sourceCrosscutOutputInsideBoundaryWord_right_eq_seamColorWord
      data boundary seamEndpoints output (Fin.cast pair.length_eq.symm step)

/-- The diagonal source `Count` entry selected by every shortened-splice Tait
coloring is positive.  This is the exact finite-count form of the output
restriction, ready for the later transfer-factorization argument. -/
theorem sourceCrosscutSpliceOutput_literalBoundaryColorCount_pos
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
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1)
    (output :
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output.EdgeColoring
        Color)
    (houtput : RotationSystem.IsTaitEdgeColoring
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output output) :
    0 < pair.sourceCrosscutLiteralOpenBoundaryColorCount data boundary
      (seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints) output)
      (fun step => seamColorWord
        (pair.sourceCrosscutSpliceData data boundary seamEndpoints) output
        (Fin.cast pair.length_eq.symm step)) := by
  rw [pair.sourceCrosscutLiteralOpenBoundaryColorCount_apply]
  apply Finset.card_pos.mpr
  exact ⟨pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output,
    pair.sourceCrosscutSpliceOutputOpenColoring_mem_literalBoundaryFiber
      data boundary seamEndpoints output houtput⟩

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
