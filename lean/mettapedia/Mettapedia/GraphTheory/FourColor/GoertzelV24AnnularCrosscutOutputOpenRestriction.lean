import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLiteralOpenRegion
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionOutputRestriction

/-!
# Reading a source crosscut splice as its literal open tangle

The two simple source transversals construct both the concrete shortened map
and the literal retained open tangle.  This module identifies the latter with
the restriction of a coloring of the former.  Thus the semantic `Count`
object used by the source is populated by an actual coloring of its source
crosscut region, not by an abstract boundary word.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutOpenRegionalProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionOutputRestriction
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SpliceUnification
open GoertzelV24SpliceUnification.OrderedCutSpliceData
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- A Tait coloring of the concrete source crosscut splice restricts to an
actual coloring of the literal open tangle bounded by the same two source
transversals. -/
noncomputable def sourceCrosscutSpliceOutputOpenColoring
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
    (coloring :
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output.EdgeColoring
        Color) :
    (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color := by
  exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionOutputRestriction.OrderedCutSpliceData.outputOpenColoring
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints) coloring

/-- The source literal open tangle inherits the Tait property from the
shortened source crosscut splice. -/
theorem sourceCrosscutSpliceOutputOpenColoring_isTait
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
    (coloring :
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output.EdgeColoring
        Color)
    (hcoloring : RotationSystem.IsTaitEdgeColoring
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output coloring) :
    (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring
      (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints
        coloring) := by
  exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionOutputRestriction.OrderedCutSpliceData.outputOpenColoring_isTait
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints) coloring hcoloring

/-- Reading the source open tangle at any of its darts is literally reading
the corresponding dart of the shortened splice.  In particular this gives
the future semantic-profile construction its boundary colors from a concrete
shortened-map coloring. -/
theorem sourceCrosscutSpliceOutputOpenColoring_edgeOf
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
    (coloring :
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output.EdgeColoring
        Color)
    (dart : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component)) :
    pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints
        coloring ((pair.sourceCrosscutOpenRegion data boundary).edgeOf dart) =
      _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionOutputRestriction.OrderedCutSpliceData.outputOpenDartColor
        (pair.sourceCrosscutSpliceData data boundary seamEndpoints) coloring dart := by
  exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionOutputRestriction.OrderedCutSpliceData.outputOpenColoring_edgeOf
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints) coloring dart

/-- The actual *seam* words that extend to a Tait coloring of the literal
source crosscut tangle.  Both source transversals must read the same word
(after the certified length transport): a sewn output has this property, and
it is the condition required to glue the complementary tangle back in.

This is a semantic set: membership is witnessed by a concrete open-tangle
coloring, not by a syntactic profile code. -/
def sourceCrosscutOpenExtendableWords
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
    SemanticBoundaryProfile pair.left.walk.length :=
  { word | ∃ coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color,
      (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring coloring ∧
        (∀ step,
          word step = coloring ((pair.sourceCrosscutOpenRegion data boundary).edgeOf
            (Sum.inl (orderedBoundaryDart data.toRotationSystem
              (fun vertex => vertex ∈ pair.componentSide boundary.component)
              (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1))) ∧
        ∀ step,
          word step = coloring ((pair.sourceCrosscutOpenRegion data boundary).edgeOf
            (Sum.inl (orderedBoundaryDart data.toRotationSystem
              (fun vertex => vertex ∈ pair.componentSide boundary.component)
              (fun index => pair.right.crossingEdge hunique
                (Fin.cast pair.length_eq index))
              (fun index => boundary.rightCrosses
                (Fin.cast pair.length_eq index)) step).1.1)) }

/-- At every ordered left source-crosscut port, the literal open tangle reads
the seam word of the shortened splice.  This is the concrete map from a
shortened coloring into the source's finite interface semantics. -/
theorem sourceCrosscutSpliceOutputOpenColoring_leftBoundary_eq_seamColorWord
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
    (coloring :
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output.EdgeColoring
        Color)
    (step : Fin pair.left.walk.length) :
    pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints
        coloring ((pair.sourceCrosscutOpenRegion data boundary).edgeOf
          (Sum.inl (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1)) =
      seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
        coloring step := by
  rw [pair.sourceCrosscutSpliceOutputOpenColoring_edgeOf data boundary
    seamEndpoints coloring]
  exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionOutputRestriction.OrderedCutSpliceData.outputOpenDartColor_leftBoundary_eq_seamColorWord
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints) coloring step

/-- The aligned right source boundary of a sewn output reads the very same
seam word as the left boundary.  This is the second half of seam compatibility
for the literal retained open tangle. -/
theorem sourceCrosscutSpliceOutputOpenColoring_rightBoundary_eq_seamColorWord
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
    (coloring :
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output.EdgeColoring
        Color)
    (step : Fin pair.left.walk.length) :
    pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints
        coloring ((pair.sourceCrosscutOpenRegion data boundary).edgeOf
          (Sum.inl (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1)) =
      seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
        coloring step := by
  rw [pair.sourceCrosscutSpliceOutputOpenColoring_edgeOf data boundary
    seamEndpoints coloring]
  exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionOutputRestriction.OrderedCutSpliceData.outputOpenDartColor_rightBoundary_eq_seamColorWord
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints) coloring step

/-- Every Tait coloring of the shortened source splice supplies a witnessed
member of the literal source tangle's semantic boundary-word set.  This is
the `shortened_word_mem_inner` half of the reverse-completion interface for
this concrete splice; the opposite extension/gluing direction remains a
separate theorem. -/
theorem seamColorWord_mem_sourceCrosscutOpenExtendableWords
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
    (coloring :
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output.EdgeColoring
        Color)
    (hcoloring : RotationSystem.IsTaitEdgeColoring
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output coloring) :
    seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
      coloring ∈ pair.sourceCrosscutOpenExtendableWords data boundary := by
  refine ⟨pair.sourceCrosscutSpliceOutputOpenColoring data boundary
    seamEndpoints coloring,
    pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary
      seamEndpoints coloring hcoloring, ?_, ?_⟩
  · intro step
    symm
    exact pair.sourceCrosscutSpliceOutputOpenColoring_leftBoundary_eq_seamColorWord
      data boundary seamEndpoints coloring step
  · intro step
    symm
    exact pair.sourceCrosscutSpliceOutputOpenColoring_rightBoundary_eq_seamColorWord
      data boundary seamEndpoints coloring step

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
