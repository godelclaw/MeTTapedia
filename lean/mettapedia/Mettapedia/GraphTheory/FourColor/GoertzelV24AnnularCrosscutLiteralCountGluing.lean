import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLiteralProfileMatrix

/-!
# Literal `Count` support under source-crosscut gluing

The source's compositional operation glues two literal open tangles along
their matching seam.  This file gives the support-level counting statement:
positive finite counts on the retained and complementary pieces at the same
source seam word produce an ambient Tait coloring.  It is the nonzero-entry
form of the matrix-product law; exact multiplicities can be refined later
without changing the geometric gluing construction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionRotation
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SpliceUnification
open GoertzelV24SpliceUnification.OrderedCutSpliceData
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The finite fiber of complementary literal open Tait colorings realizing
one aligned source seam word. -/
noncomputable def sourceCrosscutComplementSeamColoringFiber
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
    (hcubic : data.toRotationSystem.IsCubic)
    (word : Fin pair.left.walk.length → Color) :
    Finset ((pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color) := by
  classical
  exact Finset.univ.filter fun coloring =>
    (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
      coloring ∧
      (∀ step : Fin pair.left.walk.length,
        pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic coloring
          (.inl step) = word step) ∧
      (∀ step : Fin pair.right.walk.length,
        pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic coloring
          (.inr step) = word (Fin.cast pair.length_eq.symm step))

/-- The generated finite count of complementary open Tait colorings at one
source seam word. -/
noncomputable def sourceCrosscutComplementSeamColorCount
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
    (hcubic : data.toRotationSystem.IsCubic)
    (word : Fin pair.left.walk.length → Color) : Nat :=
  (pair.sourceCrosscutComplementSeamColoringFiber data boundary hcubic word).card

@[simp]
theorem sourceCrosscutComplementSeamColorCount_apply
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
    (hcubic : data.toRotationSystem.IsCubic)
    (word : Fin pair.left.walk.length → Color) :
    pair.sourceCrosscutComplementSeamColorCount data boundary hcubic word =
      (pair.sourceCrosscutComplementSeamColoringFiber data boundary hcubic word).card :=
  rfl

/-- Membership in a complementary literal count fiber has exactly the
semantic content of the source's extendable-seam-word set. -/
theorem mem_sourceCrosscutComplementSeamColoringFiber_iff
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
    (hcubic : data.toRotationSystem.IsCubic)
    (word : Fin pair.left.walk.length → Color)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color) :
    coloring ∈ pair.sourceCrosscutComplementSeamColoringFiber data boundary hcubic word ↔
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
        coloring ∧
      (∀ step : Fin pair.left.walk.length,
        pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic coloring
          (.inl step) = word step) ∧
      (∀ step : Fin pair.right.walk.length,
        pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic coloring
          (.inr step) = word (Fin.cast pair.length_eq.symm step)) := by
  classical
  simp [sourceCrosscutComplementSeamColoringFiber]

/-- A complementary seam word has positive generated count exactly when it
is semantically extendable through the literal complementary tangle. -/
theorem sourceCrosscutComplementSeamColorCount_pos_iff
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
    (hcubic : data.toRotationSystem.IsCubic)
    (word : Fin pair.left.walk.length → Color) :
    0 < pair.sourceCrosscutComplementSeamColorCount data boundary hcubic word ↔
      word ∈ pair.sourceCrosscutComplementSeamExtendableWords data boundary hcubic := by
  rw [pair.sourceCrosscutComplementSeamColorCount_apply]
  constructor
  · intro hpositive
    rcases Finset.card_pos.mp hpositive with ⟨coloring, hmember⟩
    rcases (pair.mem_sourceCrosscutComplementSeamColoringFiber_iff data boundary
      hcubic word coloring).1 hmember with ⟨hcoloring, hleft, hright⟩
    exact ⟨coloring, hcoloring, hleft, hright⟩
  · rintro ⟨coloring, hcoloring, hleft, hright⟩
    apply Finset.card_pos.mpr
    refine ⟨coloring, ?_⟩
    exact (pair.mem_sourceCrosscutComplementSeamColoringFiber_iff data boundary
      hcubic word coloring).2 ⟨hcoloring, hleft, hright⟩

/-- The retained-side color count restricted to the seam-compatible diagonal
of its two boundary coordinates. -/
noncomputable def sourceCrosscutLiteralOpenSeamColorCount
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
    (word : Fin pair.left.walk.length → Color) : Nat :=
  pair.sourceCrosscutLiteralOpenBoundaryColorCount data boundary word
    (fun step => word (Fin.cast pair.length_eq.symm step))

/-- Positive retained and complementary seam counts at one word glue to a
proper ambient Tait coloring.  This is the source's compositional gluing law
at the support level, with both witnesses extracted from finite literal
coloring fibers. -/
theorem taitColorable_of_positive_sourceCrosscutSeamColorCounts
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
    (hcubic : data.toRotationSystem.IsCubic)
    (word : Fin pair.left.walk.length → Color)
    (hinside : 0 < pair.sourceCrosscutLiteralOpenSeamColorCount data boundary word)
    (houtside : 0 < pair.sourceCrosscutComplementSeamColorCount
      data boundary hcubic word) :
    TaitColorable (RS := data.toRotationSystem) := by
  rw [sourceCrosscutLiteralOpenSeamColorCount,
    pair.sourceCrosscutLiteralOpenBoundaryColorCount_apply] at hinside
  rcases Finset.card_pos.mp hinside with ⟨inside, hinsideMember⟩
  rcases (pair.mem_sourceCrosscutLiteralOpenTaitColoringFiber_iff data boundary
    word (fun step => word (Fin.cast pair.length_eq.symm step)) inside).1
      hinsideMember with ⟨hinsideTait, hinsideLeft, hinsideRight⟩
  rw [pair.sourceCrosscutComplementSeamColorCount_apply] at houtside
  rcases Finset.card_pos.mp houtside with ⟨outside, houtsideMember⟩
  rcases (pair.mem_sourceCrosscutComplementSeamColoringFiber_iff data boundary
    hcubic word outside).1 houtsideMember with ⟨houtsideTait, houtsideLeft, houtsideRight⟩
  apply pair.exists_sourceCrosscutAmbientTaitColoring_of_openColorings_of_words_eq
    data boundary hcubic inside outside hinsideTait houtsideTait
  funext index
  rcases index with step | step
  · calc
      pair.sourceCrosscutInsideBoundaryWord data boundary inside (.inl step) =
          word step := by
        simpa [sourceCrosscutLiteralOpenLeftBoundaryWord] using congrFun hinsideLeft step
      _ = pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic outside
          (.inl step) := (houtsideLeft step).symm
  · calc
      pair.sourceCrosscutInsideBoundaryWord data boundary inside (.inr step) =
          word (Fin.cast pair.length_eq.symm step) := by
        simpa [sourceCrosscutLiteralOpenRightBoundaryWord] using congrFun hinsideRight step
      _ = pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic outside
          (.inr step) := (houtsideRight step).symm

/-- A shortened-splice coloring supplies the retained positive seam count;
therefore a positive complementary count at its sewn word completes it back
to a Tait coloring of the original source graph.  This is the literal-count
form of the reverse-completion step. -/
theorem sourceCrosscutComplete_of_positiveComplementSeamColorCount
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
    (hcubic : data.toRotationSystem.IsCubic)
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
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output output)
    (hcomplement :
      0 < pair.sourceCrosscutComplementSeamColorCount data boundary hcubic
        (seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
          output)) :
    TaitColorable (RS := data.toRotationSystem) := by
  apply pair.taitColorable_of_positive_sourceCrosscutSeamColorCounts
    data boundary hcubic
      (seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints) output)
  · simpa [sourceCrosscutLiteralOpenSeamColorCount] using
      (pair.sourceCrosscutSpliceOutput_literalBoundaryColorCount_pos
        data boundary seamEndpoints output houtput)
  · exact hcomplement

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
