import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutOpenGluing

/-!
# Source-ordered boundary words for literal crosscut gluing

The two source transversals enumerate every exposed dart of their selected
deletion component.  This module reads colors of the two complementary
literal open tangles in that actual source order, and proves that equality of
the resulting words is precisely the boundary agreement required to glue
them.  It is the explicit hand-off from finite profile semantics to the
geometric color gluing theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionColorGluing
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

/-- The explicit source coordinate carrier for all exposed darts: the left
transversal followed by the right transversal. -/
abbrev SourceCrosscutBoundaryIndex
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique) :=
  Fin pair.left.walk.length ⊕ Fin pair.right.walk.length

/-- The actual outward boundary dart named by one source coordinate. -/
noncomputable def sourceCrosscutBoundaryDartAt
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
    pair.SourceCrosscutBoundaryIndex → BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component)
  | .inl step =>
      (orderedBoundaryDart data.toRotationSystem
        (fun vertex => vertex ∈ pair.componentSide boundary.component)
        (pair.left.crossingEdge hunique) boundary.leftCrosses step).1
  | .inr step =>
      (orderedBoundaryDart data.toRotationSystem
        (fun vertex => vertex ∈ pair.componentSide boundary.component)
        (pair.right.crossingEdge hunique) boundary.rightCrosses step).1

/-- The edge exposed by each source boundary dart is exactly its existing
source-crosscut port. -/
theorem sourceCrosscutBoundaryDartAt_edgeOf
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
    (index : pair.SourceCrosscutBoundaryIndex) :
    data.toRotationSystem.edgeOf
      (pair.sourceCrosscutBoundaryDartAt data boundary index).1.1 =
      (pair.sourceCrosscutPort data boundary index).1 := by
  rcases index with step | step
  · change data.toRotationSystem.edgeOf
        (orderedBoundaryDart data.toRotationSystem
          (fun vertex => vertex ∈ pair.componentSide boundary.component)
          (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 = _
    rw [orderedBoundaryDart_edgeOf]
    rfl
  · change data.toRotationSystem.edgeOf
        (orderedBoundaryDart data.toRotationSystem
          (fun vertex => vertex ∈ pair.componentSide boundary.component)
          (pair.right.crossingEdge hunique) boundary.rightCrosses step).1.1.1 = _
    rw [orderedBoundaryDart_edgeOf]
    rfl

/-- The source coordinate list covers every literal outward boundary dart of
the selected component.  Coverage is not an enumeration convention: it uses
the already-proved exact component boundary and the source-port equivalence. -/
theorem sourceCrosscutBoundaryDartAt_surjective
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
    Function.Surjective (pair.sourceCrosscutBoundaryDartAt data boundary) := by
  intro exposed
  let crossing : VertexSetCrossingEdge data.toRotationSystem
      (pair.componentSide boundary.component) :=
    ⟨data.toRotationSystem.edgeOf exposed.1.1,
      boundaryDart_edge_mem_vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component) exposed⟩
  rcases pair.sourceCrosscutPort_surjective data boundary crossing with
    ⟨index, hindex⟩
  refine ⟨index, ?_⟩
  apply boundaryDart_eq_of_edgeOf_eq data.toRotationSystem
    (fun vertex => vertex ∈ pair.componentSide boundary.component)
  rw [pair.sourceCrosscutBoundaryDartAt_edgeOf data boundary index]
  exact congrArg Subtype.val hindex

/-- Read the retained-side literal open coloring at every source boundary
dart, retaining the exact left-then-right transversal order. -/
noncomputable def sourceCrosscutInsideBoundaryWord
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
    (inside : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color) :
    pair.SourceCrosscutBoundaryIndex → Color :=
  fun index =>
    openOldDartColor data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component)
      (pair.sourceCrosscutOpenRoot data boundary) inside
      (pair.sourceCrosscutBoundaryDartAt data boundary index).1.1
      (pair.sourceCrosscutBoundaryDartAt data boundary index).1.2

/-- Read the complementary literal open coloring at the opposite dart of
each same source boundary edge. -/
noncomputable def sourceCrosscutOutsideBoundaryWordOfBoundary
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
    (outside :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
        Color) :
    pair.SourceCrosscutBoundaryIndex → Color :=
  fun index =>
    openOldDartColor data.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component)
      (pair.sourceCrosscutComplementRootOfBoundary data boundary) outside
      (data.toRotationSystem.alpha
        (pair.sourceCrosscutBoundaryDartAt data boundary index).1.1)
      (pair.sourceCrosscutBoundaryDartAt data boundary index).2

/-- Compatibility spelling of the complementary boundary word for callers
that still carry the former global-cubicity premise. -/
noncomputable def sourceCrosscutOutsideBoundaryWord
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
    (_hcubic : data.toRotationSystem.IsCubic)
    (outside :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring Color) :
    pair.SourceCrosscutBoundaryIndex → Color :=
  pair.sourceCrosscutOutsideBoundaryWordOfBoundary data boundary outside

/-- Equality of the two literal source-ordered boundary words gives the
generic open-region boundary agreement without any global degree premise. -/
theorem sourceCrosscutOpenBoundaryAgreement_of_words_eqOfBoundary
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
    (inside : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (outside :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring Color)
    (hwords : pair.sourceCrosscutInsideBoundaryWord data boundary inside =
      pair.sourceCrosscutOutsideBoundaryWordOfBoundary data boundary outside) :
    pair.SourceCrosscutOpenBoundaryAgreementOfBoundary data boundary inside outside := by
  intro dart hinside houtside
  let exposed : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component) :=
    ⟨⟨dart, hinside⟩, houtside⟩
  let insideColor : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component) → Color :=
    fun boundaryDart =>
      openOldDartColor data.toRotationSystem
        (fun vertex => vertex ∈ pair.componentSide boundary.component)
        (pair.sourceCrosscutOpenRoot data boundary) inside
        boundaryDart.1.1 boundaryDart.1.2
  let outsideColor : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component) → Color :=
    fun boundaryDart =>
      openOldDartColor data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component)
        (pair.sourceCrosscutComplementRootOfBoundary data boundary) outside
        (data.toRotationSystem.alpha boundaryDart.1.1) boundaryDart.2
  rcases pair.sourceCrosscutBoundaryDartAt_surjective data boundary exposed with
    ⟨index, hindex⟩
  have hword := congrFun hwords index
  change insideColor (pair.sourceCrosscutBoundaryDartAt data boundary index) =
    outsideColor (pair.sourceCrosscutBoundaryDartAt data boundary index) at hword
  change insideColor exposed = outsideColor exposed
  simpa [hindex] using hword

/-- The two literal source crosscut tangles close to an ambient Tait coloring
whenever their source-ordered boundary words agree, with the complementary
root supplied by the boundary package. -/
theorem exists_sourceCrosscutAmbientTaitColoring_of_openColorings_of_words_eqOfBoundary
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
    (inside : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (outside :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring Color)
    (hinside : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring inside)
    (houtside :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).IsTaitEdgeColoring
        outside)
    (hwords : pair.sourceCrosscutInsideBoundaryWord data boundary inside =
      pair.sourceCrosscutOutsideBoundaryWordOfBoundary data boundary outside) :
    ∃ closed : data.toRotationSystem.EdgeColoring Color,
      data.toRotationSystem.IsTaitEdgeColoring closed := by
  exact pair.exists_sourceCrosscutAmbientTaitColoring_of_openColoringsOfBoundary
    data boundary inside outside hinside houtside
    (pair.sourceCrosscutOpenBoundaryAgreement_of_words_eqOfBoundary
      data boundary inside outside hwords)

/-- Equality of the two literal source-ordered boundary words is exactly the
generic open-region boundary agreement.  This eliminates the universal seam
hypothesis in favor of finite data indexed by the actual paired
transversals. -/
theorem sourceCrosscutOpenBoundaryAgreement_of_words_eq
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
    (inside : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (outside :
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color)
    (hwords : pair.sourceCrosscutInsideBoundaryWord data boundary inside =
      pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic outside) :
    pair.SourceCrosscutOpenBoundaryAgreement data boundary hcubic inside outside := by
  intro dart hinside houtside
  let exposed : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component) :=
    ⟨⟨dart, hinside⟩, houtside⟩
  let insideColor : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component) → Color :=
    fun boundaryDart =>
      openOldDartColor data.toRotationSystem
        (fun vertex => vertex ∈ pair.componentSide boundary.component)
        (pair.sourceCrosscutOpenRoot data boundary) inside
        boundaryDart.1.1 boundaryDart.1.2
  let outsideColor : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide boundary.component) → Color :=
    fun boundaryDart =>
      openOldDartColor data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component)
        (pair.sourceCrosscutComplementRoot data boundary hcubic) outside
        (data.toRotationSystem.alpha boundaryDart.1.1) boundaryDart.2
  rcases pair.sourceCrosscutBoundaryDartAt_surjective data boundary exposed with
    ⟨index, hindex⟩
  have hword := congrFun hwords index
  change insideColor (pair.sourceCrosscutBoundaryDartAt data boundary index) =
    outsideColor (pair.sourceCrosscutBoundaryDartAt data boundary index) at hword
  change insideColor exposed = outsideColor exposed
  simpa [hindex] using hword

/-- The two literal source crosscut tangles close to an ambient Tait coloring
whenever their source-ordered boundary words are equal.  This is the direct
finite-word form of the source's open-tangle gluing operation. -/
theorem exists_sourceCrosscutAmbientTaitColoring_of_openColorings_of_words_eq
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
    (inside : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (outside :
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color)
    (hinside : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring inside)
    (houtside :
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
        outside)
    (hwords : pair.sourceCrosscutInsideBoundaryWord data boundary inside =
      pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic outside) :
    ∃ closed : data.toRotationSystem.EdgeColoring Color,
      data.toRotationSystem.IsTaitEdgeColoring closed := by
  exact pair.exists_sourceCrosscutAmbientTaitColoring_of_openColorings
    data boundary hcubic inside outside hinside houtside
    (pair.sourceCrosscutOpenBoundaryAgreement_of_words_eq data boundary hcubic
      inside outside hwords)

/-- The retained literal source tangle read from a shortened splice has the
sewn seam word on every left source boundary port. -/
theorem sourceCrosscutOutputInsideBoundaryWord_left_eq_seamColorWord
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
    (step : Fin pair.left.walk.length) :
    pair.sourceCrosscutInsideBoundaryWord data boundary
      (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
        (.inl step) =
      seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
        output step := by
  change pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints
      output ((pair.sourceCrosscutOpenRegion data boundary).edgeOf
        (Sum.inl (orderedBoundaryDart data.toRotationSystem
          (fun vertex => vertex ∈ pair.componentSide boundary.component)
          (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1)) = _
  exact pair.sourceCrosscutSpliceOutputOpenColoring_leftBoundary_eq_seamColorWord
    data boundary seamEndpoints output step

/-- The same shortened coloring has that sewn seam word on the aligned right
source boundary ports.  The equality is obtained from the actual output seam
edge, not by identifying the two source crosscuts syntactically. -/
theorem sourceCrosscutOutputInsideBoundaryWord_right_eq_seamColorWord
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
    (step : Fin pair.left.walk.length) :
    pair.sourceCrosscutInsideBoundaryWord data boundary
      (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
        (.inr (Fin.cast pair.length_eq step)) =
      seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
        output step := by
  change pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints
      output ((pair.sourceCrosscutOpenRegion data boundary).edgeOf
        (Sum.inl (orderedBoundaryDart data.toRotationSystem
          (fun vertex => vertex ∈ pair.componentSide boundary.component)
          (pair.right.crossingEdge hunique) boundary.rightCrosses
          (Fin.cast pair.length_eq step)).1.1)) = _
  rw [pair.sourceCrosscutSpliceOutputOpenColoring_edgeOf data boundary
    seamEndpoints output]
  exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionOutputRestriction.OrderedCutSpliceData.outputOpenDartColor_rightBoundary_eq_seamColorWord
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints) output step

/-- The semantic set of seam words extendable through the literal
complementary source tangle.  A word is accepted precisely when the
complement has a Tait coloring whose two actual source boundaries both read
that word under the crosscut alignment. -/
def sourceCrosscutComplementSeamExtendableWords
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
    (hcubic : data.toRotationSystem.IsCubic) :
    SemanticBoundaryProfile pair.left.walk.length :=
  { word | ∃ outside :
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
        Color,
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
          outside ∧
        (∀ step : Fin pair.left.walk.length,
          pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic outside
            (.inl step) = word step) ∧
        (∀ step : Fin pair.right.walk.length,
          pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic outside
            (.inr step) = word (Fin.cast pair.length_eq.symm step)) }

/-- A shortened source-splice Tait coloring completes to an ambient Tait
coloring whenever its seam word belongs to the concrete complement's
extendable-word set.  This is the genuine `complete_of_outer_word` gluing
calculation for that semantic set; the remaining profile work is to prove
membership/equality by the source's finite transfer semantics. -/
theorem sourceCrosscutComplete_of_complementSeamWord
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
    (hmember : seamColorWord (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
      output ∈ pair.sourceCrosscutComplementSeamExtendableWords data boundary hcubic) :
    TaitColorable (RS := data.toRotationSystem) := by
  rcases hmember with ⟨outside, houtside, hleft, hright⟩
  apply pair.exists_sourceCrosscutAmbientTaitColoring_of_openColorings_of_words_eq
    data boundary hcubic
    (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
    outside
    (pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary
      seamEndpoints output houtput)
    houtside
  funext index
  rcases index with step | rightStep
  · calc
      pair.sourceCrosscutInsideBoundaryWord data boundary
          (pair.sourceCrosscutSpliceOutputOpenColoring data boundary
            seamEndpoints output) (.inl step) =
          seamColorWord (pair.sourceCrosscutSpliceData data boundary
            seamEndpoints) output step :=
        pair.sourceCrosscutOutputInsideBoundaryWord_left_eq_seamColorWord
          data boundary seamEndpoints output step
      _ = pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic outside
          (.inl step) := (hleft step).symm
  · have hcast : Fin.cast pair.length_eq
        (Fin.cast pair.length_eq.symm rightStep) = rightStep := by
      apply Fin.ext
      rfl
    calc
      pair.sourceCrosscutInsideBoundaryWord data boundary
          (pair.sourceCrosscutSpliceOutputOpenColoring data boundary
            seamEndpoints output) (.inr rightStep) =
          pair.sourceCrosscutInsideBoundaryWord data boundary
            (pair.sourceCrosscutSpliceOutputOpenColoring data boundary
              seamEndpoints output)
            (.inr (Fin.cast pair.length_eq
              (Fin.cast pair.length_eq.symm rightStep))) := by
        rw [hcast]
      _ = seamColorWord (pair.sourceCrosscutSpliceData data boundary
            seamEndpoints) output (Fin.cast pair.length_eq.symm rightStep) :=
        pair.sourceCrosscutOutputInsideBoundaryWord_right_eq_seamColorWord
          data boundary seamEndpoints output
            (Fin.cast pair.length_eq.symm rightStep)
      _ = pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic outside
            (.inr rightStep) := (hright rightStep).symm

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
