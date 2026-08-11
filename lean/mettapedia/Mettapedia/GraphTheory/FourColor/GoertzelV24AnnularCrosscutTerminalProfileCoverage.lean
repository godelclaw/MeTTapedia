import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSpliceBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileFaceCapUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileVertexSideCoverage

/-!
# Terminal-profile coverage on a source annular crosscut

The generic terminal-profile update needs two regional factors whose union is
the ambient edge set and whose common seam is small.  For the source annular
crosscut these are not additional hypotheses: the factors are the retained
deletion component and its vertex complement.  They cover every edge, their
intersection is exactly the paired-transversal primal cut, and hence a
width-two pair has a four-edge seam below the source face cap five.

This file specializes the generic connectivity and occurrence-sensitive face
coverage lemmas to that literal source geometry.  It remains relational: no
outgoing profile is chosen and no transfer determinism is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileConnectivityUpdate
open GoertzelV24TerminalProfileFaceCapUpdate
open GoertzelV24TerminalProfileFaceUpdate
open GoertzelV24TerminalProfileRegionalCoverage
open GoertzelV24TerminalProfileVertexSideCoverage
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

section SourceCrosscut

variable (data : Data G)
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

/-- The retained source component and its complement cover every ambient
edge. -/
theorem sourceCrosscutRetainedRemovedRegion_union_eq_univ :
    vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component) ∪
        vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ =
      Finset.univ :=
  vertexSetRegionEdges_union_compl_eq_univ data.toRotationSystem
    (pair.componentSide boundary.component)

/-- The common edge seam of the retained and removed source regions is the
literal primal cut of the paired transversals. -/
theorem sourceCrosscutRetainedRemovedRegion_inter_eq_primalCutEdges :
    vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component) ∩
        vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ =
      pair.primalCutEdges data := by
  rw [vertexSetRegionEdges_inter_compl_eq_crossingEdges,
    pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
      data boundary.component boundary.component_boundary]

/-- Equivalently, the common seam is exactly the union of the left and right
source-transversal crossing supports. -/
theorem sourceCrosscutRetainedRemovedRegion_inter_eq_sourceCrossingSupport :
    vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component) ∩
        vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ =
      pair.left.crossingEdges hunique ∪ pair.right.crossingEdges hunique := by
  rw [pair.sourceCrosscutRetainedRemovedRegion_inter_eq_primalCutEdges
      data boundary,
    pair.primalCutEdges_eq_sourceCrossingSupport data]

/-- The source seam has exactly the sum of its two interface widths. -/
theorem sourceCrosscutRetainedRemovedRegion_inter_card_eq_interfaceWidths :
    (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component) ∩
        vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ).card =
      pair.left.walk.length + pair.right.walk.length := by
  rw [pair.sourceCrosscutRetainedRemovedRegion_inter_eq_primalCutEdges
      data boundary,
    pair.primalCutEdges_card_eq_interfaceWidths data]

/-- A width-two source pair has a literal four-edge retained/removed seam. -/
theorem sourceCrosscutRetainedRemovedRegion_inter_card_eq_four
    (hwidth : pair.left.walk.length = 2) :
    (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component) ∩
        vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ).card = 4 := by
  rw [pair.sourceCrosscutRetainedRemovedRegion_inter_card_eq_interfaceWidths
      data boundary,
    hwidth, pair.length_eq.symm.trans hwidth]

/-- In particular, the width-two source seam is below the manuscript's
cap-at-five face-progress threshold. -/
theorem sourceCrosscutRetainedRemovedRegion_inter_card_lt_five
    (hwidth : pair.left.walk.length = 2) :
    (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component) ∩
        vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ).card < 5 := by
  rw [pair.sourceCrosscutRetainedRemovedRegion_inter_card_eq_four
    data boundary hwidth]
  omega

/-- The one uncolored edge-adjacency premise used by both terminal-profile
coordinates is automatic on the actual retained/removed source split. -/
theorem sourceCrosscutRetainedRemoved_regionalEdgeAdjacencyCovered :
    RegionalEdgeAdjacencyCovered data.toRotationSystem
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ) :=
  regionalEdgeAdjacencyCovered_vertexSetRegionEdges_compl
    data.toRotationSystem (pair.componentSide boundary.component)

/-- Consequently tracked two-color connectivity composes across the actual
source seam for every ambient coloring and tracked color pair. -/
theorem sourceCrosscutRetainedRemoved_regionalTrackedAdjacencyCovered
    (C : G.edgeSet → Color) (a b : Color) :
    RegionalTrackedAdjacencyCovered data.toRotationSystem
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ) C a b :=
  regionalTrackedAdjacencyCovered_vertexSetRegionEdges_compl
    data.toRotationSystem (pair.componentSide boundary.component) C a b

/-- Under the source's cubic cyclic rotation hypotheses, occurrence-sensitive
face connectivity composes across the same literal source seam. -/
theorem sourceCrosscutRetainedRemoved_regionalFaceAdjacencyCovered
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (root : data.toRotationSystem.D) :
    RegionalFaceAdjacencyCovered data.toRotationSystem root
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ) :=
  regionalFaceAdjacencyCovered_vertexSetRegionEdges_compl
    data.toRotationSystem hcubic hrotation
      (pair.componentSide boundary.component) root

/-- Any two face-support pieces whose overlap is confined to the width-two
source seam satisfy the exact overlap-corrected cap-at-five update. -/
theorem min_card_union_eq_min_caps_sub_inter_of_inter_subset_sourceCrosscut
    (leftSupport rightSupport : Finset G.edgeSet)
    (hinter : leftSupport ∩ rightSupport ⊆
      vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component) ∩
        vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ)
    (hwidth : pair.left.walk.length = 2) :
    min (leftSupport ∪ rightSupport).card 5 =
      min (min leftSupport.card 5 + min rightSupport.card 5 -
        (leftSupport ∩ rightSupport).card) 5 := by
  apply min_card_union_eq_min_caps_sub_inter_of_inter_subset
    leftSupport rightSupport
    (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component) ∩
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
    5 hinter
  exact pair.sourceCrosscutRetainedRemovedRegion_inter_card_lt_five
    data boundary hwidth

end SourceCrosscut

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
