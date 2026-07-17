import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCyclicOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphTaitBridge

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24FourDefectBoundary
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cyclicKempeGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance cyclicKempeRetainedVertexSetFintype (first second : V) :
    Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance cyclicKempeRetainedVertexSetDecidableEq (first second : V) :
    DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- A cyclic adjacent-pair deletion, its planar-reduction coloring, and the
exact same-side incidence profile of one two-color Kempe family. -/
structure CyclicKempeProfile
    (graphData : Data G) (data : AdjacentPairData G) where
  portsCyclic : data.PortsFollowCyclicDeletedBoundaryOrder graphData
  coloring : (DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex).EdgeColoring Color
  isTaitColoring : IsTaitEdgeColoring
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) coloring
  boundaryWellFormed : data.degreeTwoBoundaryData.WellFormed
  reductionCompatible : SquareReductionSide.join01_23.Compatible
    (data.degreeTwoBoundaryData.colorWord coloring)
  firstColor : Color
  secondColor : Color
  validPair : ValidColorPair firstColor secondColor
  firstRequestSelected :
    data.degreeTwoBoundaryData.colorWord coloring 0 = firstColor ∨
      data.degreeTwoBoundaryData.colorWord coloring 0 = secondColor
  secondRequestSelected :
    data.degreeTwoBoundaryData.colorWord coloring 2 = firstColor ∨
      data.degreeTwoBoundaryData.colorWord coloring 2 = secondColor
  componentProfile :
    ∀ K : (coloring.bicoloredSubgraph firstColor secondColor).ConnectedComponent,
      (data.degreeTwoBoundaryData.KempeComponentMeetsPort
          coloring firstColor secondColor K 0 ↔
        data.degreeTwoBoundaryData.KempeComponentMeetsPort
          coloring firstColor secondColor K 1) ∧
      (data.degreeTwoBoundaryData.KempeComponentMeetsPort
          coloring firstColor secondColor K 2 ↔
        data.degreeTwoBoundaryData.KempeComponentMeetsPort
          coloring firstColor secondColor K 3)
  firstLinkage :
    ∃ K : (coloring.bicoloredSubgraph firstColor secondColor).ConnectedComponent,
      data.degreeTwoBoundaryData.KempeComponentMeetsPort
          coloring firstColor secondColor K 0 ∧
        data.degreeTwoBoundaryData.KempeComponentMeetsPort
          coloring firstColor secondColor K 1
  secondLinkage :
    ∃ K : (coloring.bicoloredSubgraph firstColor secondColor).ConnectedComponent,
      data.degreeTwoBoundaryData.KempeComponentMeetsPort
          coloring firstColor secondColor K 2 ∧
        data.degreeTwoBoundaryData.KempeComponentMeetsPort
          coloring firstColor secondColor K 3

/-- The profile produced from an adjacent pair is carried by the literal
rotation ordering, rather than merely by an existentially equal relabeling. -/
theorem nonempty_rotationOrdered_cyclicKempeProfile
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) :
    Nonempty (CyclicKempeProfile graphData
      (data.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) := by
  let ordered := data.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have horder : ordered.PortsFollowCyclicDeletedBoundaryOrder graphData :=
    data.rotationOrderedData_portsFollowCyclicDeletedBoundaryOrder graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
  rcases ordered.exists_deletedColoring_join01_23_compatible_of_order
      graphData minimal horder with
    ⟨C, hC, hcompatible⟩
  have hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  rcases ordered.exists_validColorPair_all_kempeComponents_meet_sameSidePorts_together
      hcubic hnotColorable C hC with
    ⟨a, b, hab, hselectedZero, hselectedTwo, hcomponents⟩
  have hwell := ordered.degreeTwoBoundaryData_wellFormed hcubic
  rcases ordered.degreeTwoBoundaryData.exists_kempeComponentMeetsPort_of_colorWord_selected
      hwell C hab 0 hselectedZero with ⟨firstK, hfirstK⟩
  rcases ordered.degreeTwoBoundaryData.exists_kempeComponentMeetsPort_of_colorWord_selected
      hwell C hab 2 hselectedTwo with ⟨secondK, hsecondK⟩
  exact ⟨{
    portsCyclic := horder
    coloring := C
    isTaitColoring := hC
    boundaryWellFormed := hwell
    reductionCompatible := hcompatible
    firstColor := a
    secondColor := b
    validPair := hab
    firstRequestSelected := hselectedZero
    secondRequestSelected := hselectedTwo
    componentProfile := hcomponents
    firstLinkage := ⟨firstK, hfirstK, (hcomponents firstK).1.1 hfirstK⟩
    secondLinkage := ⟨secondK, hsecondK, (hcomponents secondK).2.1 hsecondK⟩
  }⟩

/-- Every named adjacent pair in a graph-backed vertex-minimal
counterexample admits a rotation-ordered cyclic Kempe profile. -/
theorem exists_rotationOrdered_cyclicKempeProfile
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) :
    ∃ ordered : AdjacentPairData G,
      ordered.firstVertex = data.firstVertex ∧
      ordered.secondVertex = data.secondVertex ∧
      Nonempty (CyclicKempeProfile graphData ordered) := by
  let ordered := data.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  exact ⟨ordered, rfl, rfl,
    data.nonempty_rotationOrdered_cyclicKempeProfile graphData minimal⟩

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
