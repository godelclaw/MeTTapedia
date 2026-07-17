import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTerminalRouteSegments

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- A cut-avoiding first-channel prefix transports its entry-arm face
label to the left terminal face, without requiring the fusion edge itself
to avoid the cut. -/
theorem EvenKempeFusionLens.bAmbientLeftTerminalRouteFaceLabels_eq_of_not_cut
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite)
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hnot : ∀ edge ∈
      (lens.bAmbientPrefixToFusion site).reverse.support.tail,
      ¬cut (retainedEdgeToAmbientEdge data edge)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientBEntryNeighborDart data lens hab site)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientBLeftTerminalDart data lens)) := by
  let trail := lens.bLeftTerminalRouteSegment hdata hab hac site
  let hnil := lens.bLeftTerminalRouteSegment_not_nil hdata hab hac site
  have hlabels := retainedTrail_labels_eq_terminalDarts_of_support_not_cut
    graphData hcubic hrotation data labels cut hexact trail hnil
      (lens.bLeftTerminalRouteSegment_isTrail hdata hab hac site)
      (lens.bAmbientPrefixToFusion site).reverse.support.tail
      (by
        intro edge hedge
        rw [lens.bLeftTerminalRouteSegment_edges hdata hab hac site] at hedge
        exact hedge)
      hnot
  rw [lens.bLeftTerminalRouteSegment_firstDart hdata hab hac site,
    lens.bLeftTerminalRouteSegment_lastDart_symm hdata hab hac site]
    at hlabels
  simpa only [ambientBEntryNeighborDart,
    ambientBLeftTerminalDart] using hlabels

/-- The corresponding cut-avoiding second-channel prefix transports its
entry-arm label to the left terminal face. -/
theorem EvenKempeFusionLens.cAmbientLeftTerminalRouteFaceLabels_eq_of_not_cut
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite)
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hnot : ∀ edge ∈
      (lens.cAmbientPrefixToFusion site).reverse.support.tail,
      ¬cut (retainedEdgeToAmbientEdge data edge)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientCEntryNeighborDart data lens hac site)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientCLeftTerminalDart data lens)) := by
  let trail := lens.cLeftTerminalRouteSegment hdata hab hac site
  let hnil := lens.cLeftTerminalRouteSegment_not_nil hdata hab hac site
  have hlabels := retainedTrail_labels_eq_terminalDarts_of_support_not_cut
    graphData hcubic hrotation data labels cut hexact trail hnil
      (lens.cLeftTerminalRouteSegment_isTrail hdata hab hac site)
      (lens.cAmbientPrefixToFusion site).reverse.support.tail
      (by
        intro edge hedge
        rw [lens.cLeftTerminalRouteSegment_edges hdata hab hac site] at hedge
        exact hedge)
      hnot
  rw [lens.cLeftTerminalRouteSegment_firstDart hdata hab hac site,
    lens.cLeftTerminalRouteSegment_lastDart_symm hdata hab hac site]
    at hlabels
  simpa only [ambientCEntryNeighborDart,
    ambientCLeftTerminalDart] using hlabels

/-- A cut-avoiding first-channel suffix transports its exit-arm face
label to the right terminal face while omitting the fusion edge. -/
theorem EvenKempeFusionLens.bAmbientRightTerminalRouteFaceLabels_eq_of_not_cut
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite)
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hnot : ∀ edge ∈
      (lens.bAmbientSuffixFromFusion site).support.tail,
      ¬cut (retainedEdgeToAmbientEdge data edge)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientBExitNeighborDart data lens hab site)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientBRightTerminalDart data lens)) := by
  let trail := lens.bRightTerminalRouteSegment hdata hab hac site
  let hnil := lens.bRightTerminalRouteSegment_not_nil hdata hab hac site
  have hlabels := retainedTrail_labels_eq_terminalDarts_of_support_not_cut
    graphData hcubic hrotation data labels cut hexact trail hnil
      (lens.bRightTerminalRouteSegment_isTrail hdata hab hac site)
      (lens.bAmbientSuffixFromFusion site).support.tail
      (by
        intro edge hedge
        rw [lens.bRightTerminalRouteSegment_edges hdata hab hac site] at hedge
        exact hedge)
      hnot
  rw [lens.bRightTerminalRouteSegment_firstDart hdata hab hac site,
    lens.bRightTerminalRouteSegment_lastDart_symm hdata hab hac site]
    at hlabels
  simpa only [ambientBExitNeighborDart,
    ambientBRightTerminalDart] using hlabels

/-- The corresponding cut-avoiding second-channel suffix transports its
exit-arm label to the right terminal face. -/
theorem EvenKempeFusionLens.cAmbientRightTerminalRouteFaceLabels_eq_of_not_cut
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite)
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hnot : ∀ edge ∈
      (lens.cAmbientSuffixFromFusion site).support.tail,
      ¬cut (retainedEdgeToAmbientEdge data edge)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientCExitNeighborDart data lens hac site)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientCRightTerminalDart data lens)) := by
  let trail := lens.cRightTerminalRouteSegment hdata hab hac site
  let hnil := lens.cRightTerminalRouteSegment_not_nil hdata hab hac site
  have hlabels := retainedTrail_labels_eq_terminalDarts_of_support_not_cut
    graphData hcubic hrotation data labels cut hexact trail hnil
      (lens.cRightTerminalRouteSegment_isTrail hdata hab hac site)
      (lens.cAmbientSuffixFromFusion site).support.tail
      (by
        intro edge hedge
        rw [lens.cRightTerminalRouteSegment_edges hdata hab hac site] at hedge
        exact hedge)
      hnot
  rw [lens.cRightTerminalRouteSegment_firstDart hdata hab hac site,
    lens.cRightTerminalRouteSegment_lastDart_symm hdata hab hac site]
    at hlabels
  simpa only [ambientCExitNeighborDart,
    ambientCRightTerminalDart] using hlabels

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
