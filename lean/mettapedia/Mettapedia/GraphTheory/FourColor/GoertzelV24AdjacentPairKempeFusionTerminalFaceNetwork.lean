import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionFaceCutNetwork
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTerminalFaceCutTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTerminalRouteFaceCutTransport

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24AdjacentPairInsertion.AdjacentPairData.EvenKempeFusionLens
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

/-- The entry-arm state selected by the cyclic order at the left terminal. -/
def selectedLeftFusionArmState
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (position : Fin lens.fusionSiteCount) :
    (Fin lens.fusionSiteCount × Bool) × Bool :=
  if fusionLeftTerminalTurn graphData data lens = true then
    bFusionEntryArmState data lens position
  else
    cFusionEntryArmState data lens position

/-- The exit-arm state selected by the cyclic order at the right terminal. -/
def selectedRightFusionArmState
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (position : Fin lens.fusionSiteCount) :
    (Fin lens.fusionSiteCount × Bool) × Bool :=
  if fusionRightTerminalTurn graphData data lens = true then
    bFusionExitArmState data lens position
  else
    cFusionExitArmState data lens position

/-- Exact support condition for the route prefix selected at the left
terminal. The fusion edge is absent from both alternatives. -/
def selectedLeftTerminalRouteAvoidsCut
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (cut : G.edgeSet → Prop)
    (position : Fin lens.fusionSiteCount) : Prop :=
  if fusionLeftTerminalTurn graphData data lens = true then
    ∀ edge ∈
      (lens.bAmbientPrefixToFusion
        (lens.bFusionSiteAt position)).reverse.support.tail,
      ¬cut (retainedEdgeToAmbientEdge data edge)
  else
    ∀ edge ∈
      (lens.cAmbientPrefixToFusion
        (lens.bFusionSiteAt position)).reverse.support.tail,
      ¬cut (retainedEdgeToAmbientEdge data edge)

/-- Exact support condition for the route suffix selected at the right
terminal. The fusion edge is absent from both alternatives. -/
def selectedRightTerminalRouteAvoidsCut
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (cut : G.edgeSet → Prop)
    (position : Fin lens.fusionSiteCount) : Prop :=
  if fusionRightTerminalTurn graphData data lens = true then
    ∀ edge ∈
      (lens.bAmbientSuffixFromFusion
        (lens.bFusionSiteAt position)).support.tail,
      ¬cut (retainedEdgeToAmbientEdge data edge)
  else
    ∀ edge ∈
      (lens.cAmbientSuffixFromFusion
        (lens.bFusionSiteAt position)).support.tail,
      ¬cut (retainedEdgeToAmbientEdge data edge)

/-- The selected left terminal face is the face carried by its selected
fusion-network entry arm whenever the intervening route prefix avoids the
cut. -/
theorem fusionLeftTerminalTurnFaceLabel_eq_selectedArm_of_route_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (position : Fin lens.fusionSiteCount)
    (hnot : selectedLeftTerminalRouteAvoidsCut
      graphData data lens cut position) :
    labels (dartOrbitFace graphData.toRotationSystem
        (fusionLeftTerminalTurnDart graphData data lens)) =
      routeOrderedFusionArmFaceLabel
        graphData data lens hab hac labels
          (selectedLeftFusionArmState graphData data lens position) := by
  by_cases hturn : fusionLeftTerminalTurn graphData data lens = true
  · have hnotB : ∀ edge ∈
        (lens.bAmbientPrefixToFusion
          (lens.bFusionSiteAt position)).reverse.support.tail,
        ¬cut (retainedEdgeToAmbientEdge data edge) := by
      simpa only [selectedLeftTerminalRouteAvoidsCut, if_pos hturn] using hnot
    rw [fusionLeftTerminalTurnDart, if_pos hturn,
      selectedLeftFusionArmState, if_pos hturn,
      routeOrderedFusionArmFaceLabel,
      routeOrderedFusionArmDart_bEntryArmState]
    exact (bAmbientLeftTerminalRouteFaceLabels_eq_of_not_cut
      data lens hdata hab hac (lens.bFusionSiteAt position)
        graphData hcubic hrotation labels cut hexact hnotB).symm
  · have hnotC : ∀ edge ∈
        (lens.cAmbientPrefixToFusion
          (lens.bFusionSiteAt position)).reverse.support.tail,
        ¬cut (retainedEdgeToAmbientEdge data edge) := by
      simpa only [selectedLeftTerminalRouteAvoidsCut, if_neg hturn] using hnot
    rw [fusionLeftTerminalTurnDart, if_neg hturn,
      selectedLeftFusionArmState, if_neg hturn,
      routeOrderedFusionArmFaceLabel,
      routeOrderedFusionArmDart_cEntryArmState]
    exact (cAmbientLeftTerminalRouteFaceLabels_eq_of_not_cut
      data lens hdata hab hac (lens.bFusionSiteAt position)
        graphData hcubic hrotation labels cut hexact hnotC).symm

/-- The analogous selected-terminal wire at the right endpoint. -/
theorem fusionRightTerminalTurnFaceLabel_eq_selectedArm_of_route_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (position : Fin lens.fusionSiteCount)
    (hnot : selectedRightTerminalRouteAvoidsCut
      graphData data lens cut position) :
    labels (dartOrbitFace graphData.toRotationSystem
        (fusionRightTerminalTurnDart graphData data lens)) =
      routeOrderedFusionArmFaceLabel
        graphData data lens hab hac labels
          (selectedRightFusionArmState graphData data lens position) := by
  by_cases hturn : fusionRightTerminalTurn graphData data lens = true
  · have hnotB : ∀ edge ∈
        (lens.bAmbientSuffixFromFusion
          (lens.bFusionSiteAt position)).support.tail,
        ¬cut (retainedEdgeToAmbientEdge data edge) := by
      simpa only [selectedRightTerminalRouteAvoidsCut, if_pos hturn] using hnot
    rw [fusionRightTerminalTurnDart, if_pos hturn,
      selectedRightFusionArmState, if_pos hturn,
      routeOrderedFusionArmFaceLabel,
      routeOrderedFusionArmDart_bExitArmState]
    exact (bAmbientRightTerminalRouteFaceLabels_eq_of_not_cut
      data lens hdata hab hac (lens.bFusionSiteAt position)
        graphData hcubic hrotation labels cut hexact hnotB).symm
  · have hnotC : ∀ edge ∈
        (lens.cAmbientSuffixFromFusion
          (lens.bFusionSiteAt position)).support.tail,
        ¬cut (retainedEdgeToAmbientEdge data edge) := by
      simpa only [selectedRightTerminalRouteAvoidsCut, if_neg hturn] using hnot
    rw [fusionRightTerminalTurnDart, if_neg hturn,
      selectedRightFusionArmState, if_neg hturn,
      routeOrderedFusionArmFaceLabel,
      routeOrderedFusionArmDart_cExitArmState]
    exact (cAmbientRightTerminalRouteFaceLabels_eq_of_not_cut
      data lens hdata hab hac (lens.bFusionSiteAt position)
        graphData hcubic hrotation labels cut hexact hnotC).symm

/-- Crossing a non-cut left boundary edge and following the selected route
prefix embeds the boundary face into the finite fusion-face network. -/
theorem boundaryPortFaceLabel_eq_selectedLeftFusionArm_of_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (position : Fin lens.fusionSiteCount)
    (hboundary : ¬cut (graphData.toRotationSystem.edgeOf
      (boundaryPortDart data left)))
    (hroute : selectedLeftTerminalRouteAvoidsCut
      graphData data lens cut position) :
    labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data left)) =
      routeOrderedFusionArmFaceLabel
        graphData data lens hab hac labels
          (selectedLeftFusionArmState graphData data lens position) := by
  exact (fusionLeftTerminalTurn_labels_eq_of_boundary_not_cut
    graphData hcubic hrotation data lens hbc labels cut hexact hboundary).trans
      (fusionLeftTerminalTurnFaceLabel_eq_selectedArm_of_route_not_cut
        graphData hcubic hrotation data lens hdata hab hac labels cut hexact
          position hroute)

/-- The analogous boundary-to-network embedding at the right endpoint. -/
theorem boundaryPortFaceLabel_eq_selectedRightFusionArm_of_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (position : Fin lens.fusionSiteCount)
    (hboundary : ¬cut (graphData.toRotationSystem.edgeOf
      (boundaryPortDart data right)))
    (hroute : selectedRightTerminalRouteAvoidsCut
      graphData data lens cut position) :
    labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data right)) =
      routeOrderedFusionArmFaceLabel
        graphData data lens hab hac labels
          (selectedRightFusionArmState graphData data lens position) := by
  exact (fusionRightTerminalTurn_labels_eq_of_boundary_not_cut
    graphData hcubic hrotation data lens hbc labels cut hexact hboundary).trans
      (fusionRightTerminalTurnFaceLabel_eq_selectedArm_of_route_not_cut
        graphData hcubic hrotation data lens hdata hab hac labels cut hexact
          position hroute)

/-- Once the selected left arm reaches a network state, exact-cut labels
carry the boundary face to that state through the entire verified network. -/
theorem boundaryPortFaceLabel_eq_of_selectedLeftArm_connected
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (position : Fin lens.fusionSiteCount)
    (hboundary : ¬cut (graphData.toRotationSystem.edgeOf
      (boundaryPortDart data left)))
    (hroute : selectedLeftTerminalRouteAvoidsCut
      graphData data lens cut position)
    {finish : (Fin lens.fusionSiteCount × Bool) × Bool}
    (hconnected : CutAvoidingFusionFaceConnected
      graphData data lens hab hac cut
        (selectedLeftFusionArmState graphData data lens position) finish) :
    labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data left)) =
      routeOrderedFusionArmFaceLabel
        graphData data lens hab hac labels finish := by
  exact (boundaryPortFaceLabel_eq_selectedLeftFusionArm_of_not_cut
    graphData hcubic hrotation data lens hdata hab hac hbc labels cut hexact
      position hboundary hroute).trans
        (routeOrderedFusionArmFaceLabel_eq_of_cutAvoidingFusionFaceConnected
          graphData hcubic hrotation data lens hab hac hbc labels cut hexact
            hconnected)

/-- The corresponding propagation theorem from the right boundary face. -/
theorem boundaryPortFaceLabel_eq_of_selectedRightArm_connected
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (position : Fin lens.fusionSiteCount)
    (hboundary : ¬cut (graphData.toRotationSystem.edgeOf
      (boundaryPortDart data right)))
    (hroute : selectedRightTerminalRouteAvoidsCut
      graphData data lens cut position)
    {finish : (Fin lens.fusionSiteCount × Bool) × Bool}
    (hconnected : CutAvoidingFusionFaceConnected
      graphData data lens hab hac cut
        (selectedRightFusionArmState graphData data lens position) finish) :
    labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data right)) =
      routeOrderedFusionArmFaceLabel
        graphData data lens hab hac labels finish := by
  exact (boundaryPortFaceLabel_eq_selectedRightFusionArm_of_not_cut
    graphData hcubic hrotation data lens hdata hab hac hbc labels cut hexact
      position hboundary hroute).trans
        (routeOrderedFusionArmFaceLabel_eq_of_cutAvoidingFusionFaceConnected
          graphData hcubic hrotation data lens hab hac hbc labels cut hexact
            hconnected)

/-- A finite-network connection between the two rotation-selected arms
forces equality of the two boundary-face labels. All cut obligations are
localized to the boundary edges, the two trimmed terminal routes, and the
generating steps of the internal network. -/
theorem boundaryPortFaceLabels_eq_of_selectedArms_connected
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (leftPosition rightPosition : Fin lens.fusionSiteCount)
    (hleftBoundary : ¬cut (graphData.toRotationSystem.edgeOf
      (boundaryPortDart data left)))
    (hrightBoundary : ¬cut (graphData.toRotationSystem.edgeOf
      (boundaryPortDart data right)))
    (hleftRoute : selectedLeftTerminalRouteAvoidsCut
      graphData data lens cut leftPosition)
    (hrightRoute : selectedRightTerminalRouteAvoidsCut
      graphData data lens cut rightPosition)
    (hconnected : CutAvoidingFusionFaceConnected
      graphData data lens hab hac cut
        (selectedLeftFusionArmState graphData data lens leftPosition)
        (selectedRightFusionArmState graphData data lens rightPosition)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data left)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data right)) := by
  exact (boundaryPortFaceLabel_eq_of_selectedLeftArm_connected
    graphData hcubic hrotation data lens hdata hab hac hbc labels cut hexact
      leftPosition hleftBoundary hleftRoute hconnected).trans
        (boundaryPortFaceLabel_eq_selectedRightFusionArm_of_not_cut
          graphData hcubic hrotation data lens hdata hab hac hbc labels cut
            hexact rightPosition hrightBoundary hrightRoute).symm

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
