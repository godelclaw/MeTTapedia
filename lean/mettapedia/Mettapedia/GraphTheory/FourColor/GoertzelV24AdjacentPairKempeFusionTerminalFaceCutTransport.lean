import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionFaceCutTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTerminalTurns

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24FaceCutTransport
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Crossing a non-cut left boundary edge carries its retained-side face
label to the route terminal selected by the boundary rotation. -/
theorem fusionLeftTerminalTurn_labels_eq_of_boundary_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hnot : ¬cut (graphData.toRotationSystem.edgeOf
      (boundaryPortDart data left))) :
    labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data left)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (fusionLeftTerminalTurnDart graphData data lens)) := by
  apply labels_eq_of_phi_iterate_alpha_eq_of_not_cut
    graphData.toRotationSystem labels cut hexact _ _ 1
  · simpa [Function.iterate_succ_apply] using
      phi_alpha_boundaryPortDart_eq_leftTerminalTurnDart
        graphData hcubic hrotation data lens hbc
  · exact hnot

/-- The analogous transport law at the right boundary edge. -/
theorem fusionRightTerminalTurn_labels_eq_of_boundary_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hnot : ¬cut (graphData.toRotationSystem.edgeOf
      (boundaryPortDart data right))) :
    labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data right)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (fusionRightTerminalTurnDart graphData data lens)) := by
  apply labels_eq_of_phi_iterate_alpha_eq_of_not_cut
    graphData.toRotationSystem labels cut hexact _ _ 1
  · simpa [Function.iterate_succ_apply] using
      phi_alpha_boundaryPortDart_eq_rightTerminalTurnDart
        graphData hcubic hrotation data lens hbc
  · exact hnot

/-- A left endpoint outside ports `0` and `2` is outside the exact
opposite-port closure, so its boundary face reaches its selected fusion
terminal without changing side. -/
theorem fusionLeftTerminalTurn_labels_eq_of_unused_oppositePortBoundary
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          (data.oppositePortClosure path).edges)
    (hleftZero : left ≠ 0) (hleftTwo : left ≠ 2) :
    labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data left)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (fusionLeftTerminalTurnDart graphData data lens)) := by
  apply fusionLeftTerminalTurn_labels_eq_of_boundary_not_cut
    graphData hcubic hrotation data lens hbc labels
      (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges) hexact
  intro hmem
  have hport :=
    (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff path left).1
      (by simpa using hmem)
  exact hport.elim hleftZero hleftTwo

/-- The corresponding exact-cut transport at an unused right endpoint. -/
theorem fusionRightTerminalTurn_labels_eq_of_unused_oppositePortBoundary
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          (data.oppositePortClosure path).edges)
    (hrightZero : right ≠ 0) (hrightTwo : right ≠ 2) :
    labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data right)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (fusionRightTerminalTurnDart graphData data lens)) := by
  apply fusionRightTerminalTurn_labels_eq_of_boundary_not_cut
    graphData hcubic hrotation data lens hbc labels
      (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges) hexact
  intro hmem
  have hport :=
    (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff path right).1
      (by simpa using hmem)
  exact hport.elim hrightZero hrightTwo

/-- For the two canonical separated fusion lenses, the two unused port
faces carry their exact-cut labels to the selected right terminal darts.
This is the terminal interface consumed by a complementary fusion-face
chain. -/
theorem unusedBoundaryFaces_labels_eq_selectedRightTerminals
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          (data.oppositePortClosure path).edges) :
    labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data 1)) =
        labels (dartOrbitFace graphData.toRotationSystem
          (fusionRightTerminalTurnDart graphData data lens01)) ∧
      labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data 3)) =
        labels (dartOrbitFace graphData.toRotationSystem
          (fusionRightTerminalTurnDart graphData data lens23)) := by
  constructor
  · exact fusionRightTerminalTurn_labels_eq_of_unused_oppositePortBoundary
      graphData hcubic hrotation data path lens01 hbc labels hexact
        (by decide) (by decide)
  · exact fusionRightTerminalTurn_labels_eq_of_unused_oppositePortBoundary
      graphData hcubic hrotation data path lens23 hbc labels hexact
        (by decide) (by decide)

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
