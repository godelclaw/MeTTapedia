import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionFaceNetwork
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOppositePortCircuit
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceCutTransport

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

/-- The route-ordered local fusion crossing preserves any exact cut label
provided both candidate crossing arms lie outside the cut. The two arm
premises make the statement independent of which orientation realizes the
verified facial arc. -/
theorem routeOrderedFusionFaceCrossing_labels_eq_of_arms_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (state : (Fin lens.fusionSiteCount × Bool) × Bool)
    (hstart : ¬cut (graphData.toRotationSystem.edgeOf
      (routeOrderedFusionArmDart (C := C) (a := a) (b := b) (c := c)
        (left := left) (right := right) data lens hab hac state)))
    (hfinish : ¬cut (graphData.toRotationSystem.edgeOf
      (routeOrderedFusionArmDart (C := C) (a := a) (b := b) (c := c)
        (left := left) (right := right) data lens hab hac
        ((routeOrderedFusionFaceCrossing
          (C := C) (a := a) (b := b) (c := c)
          (left := left) (right := right)
          graphData data lens hab hac state) :
            (Fin lens.fusionSiteCount × Bool) × Bool)))) :
    labels (dartOrbitFace graphData.toRotationSystem
        (routeOrderedFusionArmDart (C := C) (a := a) (b := b) (c := c)
          (left := left) (right := right) data lens hab hac state)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (routeOrderedFusionArmDart (C := C) (a := a) (b := b) (c := c)
          (left := left) (right := right) data lens hab hac
          ((routeOrderedFusionFaceCrossing
            (C := C) (a := a) (b := b) (c := c)
            (left := left) (right := right)
            graphData data lens hab hac state) :
              (Fin lens.fusionSiteCount × Bool) × Bool))) := by
  rcases routeOrderedFusionFaceCrossing_facePairing
      graphData hcubic hrotation data lens hab hac hbc state with
    hforward | hreverse
  · exact labels_eq_of_phi_sq_alpha_eq_of_not_cut
      graphData.toRotationSystem labels cut hexact _ _ hforward hstart
  · exact (labels_eq_of_phi_sq_alpha_eq_of_not_cut
      graphData.toRotationSystem labels cut hexact _ _ hreverse hfinish).symm

/-- Specialization to the exact cut carried by an opposite-port closure:
a fusion crossing preserves the face-side label whenever its two possible
arm edges are absent from that closure. -/
theorem routeOrderedFusionFaceCrossing_labels_eq_of_arms_not_mem_oppositePortClosure
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
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          (data.oppositePortClosure path).edges)
    (state : (Fin lens.fusionSiteCount × Bool) × Bool)
    (hstart : (graphData.toRotationSystem.edgeOf
      (routeOrderedFusionArmDart (C := C) (a := a) (b := b) (c := c)
        (left := left) (right := right) data lens hab hac state)).1 ∉
          (data.oppositePortClosure path).edges)
    (hfinish : (graphData.toRotationSystem.edgeOf
      (routeOrderedFusionArmDart (C := C) (a := a) (b := b) (c := c)
        (left := left) (right := right) data lens hab hac
        ((routeOrderedFusionFaceCrossing
          (C := C) (a := a) (b := b) (c := c)
          (left := left) (right := right)
          graphData data lens hab hac state) :
            (Fin lens.fusionSiteCount × Bool) × Bool))).1 ∉
          (data.oppositePortClosure path).edges) :
    labels (dartOrbitFace graphData.toRotationSystem
        (routeOrderedFusionArmDart (C := C) (a := a) (b := b) (c := c)
          (left := left) (right := right) data lens hab hac state)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (routeOrderedFusionArmDart (C := C) (a := a) (b := b) (c := c)
          (left := left) (right := right) data lens hab hac
          ((routeOrderedFusionFaceCrossing
            (C := C) (a := a) (b := b) (c := c)
            (left := left) (right := right)
            graphData data lens hab hac state) :
              (Fin lens.fusionSiteCount × Bool) × Bool))) := by
  apply routeOrderedFusionFaceCrossing_labels_eq_of_arms_not_cut
    graphData hcubic hrotation data lens hab hac hbc labels
      (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
  · exact hexact
  · exact hstart
  · exact hfinish

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
