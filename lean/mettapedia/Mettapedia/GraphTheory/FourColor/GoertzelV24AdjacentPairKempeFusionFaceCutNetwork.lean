import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionOrientedFaceCutTransport

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

/-- Read the ambient face label carried by one route-ordered fusion arm. -/
def routeOrderedFusionArmFaceLabel
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (state : (Fin lens.fusionSiteCount × Bool) × Bool) : A :=
  labels (dartOrbitFace graphData.toRotationSystem
    (routeOrderedFusionArmDart data lens hab hac state))

/-- Generating edges of the cut-avoiding fusion-face network. They are
the verified local crossings at one fusion edge and the two families of
trimmed primal route segments between ordered fusion edges. The directed
crossings expose the exact single arm traversed by each local face arc. -/
inductive CutAvoidingFusionFaceStep
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (cut : G.edgeSet → Prop) :
    ((Fin lens.fusionSiteCount × Bool) × Bool) →
      ((Fin lens.fusionSiteCount × Bool) × Bool) → Prop where
  | crossing
      (state : (Fin lens.fusionSiteCount × Bool) × Bool)
      (hstart : ¬cut (graphData.toRotationSystem.edgeOf
        (routeOrderedFusionArmDart data lens hab hac state)))
      (hfinish : ¬cut (graphData.toRotationSystem.edgeOf
        (routeOrderedFusionArmDart data lens hab hac
          (routeOrderedFusionFaceCrossing
            graphData data lens hab hac state)))) :
      CutAvoidingFusionFaceStep graphData data lens hab hac cut
        state (routeOrderedFusionFaceCrossing
          graphData data lens hab hac state)
  | entryCrossing
      (position : Fin lens.fusionSiteCount)
      (hnot : ¬cut (graphData.toRotationSystem.edgeOf
        (routeOrderedFusionArmDart data lens hab hac
          (routeOrderedFusionEntryOtherState
            graphData data lens hab hac position)))) :
      CutAvoidingFusionFaceStep graphData data lens hab hac cut
        (routeOrderedFusionEntryOtherState
          graphData data lens hab hac position)
        (routeOrderedFusionExitTurnState
          graphData data lens hab hac position)
  | exitCrossing
      (position : Fin lens.fusionSiteCount)
      (hnot : ¬cut (graphData.toRotationSystem.edgeOf
        (routeOrderedFusionArmDart data lens hab hac
          (routeOrderedFusionExitOtherState
            graphData data lens hab hac position)))) :
      CutAvoidingFusionFaceStep graphData data lens hab hac cut
        (routeOrderedFusionExitOtherState
          graphData data lens hab hac position)
        (routeOrderedFusionEntryTurnState
          graphData data lens hab hac position)
  | bSegment
      (first second : Fin lens.fusionSiteCount)
      (hbOrder : lens.bFusionSupportOrderEmbedding first <
        lens.bFusionSupportOrderEmbedding second)
      (hnot : ∀ edge ∈
        (lens.bFusionOrderInterval first second hbOrder).support.tail.dropLast,
        ¬cut (retainedEdgeToAmbientEdge data edge)) :
      CutAvoidingFusionFaceStep graphData data lens hab hac cut
        (bFusionExitArmState data lens first)
        (bFusionEntryArmState data lens second)
  | cSegment
      (first second : Fin lens.fusionSiteCount)
      (hcOrder : lens.cFusionSupportOrderEmbedding
          (finCongr lens.fusionSites_length_eq
            (lens.fusionMonodromy second)) <
        lens.cFusionSupportOrderEmbedding
          (finCongr lens.fusionSites_length_eq
            (lens.fusionMonodromy first)))
      (hnot : ∀ edge ∈
        (lens.cFusionOrderInterval first second hcOrder).reverse.support.tail.dropLast,
        ¬cut (retainedEdgeToAmbientEdge data edge)) :
      CutAvoidingFusionFaceStep graphData data lens hab hac cut
        (cFusionExitArmState data lens second)
        (cFusionEntryArmState data lens first)

/-- Every generating edge of the fusion-face network preserves an exact
cut label. -/
theorem routeOrderedFusionArmFaceLabel_eq_of_cutAvoidingFusionFaceStep
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
    {start finish : (Fin lens.fusionSiteCount × Bool) × Bool}
    (hstep : CutAvoidingFusionFaceStep
      graphData data lens hab hac cut start finish) :
    routeOrderedFusionArmFaceLabel graphData data lens hab hac labels start =
      routeOrderedFusionArmFaceLabel graphData data lens hab hac labels finish := by
  induction hstep with
  | crossing state hstart hfinish =>
      exact routeOrderedFusionFaceCrossing_labels_eq_of_arms_not_cut
        graphData hcubic hrotation data lens hab hac hbc labels cut hexact
          state hstart hfinish
  | entryCrossing position hnot =>
      simpa [routeOrderedFusionArmFaceLabel] using
        routeOrderedFusionEntryOtherFaceLabels_eq_exitTurn_of_not_cut
          graphData hcubic hrotation data lens hab hac hbc labels cut hexact
            position hnot
  | exitCrossing position hnot =>
      simpa [routeOrderedFusionArmFaceLabel] using
        routeOrderedFusionExitOtherFaceLabels_eq_entryTurn_of_not_cut
          graphData hcubic hrotation data lens hab hac hbc labels cut hexact
            position hnot
  | bSegment first second hbOrder hnot =>
      exact EvenKempeFusionLens.bRouteStateFaceLabels_eq_of_not_cut
        data lens hab hac first second hbOrder graphData hcubic hrotation
          labels cut hexact hnot
  | cSegment first second hcOrder hnot =>
      exact EvenKempeFusionLens.cRouteStateFaceLabels_eq_of_not_cut
        data lens hab hac first second hcOrder graphData hcubic hrotation
          labels cut hexact hnot

/-- Two fusion-arm states are connected when they lie in the equivalence
closure of the cut-avoiding local crossings and primal route wires. -/
def CutAvoidingFusionFaceConnected
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (cut : G.edgeSet → Prop)
    (start finish : (Fin lens.fusionSiteCount × Bool) × Bool) : Prop :=
  Relation.EqvGen
    (CutAvoidingFusionFaceStep graphData data lens hab hac cut) start finish

/-- Exact-cut labels are constant on every connected component of the
fusion-face network. This is the compositional closure needed to replace a
sequence of local face calculations by one finite reachability proof. -/
theorem routeOrderedFusionArmFaceLabel_eq_of_cutAvoidingFusionFaceConnected
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
    {start finish : (Fin lens.fusionSiteCount × Bool) × Bool}
    (hconnected : CutAvoidingFusionFaceConnected
      graphData data lens hab hac cut start finish) :
    routeOrderedFusionArmFaceLabel graphData data lens hab hac labels start =
      routeOrderedFusionArmFaceLabel graphData data lens hab hac labels finish := by
  induction hconnected with
  | rel start finish hstep =>
      exact routeOrderedFusionArmFaceLabel_eq_of_cutAvoidingFusionFaceStep
        graphData hcubic hrotation data lens hab hac hbc labels cut hexact hstep
  | refl state => rfl
  | symm start finish _ inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans start middle finish _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
