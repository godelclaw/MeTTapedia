import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelLocalFaceState
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelTailFaceCutTransport

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
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

/-- The local finite face-transfer state of a `bc` cross channel. -/
def EvenKempeFusionLens.bcCrossExitFaceTransferBit
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (graphData : Data G)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.bRoute.CrossSite lens23.cRoute) : Bool :=
  crossExitFaceTransferBit data graphData
    lens01.bRoute lens23.cRoute hab hac hbc site

/-- The symmetric finite state for a `cb` cross channel. -/
def EvenKempeFusionLens.cbCrossExitFaceTransferBit
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (graphData : Data G)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.cRoute.CrossSite lens23.bRoute) : Bool :=
  crossExitFaceTransferBit data graphData
    lens01.cRoute lens23.bRoute hac hab hbc.symm site

/-- An accepted singleton `bc` cross state transports one exact-cut face
label all the way between the unused right terminals at ports `1` and `3`. -/
theorem EvenKempeFusionLens.bcRightTerminalFaceLabels_eq_of_transferBit_eq_true
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          (data.oppositePortClosure path).edges)
    (htransfer : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23
      hab hac hbc site = true) :
    labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          lens01.bRoute.rightTerminalDart)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          lens23.cRoute.rightTerminalDart)) := by
  have htails :=
    EvenKempeFusionLens.bcCrossSpliceSuffixes_not_mem_oppositePortClosure_edges
      data lens01 lens23 hcount site path hsupport
  have hfirstNotCut :
      (graphData.toRotationSystem.edgeOf
          (ambientFirstCrossExitDart data lens01.bRoute lens23.cRoute
            hab hbc site)).1 ∉
        (data.oppositePortClosure path).edges := by
    rw [toRotationSystem_edgeOf_ambientFirstCrossExitDart]
    exact htails.1 _
      (lens01.bRoute.firstCrossExitEdge_mem_tail_support
        lens23.cRoute hab hbc site)
  have hsecondNotCut :
      (graphData.toRotationSystem.edgeOf
          (ambientSecondCrossExitDart data lens01.bRoute lens23.cRoute
            hac hbc site)).1 ∉
        (data.oppositePortClosure path).edges := by
    rw [toRotationSystem_edgeOf_ambientSecondCrossExitDart]
    exact htails.2 _
      (lens01.bRoute.secondCrossExitEdge_mem_tail_support
        lens23.cRoute hac hbc site)
  have hlocal := crossExitFaceLabels_eq_of_transferBit_eq_true
    data graphData lens01.bRoute lens23.cRoute hab hac hbc site
      hcubic hrotation labels
      (fun edge ↦ edge.1 ∈ (data.oppositePortClosure path).edges)
      hexact (by
        simpa only [EvenKempeFusionLens.bcCrossExitFaceTransferBit] using
          htransfer)
      hfirstNotCut hsecondNotCut
  have htail := EvenKempeFusionLens.bcRightTailFaceLabels_eq
    graphData data lens01 lens23 hdata hab hac hbc hcount site path hsupport
      hcubic hrotation labels hexact
  exact htail.1.symm.trans (hlocal.trans htail.2)

/-- An accepted singleton `cb` cross state has the same terminal
face-label consequence. -/
theorem EvenKempeFusionLens.cbRightTerminalFaceLabels_eq_of_transferBit_eq_true
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          (data.oppositePortClosure path).edges)
    (htransfer : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23
      hab hac hbc site = true) :
    labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          lens01.cRoute.rightTerminalDart)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          lens23.bRoute.rightTerminalDart)) := by
  have htails :=
    EvenKempeFusionLens.cbCrossSpliceSuffixes_not_mem_oppositePortClosure_edges
      data lens01 lens23 hcount site path hsupport
  have hfirstNotCut :
      (graphData.toRotationSystem.edgeOf
          (ambientFirstCrossExitDart data lens01.cRoute lens23.bRoute
            hac hbc.symm site)).1 ∉
        (data.oppositePortClosure path).edges := by
    rw [toRotationSystem_edgeOf_ambientFirstCrossExitDart]
    exact htails.1 _
      (lens01.cRoute.firstCrossExitEdge_mem_tail_support
        lens23.bRoute hac hbc.symm site)
  have hsecondNotCut :
      (graphData.toRotationSystem.edgeOf
          (ambientSecondCrossExitDart data lens01.cRoute lens23.bRoute
            hab hbc.symm site)).1 ∉
        (data.oppositePortClosure path).edges := by
    rw [toRotationSystem_edgeOf_ambientSecondCrossExitDart]
    exact htails.2 _
      (lens01.cRoute.secondCrossExitEdge_mem_tail_support
        lens23.bRoute hab hbc.symm site)
  have hlocal := crossExitFaceLabels_eq_of_transferBit_eq_true
    data graphData lens01.cRoute lens23.bRoute hac hab hbc.symm site
      hcubic hrotation labels
      (fun edge ↦ edge.1 ∈ (data.oppositePortClosure path).edges)
      hexact (by
        simpa only [EvenKempeFusionLens.cbCrossExitFaceTransferBit] using
          htransfer)
      hfirstNotCut hsecondNotCut
  have htail := EvenKempeFusionLens.cbRightTailFaceLabels_eq
    graphData data lens01 lens23 hdata hab hac hbc hcount site path hsupport
      hcubic hrotation labels hexact
  exact htail.1.symm.trans (hlocal.trans htail.2)

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
