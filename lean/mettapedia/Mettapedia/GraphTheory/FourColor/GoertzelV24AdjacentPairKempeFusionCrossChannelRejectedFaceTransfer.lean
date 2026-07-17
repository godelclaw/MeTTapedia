import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelRejectedTrail

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

/-- The ambient central dart at a cross site carries exactly the selected
retained cross edge. -/
@[simp] theorem toRotationSystem_edgeOf_ambientFirstCrossDart
    (graphData : Data G) (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    graphData.toRotationSystem.edgeOf
        (ambientFirstCrossDart data first second hab hbc site) =
      retainedEdgeToAmbientEdge data site.1 := by
  apply Subtype.ext
  change
    (retainedDartToAmbientDart data
      (first.firstCrossDart second hab hbc site)).edge =
        site.1.1.map Subtype.val
  rw [retainedDartToAmbientDart_edge,
    first.firstCrossDart_edge second hab hbc site]

/-- A rejected cross state is the actual transposition of the two exact-cut
face sides whenever the central edge is cut and both outgoing arms are not. -/
theorem crossExitFaceLabels_ne_of_transferBit_eq_false
    (data : AdjacentPairData G) (graphData : Data G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second)
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
    (hfalse : crossExitFaceTransferBit data graphData first second
      hab hac hbc site = false)
    (hcentralCut : cut (graphData.toRotationSystem.edgeOf
      (ambientFirstCrossDart data first second hab hbc site)))
    (hfirstNotCut : ¬cut (graphData.toRotationSystem.edgeOf
      (ambientFirstCrossExitDart data first second hab hbc site)))
    (hsecondNotCut : ¬cut (graphData.toRotationSystem.edgeOf
      (ambientSecondCrossExitDart data first second hac hbc site))) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientFirstCrossExitDart data first second hab hbc site)) ≠
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientSecondCrossExitDart data first second hac hbc site)) := by
  have hstate :=
    (crossExitFaceTransferBit_eq_false_iff_pairing_false_and_turns_eq
      data graphData first second hab hac hbc site).1 hfalse
  have hopposite : crossExitOppositeTransferBit data graphData
      first second hab hac hbc site = false := by
    rw [← crossExitFaceTransferBit_eq_opposite_of_pairing_false
      data graphData first second hab hac hbc site hstate.1]
    exact hfalse
  have hreversed :=
    first.secondCrossDart_eq_firstCrossDart_symm_of_pairing_false
      second hab hac hbc site hstate.1
  have hentryBaseRetained :
      (first.secondCrossExitDart second hac hbc site).fst =
        (first.firstCrossDart second hab hbc site).fst := by
    calc
      (first.secondCrossExitDart second hac hbc site).fst =
          (first.secondCrossDart second hac hbc site).snd := rfl
      _ = ((first.firstCrossDart second hab hbc site).symm).snd :=
        congrArg (fun dart ↦ dart.snd) hreversed
      _ = (first.firstCrossDart second hab hbc site).fst := rfl
  have hne := graphData.toRotationSystem
    |>.labels_ne_of_oppositeArms_of_transferBit_eq_false
      hcubic hrotation labels cut hexact
      (ambientFirstCrossDart data first second hab hbc site)
      (ambientSecondCrossExitDart data first second hac hbc site)
      (ambientFirstCrossExitDart data first second hab hbc site)
      (by
        simpa only [SimpleGraphDartRotation.Data.toRotationSystem_vertOf,
          ambientFirstCrossDart, ambientSecondCrossExitDart,
          retainedDartToAmbientDart_fst] using
            congrArg Subtype.val hentryBaseRetained)
      (by
        simp only [SimpleGraphDartRotation.Data.toRotationSystem_vertOf,
          SimpleGraphDartRotation.Data.toRotationSystem_alpha,
          ambientFirstCrossDart, ambientFirstCrossExitDart,
          retainedDartToAmbientDart_fst]
        exact congrArg Subtype.val
          (first.firstCrossDart_snd second hab hbc site).symm)
      (by
        intro hdarts
        exact first.firstCrossDart_ne_secondCrossExitDart
          second hab hac hbc site
          (retainedDartToAmbientDart_injective data hdarts))
      (by
        intro hdarts
        apply first.firstCrossDart_symm_ne_firstCrossExitDart
          second hab hbc site
        apply retainedDartToAmbientDart_injective data
        change
          (retainedDartToAmbientDart data
            (first.firstCrossDart second hab hbc site)).symm =
          retainedDartToAmbientDart data
            (first.firstCrossExitDart second hab hbc site) at hdarts
        simpa only [ambientFirstCrossDart,
          ambientFirstCrossExitDart,
          SimpleGraphDartRotation.Data.toRotationSystem_alpha,
          retainedDartToAmbientDart_symm] using hdarts)
      hopposite hcentralCut hsecondNotCut hfirstNotCut
  exact hne.symm

/-- In an exact sparse `bc` closure, rejection makes the two outgoing
cross-arm face labels different. -/
theorem EvenKempeFusionLens.bcCrossExitFaceLabels_ne_of_rejected
    (graphData : Data G) (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
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
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (hsite : (retainedEdgeToAmbientEdge data site.1).1 ∈
      (data.oppositePortClosure path).edges) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientFirstCrossExitDart data lens01.bRoute lens23.cRoute
          hab hbc site)) ≠
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientSecondCrossExitDart data lens01.bRoute lens23.cRoute
          hac hbc site)) := by
  have htails :=
    EvenKempeFusionLens.bcCrossSpliceSuffixes_not_mem_oppositePortClosure_edges
      data lens01 lens23 hcount site path hsupport
  apply crossExitFaceLabels_ne_of_transferBit_eq_false
    data graphData lens01.bRoute lens23.cRoute hab hac hbc site
      hcubic hrotation labels
      (fun edge ↦ edge.1 ∈ (data.oppositePortClosure path).edges)
      hexact
  · simpa only [EvenKempeFusionLens.bcCrossExitFaceTransferBit] using
      hfalse
  · simpa only [toRotationSystem_edgeOf_ambientFirstCrossDart] using
      hsite
  · rw [toRotationSystem_edgeOf_ambientFirstCrossExitDart]
    exact htails.1 _
      (lens01.bRoute.firstCrossExitEdge_mem_tail_support
        lens23.cRoute hab hbc site)
  · rw [toRotationSystem_edgeOf_ambientSecondCrossExitDart]
    exact htails.2 _
      (lens01.bRoute.secondCrossExitEdge_mem_tail_support
        lens23.cRoute hac hbc site)

/-- The rejected `bc` transposition propagates along both cut-free tails,
so the two unused route-terminal faces are different. -/
theorem EvenKempeFusionLens.bcRightTerminalFaceLabels_ne_of_rejected
    (graphData : Data G) (data : AdjacentPairData G)
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
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (hsite : (retainedEdgeToAmbientEdge data site.1).1 ∈
      (data.oppositePortClosure path).edges) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientBRightTerminalDart data lens01)) ≠
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientCRightTerminalDart data lens23)) := by
  have hlocal := EvenKempeFusionLens.bcCrossExitFaceLabels_ne_of_rejected
    graphData data lens01 lens23 hab hac hbc hcount site path hsupport
      hcubic hrotation labels hexact hfalse hsite
  have htails := EvenKempeFusionLens.bcRightTailFaceLabels_eq
    graphData data lens01 lens23 hdata hab hac hbc hcount site path hsupport
      hcubic hrotation labels hexact
  intro heq
  exact hlocal (htails.1.trans (heq.trans htails.2.symm))

/-- The same cut-side transposition holds in the `cb` orientation. -/
theorem EvenKempeFusionLens.cbCrossExitFaceLabels_ne_of_rejected
    (graphData : Data G) (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
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
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (hsite : (retainedEdgeToAmbientEdge data site.1).1 ∈
      (data.oppositePortClosure path).edges) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientFirstCrossExitDart data lens01.cRoute lens23.bRoute
          hac hbc.symm site)) ≠
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientSecondCrossExitDart data lens01.cRoute lens23.bRoute
          hab hbc.symm site)) := by
  have htails :=
    EvenKempeFusionLens.cbCrossSpliceSuffixes_not_mem_oppositePortClosure_edges
      data lens01 lens23 hcount site path hsupport
  apply crossExitFaceLabels_ne_of_transferBit_eq_false
    data graphData lens01.cRoute lens23.bRoute hac hab hbc.symm site
      hcubic hrotation labels
      (fun edge ↦ edge.1 ∈ (data.oppositePortClosure path).edges)
      hexact
  · simpa only [EvenKempeFusionLens.cbCrossExitFaceTransferBit] using
      hfalse
  · simpa only [toRotationSystem_edgeOf_ambientFirstCrossDart] using
      hsite
  · rw [toRotationSystem_edgeOf_ambientFirstCrossExitDart]
    exact htails.1 _
      (lens01.cRoute.firstCrossExitEdge_mem_tail_support
        lens23.bRoute hac hbc.symm site)
  · rw [toRotationSystem_edgeOf_ambientSecondCrossExitDart]
    exact htails.2 _
      (lens01.cRoute.secondCrossExitEdge_mem_tail_support
        lens23.bRoute hab hbc.symm site)

/-- The `cb` rejected state likewise transports opposite cut sides to its
two unused route terminals. -/
theorem EvenKempeFusionLens.cbRightTerminalFaceLabels_ne_of_rejected
    (graphData : Data G) (data : AdjacentPairData G)
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
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (hsite : (retainedEdgeToAmbientEdge data site.1).1 ∈
      (data.oppositePortClosure path).edges) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientCRightTerminalDart data lens01)) ≠
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientBRightTerminalDart data lens23)) := by
  have hlocal := EvenKempeFusionLens.cbCrossExitFaceLabels_ne_of_rejected
    graphData data lens01 lens23 hab hac hbc hcount site path hsupport
      hcubic hrotation labels hexact hfalse hsite
  have htails := EvenKempeFusionLens.cbRightTailFaceLabels_eq
    graphData data lens01 lens23 hdata hab hac hbc hcount site path hsupport
      hcubic hrotation labels hexact
  intro heq
  exact hlocal (htails.1.trans (heq.trans htails.2.symm))

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
