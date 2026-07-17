import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelTailSegments
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionComplementCutAvoidance

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

/-- The two strict tails complementary to an exact singleton `bc` splice
transport its face-side label from the shared cross site to the unused
ports `1` and `3`. -/
theorem EvenKempeFusionLens.bcRightTailFaceLabels_eq
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
          (data.oppositePortClosure path).edges) :
    labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          (lens01.bRoute.firstCrossExitDart
            lens23.cRoute hab hbc site))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          lens01.bRoute.rightTerminalDart)) ∧
    labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          (lens01.bRoute.secondCrossExitDart
            lens23.cRoute hac hbc site))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          lens23.cRoute.rightTerminalDart)) := by
  have htails :=
    EvenKempeFusionLens.bcCrossSpliceSuffixes_not_mem_oppositePortClosure_edges
      data lens01 lens23 hcount site path hsupport
  have hfirstEndMem : data.degreeTwoBoundaryData.defectVertex 1 ∈
      lens01.bRoute.rightEdge.1.1 := by
    have h := lens01.bRoute.rightIncident
    rw [incidentEdgeFinset, Finset.mem_filter] at h
    exact h.2
  have hsecondEndMem : data.degreeTwoBoundaryData.defectVertex 3 ∈
      lens23.cRoute.rightEdge.1.1 := by
    have h := lens23.cRoute.rightIncident
    rw [incidentEdgeFinset, Finset.mem_filter] at h
    exact h.2
  let firstTail :=
    EvenKempeFusionLens.bcFirstRightTailSegment
      lens01 lens23 hdata hab hac hbc site
  let secondTail :=
    EvenKempeFusionLens.bcSecondRightTailSegment
      lens01 lens23 hdata hab hac hbc site
  have hfirstNil : ¬firstTail.Nil := by
    dsimp only [firstTail,
      EvenKempeFusionLens.bcFirstRightTailSegment]
    exact lens01.bRoute.firstCrossTailSegment_not_nil
      lens23.cRoute hab hbc site (data.degreeTwoBoundaryData.defectVertex 1)
      hfirstEndMem
      (lens01.bcFirstSuffix_endCap_ne lens23 hdata hab hac hbc site)
  have hsecondNil : ¬secondTail.Nil := by
    dsimp only [secondTail,
      EvenKempeFusionLens.bcSecondRightTailSegment]
    exact lens01.bRoute.secondCrossTailSegment_not_nil
      lens23.cRoute hac hbc site (data.degreeTwoBoundaryData.defectVertex 3)
      hsecondEndMem
      (lens01.bcSecondSuffix_endCap_ne lens23 hdata hab hac hbc site)
  have hfirstTrail : firstTail.IsTrail := by
    dsimp only [firstTail,
      EvenKempeFusionLens.bcFirstRightTailSegment]
    exact lens01.bRoute.firstCrossTailSegment_isTrail
      lens23.cRoute hab hbc site (data.degreeTwoBoundaryData.defectVertex 1)
      hfirstEndMem
      (lens01.bcFirstSuffix_endCap_ne lens23 hdata hab hac hbc site)
  have hsecondTrail : secondTail.IsTrail := by
    dsimp only [secondTail,
      EvenKempeFusionLens.bcSecondRightTailSegment]
    exact lens01.bRoute.secondCrossTailSegment_isTrail
      lens23.cRoute hac hbc site (data.degreeTwoBoundaryData.defectVertex 3)
      hsecondEndMem
      (lens01.bcSecondSuffix_endCap_ne lens23 hdata hab hac hbc site)
  have hfirstEdges : firstTail.edges =
      (lens01.bRoute.firstSuffixFromCrossSite
        lens23.cRoute site).support.tail.map Subtype.val := by
    dsimp only [firstTail,
      EvenKempeFusionLens.bcFirstRightTailSegment]
    exact lens01.bRoute.firstCrossTailSegment_edges
      lens23.cRoute hab hbc site (data.degreeTwoBoundaryData.defectVertex 1)
      hfirstEndMem
      (lens01.bcFirstSuffix_endCap_ne lens23 hdata hab hac hbc site)
  have hsecondEdges : secondTail.edges =
      (lens01.bRoute.secondSuffixFromCrossSite
        lens23.cRoute site).support.tail.map Subtype.val := by
    dsimp only [secondTail,
      EvenKempeFusionLens.bcSecondRightTailSegment]
    exact lens01.bRoute.secondCrossTailSegment_edges
      lens23.cRoute hac hbc site (data.degreeTwoBoundaryData.defectVertex 3)
      hsecondEndMem
      (lens01.bcSecondSuffix_endCap_ne lens23 hdata hab hac hbc site)
  have hfirstDart : firstTail.firstDart hfirstNil =
      lens01.bRoute.firstCrossExitDart
        lens23.cRoute hab hbc site := by
    dsimp only [firstTail,
      EvenKempeFusionLens.bcFirstRightTailSegment]
    exact lens01.bRoute.firstCrossTailSegment_firstDart
      lens23.cRoute hab hbc site (data.degreeTwoBoundaryData.defectVertex 1)
      hfirstEndMem
      (lens01.bcFirstSuffix_endCap_ne lens23 hdata hab hac hbc site)
      hfirstNil
  have hsecondDart : secondTail.firstDart hsecondNil =
      lens01.bRoute.secondCrossExitDart
        lens23.cRoute hac hbc site := by
    dsimp only [secondTail,
      EvenKempeFusionLens.bcSecondRightTailSegment]
    exact lens01.bRoute.secondCrossTailSegment_firstDart
      lens23.cRoute hac hbc site (data.degreeTwoBoundaryData.defectVertex 3)
      hsecondEndMem
      (lens01.bcSecondSuffix_endCap_ne lens23 hdata hab hac hbc site)
      hsecondNil
  have hfirstLast : (firstTail.lastDart hfirstNil).symm =
      lens01.bRoute.rightTerminalDart := by
    dsimp only [firstTail,
      EvenKempeFusionLens.bcFirstRightTailSegment]
    exact lens01.bRoute.firstCrossTailSegment_lastDart_symm
      lens23.cRoute hab hbc site
      (lens01.bcFirstSuffix_endCap_ne lens23 hdata hab hac hbc site)
      hfirstNil
  have hsecondLast : (secondTail.lastDart hsecondNil).symm =
      lens23.cRoute.rightTerminalDart := by
    dsimp only [secondTail,
      EvenKempeFusionLens.bcSecondRightTailSegment]
    exact lens01.bRoute.secondCrossTailSegment_lastDart_symm
      lens23.cRoute hac hbc site
      (lens01.bcSecondSuffix_endCap_ne lens23 hdata hab hac hbc site)
      hsecondNil
  have hfirstLabels :=
    retainedTrail_labels_eq_terminalDarts_of_support_not_cut
      graphData hcubic hrotation data labels
      (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
      hexact firstTail hfirstNil hfirstTrail
      (lens01.bRoute.firstSuffixFromCrossSite
        lens23.cRoute site).support.tail
      (by
        intro edge hedge
        rw [hfirstEdges] at hedge
        exact hedge)
      htails.1
  have hsecondLabels :=
    retainedTrail_labels_eq_terminalDarts_of_support_not_cut
      graphData hcubic hrotation data labels
      (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
      hexact secondTail hsecondNil hsecondTrail
      (lens01.bRoute.secondSuffixFromCrossSite
        lens23.cRoute site).support.tail
      (by
        intro edge hedge
        rw [hsecondEdges] at hedge
        exact hedge)
      htails.2
  constructor
  · simpa only [hfirstDart, hfirstLast] using hfirstLabels
  · simpa only [hsecondDart, hsecondLast] using hsecondLabels

/-- The two strict tails complementary to an exact singleton `cb` splice
transport its face-side label from the shared cross site to the unused
ports `1` and `3`. -/
theorem EvenKempeFusionLens.cbRightTailFaceLabels_eq
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
          (data.oppositePortClosure path).edges) :
    labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          (lens01.cRoute.firstCrossExitDart
            lens23.bRoute hac hbc.symm site))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          lens01.cRoute.rightTerminalDart)) ∧
    labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          (lens01.cRoute.secondCrossExitDart
            lens23.bRoute hab hbc.symm site))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data
          lens23.bRoute.rightTerminalDart)) := by
  have htails :=
    EvenKempeFusionLens.cbCrossSpliceSuffixes_not_mem_oppositePortClosure_edges
      data lens01 lens23 hcount site path hsupport
  have hfirstEndMem : data.degreeTwoBoundaryData.defectVertex 1 ∈
      lens01.cRoute.rightEdge.1.1 := by
    have h := lens01.cRoute.rightIncident
    rw [incidentEdgeFinset, Finset.mem_filter] at h
    exact h.2
  have hsecondEndMem : data.degreeTwoBoundaryData.defectVertex 3 ∈
      lens23.bRoute.rightEdge.1.1 := by
    have h := lens23.bRoute.rightIncident
    rw [incidentEdgeFinset, Finset.mem_filter] at h
    exact h.2
  let firstTail :=
    EvenKempeFusionLens.cbFirstRightTailSegment
      lens01 lens23 hdata hab hac hbc site
  let secondTail :=
    EvenKempeFusionLens.cbSecondRightTailSegment
      lens01 lens23 hdata hab hac hbc site
  have hfirstNil : ¬firstTail.Nil := by
    dsimp only [firstTail,
      EvenKempeFusionLens.cbFirstRightTailSegment]
    exact lens01.cRoute.firstCrossTailSegment_not_nil
      lens23.bRoute hac hbc.symm site
      (data.degreeTwoBoundaryData.defectVertex 1)
      hfirstEndMem
      (lens01.cbFirstSuffix_endCap_ne lens23 hdata hab hac hbc site)
  have hsecondNil : ¬secondTail.Nil := by
    dsimp only [secondTail,
      EvenKempeFusionLens.cbSecondRightTailSegment]
    exact lens01.cRoute.secondCrossTailSegment_not_nil
      lens23.bRoute hab hbc.symm site
      (data.degreeTwoBoundaryData.defectVertex 3)
      hsecondEndMem
      (lens01.cbSecondSuffix_endCap_ne lens23 hdata hab hac hbc site)
  have hfirstTrail : firstTail.IsTrail := by
    dsimp only [firstTail,
      EvenKempeFusionLens.cbFirstRightTailSegment]
    exact lens01.cRoute.firstCrossTailSegment_isTrail
      lens23.bRoute hac hbc.symm site
      (data.degreeTwoBoundaryData.defectVertex 1)
      hfirstEndMem
      (lens01.cbFirstSuffix_endCap_ne lens23 hdata hab hac hbc site)
  have hsecondTrail : secondTail.IsTrail := by
    dsimp only [secondTail,
      EvenKempeFusionLens.cbSecondRightTailSegment]
    exact lens01.cRoute.secondCrossTailSegment_isTrail
      lens23.bRoute hab hbc.symm site
      (data.degreeTwoBoundaryData.defectVertex 3)
      hsecondEndMem
      (lens01.cbSecondSuffix_endCap_ne lens23 hdata hab hac hbc site)
  have hfirstEdges : firstTail.edges =
      (lens01.cRoute.firstSuffixFromCrossSite
        lens23.bRoute site).support.tail.map Subtype.val := by
    dsimp only [firstTail,
      EvenKempeFusionLens.cbFirstRightTailSegment]
    exact lens01.cRoute.firstCrossTailSegment_edges
      lens23.bRoute hac hbc.symm site
      (data.degreeTwoBoundaryData.defectVertex 1)
      hfirstEndMem
      (lens01.cbFirstSuffix_endCap_ne lens23 hdata hab hac hbc site)
  have hsecondEdges : secondTail.edges =
      (lens01.cRoute.secondSuffixFromCrossSite
        lens23.bRoute site).support.tail.map Subtype.val := by
    dsimp only [secondTail,
      EvenKempeFusionLens.cbSecondRightTailSegment]
    exact lens01.cRoute.secondCrossTailSegment_edges
      lens23.bRoute hab hbc.symm site
      (data.degreeTwoBoundaryData.defectVertex 3)
      hsecondEndMem
      (lens01.cbSecondSuffix_endCap_ne lens23 hdata hab hac hbc site)
  have hfirstDart : firstTail.firstDart hfirstNil =
      lens01.cRoute.firstCrossExitDart
        lens23.bRoute hac hbc.symm site := by
    dsimp only [firstTail,
      EvenKempeFusionLens.cbFirstRightTailSegment]
    exact lens01.cRoute.firstCrossTailSegment_firstDart
      lens23.bRoute hac hbc.symm site
      (data.degreeTwoBoundaryData.defectVertex 1)
      hfirstEndMem
      (lens01.cbFirstSuffix_endCap_ne lens23 hdata hab hac hbc site)
      hfirstNil
  have hsecondDart : secondTail.firstDart hsecondNil =
      lens01.cRoute.secondCrossExitDart
        lens23.bRoute hab hbc.symm site := by
    dsimp only [secondTail,
      EvenKempeFusionLens.cbSecondRightTailSegment]
    exact lens01.cRoute.secondCrossTailSegment_firstDart
      lens23.bRoute hab hbc.symm site
      (data.degreeTwoBoundaryData.defectVertex 3)
      hsecondEndMem
      (lens01.cbSecondSuffix_endCap_ne lens23 hdata hab hac hbc site)
      hsecondNil
  have hfirstLast : (firstTail.lastDart hfirstNil).symm =
      lens01.cRoute.rightTerminalDart := by
    dsimp only [firstTail,
      EvenKempeFusionLens.cbFirstRightTailSegment]
    exact lens01.cRoute.firstCrossTailSegment_lastDart_symm
      lens23.bRoute hac hbc.symm site
      (lens01.cbFirstSuffix_endCap_ne lens23 hdata hab hac hbc site)
      hfirstNil
  have hsecondLast : (secondTail.lastDart hsecondNil).symm =
      lens23.bRoute.rightTerminalDart := by
    dsimp only [secondTail,
      EvenKempeFusionLens.cbSecondRightTailSegment]
    exact lens01.cRoute.secondCrossTailSegment_lastDart_symm
      lens23.bRoute hab hbc.symm site
      (lens01.cbSecondSuffix_endCap_ne lens23 hdata hab hac hbc site)
      hsecondNil
  have hfirstLabels :=
    retainedTrail_labels_eq_terminalDarts_of_support_not_cut
      graphData hcubic hrotation data labels
      (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
      hexact firstTail hfirstNil hfirstTrail
      (lens01.cRoute.firstSuffixFromCrossSite
        lens23.bRoute site).support.tail
      (by
        intro edge hedge
        rw [hfirstEdges] at hedge
        exact hedge)
      htails.1
  have hsecondLabels :=
    retainedTrail_labels_eq_terminalDarts_of_support_not_cut
      graphData hcubic hrotation data labels
      (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
      hexact secondTail hsecondNil hsecondTrail
      (lens01.cRoute.secondSuffixFromCrossSite
        lens23.bRoute site).support.tail
      (by
        intro edge hedge
        rw [hsecondEdges] at hedge
        exact hedge)
      htails.2
  constructor
  · simpa only [hfirstDart, hfirstLast] using hfirstLabels
  · simpa only [hsecondDart, hsecondLast] using hsecondLabels

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
