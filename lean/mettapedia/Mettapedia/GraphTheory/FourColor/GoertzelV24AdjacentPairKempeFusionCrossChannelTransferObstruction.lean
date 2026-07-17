import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelTerminalCutFreedom
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairRotationPortFaceCut

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
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

/-- Once the two route terminals at a port have the same face label, the
rotation-selected terminal has that label independently of its turn bit. -/
theorem fusionRightTerminalTurnDart_faceLabels_eq_routeTerminals
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hroutes :
      labels (dartOrbitFace graphData.toRotationSystem
          (ambientBRightTerminalDart data lens)) =
        labels (dartOrbitFace graphData.toRotationSystem
          (ambientCRightTerminalDart data lens))) :
    labels (dartOrbitFace graphData.toRotationSystem
        (fusionRightTerminalTurnDart graphData data lens)) =
          labels (dartOrbitFace graphData.toRotationSystem
            (ambientBRightTerminalDart data lens)) ∧
      labels (dartOrbitFace graphData.toRotationSystem
        (fusionRightTerminalTurnDart graphData data lens)) =
          labels (dartOrbitFace graphData.toRotationSystem
            (ambientCRightTerminalDart data lens)) := by
  by_cases hturn : fusionRightTerminalTurn graphData data lens = true
  · simp [fusionRightTerminalTurnDart, hturn, hroutes]
  · simp [fusionRightTerminalTurnDart, hturn, hroutes]

/-- Unpack a rejected `bc` transfer bit as reversed pairing and equal
endpoint turns. -/
theorem EvenKempeFusionLens.bcRejectedCrossState_of_faceTransferBit_eq_false
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    lens01.bRoute.crossPairingBit lens23.cRoute
        hab hac hbc site = false ∧
      graphData.toRotationSystem.orientedEdgeArmTurn
          (ambientFirstCrossDart data lens01.bRoute lens23.cRoute
            hab hbc site)
          (ambientSecondCrossExitDart data lens01.bRoute lens23.cRoute
            hac hbc site) =
        graphData.toRotationSystem.orientedEdgeArmTurn
          (graphData.toRotationSystem.alpha
            (ambientFirstCrossDart data lens01.bRoute lens23.cRoute
              hab hbc site))
          (ambientFirstCrossExitDart data lens01.bRoute lens23.cRoute
            hab hbc site) := by
  apply (crossExitFaceTransferBit_eq_false_iff_pairing_false_and_turns_eq
    data graphData lens01.bRoute lens23.cRoute hab hac hbc site).1
  simpa only [EvenKempeFusionLens.bcCrossExitFaceTransferBit] using hfalse

/-- The rejected `cb` state has the symmetric reversed-pairing/equal-turn
description. -/
theorem EvenKempeFusionLens.cbRejectedCrossState_of_faceTransferBit_eq_false
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    lens01.cRoute.crossPairingBit lens23.bRoute
        hac hab hbc.symm site = false ∧
      graphData.toRotationSystem.orientedEdgeArmTurn
          (ambientFirstCrossDart data lens01.cRoute lens23.bRoute
            hac hbc.symm site)
          (ambientSecondCrossExitDart data lens01.cRoute lens23.bRoute
            hab hbc.symm site) =
        graphData.toRotationSystem.orientedEdgeArmTurn
          (graphData.toRotationSystem.alpha
            (ambientFirstCrossDart data lens01.cRoute lens23.bRoute
              hac hbc.symm site))
          (ambientFirstCrossExitDart data lens01.cRoute lens23.bRoute
            hac hbc.symm site) := by
  apply (crossExitFaceTransferBit_eq_false_iff_pairing_false_and_turns_eq
    data graphData lens01.cRoute lens23.bRoute hac hab hbc.symm site).1
  simpa only [EvenKempeFusionLens.cbCrossExitFaceTransferBit] using hfalse

/-- Exact separation of the two unused boundary faces rules out the accepted
state of a sparse `bc` cross channel. -/
theorem EvenKempeFusionLens.bcCrossExitFaceTransferBit_eq_false_of_unusedBoundaryFaces_ne
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
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
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
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          (data.oppositePortClosure path).edges)
    (hunused :
      labels (dartOrbitFace graphData.toRotationSystem
          (boundaryPortDart data 1)) ≠
        labels (dartOrbitFace graphData.toRotationSystem
          (boundaryPortDart data 3))) :
    EvenKempeFusionLens.bcCrossExitFaceTransferBit lens01 graphData lens23
      hab hac hbc site = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htransfer
  have hroutes :=
    EvenKempeFusionLens.bcRightTerminalFaceLabels_eq_at_unusedPorts
      graphData data lens01 lens23 hab hac hbc hbDisjoint hcDisjoint hcount
        site path hsupport hcubic hrotation labels hexact
  have hselected01 :=
    fusionRightTerminalTurnDart_faceLabels_eq_routeTerminals
      graphData data lens01 labels hroutes.1
  have hselected23 :=
    fusionRightTerminalTurnDart_faceLabels_eq_routeTerminals
      graphData data lens23 labels hroutes.2
  have hboundary := unusedBoundaryFaces_labels_eq_selectedRightTerminals
    graphData hcubic hrotation data path lens01 lens23 hbc labels hexact
  have hcross :=
    EvenKempeFusionLens.bcRightTerminalFaceLabels_eq_of_transferBit_eq_true
      graphData data lens01 lens23 hdata hab hac hbc hcount site path hsupport
        hcubic hrotation labels hexact htransfer
  apply hunused
  calc
    labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data 1)) =
        labels (dartOrbitFace graphData.toRotationSystem
          (fusionRightTerminalTurnDart graphData data lens01)) := hboundary.1
    _ = labels (dartOrbitFace graphData.toRotationSystem
          (ambientBRightTerminalDart data lens01)) := hselected01.1
    _ = labels (dartOrbitFace graphData.toRotationSystem
          (ambientCRightTerminalDart data lens23)) := hcross
    _ = labels (dartOrbitFace graphData.toRotationSystem
          (fusionRightTerminalTurnDart graphData data lens23)) :=
      hselected23.2.symm
    _ = labels (dartOrbitFace graphData.toRotationSystem
          (boundaryPortDart data 3)) := hboundary.2.symm

/-- The symmetric exact-cut obstruction rules out the accepted `cb` state. -/
theorem EvenKempeFusionLens.cbCrossExitFaceTransferBit_eq_false_of_unusedBoundaryFaces_ne
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
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
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
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          (data.oppositePortClosure path).edges)
    (hunused :
      labels (dartOrbitFace graphData.toRotationSystem
          (boundaryPortDart data 1)) ≠
        labels (dartOrbitFace graphData.toRotationSystem
          (boundaryPortDart data 3))) :
    EvenKempeFusionLens.cbCrossExitFaceTransferBit lens01 graphData lens23
      hab hac hbc site = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htransfer
  have hroutes :=
    EvenKempeFusionLens.cbRightTerminalFaceLabels_eq_at_unusedPorts
      graphData data lens01 lens23 hab hac hbc hbDisjoint hcDisjoint hcount
        site path hsupport hcubic hrotation labels hexact
  have hselected01 :=
    fusionRightTerminalTurnDart_faceLabels_eq_routeTerminals
      graphData data lens01 labels hroutes.1
  have hselected23 :=
    fusionRightTerminalTurnDart_faceLabels_eq_routeTerminals
      graphData data lens23 labels hroutes.2
  have hboundary := unusedBoundaryFaces_labels_eq_selectedRightTerminals
    graphData hcubic hrotation data path lens01 lens23 hbc labels hexact
  have hcross :=
    EvenKempeFusionLens.cbRightTerminalFaceLabels_eq_of_transferBit_eq_true
      graphData data lens01 lens23 hdata hab hac hbc hcount site path hsupport
        hcubic hrotation labels hexact htransfer
  apply hunused
  calc
    labels (dartOrbitFace graphData.toRotationSystem
        (boundaryPortDart data 1)) =
        labels (dartOrbitFace graphData.toRotationSystem
          (fusionRightTerminalTurnDart graphData data lens01)) := hboundary.1
    _ = labels (dartOrbitFace graphData.toRotationSystem
          (ambientCRightTerminalDart data lens01)) := hselected01.2
    _ = labels (dartOrbitFace graphData.toRotationSystem
          (ambientBRightTerminalDart data lens23)) := hcross
    _ = labels (dartOrbitFace graphData.toRotationSystem
          (fusionRightTerminalTurnDart graphData data lens23)) :=
      hselected23.1.symm
    _ = labels (dartOrbitFace graphData.toRotationSystem
          (boundaryPortDart data 3)) := hboundary.2.symm

/-- In a graph-backed vertex-minimal counterexample, the canonical spherical
face cut supplies the unused-face separation needed to force a sparse `bc`
cross state to be rejected. -/
theorem EvenKempeFusionLens.rotationOrdered_bcCrossExitFaceTransferBit_eq_false_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 0 1)
    (lens23 : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 2 3)
    (hdata : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (path : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).Walk
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).retainedPort 0)
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).retainedPort 2))
    (htrail : path.IsTrail)
    (hsupport : path.edges ⊆
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val) :
    EvenKempeFusionLens.bcCrossExitFaceTransferBit lens01 graphData lens23
      hab hac hbc site = false := by
  let ordered := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  rcases baseData.exists_rotationOrdered_oppositePortClosure_exactFaceCut_of_minimal_of_isTrail
      graphData minimal minimal.spherical.cubic minimal.vertexRotationCyclic
        path htrail with
    ⟨labels, _hlabels, hexact, _hports, _hcentral, hunused⟩
  exact EvenKempeFusionLens.bcCrossExitFaceTransferBit_eq_false_of_unusedBoundaryFaces_ne
    graphData ordered lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
      hcount site path hsupport minimal.spherical.cubic
      minimal.vertexRotationCyclic labels hexact hunused

/-- The rotation-ordered `cb` branch is rejected by the same minimal
spherical exact-cut argument. -/
theorem EvenKempeFusionLens.rotationOrdered_cbCrossExitFaceTransferBit_eq_false_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 0 1)
    (lens23 : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 2 3)
    (hdata : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (path : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).Walk
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).retainedPort 0)
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).retainedPort 2))
    (htrail : path.IsTrail)
    (hsupport : path.edges ⊆
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val) :
    EvenKempeFusionLens.cbCrossExitFaceTransferBit lens01 graphData lens23
      hab hac hbc site = false := by
  let ordered := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  rcases baseData.exists_rotationOrdered_oppositePortClosure_exactFaceCut_of_minimal_of_isTrail
      graphData minimal minimal.spherical.cubic minimal.vertexRotationCyclic
        path htrail with
    ⟨labels, _hlabels, hexact, _hports, _hcentral, hunused⟩
  exact EvenKempeFusionLens.cbCrossExitFaceTransferBit_eq_false_of_unusedBoundaryFaces_ne
    graphData ordered lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
      hcount site path hsupport minimal.spherical.cubic
      minimal.vertexRotationCyclic labels hexact hunused

/-- A nonempty sparse `bc` channel supplies its own supported opposite-port
trail, so the rejected state has no residual path hypothesis. -/
theorem EvenKempeFusionLens.exists_rotationOrdered_bcCrossExitFaceTransferBit_eq_false_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 0 1)
    (lens23 : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 2 3)
    (hdata : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (hnonempty : lens01.bcCrossSites lens23 ≠ []) :
    ∃ site : lens01.bRoute.CrossSite lens23.cRoute,
      EvenKempeFusionLens.bcCrossExitFaceTransferBit lens01 graphData lens23
        hab hac hbc site = false := by
  let ordered := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  rcases lens01.exists_bcPrimalTrail_with_crossSpliceCoverage lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨site, path, htrail, _hpositive, hsupport, _hrouteSupport, _hcoverage⟩
  exact ⟨site,
    EvenKempeFusionLens.rotationOrdered_bcCrossExitFaceTransferBit_eq_false_of_minimal
      graphData minimal baseData lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount site path htrail hsupport⟩

/-- The symmetric nonempty sparse `cb` channel likewise produces a rejected
state without an externally chosen trail. -/
theorem EvenKempeFusionLens.exists_rotationOrdered_cbCrossExitFaceTransferBit_eq_false_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 0 1)
    (lens23 : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 2 3)
    (hdata : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (hnonempty : lens01.cbCrossSites lens23 ≠ []) :
    ∃ site : lens01.cRoute.CrossSite lens23.bRoute,
      EvenKempeFusionLens.cbCrossExitFaceTransferBit lens01 graphData lens23
        hab hac hbc site = false := by
  let ordered := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  rcases lens01.exists_cbPrimalTrail_with_crossSpliceCoverage lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨site, path, htrail, _hpositive, hsupport, _hrouteSupport, _hcoverage⟩
  exact ⟨site,
    EvenKempeFusionLens.rotationOrdered_cbCrossExitFaceTransferBit_eq_false_of_minimal
      graphData minimal baseData lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount site path htrail hsupport⟩

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
