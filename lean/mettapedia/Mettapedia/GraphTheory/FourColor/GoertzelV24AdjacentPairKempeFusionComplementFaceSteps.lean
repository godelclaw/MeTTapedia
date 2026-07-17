import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionComplementCutAvoidance
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionFaceCutNetwork

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
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

/-- The ambient entry-side `b` dart carries the retained previous `b` arm. -/
theorem toRotationSystem_edgeOf_ambientBEntryNeighborDart
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    graphData.toRotationSystem.edgeOf
        (ambientBEntryNeighborDart data lens hab site) =
      retainedEdgeToAmbientEdge data (lens.bPreviousVertex site).1 := by
  apply Subtype.ext
  simp [ambientBEntryNeighborDart]
  rfl

/-- The ambient exit-side `b` dart carries the retained next `b` arm. -/
theorem toRotationSystem_edgeOf_ambientBExitNeighborDart
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    graphData.toRotationSystem.edgeOf
        (ambientBExitNeighborDart data lens hab site) =
      retainedEdgeToAmbientEdge data (lens.bNextVertex site).1 := by
  apply Subtype.ext
  simp [ambientBExitNeighborDart]
  rfl

/-- The ambient entry companion carries the chirality-selected `c` arm. -/
theorem toRotationSystem_edgeOf_ambientCEntryCompanionDart
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    graphData.toRotationSystem.edgeOf
        (ambientCEntryCompanionDart data lens hab hac site) =
      retainedEdgeToAmbientEdge data
        (lens.cEdgeAtBEntry hab hac site) := by
  apply Subtype.ext
  simp [ambientCEntryCompanionDart]

/-- The ambient exit companion carries the other chirality-selected `c` arm. -/
theorem toRotationSystem_edgeOf_ambientCExitCompanionDart
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    graphData.toRotationSystem.edgeOf
        (ambientCExitCompanionDart data lens hab hac site) =
      retainedEdgeToAmbientEdge data
        (lens.cEdgeAtBExit hab hac site) := by
  apply Subtype.ext
  simp [ambientCExitCompanionDart]

/-- If both `c` arms at a fusion site avoid a cut, then the companion arm
selected at the `b`-entry endpoint avoids it as well. -/
theorem EvenKempeFusionLens.cEdgeAtBEntry_not_cut_of_fusionArms_not_cut
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (cut : G.edgeSet → Prop) (site : lens.FusionSite)
    (harms :
      ¬cut (retainedEdgeToAmbientEdge data (lens.cPreviousVertex site).1) ∧
      ¬cut (retainedEdgeToAmbientEdge data (lens.cNextVertex site).1)) :
    ¬cut (retainedEdgeToAmbientEdge data
      (lens.cEdgeAtBEntry hab hac site)) := by
  by_cases hchirality : lens.fusionChirality hab hac site = true
  · rw [GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData.EvenKempeFusionLens.cEdgeAtBEntry,
      if_pos hchirality]
    exact harms.1
  · rw [GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData.EvenKempeFusionLens.cEdgeAtBEntry,
      if_neg hchirality]
    exact harms.2

/-- The analogous exit companion is cut-free when both local `c` arms are. -/
theorem EvenKempeFusionLens.cEdgeAtBExit_not_cut_of_fusionArms_not_cut
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (cut : G.edgeSet → Prop) (site : lens.FusionSite)
    (harms :
      ¬cut (retainedEdgeToAmbientEdge data (lens.cPreviousVertex site).1) ∧
      ¬cut (retainedEdgeToAmbientEdge data (lens.cNextVertex site).1)) :
    ¬cut (retainedEdgeToAmbientEdge data
      (lens.cEdgeAtBExit hab hac site)) := by
  by_cases hchirality : lens.fusionChirality hab hac site = true
  · rw [GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData.EvenKempeFusionLens.cEdgeAtBExit,
      if_pos hchirality]
    exact harms.2
  · rw [GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData.EvenKempeFusionLens.cEdgeAtBExit,
      if_neg hchirality]
    exact harms.1

/-- On the first lens of a `bc` channel, a positive entry turn exposes a
`c` companion arm, hence gives a crossing of the exact closure cut. -/
theorem EvenKempeFusionLens.bcFirstEntryCrossing_of_fusionEntryTurn_eq_true
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
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support).map Subtype.val)
    (position : Fin lens01.fusionSiteCount)
    (hturn : fusionEntryTurn graphData data lens01 hab
      (lens01.bFusionSiteAt position) = true) :
    CutAvoidingFusionFaceStep graphData data lens01 hab hac
        (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
        (routeOrderedFusionEntryOtherState
          graphData data lens01 hab hac position)
        (routeOrderedFusionExitTurnState
          graphData data lens01 hab hac position) := by
  apply CutAvoidingFusionFaceStep.entryCrossing
  rw [routeOrderedFusionArmDart_entryOtherState,
    fusionEntryOtherDart, if_pos hturn,
    toRotationSystem_edgeOf_ambientCEntryCompanionDart]
  have harms :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.EvenKempeFusionLens.c01FusionArms_not_mem_bcOppositePortClosure_edges
      data lens01 lens23
        hac hbc hcDisjoint path hsupport
        (lens01.bFusionSiteAt position)
  exact EvenKempeFusionLens.cEdgeAtBEntry_not_cut_of_fusionArms_not_cut
    data lens01 hab hac
      (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
      (lens01.bFusionSiteAt position) harms

/-- The positive exit turn on the first lens of a `bc` channel exposes the
other cut-free `c` companion arm. -/
theorem EvenKempeFusionLens.bcFirstExitCrossing_of_fusionExitTurn_eq_true
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
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support).map Subtype.val)
    (position : Fin lens01.fusionSiteCount)
    (hturn : fusionExitTurn graphData data lens01 hab
      (lens01.bFusionSiteAt position) = true) :
    CutAvoidingFusionFaceStep graphData data lens01 hab hac
        (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
        (routeOrderedFusionExitOtherState
          graphData data lens01 hab hac position)
        (routeOrderedFusionEntryTurnState
          graphData data lens01 hab hac position) := by
  apply CutAvoidingFusionFaceStep.exitCrossing
  rw [routeOrderedFusionArmDart_exitOtherState,
    fusionExitOtherDart, if_pos hturn,
    toRotationSystem_edgeOf_ambientCExitCompanionDart]
  have harms :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.EvenKempeFusionLens.c01FusionArms_not_mem_bcOppositePortClosure_edges
      data lens01 lens23
        hac hbc hcDisjoint path hsupport
        (lens01.bFusionSiteAt position)
  exact EvenKempeFusionLens.cEdgeAtBExit_not_cut_of_fusionArms_not_cut
    data lens01 hab hac
      (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
      (lens01.bFusionSiteAt position) harms

/-- On the second lens of a `bc` channel, a negative entry turn exposes the
cut-free previous `b` arm. -/
theorem EvenKempeFusionLens.bcSecondEntryCrossing_of_fusionEntryTurn_eq_false
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
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support).map Subtype.val)
    (position : Fin lens23.fusionSiteCount)
    (hturn : fusionEntryTurn graphData data lens23 hab
      (lens23.bFusionSiteAt position) = false) :
    CutAvoidingFusionFaceStep graphData data lens23 hab hac
        (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
        (routeOrderedFusionEntryOtherState
          graphData data lens23 hab hac position)
        (routeOrderedFusionExitTurnState
          graphData data lens23 hab hac position) := by
  apply CutAvoidingFusionFaceStep.entryCrossing
  have hnot : fusionEntryTurn graphData data lens23 hab
      (lens23.bFusionSiteAt position) ≠ true := by
    intro htrue
    exact Bool.false_ne_true (hturn.symm.trans htrue)
  rw [routeOrderedFusionArmDart_entryOtherState,
    fusionEntryOtherDart, if_neg hnot,
    toRotationSystem_edgeOf_ambientBEntryNeighborDart]
  exact
    (GoertzelV24AdjacentPairInsertion.AdjacentPairData.EvenKempeFusionLens.b23FusionArms_not_mem_bcOppositePortClosure_edges
      data lens01 lens23 hab hbc hbDisjoint path hsupport
        (lens23.bFusionSiteAt position)).1

/-- The negative exit turn on the second lens of a `bc` channel exposes the
cut-free next `b` arm. -/
theorem EvenKempeFusionLens.bcSecondExitCrossing_of_fusionExitTurn_eq_false
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
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support).map Subtype.val)
    (position : Fin lens23.fusionSiteCount)
    (hturn : fusionExitTurn graphData data lens23 hab
      (lens23.bFusionSiteAt position) = false) :
    CutAvoidingFusionFaceStep graphData data lens23 hab hac
        (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
        (routeOrderedFusionExitOtherState
          graphData data lens23 hab hac position)
        (routeOrderedFusionEntryTurnState
          graphData data lens23 hab hac position) := by
  apply CutAvoidingFusionFaceStep.exitCrossing
  have hnot : fusionExitTurn graphData data lens23 hab
      (lens23.bFusionSiteAt position) ≠ true := by
    intro htrue
    exact Bool.false_ne_true (hturn.symm.trans htrue)
  rw [routeOrderedFusionArmDart_exitOtherState,
    fusionExitOtherDart, if_neg hnot,
    toRotationSystem_edgeOf_ambientBExitNeighborDart]
  exact
    (GoertzelV24AdjacentPairInsertion.AdjacentPairData.EvenKempeFusionLens.b23FusionArms_not_mem_bcOppositePortClosure_edges
      data lens01 lens23 hab hbc hbDisjoint path hsupport
        (lens23.bFusionSiteAt position)).2

/-- On the first lens of a `cb` channel, a negative entry turn exposes the
cut-free previous `b` arm. -/
theorem EvenKempeFusionLens.cbFirstEntryCrossing_of_fusionEntryTurn_eq_false
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
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support).map Subtype.val)
    (position : Fin lens01.fusionSiteCount)
    (hturn : fusionEntryTurn graphData data lens01 hab
      (lens01.bFusionSiteAt position) = false) :
    CutAvoidingFusionFaceStep graphData data lens01 hab hac
        (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
        (routeOrderedFusionEntryOtherState
          graphData data lens01 hab hac position)
        (routeOrderedFusionExitTurnState
          graphData data lens01 hab hac position) := by
  apply CutAvoidingFusionFaceStep.entryCrossing
  have hnot : fusionEntryTurn graphData data lens01 hab
      (lens01.bFusionSiteAt position) ≠ true := by
    intro htrue
    exact Bool.false_ne_true (hturn.symm.trans htrue)
  rw [routeOrderedFusionArmDart_entryOtherState,
    fusionEntryOtherDart, if_neg hnot,
    toRotationSystem_edgeOf_ambientBEntryNeighborDart]
  exact
    (GoertzelV24AdjacentPairInsertion.AdjacentPairData.EvenKempeFusionLens.b01FusionArms_not_mem_cbOppositePortClosure_edges
      data lens01 lens23 hab hbc hbDisjoint path hsupport
        (lens01.bFusionSiteAt position)).1

/-- The negative exit turn on the first lens of a `cb` channel exposes the
cut-free next `b` arm. -/
theorem EvenKempeFusionLens.cbFirstExitCrossing_of_fusionExitTurn_eq_false
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
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support).map Subtype.val)
    (position : Fin lens01.fusionSiteCount)
    (hturn : fusionExitTurn graphData data lens01 hab
      (lens01.bFusionSiteAt position) = false) :
    CutAvoidingFusionFaceStep graphData data lens01 hab hac
        (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
        (routeOrderedFusionExitOtherState
          graphData data lens01 hab hac position)
        (routeOrderedFusionEntryTurnState
          graphData data lens01 hab hac position) := by
  apply CutAvoidingFusionFaceStep.exitCrossing
  have hnot : fusionExitTurn graphData data lens01 hab
      (lens01.bFusionSiteAt position) ≠ true := by
    intro htrue
    exact Bool.false_ne_true (hturn.symm.trans htrue)
  rw [routeOrderedFusionArmDart_exitOtherState,
    fusionExitOtherDart, if_neg hnot,
    toRotationSystem_edgeOf_ambientBExitNeighborDart]
  exact
    (GoertzelV24AdjacentPairInsertion.AdjacentPairData.EvenKempeFusionLens.b01FusionArms_not_mem_cbOppositePortClosure_edges
      data lens01 lens23 hab hbc hbDisjoint path hsupport
        (lens01.bFusionSiteAt position)).2

/-- On the second lens of a `cb` channel, a positive entry turn exposes a
cut-free `c` companion arm. -/
theorem EvenKempeFusionLens.cbSecondEntryCrossing_of_fusionEntryTurn_eq_true
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
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support).map Subtype.val)
    (position : Fin lens23.fusionSiteCount)
    (hturn : fusionEntryTurn graphData data lens23 hab
      (lens23.bFusionSiteAt position) = true) :
    CutAvoidingFusionFaceStep graphData data lens23 hab hac
        (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
        (routeOrderedFusionEntryOtherState
          graphData data lens23 hab hac position)
        (routeOrderedFusionExitTurnState
          graphData data lens23 hab hac position) := by
  apply CutAvoidingFusionFaceStep.entryCrossing
  rw [routeOrderedFusionArmDart_entryOtherState,
    fusionEntryOtherDart, if_pos hturn,
    toRotationSystem_edgeOf_ambientCEntryCompanionDart]
  have harms :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.EvenKempeFusionLens.c23FusionArms_not_mem_cbOppositePortClosure_edges
      data lens01 lens23
        hac hbc hcDisjoint path hsupport
        (lens23.bFusionSiteAt position)
  exact EvenKempeFusionLens.cEdgeAtBEntry_not_cut_of_fusionArms_not_cut
    data lens23 hab hac
      (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
      (lens23.bFusionSiteAt position) harms

/-- The positive exit turn on the second lens of a `cb` channel exposes the
other cut-free `c` companion arm. -/
theorem EvenKempeFusionLens.cbSecondExitCrossing_of_fusionExitTurn_eq_true
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
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support).map Subtype.val)
    (position : Fin lens23.fusionSiteCount)
    (hturn : fusionExitTurn graphData data lens23 hab
      (lens23.bFusionSiteAt position) = true) :
    CutAvoidingFusionFaceStep graphData data lens23 hab hac
        (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
        (routeOrderedFusionExitOtherState
          graphData data lens23 hab hac position)
        (routeOrderedFusionEntryTurnState
          graphData data lens23 hab hac position) := by
  apply CutAvoidingFusionFaceStep.exitCrossing
  rw [routeOrderedFusionArmDart_exitOtherState,
    fusionExitOtherDart, if_pos hturn,
    toRotationSystem_edgeOf_ambientCExitCompanionDart]
  have harms :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.EvenKempeFusionLens.c23FusionArms_not_mem_cbOppositePortClosure_edges
      data lens01 lens23
        hac hbc hcDisjoint path hsupport
        (lens23.bFusionSiteAt position)
  exact EvenKempeFusionLens.cEdgeAtBExit_not_cut_of_fusionArms_not_cut
    data lens23 hab hac
      (fun edge => edge.1 ∈ (data.oppositePortClosure path).edges)
      (lens23.bFusionSiteAt position) harms

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
