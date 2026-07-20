import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionKempeBoundaryAction

/-! First-hit terminal normalization of the singleton companion trail. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

/-- Every simple path from one terminal to another has a positive prefix
ending at its first later terminal.  No internal vertex of that prefix is a
terminal. -/
theorem exists_firstTerminalPrefix
    {W : Type*} [DecidableEq W] {H : SimpleGraph W}
    {start finish : W} (terminals : Finset W)
    (path : H.Walk start finish) (hfinish : finish ∈ terminals)
    (hfinishNe : finish ≠ start) (hpath : path.IsPath) :
    ∃ (terminal : W) (initialPath : H.Walk start terminal),
      terminal ∈ terminals ∧ terminal ≠ start ∧
        initialPath.IsPath ∧ 0 < initialPath.length ∧
        (∀ position : Nat, 0 < position → position < initialPath.length →
          initialPath.getVert position ∉ terminals) ∧
        initialPath.IsSubwalk path := by
  classical
  let IsLaterTerminal : Nat → Prop := fun position =>
    0 < position ∧ position ≤ path.length ∧
      path.getVert position ∈ terminals
  have hpathPositive : 0 < path.length := by
    by_contra hnot
    have hzero : path.length = 0 := Nat.eq_zero_of_not_pos hnot
    exact hfinishNe (path.eq_of_length_eq_zero hzero).symm
  have hexists : ∃ position, IsLaterTerminal position := by
    refine ⟨path.length, hpathPositive, le_rfl, ?_⟩
    simpa only [path.getVert_length] using hfinish
  let firstPosition := Nat.find hexists
  have hfirst := Nat.find_spec hexists
  have hfirstSpec : IsLaterTerminal firstPosition := by
    simpa only [firstPosition] using hfirst
  let initialPath : H.Walk start (path.getVert firstPosition) :=
    path.take firstPosition
  have hprefixLength : initialPath.length = firstPosition := by
    simp only [initialPath, path.take_length,
      Nat.min_eq_left hfirstSpec.2.1]
  have hprefixPositive : 0 < initialPath.length := by
    rw [hprefixLength]
    exact hfirstSpec.1
  have hprefixPath : initialPath.IsPath := hpath.take firstPosition
  have hterminalNe : path.getVert firstPosition ≠ start := by
    intro heq
    have hnil : initialPath.Nil :=
      hprefixPath.nil_iff_eq.mpr heq.symm
    exact (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hprefixPositive) hnil
  refine ⟨path.getVert firstPosition, initialPath, hfirstSpec.2.2,
    hterminalNe, hprefixPath, hprefixPositive, ?_,
    path.isSubwalk_take firstPosition⟩
  intro position hpositionPositive hpositionLength hterminal
  have hpositionFirst : position < firstPosition := by
    simpa only [hprefixLength] using hpositionLength
  have hprefixGetVert : initialPath.getVert position = path.getVert position := by
    simp only [initialPath, path.take_getVert,
      Nat.min_eq_right (Nat.le_of_lt hpositionFirst)]
  have hlater : IsLaterTerminal position := by
    refine ⟨hpositionPositive,
      le_trans (Nat.le_of_lt hpositionFirst) hfirstSpec.2.1, ?_⟩
    simpa only [hprefixGetVert] using hterminal
  have hminimal : firstPosition ≤ position := Nat.find_min' hexists hlater
  omega

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}

/-- A singleton companion transfer truncated at the first named common-core
terminal after its singleton-side start. -/
structure FirstHitSingletonCompanionTransferPath where
  transfer : SingletonCompanionTransferPath collar sourceEscape
  internal_not_commonPort :
    ∀ position : Nat, 0 < position → position < transfer.path.length →
      transfer.path.getVert position ∉ collar.commonPortVertexFinset

/-- Every intrinsic singleton collar admits a first-hit companion transfer. -/
theorem nonempty_firstHitSingletonCompanionTransferPath
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    Nonempty (FirstHitSingletonCompanionTransferPath
      (collar := collar) (sourceEscape := sourceEscape)) := by
  classical
  rcases collar.nonempty_singletonCompanionTransferPath sourceEscape with
    ⟨raw⟩
  have hfinishNe : raw.finish.1 ≠
      collar.targetPortInCommonCore raw.targetPort := by
    intro heq
    apply raw.finish_ne_start
    apply Subtype.ext
    simpa only [targetPortCommonTerminal] using heq
  rcases exists_firstTerminalPrefix collar.commonPortVertexFinset raw.path
      raw.finish.2 hfinishNe raw.path_isPath with
    ⟨finish, initialPath, hfinish, hfinishNe, hprefixPath,
      hprefixPositive, hinterior, hsubwalk⟩
  let truncated : SingletonCompanionTransferPath collar sourceEscape := {
    coordinate := raw.coordinate
    targetPort := raw.targetPort
    finish := ⟨finish, hfinish⟩
    path := initialPath
    singletonInside := raw.singletonInside
    finish_ne_start := by
      intro heq
      exact hfinishNe (congrArg Subtype.val heq)
    path_isPath := hprefixPath
    path_positive := hprefixPositive
    support := by
      intro edge hedge
      apply raw.support edge
      have hedgeValue : edge.1 ∈ initialPath.edges := by
        rw [← initialPath.edgeSubtypeSupport_map_val]
        exact List.mem_map.mpr ⟨edge, hedge, rfl⟩
      have hedgeRawValue : edge.1 ∈ raw.path.edges :=
        hsubwalk.edges_subset hedgeValue
      rw [← raw.path.edgeSubtypeSupport_map_val] at hedgeRawValue
      rcases List.mem_map.mp hedgeRawValue with
        ⟨rawEdge, hrawEdge, hvalue⟩
      have hedgeEq : rawEdge = edge := Subtype.ext hvalue
      simpa only [hedgeEq] using hrawEdge }
  exact ⟨{
    transfer := truncated
    internal_not_commonPort := by
      intro position hpositive hlength
      exact hinterior position hpositive hlength }⟩

namespace FirstHitSingletonCompanionTransferPath

variable (firstHit : FirstHitSingletonCompanionTransferPath
  (collar := collar) (sourceEscape := sourceEscape))

/-- The common vertex of a resolved consecutive support pair is the
corresponding strictly internal primal-path vertex. -/
theorem resolvedChange_commonVertex_eq_getVert_and_internal
    (change : firstHit.transfer.ResolvedCompanionChange) :
    SimpleGraph.lineGraphCommonVertex change.firstSecond =
        firstHit.transfer.path.getVert (change.before.length + 1) ∧
      0 < change.before.length + 1 ∧
      change.before.length + 1 < firstHit.transfer.path.length := by
  classical
  have hlength := congrArg List.length change.word_eq
  rw [firstHit.transfer.supportEdgeWord_length] at hlength
  simp only [List.length_append, List.length_cons] at hlength
  have hsupportFactor :
      firstHit.transfer.path.edgeSubtypeSupport =
        change.before.unattach ++
          change.first.1 :: change.second.1 :: change.after.unattach := by
    have hword := congrArg List.unattach change.word_eq
    simpa only [SingletonCompanionTransferPath.supportEdgeWord,
      List.unattach_attach, List.unattach_append,
      List.unattach_cons] using hword
  let lineWalk := firstHit.transfer.path.lineGraphWalkOfTrail
    firstHit.transfer.path_positive firstHit.transfer.path_isPath.isTrail
  have hlineLength : lineWalk.length =
      firstHit.transfer.path.length - 1 := by
    exact firstHit.transfer.path.lineGraphWalkOfTrail_length
      firstHit.transfer.path_positive firstHit.transfer.path_isPath.isTrail
  have hlineSupport : lineWalk.support =
      change.before.unattach ++
        change.first.1 :: change.second.1 :: change.after.unattach := by
    calc
      lineWalk.support = firstHit.transfer.path.edgeSubtypeSupport := by
        dsimp only [lineWalk]
        exact firstHit.transfer.path.lineGraphWalkOfTrail_support
          firstHit.transfer.path_positive
          firstHit.transfer.path_isPath.isTrail
      _ = change.before.unattach ++
          change.first.1 :: change.second.1 :: change.after.unattach :=
        hsupportFactor
  have hposition : change.before.length < lineWalk.length := by
    rw [hlineLength]
    omega
  let position : Fin lineWalk.length :=
    ⟨change.before.length, hposition⟩
  have hfirstValue : lineWalk.getVert position.val = change.first.1 := by
    rw [lineWalk.getVert_eq_support_getElem (by omega)]
    have hoption : lineWalk.support[position.val]? = some change.first.1 := by
      rw [hlineSupport]
      change (change.before.unattach ++ change.first.1 ::
        change.second.1 :: change.after.unattach)[change.before.length]? =
          some change.first.1
      rw [List.getElem?_append, List.length_unattach]
      rw [if_neg (Nat.lt_irrefl _)]
      rw [Nat.sub_self, List.getElem?_cons_zero]
    rcases List.getElem?_eq_some_iff.mp hoption with ⟨_hindex, heq⟩
    exact heq
  have hsecondValue :
      lineWalk.getVert (position.val + 1) = change.second.1 := by
    rw [lineWalk.getVert_eq_support_getElem (by omega)]
    have hoption : lineWalk.support[position.val + 1]? =
        some change.second.1 := by
      rw [hlineSupport]
      change (change.before.unattach ++ change.first.1 ::
        change.second.1 :: change.after.unattach)[change.before.length + 1]? =
          some change.second.1
      rw [List.getElem?_append, List.length_unattach]
      rw [if_neg (by omega)]
      have hsub : change.before.length + 1 - change.before.length = 1 := by
        omega
      rw [hsub, List.getElem?_cons_succ, List.getElem?_cons_zero]
    rcases List.getElem?_eq_some_iff.mp hoption with ⟨_hindex, heq⟩
    exact heq
  have hjunction :
      SimpleGraph.lineGraphCommonVertex change.firstSecond =
        lineWalk.lineGraphJunctionAt position := by
    apply SimpleGraph.lineGraphCommonVertex_unique
      (lineWalk.adj_getVert_succ position.isLt)
    · rw [hfirstValue]
      exact SimpleGraph.lineGraphCommonVertex_mem_left change.firstSecond
    · rw [hsecondValue]
      exact SimpleGraph.lineGraphCommonVertex_mem_right change.firstSecond
  refine ⟨hjunction.trans ?_, by omega, by omega⟩
  exact firstHit.transfer.path.lineGraphWalkOfTrail_lineGraphJunctionAt_eq_getVert
    firstHit.transfer.path_positive firstHit.transfer.path_isPath.isTrail
      position

/-- Hence a resolved companion change on a first-hit path cannot occur at
any named source or target port. -/
theorem resolvedChange_commonVertex_not_commonPort
    (change : firstHit.transfer.ResolvedCompanionChange) :
    SimpleGraph.lineGraphCommonVertex change.firstSecond ∉
      collar.commonPortVertexFinset := by
  rcases firstHit.resolvedChange_commonVertex_eq_getVert_and_internal
      change with ⟨hvertex, hpositive, hinternal⟩
  rw [hvertex]
  exact firstHit.internal_not_commonPort _ hpositive hinternal

/-- Every resolved change on a first-hit path therefore has a genuine
transverse third edge carrying the distinguished discrepancy. -/
theorem resolvedChange_exists_transverseEmission
    (change : firstHit.transfer.ResolvedCompanionChange) :
    ∃ thirdEdge : collar.commonCore.edgeSet,
      collar.commonCore.lineGraph.Adj change.first.1 thirdEdge ∧
        collar.commonCore.lineGraph.Adj change.second.1 thirdEdge ∧
        collar.sourceCommonColoring sourceEscape thirdEdge +
            collar.targetCommonColoring thirdEdge =
          crossFaceZeroColor firstHit.transfer.coordinate := by
  have hnotPort := firstHit.resolvedChange_commonVertex_not_commonPort change
  rcases change.location with hsource | htarget | htransverse
  · rcases hsource with ⟨sourcePort, hsource⟩
    exact False.elim (hnotPort (by
      rw [hsource, commonPortVertexFinset]
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨sourcePort, Finset.mem_univ _, rfl⟩)))
  · rcases htarget with ⟨targetPort, htarget⟩
    exact False.elim (hnotPort (by
      rw [htarget, commonPortVertexFinset]
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨targetPort, Finset.mem_univ _, rfl⟩)))
  · exact htransverse

/-- A changed first-hit companion trail, retaining its exact word location
and the forced transverse third edge. -/
structure TransverseCompanionChange where
  resolved : firstHit.transfer.ResolvedCompanionChange
  thirdEdge : collar.commonCore.edgeSet
  firstThird : collar.commonCore.lineGraph.Adj resolved.first.1 thirdEdge
  secondThird : collar.commonCore.lineGraph.Adj resolved.second.1 thirdEdge
  discrepancy :
    collar.sourceCommonColoring sourceEscape thirdEdge +
        collar.targetCommonColoring thirdEdge =
      crossFaceZeroColor firstHit.transfer.coordinate

/-- The first-hit normalization removes both boundary-change alternatives:
the singleton trail produces a fusion connector, an adjacent orbit reentry,
or a certified transverse cross-channel. -/
theorem allEqualFusionConnector_or_adjacentReentry_or_transverseChange :
    Nonempty firstHit.transfer.AllEqualSourceFusionConnector ∨
      Nonempty firstHit.transfer.AdjacentSourceOrbitReentry ∨
      Nonempty firstHit.TransverseCompanionChange := by
  rcases firstHit.transfer.allEqualFusionConnector_or_adjacentReentry_or_resolvedChange with
    hallEqual | hadjacent | hresolved
  · exact Or.inl hallEqual
  · exact Or.inr (Or.inl hadjacent)
  · apply Or.inr
    apply Or.inr
    rcases hresolved with ⟨resolved⟩
    rcases firstHit.resolvedChange_exists_transverseEmission resolved with
      ⟨thirdEdge, hfirst, hsecond, hdiscrepancy⟩
    exact ⟨{
      resolved := resolved
      thirdEdge := thirdEdge
      firstThird := hfirst
      secondThird := hsecond
      discrepancy := hdiscrepancy }⟩

end FirstHitSingletonCompanionTransferPath

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
