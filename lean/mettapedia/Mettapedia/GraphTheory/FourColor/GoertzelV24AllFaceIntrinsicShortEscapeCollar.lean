import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceRemoteCrossingPortAvoidance

/-! Reciprocal collar retention and local color classes at an intrinsic
singleton-star reentry. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An ambient edge survives an adjacent-pair deletion exactly when all of
its endpoints survive the vertex deletion. -/
theorem isRetainedAmbientEdge_iff_endpoints_mem_retainedVertexSet
    (data : AdjacentPairData G) (edge : G.edgeSet) :
    IsRetainedAmbientEdge data edge ↔
      ∀ vertex ∈ (edge.1 : Sym2 V),
        vertex ∈ retainedVertexSet data.firstVertex data.secondVertex := by
  constructor
  · exact endpoints_mem_retainedVertexSet data edge
  · intro hendpoints
    apply isRetainedAmbientEdge_of_ne data edge
    · intro hedge
      have hfirst := hendpoints data.firstVertex (by
        rw [hedge, centralEdgeValue]
        exact Sym2.mem_mk_left _ _)
      exact hfirst.1 rfl
    · intro hedge
      have hfirst := hendpoints data.firstVertex (by
        rw [hedge, boundaryEdgeValue_zero]
        exact Sym2.mem_mk_left _ _)
      exact hfirst.1 rfl
    · intro hedge
      have hfirst := hendpoints data.firstVertex (by
        rw [hedge, boundaryEdgeValue_one]
        exact Sym2.mem_mk_left _ _)
      exact hfirst.1 rfl
    · intro hedge
      have hsecond := hendpoints data.secondVertex (by
        rw [hedge, boundaryEdgeValue_two]
        exact Sym2.mem_mk_left _ _)
      exact hsecond.2 rfl
    · intro hedge
      have hsecond := hendpoints data.secondVertex (by
        rw [hedge, boundaryEdgeValue_three]
        exact Sym2.mem_mk_left _ _)
      exact hsecond.2 rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The central edge and every boundary edge of an adjacent-pair collar
are incident in the line graph. -/
theorem centralEdge_adj_boundaryEdge
    (data : AdjacentPairData G) (port : Fin 4) :
    G.lineGraph.Adj (centralEdge data) (boundaryEdge data port) := by
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  refine ⟨?_, boundaryDeletedVertex data port, ?_, ?_⟩
  · intro hedge
    exact centralEdgeValue_ne_boundaryEdgeValue data port
      (congrArg Subtype.val hedge)
  · fin_cases port <;>
      simp [centralEdge, centralEdgeValue, boundaryDeletedVertex]
  · rw [boundaryEdge_val, boundaryEdgeValue_eq]
    exact Sym2.mem_mk_left _ _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The two boundary edges on the first restored vertex are incident. -/
theorem boundaryEdge_zero_adj_one (data : AdjacentPairData G) :
    G.lineGraph.Adj (boundaryEdge data 0) (boundaryEdge data 1) := by
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  refine ⟨?_, data.firstVertex, ?_, ?_⟩
  · intro hedge
    apply boundaryEdgeValue_ne data (first := 0) (second := 1) (by decide)
    exact congrArg Subtype.val hedge
  · rw [boundaryEdge_val, boundaryEdgeValue_zero]
    exact Sym2.mem_mk_left _ _
  · rw [boundaryEdge_val, boundaryEdgeValue_one]
    exact Sym2.mem_mk_left _ _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The two boundary edges on the second restored vertex are incident. -/
theorem boundaryEdge_two_adj_three (data : AdjacentPairData G) :
    G.lineGraph.Adj (boundaryEdge data 2) (boundaryEdge data 3) := by
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  refine ⟨?_, data.secondVertex, ?_, ?_⟩
  · intro hedge
    apply boundaryEdgeValue_ne data (first := 2) (second := 3) (by decide)
    exact congrArg Subtype.val hedge
  · rw [boundaryEdge_val, boundaryEdgeValue_two]
    exact Sym2.mem_mk_left _ _
  · rw [boundaryEdge_val, boundaryEdgeValue_three]
    exact Sym2.mem_mk_left _ _

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- An intrinsic singleton target together with an actual target escape
coloring and the reciprocal retention of the entire source collar. -/
structure IntrinsicShortTargetEscapeCollar
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (targetEdge : G.edgeSet) where
  targetBase : AdjacentPairData G
  targetNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal targetBase
  targetOutcome : targetNormal.TerminalFusionOutcome ∨
    targetNormal.CertifiedRebasePumpingLaunch
  targetEscape : targetNormal.KempeOrbitAdjacentEscape
  targetCentral_eq :
    centralEdge
        (RecoveredRotationOrderedData graphData minimal targetBase) =
      targetEdge
  targetRetainedBySource :
    IsRetainedAmbientEdge
      (RecoveredRotationOrderedData graphData minimal baseData) targetEdge
  targetCrossing : targetEdge ∈ cycle.crossingEdges
  singletonProfile : Nonempty cycle.SingletonPrimalCutProfile
  sourceCentralRetainedByTarget :
    IsRetainedAmbientEdge
      (RecoveredRotationOrderedData graphData minimal targetBase)
      (centralEdge
        (RecoveredRotationOrderedData graphData minimal baseData))
  sourceBoundaryRetainedByTarget : ∀ port : Fin 4,
    IsRetainedAmbientEdge
      (RecoveredRotationOrderedData graphData minimal targetBase)
      (boundaryEdge
        (RecoveredRotationOrderedData graphData minimal baseData) port)

namespace IntrinsicShortTargetEscapeCollar

abbrev sourceData
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (_collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :=
  RecoveredRotationOrderedData graphData minimal baseData

abbrev targetData
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :=
  RecoveredRotationOrderedData graphData minimal collar.targetBase

/-- The source central edge as an edge of the target-pair deletion. -/
def sourceCentralInTarget
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).edgeSet :=
  ambientEdgeToRetainedEdge collar.targetData
    (centralEdge collar.sourceData) collar.sourceCentralRetainedByTarget

/-- A source boundary edge as an edge of the target-pair deletion. -/
def sourceBoundaryInTarget
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (port : Fin 4) :
    (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).edgeSet :=
  ambientEdgeToRetainedEdge collar.targetData
    (boundaryEdge collar.sourceData port)
      (collar.sourceBoundaryRetainedByTarget port)

/-- The four source-collar colors read in the target escape coloring. -/
def sourceBoundaryWord
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    SquareBoundaryWord :=
  fun port => collar.targetEscape.coloring
    (collar.sourceBoundaryInTarget port)

/-- The source central-edge color read in the target escape coloring. -/
def sourceBridgeColor
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) : Color :=
  collar.targetEscape.coloring collar.sourceCentralInTarget

theorem sourceCentralInTarget_adj_sourceBoundaryInTarget
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (port : Fin 4) :
    (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).lineGraph.Adj
        collar.sourceCentralInTarget
        (collar.sourceBoundaryInTarget port) := by
  exact ambientEdgeToRetainedEdge_adj collar.targetData
    (centralEdge collar.sourceData) (boundaryEdge collar.sourceData port)
      collar.sourceCentralRetainedByTarget
        (collar.sourceBoundaryRetainedByTarget port)
          (centralEdge_adj_boundaryEdge collar.sourceData port)

theorem sourceBoundaryInTarget_zero_adj_one
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).lineGraph.Adj
        (collar.sourceBoundaryInTarget 0)
        (collar.sourceBoundaryInTarget 1) := by
  exact ambientEdgeToRetainedEdge_adj collar.targetData
    (boundaryEdge collar.sourceData 0) (boundaryEdge collar.sourceData 1)
      (collar.sourceBoundaryRetainedByTarget 0)
        (collar.sourceBoundaryRetainedByTarget 1)
          (boundaryEdge_zero_adj_one collar.sourceData)

theorem sourceBoundaryInTarget_two_adj_three
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).lineGraph.Adj
        (collar.sourceBoundaryInTarget 2)
        (collar.sourceBoundaryInTarget 3) := by
  exact ambientEdgeToRetainedEdge_adj collar.targetData
    (boundaryEdge collar.sourceData 2) (boundaryEdge collar.sourceData 3)
      (collar.sourceBoundaryRetainedByTarget 2)
        (collar.sourceBoundaryRetainedByTarget 3)
          (boundaryEdge_two_adj_three collar.sourceData)

/-- The target escape coloring gives a literal accepted local extension
across the source adjacent-pair collar. -/
theorem sourceBridgeExtension
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    IsTwoVertexBridgeExtension collar.sourceBoundaryWord
      collar.sourceBridgeColor := by
  constructor
  · refine ⟨collar.targetEscape.isTait _, collar.targetEscape.isTait _,
      collar.targetEscape.isTait _, ?_, ?_, ?_⟩
    · exact collar.targetEscape.coloring.valid
        collar.sourceBoundaryInTarget_zero_adj_one
    · exact (collar.targetEscape.coloring.valid
        (collar.sourceCentralInTarget_adj_sourceBoundaryInTarget 0)).symm
    · exact (collar.targetEscape.coloring.valid
        (collar.sourceCentralInTarget_adj_sourceBoundaryInTarget 1)).symm
  · refine ⟨collar.targetEscape.isTait _, collar.targetEscape.isTait _,
      collar.targetEscape.isTait _, ?_, ?_, ?_⟩
    · exact collar.targetEscape.coloring.valid
        collar.sourceBoundaryInTarget_two_adj_three
    · exact (collar.targetEscape.coloring.valid
        (collar.sourceCentralInTarget_adj_sourceBoundaryInTarget 2)).symm
    · exact (collar.targetEscape.coloring.valid
        (collar.sourceCentralInTarget_adj_sourceBoundaryInTarget 3)).symm

/-- Consequently the source collar is seen from the target escape in one
of the two locally extendable four-port classes. -/
theorem sourceBoundaryWord_extendableClass
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.sourceBoundaryWord.Nonzero ∧
      (collar.sourceBoundaryWord.Adjacent12_30 ∨
        collar.sourceBoundaryWord.OppositePairs) := by
  have hmem : collar.sourceBridgeColor ∈
      twoVertexBridgeExtensions collar.sourceBoundaryWord :=
    mem_twoVertexBridgeExtensions_iff.mpr collar.sourceBridgeExtension
  have hpositive : 0 <
      (twoVertexBridgeExtensions collar.sourceBoundaryWord).card :=
    Finset.card_pos.mpr ⟨collar.sourceBridgeColor, hmem⟩
  rw [twoVertexBridgeExtension_card] at hpositive
  by_cases hclass : collar.sourceBoundaryWord.Nonzero ∧
      (collar.sourceBoundaryWord.Adjacent12_30 ∨
        collar.sourceBoundaryWord.OppositePairs)
  · exact hclass
  · simp [hclass] at hpositive

/-- In particular the target escape cannot present the source collar in
the source escape's canonical nonextendable `01|23` class. -/
theorem sourceBoundaryWord_not_adjacent01_23
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    ¬ collar.sourceBoundaryWord.Adjacent01_23 := by
  intro hadjacent
  exact collar.sourceBridgeExtension.1.2.2.2.1 hadjacent.1

end IntrinsicShortTargetEscapeCollar

/-- Every intrinsic singleton target exposes both escape colorings' local
collars inside the opposite adjacent-pair deletion. -/
theorem IntrinsicShortFusionTarget.nonempty_targetEscapeCollar
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (target : cycle.IntrinsicShortFusionTarget targetEdge) :
    Nonempty (cycle.IntrinsicShortTargetEscapeCollar targetEdge) := by
  have htargetRetained := target.isRetainedAmbientEdge
  rcases target with
    ⟨first, second, _hne, _hadj, htargetValue, _hcentral, _hboundary,
      hkempe, hsingleton, hcrossing⟩
  rcases hkempe with
    ⟨targetBase, htargetFirstBase, htargetSecondBase, targetNormal,
      htargetOutcome, ⟨targetEscape⟩⟩
  let sourceData := RecoveredRotationOrderedData graphData minimal baseData
  let targetData := RecoveredRotationOrderedData graphData minimal targetBase
  have htargetFirst : targetData.firstVertex = first := by
    simpa [targetData, RecoveredRotationOrderedData, rotationOrderedData]
      using htargetFirstBase
  have htargetSecond : targetData.secondVertex = second := by
    simpa [targetData, RecoveredRotationOrderedData, rotationOrderedData]
      using htargetSecondBase
  have hfirstSourceRetained : first ∈
      retainedVertexSet sourceData.firstVertex sourceData.secondVertex := by
    apply endpoints_mem_retainedVertexSet sourceData targetEdge
      htargetRetained first
    rw [htargetValue]
    exact Sym2.mem_mk_left _ _
  have hsecondSourceRetained : second ∈
      retainedVertexSet sourceData.firstVertex sourceData.secondVertex := by
    apply endpoints_mem_retainedVertexSet sourceData targetEdge
      htargetRetained second
    rw [htargetValue]
    exact Sym2.mem_mk_right _ _
  have hfirstPort : ∀ port : Fin 4,
      first ≠ sourceData.portVertex port := by
    intro port
    apply cycle.crossingEdge_endpoint_ne_portVertex hcrossing
    rw [htargetValue]
    exact Sym2.mem_mk_left _ _
  have hsecondPort : ∀ port : Fin 4,
      second ≠ sourceData.portVertex port := by
    intro port
    apply cycle.crossingEdge_endpoint_ne_portVertex hcrossing
    rw [htargetValue]
    exact Sym2.mem_mk_right _ _
  have hsourceFirstTargetRetained : sourceData.firstVertex ∈
      retainedVertexSet targetData.firstVertex targetData.secondVertex := by
    rw [htargetFirst, htargetSecond]
    exact ⟨hfirstSourceRetained.1.symm, hsecondSourceRetained.1.symm⟩
  have hsourceSecondTargetRetained : sourceData.secondVertex ∈
      retainedVertexSet targetData.firstVertex targetData.secondVertex := by
    rw [htargetFirst, htargetSecond]
    exact ⟨hfirstSourceRetained.2.symm, hsecondSourceRetained.2.symm⟩
  have hsourcePortTargetRetained : ∀ port : Fin 4,
      sourceData.portVertex port ∈
        retainedVertexSet targetData.firstVertex targetData.secondVertex := by
    intro port
    rw [htargetFirst, htargetSecond]
    exact ⟨(hfirstPort port).symm, (hsecondPort port).symm⟩
  have hsourceCentralRetained : IsRetainedAmbientEdge targetData
      (centralEdge sourceData) := by
    apply (isRetainedAmbientEdge_iff_endpoints_mem_retainedVertexSet
      targetData (centralEdge sourceData)).2
    intro vertex hvertex
    rw [centralEdge_val, centralEdgeValue] at hvertex
    rcases (Sym2.mem_iff.mp hvertex) with rfl | rfl
    · exact hsourceFirstTargetRetained
    · exact hsourceSecondTargetRetained
  have hsourceBoundaryRetained : ∀ port : Fin 4,
      IsRetainedAmbientEdge targetData (boundaryEdge sourceData port) := by
    intro port
    apply (isRetainedAmbientEdge_iff_endpoints_mem_retainedVertexSet
      targetData (boundaryEdge sourceData port)).2
    intro vertex hvertex
    rw [boundaryEdge_val, boundaryEdgeValue_eq] at hvertex
    rcases (Sym2.mem_iff.mp hvertex) with hdeleted | hport
    · subst vertex
      fin_cases port
      · simpa [boundaryDeletedVertex] using hsourceFirstTargetRetained
      · simpa [boundaryDeletedVertex] using hsourceFirstTargetRetained
      · simpa [boundaryDeletedVertex] using hsourceSecondTargetRetained
      · simpa [boundaryDeletedVertex] using hsourceSecondTargetRetained
    · subst vertex
      exact hsourcePortTargetRetained port
  have htargetCentral : centralEdge targetData = targetEdge := by
    apply Subtype.ext
    rw [centralEdge_val, centralEdgeValue, htargetFirst, htargetSecond]
    exact htargetValue.symm
  exact ⟨{
    targetBase := targetBase
    targetNormal := targetNormal
    targetOutcome := htargetOutcome
    targetEscape := targetEscape
    targetCentral_eq := htargetCentral
    targetRetainedBySource := htargetRetained
    targetCrossing := hcrossing
    singletonProfile := hsingleton
    sourceCentralRetainedByTarget := hsourceCentralRetained
    sourceBoundaryRetainedByTarget := hsourceBoundaryRetained }⟩

/-- For any source normal, the singleton collar exposes the exact two
boundary sectors that a cross-base argument must connect: the source escape
is canonical nonextendable `01|23`, while the target escape makes the same
source collar locally extendable.  No reachability between them is asserted. -/
theorem IntrinsicShortFusionTarget.exists_sourceEscape_targetExtendableClass
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData)
    (target : cycle.IntrinsicShortFusionTarget targetEdge) :
    ∃ (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
        (targetCollar : cycle.IntrinsicShortTargetEscapeCollar targetEdge),
      SquareBoundaryWord.Adjacent01_23
          ((RecoveredRotationOrderedData graphData minimal
            baseData).degreeTwoBoundaryData.colorWord
              sourceEscape.coloring) ∧
        targetCollar.sourceBoundaryWord.Nonzero ∧
        (targetCollar.sourceBoundaryWord.Adjacent12_30 ∨
          targetCollar.sourceBoundaryWord.OppositePairs) := by
  rcases sourceNormal.nonempty_kempeOrbitAdjacentEscape with ⟨sourceEscape⟩
  rcases target.nonempty_targetEscapeCollar with ⟨targetCollar⟩
  exact ⟨sourceEscape, targetCollar,
    sourceEscape.boundary_adjacent01_23,
    targetCollar.sourceBoundaryWord_extendableClass⟩

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
