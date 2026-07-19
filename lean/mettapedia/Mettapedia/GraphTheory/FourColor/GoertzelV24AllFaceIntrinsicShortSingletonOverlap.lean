import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortOverlapAlgebra
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceSize

/-! The two-port overlap geometry forced by the singleton side of an
intrinsic-short reentry. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24MinimalFaceSize
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphTaitBridge
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

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- The support of a singleton primal-cut component contains only one
ambient vertex. -/
theorem SingletonPrimalCutProfile.vertex_eq_of_mem_component
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    (profile : cycle.SingletonPrimalCutProfile)
    {first second : V}
    (hfirst : first ∈ profile.component.supp)
    (hsecond : second ∈ profile.component.supp) :
    first = second := by
  have hsubsingleton :
      Subsingleton {vertex : V // vertex ∈ profile.component.supp} :=
    (Nat.card_eq_one_iff_unique.mp profile.component_card_eq_one).1
  exact congrArg Subtype.val
    (hsubsingleton.elim ⟨first, hfirst⟩ ⟨second, hsecond⟩)

namespace IntrinsicShortTargetEscapeCollar

/-- The singleton profile retained by the escape collar. -/
noncomputable def singletonCutProfile
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    cycle.SingletonPrimalCutProfile :=
  Classical.choice collar.singletonProfile

/-- The target central edge crosses the exact singleton-component side. -/
theorem targetEdge_mem_singletonBoundary
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    targetEdge ∈ crossingEdgeFinset G
      (fun vertex => vertex ∈ collar.singletonCutProfile.component.supp) := by
  rw [collar.singletonCutProfile.component_boundary_eq]
  exact collar.targetCrossing

/-- Exactly one endpoint of the target central edge lies in the singleton
component. -/
theorem targetEndpoint_singletonSide_xor
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    (collar.targetData.firstVertex ∈
          collar.singletonCutProfile.component.supp ∧
        collar.targetData.secondVertex ∉
          collar.singletonCutProfile.component.supp) ∨
      (collar.targetData.firstVertex ∉
          collar.singletonCutProfile.component.supp ∧
        collar.targetData.secondVertex ∈
          collar.singletonCutProfile.component.supp) := by
  have hcross : EdgeCrossesVertexSide G
      (fun vertex => vertex ∈ collar.singletonCutProfile.component.supp)
      targetEdge :=
    (mem_crossingEdgeFinset_iff _ _).1
      collar.targetEdge_mem_singletonBoundary
  have hvalue := congrArg Subtype.val collar.targetCentral_eq
  rw [centralEdge_val, centralEdgeValue] at hvalue
  have hnotIff := not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
    (side := fun vertex =>
      vertex ∈ collar.singletonCutProfile.component.supp)
    hvalue.symm hcross
  by_cases hfirst : collar.targetData.firstVertex ∈
      collar.singletonCutProfile.component.supp <;>
    by_cases hsecond : collar.targetData.secondVertex ∈
      collar.singletonCutProfile.component.supp <;>
    simp_all

/-- A boundary edge based at the singleton endpoint is itself one of the
three remote crossing edges. -/
theorem targetBoundary_mem_crossingEdges_of_deletedVertex_mem_singleton
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4)
    (hinside : boundaryDeletedVertex collar.targetData targetPort ∈
      collar.singletonCutProfile.component.supp) :
    boundaryEdge collar.targetData targetPort ∈ cycle.crossingEdges := by
  have houtside : collar.targetData.portVertex targetPort ∉
      collar.singletonCutProfile.component.supp := by
    intro hport
    exact boundaryDeletedVertex_ne_portVertex collar.targetData
      targetPort targetPort
        (collar.singletonCutProfile.vertex_eq_of_mem_component
          hinside hport)
  rw [← collar.singletonCutProfile.component_boundary_eq,
    mem_crossingEdgeFinset_iff]
  refine ⟨boundaryDeletedVertex collar.targetData targetPort,
    collar.targetData.portVertex targetPort, ?_, ?_, hinside, houtside⟩
  · rw [boundaryEdge_val, boundaryEdgeValue_eq]
    exact Sym2.mem_mk_left _ _
  · rw [boundaryEdge_val, boundaryEdgeValue_eq]
    exact Sym2.mem_mk_right _ _

/-- No target port based at the singleton endpoint can literally overlap a
source port. -/
theorem not_portOverlap_of_targetDeletedVertex_mem_singleton
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort targetPort : Fin 4)
    (hinside : boundaryDeletedVertex collar.targetData targetPort ∈
      collar.singletonCutProfile.component.supp) :
    ¬ collar.PortOverlap sourcePort targetPort := by
  intro hoverlap
  have hcrossing :=
    collar.targetBoundary_mem_crossingEdges_of_deletedVertex_mem_singleton
      targetPort hinside
  have havoid := cycle.crossingEdge_endpoint_ne_portVertex hcrossing
    (collar.targetData.portVertex_mem_boundaryEdgeValue targetPort)
      sourcePort
  exact havoid hoverlap.symm

/-- Every literal overlap is based at the non-singleton endpoint of the
target pair. -/
theorem targetDeletedVertex_not_mem_singleton_of_portOverlap
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    {sourcePort targetPort : Fin 4}
    (hoverlap : collar.PortOverlap sourcePort targetPort) :
    boundaryDeletedVertex collar.targetData targetPort ∉
      collar.singletonCutProfile.component.supp := by
  intro hinside
  exact collar.not_portOverlap_of_targetDeletedVertex_mem_singleton
    sourcePort targetPort hinside hoverlap

/-- Depending on the orientation of the target edge, every overlap uses
either target ports `2,3` or target ports `0,1`; the two ports at the
singleton endpoint are excluded. -/
theorem portOverlap_targetPort_pair
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    ((collar.targetData.firstVertex ∈
          collar.singletonCutProfile.component.supp) ∧
        ∀ {sourcePort targetPort : Fin 4},
          collar.PortOverlap sourcePort targetPort →
            targetPort = 2 ∨ targetPort = 3) ∨
      ((collar.targetData.secondVertex ∈
          collar.singletonCutProfile.component.supp) ∧
        ∀ {sourcePort targetPort : Fin 4},
          collar.PortOverlap sourcePort targetPort →
            targetPort = 0 ∨ targetPort = 1) := by
  rcases collar.targetEndpoint_singletonSide_xor with
    ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · left
    refine ⟨hfirst, ?_⟩
    intro sourcePort targetPort hoverlap
    have houtside :=
      collar.targetDeletedVertex_not_mem_singleton_of_portOverlap hoverlap
    fin_cases targetPort <;>
      simp [boundaryDeletedVertex, hfirst, hsecond] at houtside ⊢
  · right
    refine ⟨hsecond, ?_⟩
    intro sourcePort targetPort hoverlap
    have houtside :=
      collar.targetDeletedVertex_not_mem_singleton_of_portOverlap hoverlap
    fin_cases targetPort <;>
      simp [boundaryDeletedVertex, hfirst, hsecond] at houtside ⊢

/-- The literal source/target overlap relation has at most two elements. -/
theorem card_portOverlapPair_le_two
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Fintype.card collar.PortOverlapPair ≤ 2 := by
  rcases collar.portOverlap_targetPort_pair with
    ⟨_hfirst, hports⟩ | ⟨_hsecond, hports⟩
  · let projection : collar.PortOverlapPair → Fin 2 := fun overlap =>
      if overlap.1.2 = 2 then 0 else 1
    have hinjective : Function.Injective projection := by
      rintro ⟨⟨firstSource, firstTarget⟩, hfirst⟩
        ⟨⟨secondSource, secondTarget⟩, hsecond⟩ heq
      have hfirstTarget := hports hfirst
      have hsecondTarget := hports hsecond
      have htarget : firstTarget = secondTarget := by
        rcases hfirstTarget with rfl | rfl <;>
          rcases hsecondTarget with rfl | rfl <;>
          simp [projection] at heq ⊢
      subst secondTarget
      have hsource := collar.portOverlap_source_unique hfirst hsecond
      apply Subtype.ext
      exact Prod.ext hsource rfl
    simpa using Fintype.card_le_of_injective projection hinjective
  · let projection : collar.PortOverlapPair → Fin 2 := fun overlap =>
      if overlap.1.2 = 0 then 0 else 1
    have hinjective : Function.Injective projection := by
      rintro ⟨⟨firstSource, firstTarget⟩, hfirst⟩
        ⟨⟨secondSource, secondTarget⟩, hsecond⟩ heq
      have hfirstTarget := hports hfirst
      have hsecondTarget := hports hsecond
      have htarget : firstTarget = secondTarget := by
        rcases hfirstTarget with rfl | rfl <;>
          rcases hsecondTarget with rfl | rfl <;>
          simp [projection] at heq ⊢
      subst secondTarget
      have hsource := collar.portOverlap_source_unique hfirst hsecond
      apply Subtype.ext
      exact Prod.ext hsource rfl
    simpa using Fintype.card_le_of_injective projection hinjective

private theorem boundaryDeletedVertex_adj_portVertex
    (data : AdjacentPairData G) (port : Fin 4) :
    G.Adj (boundaryDeletedVertex data port) (data.portVertex port) := by
  fin_cases port
  · simpa [boundaryDeletedVertex] using data.first_adj_port_zero
  · simpa [boundaryDeletedVertex] using data.first_adj_port_one
  · simpa [boundaryDeletedVertex] using data.second_adj_port_two
  · simpa [boundaryDeletedVertex] using data.second_adj_port_three

/-- A source boundary base and a target boundary base are always distinct:
the two deleted adjacent pairs are disjoint. -/
theorem sourceBoundaryDeletedVertex_ne_targetBoundaryDeletedVertex
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort targetPort : Fin 4) :
    boundaryDeletedVertex collar.sourceData sourcePort ≠
      boundaryDeletedVertex collar.targetData targetPort := by
  have hfirst := collar.targetFirst_mem_sourceRetainedVertexSet
  have hsecond := collar.targetSecond_mem_sourceRetainedVertexSet
  have hsourceFirst_targetFirst :
      collar.sourceData.firstVertex ≠ collar.targetData.firstVertex :=
    hfirst.1.symm
  have hsourceSecond_targetFirst :
      collar.sourceData.secondVertex ≠ collar.targetData.firstVertex :=
    hfirst.2.symm
  have hsourceFirst_targetSecond :
      collar.sourceData.firstVertex ≠ collar.targetData.secondVertex :=
    hsecond.1.symm
  have hsourceSecond_targetSecond :
      collar.sourceData.secondVertex ≠ collar.targetData.secondVertex :=
    hsecond.2.symm
  fin_cases sourcePort <;> fin_cases targetPort <;>
    simp [boundaryDeletedVertex, hsourceFirst_targetFirst,
      hsourceSecond_targetFirst, hsourceFirst_targetSecond,
      hsourceSecond_targetSecond]

/-- Two overlaps cannot use the same source boundary base and the same
target boundary base. Otherwise their four incidence edges form a forbidden
four-cycle. -/
theorem portOverlap_eq_of_boundaryDeletedVertices_eq
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    {firstSource firstTarget secondSource secondTarget : Fin 4}
    (hfirst : collar.PortOverlap firstSource firstTarget)
    (hsecond : collar.PortOverlap secondSource secondTarget)
    (hsourceBase :
      boundaryDeletedVertex collar.sourceData firstSource =
        boundaryDeletedVertex collar.sourceData secondSource)
    (htargetBase :
      boundaryDeletedVertex collar.targetData firstTarget =
        boundaryDeletedVertex collar.targetData secondTarget) :
    firstSource = secondSource ∧ firstTarget = secondTarget := by
  by_cases hsourcePort : firstSource = secondSource
  · subst secondSource
    exact ⟨rfl, collar.portOverlap_target_unique hfirst hsecond⟩
  · have htargetPort : firstTarget ≠ secondTarget := by
      intro heq
      subst secondTarget
      exact hsourcePort (collar.portOverlap_source_unique hfirst hsecond)
    have hfirstSecond : G.Adj
        (boundaryDeletedVertex collar.sourceData firstSource)
        (collar.sourceData.portVertex firstSource) :=
      boundaryDeletedVertex_adj_portVertex collar.sourceData firstSource
    have hsecondThird : G.Adj
        (collar.sourceData.portVertex firstSource)
        (boundaryDeletedVertex collar.targetData firstTarget) := by
      rw [hfirst]
      exact (boundaryDeletedVertex_adj_portVertex
        collar.targetData firstTarget).symm
    have hthirdFourth : G.Adj
        (boundaryDeletedVertex collar.targetData firstTarget)
        (collar.sourceData.portVertex secondSource) := by
      rw [hsecond, htargetBase]
      exact boundaryDeletedVertex_adj_portVertex
        collar.targetData secondTarget
    have hfourthFirst : G.Adj
        (collar.sourceData.portVertex secondSource)
        (boundaryDeletedVertex collar.sourceData firstSource) := by
      rw [hsourceBase]
      exact (boundaryDeletedVertex_adj_portVertex
        collar.sourceData secondSource).symm
    have hfirstThird :=
      collar.sourceBoundaryDeletedVertex_ne_targetBoundaryDeletedVertex
        firstSource firstTarget
    have hsecondFourth :
        collar.sourceData.portVertex firstSource ≠
          collar.sourceData.portVertex secondSource :=
      collar.sourceData.portVertex_ne hsourcePort
    exact False.elim
      (no_fourCycle_of_vertexMinimalTaitCounterexample graphData minimal
        hfirstSecond hsecondThird hthirdFourth hfourthFirst
          hfirstThird hsecondFourth)

/-- All overlaps use the same target boundary base, namely the
non-singleton endpoint of the target edge. -/
theorem targetBoundaryDeletedVertex_eq_of_portOverlaps
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    {firstSource firstTarget secondSource secondTarget : Fin 4}
    (hfirst : collar.PortOverlap firstSource firstTarget)
    (hsecond : collar.PortOverlap secondSource secondTarget) :
    boundaryDeletedVertex collar.targetData firstTarget =
      boundaryDeletedVertex collar.targetData secondTarget := by
  rcases collar.portOverlap_targetPort_pair with
    ⟨_hsingleton, hports⟩ | ⟨_hsingleton, hports⟩
  · rcases hports hfirst with rfl | rfl <;>
      rcases hports hsecond with rfl | rfl <;>
      simp [boundaryDeletedVertex]
  · rcases hports hfirst with rfl | rfl <;>
      rcases hports hsecond with rfl | rfl <;>
      simp [boundaryDeletedVertex]

/-- Distinct overlaps lie on opposite source boundary bases. Thus the
two-port bound, when sharp, places one overlap at each restored source
vertex. -/
theorem sourceBoundaryDeletedVertex_ne_of_distinct_portOverlaps
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (first second : collar.PortOverlapPair)
    (hne : first ≠ second) :
    boundaryDeletedVertex collar.sourceData first.1.1 ≠
      boundaryDeletedVertex collar.sourceData second.1.1 := by
  intro hsourceBase
  have htargetBase := collar.targetBoundaryDeletedVertex_eq_of_portOverlaps
    first.2 second.2
  have hpairs := collar.portOverlap_eq_of_boundaryDeletedVertices_eq
    first.2 second.2 hsourceBase htargetBase
  apply hne
  apply Subtype.ext
  exact Prod.ext hpairs.1 hpairs.2

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
