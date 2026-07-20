import Mathlib.Combinatorics.SimpleGraph.Matching
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionCoordinateSwitch

/-! Finite support components entered by complementary-coordinate turns. -/

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

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]

/-- In a finite graph of maximum degree two, a degree-two root either shares
its component with an odd vertex or lies on a simple cycle. -/
theorem exists_reachable_odd_or_cycle_of_degree_eq_two_of_degree_le_two
    (start : W) (hstartDegree : H.degree start = 2)
    (hdegree : ∀ vertex : W, H.degree vertex ≤ 2) :
    (∃ finish : W, finish ≠ start ∧ Odd (H.degree finish) ∧
      H.Reachable start finish) ∨
    ∃ cycle : H.Walk start start, cycle.IsCycle := by
  classical
  let component : H.ConnectedComponent := H.connectedComponentMk start
  have hstartComponent : start ∈ component.supp := by
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  by_cases hodd : ∃ finish : W,
      finish ∈ component.supp ∧ Odd (H.degree finish)
  · left
    rcases hodd with ⟨finish, hfinishComponent, hfinishOdd⟩
    have hfinishNe : finish ≠ start := by
      intro heq
      subst finish
      rcases hfinishOdd with ⟨multiple, hmultiple⟩
      omega
    exact ⟨finish, hfinishNe, hfinishOdd,
      component.reachable_of_mem_supp
        hstartComponent hfinishComponent⟩
  · right
    let componentGraph : SimpleGraph component.supp :=
      H.induce component.supp
    letI componentVertexFintype : Fintype component.supp :=
      Subtype.fintype _
    letI componentNeighborFintype
        (vertex : component.supp) :
        Fintype (componentGraph.neighborSet vertex) :=
      Subtype.fintype _
    let startInComponent : component.supp :=
      ⟨start, hstartComponent⟩
    have hcomponentCycles : componentGraph.IsCycles := by
      intro vertex hneighbor
      have hneighbors : H.neighborSet vertex.1 ⊆ component.supp := by
        intro neighbor hadjacent
        exact component.mem_supp_of_adj_mem_supp
          vertex.2 hadjacent
      have hdegreeEq : componentGraph.degree vertex =
          H.degree vertex.1 := by
        have hinduced := SimpleGraph.degree_induce_of_neighborSet_subset
          (G := H) (s := component.supp) (v := vertex) hneighbors
        exact hinduced.trans
          (degree_eq_of_neighborFintypes H vertex.1
            (Subtype.fintype _) inferInstance)
      have hpositive : 0 < componentGraph.degree vertex :=
        SimpleGraph.degree_pos_iff_nonempty.mpr hneighbor
      have hnotOdd : ¬ Odd (H.degree vertex.1) := by
        intro hvertexOdd
        exact hodd ⟨vertex.1, vertex.2, hvertexOdd⟩
      have hnotOne : H.degree vertex.1 ≠ 1 := by
        intro hdegreeOne
        apply hnotOdd
        simp [hdegreeOne]
      have hdegreeTwo : H.degree vertex.1 = 2 := by
        have hpositiveAmbient : 0 < H.degree vertex.1 := by
          simpa [hdegreeEq] using hpositive
        exact Nat.le_antisymm (hdegree vertex.1) (by omega)
      rw [Set.ncard_eq_toFinset_card']
      exact hdegreeEq.trans hdegreeTwo
    have hstartNeighbor :
        (componentGraph.neighborSet startInComponent).Nonempty := by
      have hpositive : 0 < H.degree start := by
        simp [hstartDegree]
      rcases SimpleGraph.degree_pos_iff_nonempty.mp hpositive with
        ⟨neighbor, hadjacent⟩
      have hneighborComponent : neighbor ∈ component.supp :=
        component.mem_supp_of_adj_mem_supp
          hstartComponent hadjacent
      exact ⟨⟨neighbor, hneighborComponent⟩, hadjacent⟩
    let cycleComponent : componentGraph.ConnectedComponent :=
      componentGraph.connectedComponentMk startInComponent
    have hstartCycleComponent :
        startInComponent ∈ cycleComponent.supp := by
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    rcases
        hcomponentCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
          hstartCycleComponent hstartNeighbor with
      ⟨componentCycle, hcomponentCycle, _hcomponentCycleSupport⟩
    let cycle : H.Walk start start :=
      componentCycle.map
        (SimpleGraph.Embedding.induce (G := H) component.supp).toHom
    exact ⟨cycle,
      hcomponentCycle.map
        (SimpleGraph.Embedding.induce (G := H) component.supp).injective⟩

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

namespace FirstHitSingletonCompanionTransferPath

variable {firstHit : FirstHitSingletonCompanionTransferPath
  (collar := collar) (sourceEscape := sourceEscape)}

namespace TransverseCompanionChange

variable {change : firstHit.TransverseCompanionChange}

namespace ComplementarySupportCorner

/-- Following the complementary support component from a transverse turn
either reaches a distinct named collar terminal or closes into a simple
scalar-support cycle rooted at the turn. -/
theorem exists_distinct_terminal_reachable_or_supportCycle
    (corner : change.ComplementarySupportCorner) :
    let supportGraph := collar.coordinateDiscrepancySupportGraph
      sourceEscape (!firstHit.transfer.coordinate)
    let junction := SimpleGraph.lineGraphCommonVertex
      corner.incoming_transverse_adj
    (∃ finish : collar.commonCoreVertex,
        finish ∈ collar.commonPortVertexFinset ∧
        finish ≠ junction ∧
        supportGraph.Reachable junction finish) ∨
      ∃ supportCycle : supportGraph.Walk junction junction,
        supportCycle.IsCycle := by
  classical
  let scalarChain : collar.commonCore.edgeSet → F2 :=
    fun edge => crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge)
  let supportGraph : SimpleGraph collar.commonCoreVertex :=
    scalarSupportGraph scalarChain
  let junction := SimpleGraph.lineGraphCommonVertex
    corner.incoming_transverse_adj
  change (∃ finish : collar.commonCoreVertex,
      finish ∈ collar.commonPortVertexFinset ∧
      finish ≠ junction ∧
      supportGraph.Reachable junction finish) ∨
    ∃ supportCycle : supportGraph.Walk junction junction,
      supportCycle.IsCycle
  have hjunctionDegree : supportGraph.degree junction = 2 := by
    rw [← incidentEdgeFinset_card_eq_degree]
    have hcornerDegree := corner.supportJunction_degree_eq_two
    change (incidentEdgeFinset supportGraph junction).card = 2 at hcornerDegree
    exact hcornerDegree
  have hdegree : ∀ vertex : collar.commonCoreVertex,
      supportGraph.degree vertex ≤ 2 := by
    intro vertex
    rw [← incidentEdgeFinset_card_eq_degree]
    exact taitDiscrepancySupport_incidentCard_le_two
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!firstHit.transfer.coordinate) vertex
      (collar.commonCore_incidentEdgeFinset_card_le_three vertex)
  have hoddTerminal : ∀ vertex : collar.commonCoreVertex,
      Odd (supportGraph.degree vertex) →
        vertex ∈ collar.commonPortVertexFinset := by
    intro vertex hodd
    have hscalarBoundary :
        scalarVertexKirchhoffSum collar.commonCore scalarChain vertex ≠ 0 := by
      exact (scalarSupportGraph_degree_odd_iff scalarChain vertex).1 hodd
    by_contra hterminal
    apply hscalarBoundary
    rw [scalarVertexKirchhoffSum_crossFaceCoordinate,
      collar.vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_mem_commonPortVertexFinset
        sourceEscape vertex hterminal]
    cases (!firstHit.transfer.coordinate) <;> rfl
  rcases
      exists_reachable_odd_or_cycle_of_degree_eq_two_of_degree_le_two
        (H := supportGraph) junction hjunctionDegree hdegree with
    hterminal | hcycle
  · left
    rcases hterminal with ⟨finish, hfinishNe, hfinishOdd, hreachable⟩
    exact ⟨finish, hoddTerminal finish hfinishOdd,
      hfinishNe, hreachable⟩
  · exact Or.inr hcycle

end ComplementarySupportCorner

end TransverseCompanionChange

end FirstHitSingletonCompanionTransferPath

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
