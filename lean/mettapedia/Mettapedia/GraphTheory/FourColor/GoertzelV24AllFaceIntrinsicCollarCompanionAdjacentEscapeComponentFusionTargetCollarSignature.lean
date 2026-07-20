import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionTargetTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCoordinates
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkCycleParity
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureFlow

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CorridorPumping
open GoertzelV24FourDefectBoundary
open GoertzelV24PrimalCycleSpace
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The seven possible edge-simple traversal patterns through a five-edge
adjacent-pair collar.  The three pair constructors avoid the central edge;
the four inhabitants of `cross` use it and choose one boundary edge at each
endpoint. -/
inductive TargetCollarTraversalClass where
  | firstBoundaryPair
  | secondBoundaryPair
  | bothBoundaryPairs
  | cross (firstUsesOne secondUsesThree : Bool)
deriving DecidableEq, Fintype

/-- The first-side boundary port selected by a central traversal. -/
def TargetCollarTraversalClass.firstCrossPort : Bool → Fin 4
  | false => 0
  | true => 1

/-- The second-side boundary port selected by a central traversal. -/
def TargetCollarTraversalClass.secondCrossPort : Bool → Fin 4
  | false => 2
  | true => 3

/-- The exact fixed-coordinate support of one collar traversal class. -/
def TargetCollarTraversalClass.coordinateFinset :
    TargetCollarTraversalClass → Finset (Option (Fin 4))
  | .firstBoundaryPair => {some 0, some 1}
  | .secondBoundaryPair => {some 2, some 3}
  | .bothBoundaryPairs => {some 0, some 1, some 2, some 3}
  | .cross firstUsesOne secondUsesThree =>
      {none,
        some (TargetCollarTraversalClass.firstCrossPort firstUsesOne),
        some (TargetCollarTraversalClass.secondCrossPort secondUsesThree)}

/-- Direct five-bit semantics for a collar traversal class. -/
def TargetCollarTraversalClass.Describes
    (traversalClass : TargetCollarTraversalClass)
    (centralUsed boundaryZeroUsed boundaryOneUsed boundaryTwoUsed
      boundaryThreeUsed : Prop) : Prop :=
  match traversalClass with
  | .firstBoundaryPair =>
      ¬ centralUsed ∧ boundaryZeroUsed ∧ boundaryOneUsed ∧
        ¬ boundaryTwoUsed ∧ ¬ boundaryThreeUsed
  | .secondBoundaryPair =>
      ¬ centralUsed ∧ ¬ boundaryZeroUsed ∧ ¬ boundaryOneUsed ∧
        boundaryTwoUsed ∧ boundaryThreeUsed
  | .bothBoundaryPairs =>
      ¬ centralUsed ∧ boundaryZeroUsed ∧ boundaryOneUsed ∧
        boundaryTwoUsed ∧ boundaryThreeUsed
  | .cross firstUsesOne secondUsesThree =>
      centralUsed ∧
        (if firstUsesOne then ¬ boundaryZeroUsed ∧ boundaryOneUsed
          else boundaryZeroUsed ∧ ¬ boundaryOneUsed) ∧
        (if secondUsesThree then ¬ boundaryTwoUsed ∧ boundaryThreeUsed
          else boundaryTwoUsed ∧ ¬ boundaryThreeUsed)

/-- There are exactly seven collar traversal classes. -/
theorem TargetCollarTraversalClass.card_eq_seven :
    Fintype.card TargetCollarTraversalClass = 7 := by
  decide

private theorem f2_add_eq_zero_iff_eq (left right : F2) :
    left + right = 0 ↔ left = right := by
  constructor
  · intro hzero
    calc
      left = left + 0 := by simp
      _ = left + (right + right) := by rw [zmod2_add_self]
      _ = (left + right) + right := by rw [add_assoc]
      _ = right := by rw [hzero]; simp
  · rintro rfl
    exact zmod2_add_self _

/-- The three ambient edges incident to the first vertex of an adjacent
pair are its central edge and boundary edges zero and one. -/
theorem incidentEdgeFinset_firstVertex_eq_collarTriple
    (data : AdjacentPairData G) :
    incidentEdgeFinset G data.firstVertex =
      {centralEdge data, boundaryEdge data 0, boundaryEdge data 1} := by
  ext edge
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hincident
    rcases Sym2.mem_iff_exists.mp hincident with ⟨other, hedge⟩
    have hadj : G.Adj data.firstVertex other := by
      apply (SimpleGraph.mem_edgeSet G).mp
      rw [← hedge]
      exact edge.2
    have hneighbor : other ∈ G.neighborSet data.firstVertex := hadj
    rw [data.firstNeighbors] at hneighbor
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hneighbor
    rcases hneighbor with rfl | rfl | rfl
    · exact Or.inl (Subtype.ext (by
        simpa [centralEdge_val, centralEdgeValue] using hedge))
    · exact Or.inr (Or.inl (Subtype.ext (by
        simpa [boundaryEdge_val, boundaryEdgeValue_zero] using hedge)))
    · exact Or.inr (Or.inr (Subtype.ext (by
        simpa [boundaryEdge_val, boundaryEdgeValue_one] using hedge)))
  · rintro (rfl | rfl | rfl)
    · rw [centralEdge_val, centralEdgeValue]
      exact Sym2.mem_mk_left _ _
    · rw [boundaryEdge_val, boundaryEdgeValue_zero]
      exact Sym2.mem_mk_left _ _
    · rw [boundaryEdge_val, boundaryEdgeValue_one]
      exact Sym2.mem_mk_left _ _

/-- The three ambient edges incident to the second vertex of an adjacent
pair are its central edge and boundary edges two and three. -/
theorem incidentEdgeFinset_secondVertex_eq_collarTriple
    (data : AdjacentPairData G) :
    incidentEdgeFinset G data.secondVertex =
      {centralEdge data, boundaryEdge data 2, boundaryEdge data 3} := by
  ext edge
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hincident
    rcases Sym2.mem_iff_exists.mp hincident with ⟨other, hedge⟩
    have hadj : G.Adj data.secondVertex other := by
      apply (SimpleGraph.mem_edgeSet G).mp
      rw [← hedge]
      exact edge.2
    have hneighbor : other ∈ G.neighborSet data.secondVertex := hadj
    rw [data.secondNeighbors] at hneighbor
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hneighbor
    rcases hneighbor with rfl | rfl | rfl
    · exact Or.inl (Subtype.ext (by
        simpa [centralEdge_val, centralEdgeValue, Sym2.eq_swap] using hedge))
    · exact Or.inr (Or.inl (Subtype.ext (by
        simpa [boundaryEdge_val, boundaryEdgeValue_two] using hedge)))
    · exact Or.inr (Or.inr (Subtype.ext (by
        simpa [boundaryEdge_val, boundaryEdgeValue_three] using hedge)))
  · rintro (rfl | rfl | rfl)
    · rw [centralEdge_val, centralEdgeValue]
      exact Sym2.mem_mk_right _ _
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

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {start : sourceNormal.KempeOrbitAdjacentEscape}

namespace CompanionCrossPairFusionPrimalTrail

variable (fusion : CompanionCrossPairFusionPrimalTrail collar start)

/-- The initial endpoint of every cross-pair fusion trail lies in the exact
target deletion, independently of what the trail does in its interior. -/
theorem startVertex_mem_targetRetainedVertexSet :
    fusion.startVertex.1 ∈
      retainedVertexSet collar.targetData.firstVertex
        collar.targetData.secondVertex := by
  let commonEdge := collar.commonEdgeInTarget
    fusion.lineFusion.normal.returnData.lastOverlap.overlap.commonEdge
  let ambientEdge := retainedEdgeToAmbientEdge collar.targetData commonEdge
  apply endpoints_mem_retainedVertexSet collar.targetData ambientEdge
    (retainedEdgeToAmbientEdge_isRetainedAmbientEdge
      collar.targetData commonEdge) fusion.startVertex.1
  have hfirst :
      (fusion.ambientTrail.firstDart fusion.ambientTrail_not_nil).edge =
        ambientEdge.1 := by
    simpa only [commonEdge, ambientEdge] using
      fusion.ambientTrail_firstDart_edge_eq_target
  rw [← hfirst]
  change fusion.startVertex.1 ∈
    s(fusion.startVertex.1, fusion.ambientTrail.snd)
  exact Sym2.mem_mk_left _ _

/-- The final endpoint likewise lies in the exact target deletion. -/
theorem endVertex_mem_targetRetainedVertexSet :
    fusion.endVertex.1 ∈
      retainedVertexSet collar.targetData.firstVertex
        collar.targetData.secondVertex := by
  let commonEdge := collar.commonEdgeInTarget
    fusion.lineFusion.normal.launchSupportEdge.1
  let ambientEdge := retainedEdgeToAmbientEdge collar.targetData commonEdge
  apply endpoints_mem_retainedVertexSet collar.targetData ambientEdge
    (retainedEdgeToAmbientEdge_isRetainedAmbientEdge
      collar.targetData commonEdge) fusion.endVertex.1
  have hlast :
      (fusion.ambientTrail.lastDart fusion.ambientTrail_not_nil).edge =
        ambientEdge.1 := by
    simpa only [commonEdge, ambientEdge] using
      fusion.ambientTrail_lastDart_edge_eq_target
  rw [← hlast]
  change fusion.endVertex.1 ∈
    s(fusion.ambientTrail.penultimate, fusion.endVertex.1)
  exact Sym2.mem_mk_right _ _

/-- The edge-parity boundary vanishes at the first target vertex. -/
theorem scalarVertexKirchhoffSum_walkEdgeParity_targetFirst_eq_zero :
    scalarVertexKirchhoffSum G (walkEdgeParity fusion.ambientTrail)
        collar.targetData.firstVertex = 0 := by
  rw [scalarVertexKirchhoffSum_eq_f2IncidenceMatrix_mulVec]
  have hboundary := congrFun
    (f2IncidenceMatrix_mulVec_walkEdgeParity fusion.ambientTrail)
      collar.targetData.firstVertex
  rw [hboundary]
  simp [fusion.startVertex_mem_targetRetainedVertexSet.1,
    fusion.endVertex_mem_targetRetainedVertexSet.1]

/-- The edge-parity boundary also vanishes at the second target vertex. -/
theorem scalarVertexKirchhoffSum_walkEdgeParity_targetSecond_eq_zero :
    scalarVertexKirchhoffSum G (walkEdgeParity fusion.ambientTrail)
        collar.targetData.secondVertex = 0 := by
  rw [scalarVertexKirchhoffSum_eq_f2IncidenceMatrix_mulVec]
  have hboundary := congrFun
    (f2IncidenceMatrix_mulVec_walkEdgeParity fusion.ambientTrail)
      collar.targetData.secondVertex
  rw [hboundary]
  simp [fusion.startVertex_mem_targetRetainedVertexSet.2,
    fusion.endVertex_mem_targetRetainedVertexSet.2]

/-- At the first target vertex, the mod-two usage of the central edge and
the two incident boundary edges sums to zero. -/
theorem targetFirst_collarParity :
    walkEdgeParity fusion.ambientTrail (centralEdge collar.targetData) +
        walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 0) +
      walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 1) =
        0 := by
  have hcentralZero : centralEdge collar.targetData ≠
      boundaryEdge collar.targetData 0 := by
    intro hedge
    exact centralEdgeValue_ne_boundaryEdgeValue collar.targetData 0
      (congrArg Subtype.val hedge)
  have hcentralOne : centralEdge collar.targetData ≠
      boundaryEdge collar.targetData 1 := by
    intro hedge
    exact centralEdgeValue_ne_boundaryEdgeValue collar.targetData 1
      (congrArg Subtype.val hedge)
  have hzeroOne : boundaryEdge collar.targetData 0 ≠
      boundaryEdge collar.targetData 1 := by
    intro hedge
    apply boundaryEdgeValue_ne collar.targetData
      (first := 0) (second := 1) (by decide)
    simpa only [boundaryEdge_val] using congrArg Subtype.val hedge
  have hzero :=
    fusion.scalarVertexKirchhoffSum_walkEdgeParity_targetFirst_eq_zero
  unfold scalarVertexKirchhoffSum at hzero
  rw [incidentEdgeFinset_firstVertex_eq_collarTriple] at hzero
  simpa [Finset.sum_insert, hcentralZero, hcentralOne, hzeroOne,
    add_assoc] using hzero

/-- At the second target vertex, the corresponding three collar usages
also sum to zero. -/
theorem targetSecond_collarParity :
    walkEdgeParity fusion.ambientTrail (centralEdge collar.targetData) +
        walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 2) +
      walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 3) =
        0 := by
  have hcentralTwo : centralEdge collar.targetData ≠
      boundaryEdge collar.targetData 2 := by
    intro hedge
    exact centralEdgeValue_ne_boundaryEdgeValue collar.targetData 2
      (congrArg Subtype.val hedge)
  have hcentralThree : centralEdge collar.targetData ≠
      boundaryEdge collar.targetData 3 := by
    intro hedge
    exact centralEdgeValue_ne_boundaryEdgeValue collar.targetData 3
      (congrArg Subtype.val hedge)
  have htwoThree : boundaryEdge collar.targetData 2 ≠
      boundaryEdge collar.targetData 3 := by
    intro hedge
    apply boundaryEdgeValue_ne collar.targetData
      (first := 2) (second := 3) (by decide)
    simpa only [boundaryEdge_val] using congrArg Subtype.val hedge
  have hzero :=
    fusion.scalarVertexKirchhoffSum_walkEdgeParity_targetSecond_eq_zero
  unfold scalarVertexKirchhoffSum at hzero
  rw [incidentEdgeFinset_secondVertex_eq_collarTriple] at hzero
  simpa [Finset.sum_insert, hcentralTwo, hcentralThree, htwoThree,
    add_assoc] using hzero

/-- If the trail avoids the central edge, it uses the two first-side
boundary edges together or avoids them together. -/
theorem targetFirst_boundary_mem_iff_of_central_not_mem
    (hcentral : (centralEdge collar.targetData).1 ∉
      fusion.ambientTrail.edges) :
    (boundaryEdge collar.targetData 0).1 ∈ fusion.ambientTrail.edges ↔
      (boundaryEdge collar.targetData 1).1 ∈ fusion.ambientTrail.edges := by
  have hcentralParity :=
    walkEdgeParity_apply_eq_zero_of_not_mem_edges fusion.ambientTrail
      (centralEdge collar.targetData) hcentral
  have hpair :
      walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 0) +
          walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 1) =
        0 := by
    simpa only [hcentralParity, zero_add] using fusion.targetFirst_collarParity
  have heq :
      walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 0) =
        walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 1) :=
    (f2_add_eq_zero_iff_eq _ _).1 hpair
  calc
    (boundaryEdge collar.targetData 0).1 ∈ fusion.ambientTrail.edges ↔
        walkEdgeParity fusion.ambientTrail
          (boundaryEdge collar.targetData 0) = 1 :=
      (walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail
        fusion.ambientTrail_isTrail
        (boundaryEdge collar.targetData 0)).symm
    _ ↔ walkEdgeParity fusion.ambientTrail
          (boundaryEdge collar.targetData 1) = 1 := by rw [heq]
    _ ↔ (boundaryEdge collar.targetData 1).1 ∈
          fusion.ambientTrail.edges :=
      walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail
        fusion.ambientTrail_isTrail (boundaryEdge collar.targetData 1)

/-- The same paired behavior holds at the second endpoint when the central
edge is absent. -/
theorem targetSecond_boundary_mem_iff_of_central_not_mem
    (hcentral : (centralEdge collar.targetData).1 ∉
      fusion.ambientTrail.edges) :
    (boundaryEdge collar.targetData 2).1 ∈ fusion.ambientTrail.edges ↔
      (boundaryEdge collar.targetData 3).1 ∈ fusion.ambientTrail.edges := by
  have hcentralParity :=
    walkEdgeParity_apply_eq_zero_of_not_mem_edges fusion.ambientTrail
      (centralEdge collar.targetData) hcentral
  have hpair :
      walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 2) +
          walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 3) =
        0 := by
    simpa only [hcentralParity, zero_add] using fusion.targetSecond_collarParity
  have heq :
      walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 2) =
        walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 3) :=
    (f2_add_eq_zero_iff_eq _ _).1 hpair
  calc
    (boundaryEdge collar.targetData 2).1 ∈ fusion.ambientTrail.edges ↔
        walkEdgeParity fusion.ambientTrail
          (boundaryEdge collar.targetData 2) = 1 :=
      (walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail
        fusion.ambientTrail_isTrail
        (boundaryEdge collar.targetData 2)).symm
    _ ↔ walkEdgeParity fusion.ambientTrail
          (boundaryEdge collar.targetData 3) = 1 := by rw [heq]
    _ ↔ (boundaryEdge collar.targetData 3).1 ∈
          fusion.ambientTrail.edges :=
      walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail
        fusion.ambientTrail_isTrail (boundaryEdge collar.targetData 3)

/-- If the trail uses the central edge, it uses exactly one of the two
first-side boundary edges. -/
theorem targetFirst_exactly_one_boundary_of_central_mem
    (hcentral : (centralEdge collar.targetData).1 ∈
      fusion.ambientTrail.edges) :
    ((boundaryEdge collar.targetData 0).1 ∈ fusion.ambientTrail.edges ∧
        (boundaryEdge collar.targetData 1).1 ∉ fusion.ambientTrail.edges) ∨
      ((boundaryEdge collar.targetData 0).1 ∉ fusion.ambientTrail.edges ∧
        (boundaryEdge collar.targetData 1).1 ∈ fusion.ambientTrail.edges) := by
  have hcentralParity :=
    walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
      fusion.ambientTrail_isTrail (centralEdge collar.targetData) hcentral
  have hpair :
      (1 : F2) +
          (walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 0) +
            walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 1)) =
        0 := by
    simpa only [hcentralParity, add_assoc] using fusion.targetFirst_collarParity
  have hsum :
      walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 0) +
          walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 1) =
        1 :=
    ((f2_add_eq_zero_iff_eq _ _).1 hpair).symm
  by_cases hzero :
      (boundaryEdge collar.targetData 0).1 ∈ fusion.ambientTrail.edges
  · by_cases hone :
        (boundaryEdge collar.targetData 1).1 ∈ fusion.ambientTrail.edges
    · have hzeroParity :=
        walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
          fusion.ambientTrail_isTrail (boundaryEdge collar.targetData 0) hzero
      have honeParity :=
        walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
          fusion.ambientTrail_isTrail (boundaryEdge collar.targetData 1) hone
      exfalso
      have hbad : (0 : F2) = 1 := by
        simpa only [hzeroParity, honeParity, zmod2_add_self] using hsum
      exact zero_ne_one hbad
    · exact Or.inl ⟨hzero, hone⟩
  · by_cases hone :
        (boundaryEdge collar.targetData 1).1 ∈ fusion.ambientTrail.edges
    · exact Or.inr ⟨hzero, hone⟩
    · have hzeroParity :=
        walkEdgeParity_apply_eq_zero_of_not_mem_edges fusion.ambientTrail
          (boundaryEdge collar.targetData 0) hzero
      have honeParity :=
        walkEdgeParity_apply_eq_zero_of_not_mem_edges fusion.ambientTrail
          (boundaryEdge collar.targetData 1) hone
      exfalso
      have hbad : (0 : F2) = 1 := by
        simpa only [hzeroParity, honeParity, add_zero] using hsum
      exact zero_ne_one hbad

/-- A central traversal likewise uses exactly one second-side boundary
edge. -/
theorem targetSecond_exactly_one_boundary_of_central_mem
    (hcentral : (centralEdge collar.targetData).1 ∈
      fusion.ambientTrail.edges) :
    ((boundaryEdge collar.targetData 2).1 ∈ fusion.ambientTrail.edges ∧
        (boundaryEdge collar.targetData 3).1 ∉ fusion.ambientTrail.edges) ∨
      ((boundaryEdge collar.targetData 2).1 ∉ fusion.ambientTrail.edges ∧
        (boundaryEdge collar.targetData 3).1 ∈ fusion.ambientTrail.edges) := by
  have hcentralParity :=
    walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
      fusion.ambientTrail_isTrail (centralEdge collar.targetData) hcentral
  have hpair :
      (1 : F2) +
          (walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 2) +
            walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 3)) =
        0 := by
    simpa only [hcentralParity, add_assoc] using fusion.targetSecond_collarParity
  have hsum :
      walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 2) +
          walkEdgeParity fusion.ambientTrail (boundaryEdge collar.targetData 3) =
        1 :=
    ((f2_add_eq_zero_iff_eq _ _).1 hpair).symm
  by_cases htwo :
      (boundaryEdge collar.targetData 2).1 ∈ fusion.ambientTrail.edges
  · by_cases hthree :
        (boundaryEdge collar.targetData 3).1 ∈ fusion.ambientTrail.edges
    · have htwoParity :=
        walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
          fusion.ambientTrail_isTrail (boundaryEdge collar.targetData 2) htwo
      have hthreeParity :=
        walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
          fusion.ambientTrail_isTrail (boundaryEdge collar.targetData 3) hthree
      exfalso
      have hbad : (0 : F2) = 1 := by
        simpa only [htwoParity, hthreeParity, zmod2_add_self] using hsum
      exact zero_ne_one hbad
    · exact Or.inl ⟨htwo, hthree⟩
  · by_cases hthree :
        (boundaryEdge collar.targetData 3).1 ∈ fusion.ambientTrail.edges
    · exact Or.inr ⟨htwo, hthree⟩
    · have htwoParity :=
        walkEdgeParity_apply_eq_zero_of_not_mem_edges fusion.ambientTrail
          (boundaryEdge collar.targetData 2) htwo
      have hthreeParity :=
        walkEdgeParity_apply_eq_zero_of_not_mem_edges fusion.ambientTrail
          (boundaryEdge collar.targetData 3) hthree
      exfalso
      have hbad : (0 : F2) = 1 := by
        simpa only [htwoParity, hthreeParity, add_zero] using hsum
      exact zero_ne_one hbad

end CompanionCrossPairFusionPrimalTrail

/-- A target-collar contact together with its complete seven-class traversal
certificate. -/
structure CompanionCrossPairFusionTargetCollarTraversal
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  contact : CompanionCrossPairFusionTargetCollarContact collar start
  traversalClass : TargetCollarTraversalClass
  exactUsage : traversalClass.Describes
    ((centralEdge collar.targetData).1 ∈ contact.fusion.ambientTrail.edges)
    ((boundaryEdge collar.targetData 0).1 ∈ contact.fusion.ambientTrail.edges)
    ((boundaryEdge collar.targetData 1).1 ∈ contact.fusion.ambientTrail.edges)
    ((boundaryEdge collar.targetData 2).1 ∈ contact.fusion.ambientTrail.edges)
    ((boundaryEdge collar.targetData 3).1 ∈ contact.fusion.ambientTrail.edges)

namespace CompanionCrossPairFusionTargetCollarContact

variable (contact : CompanionCrossPairFusionTargetCollarContact collar start)

/-- A collar contact gives an actual used edge among the five fixed target
collar coordinates. -/
theorem targetCollarEdge_mem_disjunction :
    (centralEdge collar.targetData).1 ∈ contact.fusion.ambientTrail.edges ∨
      (boundaryEdge collar.targetData 0).1 ∈
          contact.fusion.ambientTrail.edges ∨
      (boundaryEdge collar.targetData 1).1 ∈
          contact.fusion.ambientTrail.edges ∨
      (boundaryEdge collar.targetData 2).1 ∈
          contact.fusion.ambientTrail.edges ∨
      (boundaryEdge collar.targetData 3).1 ∈
          contact.fusion.ambientTrail.edges := by
  rcases contact.central_or_boundary with hcentral | ⟨port, hboundary⟩
  · exact Or.inl (hcentral ▸ contact.contactEdge_mem)
  · fin_cases port
    · exact Or.inr (Or.inl (hboundary ▸ contact.contactEdge_mem))
    · exact Or.inr (Or.inr (Or.inl
        (hboundary ▸ contact.contactEdge_mem)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (hboundary ▸ contact.contactEdge_mem))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (hboundary ▸ contact.contactEdge_mem))))

/-- Every contact trail has one of the seven exact collar traversal classes.
The description records all five edge-membership bits, not merely a chosen
contact witness. -/
theorem exists_exact_targetCollarTraversalClass :
    ∃ traversalClass : TargetCollarTraversalClass,
      traversalClass.Describes
        ((centralEdge collar.targetData).1 ∈
          contact.fusion.ambientTrail.edges)
        ((boundaryEdge collar.targetData 0).1 ∈
          contact.fusion.ambientTrail.edges)
        ((boundaryEdge collar.targetData 1).1 ∈
          contact.fusion.ambientTrail.edges)
        ((boundaryEdge collar.targetData 2).1 ∈
          contact.fusion.ambientTrail.edges)
        ((boundaryEdge collar.targetData 3).1 ∈
          contact.fusion.ambientTrail.edges) := by
  by_cases hcentral : (centralEdge collar.targetData).1 ∈
      contact.fusion.ambientTrail.edges
  · rcases contact.fusion.targetFirst_exactly_one_boundary_of_central_mem
        hcentral with ⟨hzero, hone⟩ | ⟨hzero, hone⟩
    · rcases contact.fusion.targetSecond_exactly_one_boundary_of_central_mem
          hcentral with ⟨htwo, hthree⟩ | ⟨htwo, hthree⟩
      · exact ⟨.cross false false, hcentral, ⟨hzero, hone⟩,
          ⟨htwo, hthree⟩⟩
      · exact ⟨.cross false true, hcentral, ⟨hzero, hone⟩,
          ⟨htwo, hthree⟩⟩
    · rcases contact.fusion.targetSecond_exactly_one_boundary_of_central_mem
          hcentral with ⟨htwo, hthree⟩ | ⟨htwo, hthree⟩
      · exact ⟨.cross true false, hcentral, ⟨hzero, hone⟩,
          ⟨htwo, hthree⟩⟩
      · exact ⟨.cross true true, hcentral, ⟨hzero, hone⟩,
          ⟨htwo, hthree⟩⟩
  · have hzeroOne :=
      contact.fusion.targetFirst_boundary_mem_iff_of_central_not_mem hcentral
    have htwoThree :=
      contact.fusion.targetSecond_boundary_mem_iff_of_central_not_mem hcentral
    by_cases hzero : (boundaryEdge collar.targetData 0).1 ∈
        contact.fusion.ambientTrail.edges
    · have hone : (boundaryEdge collar.targetData 1).1 ∈
          contact.fusion.ambientTrail.edges := hzeroOne.1 hzero
      by_cases htwo : (boundaryEdge collar.targetData 2).1 ∈
          contact.fusion.ambientTrail.edges
      · have hthree : (boundaryEdge collar.targetData 3).1 ∈
            contact.fusion.ambientTrail.edges := htwoThree.1 htwo
        exact ⟨.bothBoundaryPairs, hcentral, hzero, hone, htwo, hthree⟩
      · have hthree : (boundaryEdge collar.targetData 3).1 ∉
            contact.fusion.ambientTrail.edges := fun hthree =>
          htwo (htwoThree.2 hthree)
        exact ⟨.firstBoundaryPair, hcentral, hzero, hone, htwo, hthree⟩
    · have hone : (boundaryEdge collar.targetData 1).1 ∉
          contact.fusion.ambientTrail.edges := fun hone =>
        hzero (hzeroOne.2 hone)
      have htwo : (boundaryEdge collar.targetData 2).1 ∈
          contact.fusion.ambientTrail.edges := by
        rcases contact.targetCollarEdge_mem_disjunction with
          hcentral' | hzero' | hone' | htwo | hthree
        · exact (hcentral hcentral').elim
        · exact (hzero hzero').elim
        · exact (hone hone').elim
        · exact htwo
        · exact htwoThree.2 hthree
      have hthree : (boundaryEdge collar.targetData 3).1 ∈
          contact.fusion.ambientTrail.edges := htwoThree.1 htwo
      exact ⟨.secondBoundaryPair, hcentral, hzero, hone, htwo, hthree⟩

/-- Package a raw collar contact with its exact finite traversal class. -/
theorem nonempty_targetCollarTraversal
    (contact : CompanionCrossPairFusionTargetCollarContact collar start) :
    Nonempty (CompanionCrossPairFusionTargetCollarTraversal collar start) := by
  rcases exists_exact_targetCollarTraversalClass contact with
    ⟨traversalClass, exactUsage⟩
  exact ⟨{
    contact := contact
    traversalClass := traversalClass
    exactUsage := exactUsage }⟩

end CompanionCrossPairFusionTargetCollarContact

/-- The closed-circuit classifier with every target-collar contact reduced to
one of the seven exact edge-simple traversal classes. -/
theorem closedCircuit_exists_localCancellation_or_fusionTargetTransport_or_fusionTargetCollarTraversal_or_edgePivot_or_threePairMonodromy
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    Nonempty (CompanionCanonicalComponentDisjointClosure collar start) ∨
      Nonempty (CompanionCrossPairFusionTargetTransport collar start) ∨
        Nonempty (CompanionCrossPairFusionTargetCollarTraversal collar start) ∨
          Nonempty (CompanionSameOuterTargetAvoidingEdgePivot collar start) ∨
            Nonempty (CompanionThreePairMonodromy collar start) := by
  rcases
      closedCircuit_exists_localCancellation_or_fusionTargetTransport_or_fusionTargetCollarContact_or_edgePivot_or_threePairMonodromy
        closed with cancellation | transport | contact | pivot | monodromy
  · exact Or.inl cancellation
  · exact Or.inr (Or.inl transport)
  · rcases contact with ⟨contact⟩
    exact Or.inr (Or.inr (Or.inl
      (CompanionCrossPairFusionTargetCollarContact.nonempty_targetCollarTraversal
        contact)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl pivot)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr monodromy)))

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
