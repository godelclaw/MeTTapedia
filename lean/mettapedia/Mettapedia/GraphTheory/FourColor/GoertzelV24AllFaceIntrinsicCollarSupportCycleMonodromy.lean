import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarSupportCycleCrossing
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelOrder

/-! The two exact orders on crossings shared by a collar discrepancy support
cycle and its remote facial-dual separator. -/

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

private theorem f2_ne_zero_iff_eq_one (value : F2) :
    value ≠ 0 ↔ value = 1 := by
  constructor
  · intro hvalue
    fin_cases value
    · exact False.elim (hvalue rfl)
    · rfl
  · intro hvalue
    rw [hvalue]
    exact one_ne_zero

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open RotationOrderedFusionEscapeColorState

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

/-- The crossed primal edges, with their ambient `Sym2` values exposed. -/
def crossingSym2Finset
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) : Finset (Sym2 V) :=
  cycle.crossingEdges.image Subtype.val

/-- Common crossings in the order inherited from a primal support cycle. -/
def supportCrossingOrder
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} (supportCycle : G.Walk root root) : List (Sym2 V) :=
  supportCycle.edges.filter fun edge =>
    edge ∈ cycle.crossingSym2Finset

/-- All remote crossings in the order inherited from the facial-dual
cycle. -/
def remoteCrossingWord
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) : List (Sym2 V) :=
  List.ofFn fun step : Fin cycle.walk.length =>
    (cycle.crossingAt step : Sym2 V)

/-- Common crossings in remote facial-dual order. -/
def remoteSupportCrossingOrder
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} (supportCycle : G.Walk root root) : List (Sym2 V) :=
  cycle.remoteCrossingWord.filter fun edge =>
    edge ∈ supportCycle.edges

/-- Indexed remote-cycle steps whose crossed primal edge lies on the
chosen support cycle. -/
def supportCrossingStepFinset
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} (supportCycle : G.Walk root root) :
    Finset (Fin cycle.walk.length) :=
  Finset.univ.filter fun step =>
    (cycle.crossingAt step : Sym2 V) ∈ supportCycle.edges

/-- Filtering the indexed remote word counts exactly the supported remote
steps. -/
theorem remoteSupportCrossingOrder_length_eq_stepFinset_card
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} (supportCycle : G.Walk root root) :
    (cycle.remoteSupportCrossingOrder supportCycle).length =
      (cycle.supportCrossingStepFinset supportCycle).card := by
  change
    ((List.ofFn fun step : Fin cycle.walk.length =>
      (cycle.crossingAt step : Sym2 V)).filter fun edge =>
        edge ∈ supportCycle.edges).length =
      (Finset.univ.filter fun step : Fin cycle.walk.length =>
        (cycle.crossingAt step : Sym2 V) ∈ supportCycle.edges).card
  change
    (Multiset.filter (fun edge : Sym2 V => edge ∈ supportCycle.edges)
      (↑(List.ofFn fun step : Fin cycle.walk.length =>
        (cycle.crossingAt step : Sym2 V)) : Multiset (Sym2 V))).card =
      ((Finset.univ.filter fun step : Fin cycle.walk.length =>
        (cycle.crossingAt step : Sym2 V) ∈ supportCycle.edges).val).card
  rw [Finset.filter_val, ← Fin.univ_val_map, Multiset.filter_map,
    Multiset.card_map]
  rfl

@[simp] theorem mem_supportCrossingOrder_iff
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} (supportCycle : G.Walk root root) (edge : Sym2 V) :
    edge ∈ cycle.supportCrossingOrder supportCycle ↔
      edge ∈ supportCycle.edges ∧
        edge ∈ cycle.crossingSym2Finset := by
  simp [supportCrossingOrder]

@[simp] theorem mem_remoteCrossingWord_iff
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (edge : Sym2 V) :
    edge ∈ cycle.remoteCrossingWord ↔
      edge ∈ cycle.crossingSym2Finset := by
  simp only [remoteCrossingWord, List.mem_ofFn, crossingSym2Finset,
    Finset.mem_image]
  constructor
  · rintro ⟨step, rfl⟩
    refine ⟨cycle.crossingAt step, ?_, rfl⟩
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk (cycle.crossingAt step)).2 ⟨step, rfl⟩
  · rintro ⟨crossing, hcrossing, rfl⟩
    rcases (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk crossing).1 hcrossing with ⟨step, hstep⟩
    exact ⟨step, congrArg Subtype.val hstep⟩

@[simp] theorem mem_remoteSupportCrossingOrder_iff
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} (supportCycle : G.Walk root root) (edge : Sym2 V) :
    edge ∈ cycle.remoteSupportCrossingOrder supportCycle ↔
      edge ∈ supportCycle.edges ∧
        edge ∈ cycle.crossingSym2Finset := by
  simp [remoteSupportCrossingOrder, and_comm]

/-- A simple remote dual cycle crosses distinct primal edges in its cyclic
step order. -/
theorem remoteCrossingWord_nodup
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) :
    cycle.remoteCrossingWord.Nodup := by
  rw [remoteCrossingWord, List.nodup_ofFn]
  intro first second hedges
  apply dualWalkCrossingEdge_injective_of_isCycle
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
    (orbitFace_incidence_le_two graphData.toRotationSystem)
    (pairwiseUniqueSharedInteriorEdges graphData minimal)
    cycle.walk cycle.isCycle
  exact Subtype.ext hedges

theorem supportCrossingOrder_nodup
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} {supportCycle : G.Walk root root}
    (hsupportCycle : supportCycle.IsCycle) :
    (cycle.supportCrossingOrder supportCycle).Nodup := by
  exact hsupportCycle.edges_nodup.filter _

theorem remoteSupportCrossingOrder_nodup
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} (supportCycle : G.Walk root root) :
    (cycle.remoteSupportCrossingOrder supportCycle).Nodup := by
  exact cycle.remoteCrossingWord_nodup.filter _

/-- A primal simple cycle meets the remote facial-dual cycle in an even
number of indexed crossings. -/
theorem supportCrossingStepFinset_card_even
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} {supportCycle : G.Walk root root}
    (hsupportCycle : supportCycle.IsCycle) :
    Even (cycle.supportCrossingStepFinset supportCycle).card := by
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Connected :=
    orbitFaceInteriorDual_connected graphData.toRotationSystem
      minimal.spherical.cubic minimal.primalConnected
      minimal.vertexRotationCyclic
  have hsum :
      (∑ step : Fin cycle.walk.length,
        walkEdgeParity supportCycle (cycle.crossingAt step)) = 0 := by
    simpa [crossingAt] using
      (GoertzelV24DualCycleSeparator.f2CycleSpace_sum_crossings_eq_zero_of_dualCycle
        graphData minimal.facesTwoSided hdual hconnected minimal.spherical
        (pairwiseUniqueSharedInteriorEdges graphData minimal)
        cycle.walk cycle.isCycle
        (walkEdgeParity_mem_f2CycleSpace_of_closed supportCycle))
  have hsum' :
      (∑ step ∈ (Finset.univ : Finset (Fin cycle.walk.length)),
        walkEdgeParity supportCycle (cycle.crossingAt step)) = 0 := by
    simpa using hsum
  have heven := filter_ne_zero_card_even_of_f2_sum_eq_zero
    (Finset.univ : Finset (Fin cycle.walk.length))
    (fun step => walkEdgeParity supportCycle (cycle.crossingAt step)) hsum'
  have hfilter :
      (Finset.univ.filter fun step : Fin cycle.walk.length =>
        walkEdgeParity supportCycle (cycle.crossingAt step) ≠ 0) =
      cycle.supportCrossingStepFinset supportCycle := by
    ext step
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      supportCrossingStepFinset]
    rw [f2_ne_zero_iff_eq_one,
      walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail
        hsupportCycle.isTrail]
  rw [hfilter] at heven
  exact heven

/-- The two orders enumerate exactly the same physical crossings. -/
theorem supportCrossingOrder_perm_remote
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} {supportCycle : G.Walk root root}
    (hsupportCycle : supportCycle.IsCycle) :
    (cycle.supportCrossingOrder supportCycle).Perm
      (cycle.remoteSupportCrossingOrder supportCycle) := by
  apply (List.perm_ext_iff_of_nodup
    (cycle.supportCrossingOrder_nodup hsupportCycle)
    (cycle.remoteSupportCrossingOrder_nodup supportCycle)).2
  intro edge
  rw [cycle.mem_supportCrossingOrder_iff,
    cycle.mem_remoteSupportCrossingOrder_iff]

/-- The common crossing list has even length, independently of which of
its two cyclic orders is used. -/
theorem supportCrossingOrder_length_even
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} {supportCycle : G.Walk root root}
    (hsupportCycle : supportCycle.IsCycle) :
    Even (cycle.supportCrossingOrder supportCycle).length := by
  have horders :=
    (cycle.supportCrossingOrder_perm_remote hsupportCycle).length_eq
  rw [horders,
    cycle.remoteSupportCrossingOrder_length_eq_stepFinset_card supportCycle]
  exact cycle.supportCrossingStepFinset_card_even hsupportCycle

/-- The common crossing width cannot exceed the length of the remote dual
cycle. -/
theorem supportCrossingOrder_length_le_walk_length
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} {supportCycle : G.Walk root root}
    (hsupportCycle : supportCycle.IsCycle) :
    (cycle.supportCrossingOrder supportCycle).length ≤
      cycle.walk.length := by
  calc
    (cycle.supportCrossingOrder supportCycle).length =
        (cycle.remoteSupportCrossingOrder supportCycle).length :=
      (cycle.supportCrossingOrder_perm_remote hsupportCycle).length_eq
    _ ≤ cycle.remoteCrossingWord.length :=
      List.length_filter_le _ _
    _ = cycle.walk.length := by simp [remoteCrossingWord]

/-- Identity on physical crossings transports support-cycle order to
remote facial-dual order. -/
def crossingOrderTransport
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {root : V} {supportCycle : G.Walk root root}
    (hsupportCycle : supportCycle.IsCycle) :
    OrderedListTransport
      (cycle.supportCrossingOrder supportCycle)
      (cycle.remoteSupportCrossingOrder supportCycle) where
  perm := cycle.supportCrossingOrder_perm_remote hsupportCycle
  firstNodup := cycle.supportCrossingOrder_nodup hsupportCycle

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
  CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
    rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}

/-- The geometric and coloring data carried by one scalar discrepancy
support cycle through an intrinsic singleton collar. -/
structure ScalarSupportCrossingState
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) where
  coordinate : Bool
  root : V
  supportCycle : G.Walk root root
  supportCycle_isCycle : supportCycle.IsCycle
  target_mem : (targetEdge : Sym2 V) ∈ supportCycle.edges
  otherCrossing : G.edgeSet
  otherCrossing_mem_remote : otherCrossing ∈ cycle.crossingEdges
  otherCrossing_ne_target : otherCrossing ≠ targetEdge
  otherCrossing_mem_support :
    (otherCrossing : Sym2 V) ∈ supportCycle.edges
  support_nonzero : ∀ edge : G.edgeSet,
    (edge : Sym2 V) ∈ supportCycle.edges →
      crossFaceCoordinate coordinate
        (alignedOneZeroDiscrepancy collar sourceEscape edge) ≠ 0

/-- Every intrinsic singleton collar and genuine source escape supplies a
scalar support crossing state. -/
theorem exists_scalarSupportCrossingState
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    Nonempty (ScalarSupportCrossingState collar sourceEscape) := by
  rcases collar.exists_scalarSupportCycle_with_other_remoteCrossing
      sourceEscape with
    ⟨coordinate, root, supportCycle, otherCrossing,
      hcycle, htarget, hotherRemote, hotherNe, hotherSupport,
      hnonzero⟩
  exact ⟨{
    coordinate := coordinate
    root := root
    supportCycle := supportCycle
    supportCycle_isCycle := hcycle
    target_mem := htarget
    otherCrossing := otherCrossing
    otherCrossing_mem_remote := hotherRemote
    otherCrossing_ne_target := hotherNe
    otherCrossing_mem_support := hotherSupport
    support_nonzero := hnonzero
  }⟩

variable {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}

namespace ScalarSupportCrossingState

variable (state : ScalarSupportCrossingState collar sourceEscape)

theorem target_mem_supportCrossingOrder :
    (targetEdge : Sym2 V) ∈
      cycle.supportCrossingOrder state.supportCycle := by
  apply (cycle.mem_supportCrossingOrder_iff state.supportCycle
    targetEdge).2
  refine ⟨state.target_mem, ?_⟩
  apply Finset.mem_image.2
  refine ⟨targetEdge, collar.targetCrossing, rfl⟩

theorem other_mem_supportCrossingOrder :
    (state.otherCrossing : Sym2 V) ∈
      cycle.supportCrossingOrder state.supportCycle := by
  apply (cycle.mem_supportCrossingOrder_iff state.supportCycle
    state.otherCrossing).2
  refine ⟨state.otherCrossing_mem_support, ?_⟩
  exact Finset.mem_image.2
    ⟨state.otherCrossing, state.otherCrossing_mem_remote, rfl⟩

/-- At least two physical crossings occur in both orders. -/
theorem two_le_supportCrossingOrder_length :
    2 ≤ (cycle.supportCrossingOrder state.supportCycle).length := by
  let crossings := cycle.supportCrossingOrder state.supportCycle
  have htarget : (targetEdge : Sym2 V) ∈ crossings :=
    state.target_mem_supportCrossingOrder
  have hother : (state.otherCrossing : Sym2 V) ∈ crossings :=
    state.other_mem_supportCrossingOrder
  have hne : (state.otherCrossing : Sym2 V) ≠
      (targetEdge : Sym2 V) := by
    intro hedges
    exact state.otherCrossing_ne_target (Subtype.ext hedges)
  have hsubset :
      ({(targetEdge : Sym2 V),
        (state.otherCrossing : Sym2 V)} : Finset (Sym2 V)) ⊆
        crossings.toFinset := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact List.mem_toFinset.2 htarget
    · exact List.mem_toFinset.2 hother
  have hcard := Finset.card_le_card hsubset
  rw [List.toFinset_card_of_nodup
    (cycle.supportCrossingOrder_nodup state.supportCycle_isCycle)] at hcard
  simpa [hne.symm] using hcard

/-- The finite order transport naturally attached to the chosen scalar
support cycle. -/
def orderTransport :
    OrderedListTransport
      (cycle.supportCrossingOrder state.supportCycle)
      (cycle.remoteSupportCrossingOrder state.supportCycle) :=
  cycle.crossingOrderTransport state.supportCycle_isCycle

theorem target_mem_remoteSupportCrossingOrder :
    (targetEdge : Sym2 V) ∈
      cycle.remoteSupportCrossingOrder state.supportCycle :=
  state.orderTransport.perm.mem_iff.mp
    state.target_mem_supportCrossingOrder

theorem other_mem_remoteSupportCrossingOrder :
    (state.otherCrossing : Sym2 V) ∈
      cycle.remoteSupportCrossingOrder state.supportCycle :=
  state.orderTransport.perm.mem_iff.mp
    state.other_mem_supportCrossingOrder

/-- The unique support-order position of the distinguished target
crossing. -/
def supportTargetPosition :
    Fin (cycle.supportCrossingOrder state.supportCycle).length :=
  (List.Nodup.getEquiv
    (cycle.supportCrossingOrder state.supportCycle)
    (cycle.supportCrossingOrder_nodup
      state.supportCycle_isCycle)).symm
    ⟨(targetEdge : Sym2 V), state.target_mem_supportCrossingOrder⟩

/-- The unique remote-order position of the same target crossing. -/
def remoteTargetPosition :
    Fin (cycle.remoteSupportCrossingOrder state.supportCycle).length :=
  (List.Nodup.getEquiv
    (cycle.remoteSupportCrossingOrder state.supportCycle)
    (cycle.remoteSupportCrossingOrder_nodup state.supportCycle)).symm
    ⟨(targetEdge : Sym2 V),
      state.target_mem_remoteSupportCrossingOrder⟩

/-- The unique support-order position of the certified second
crossing. -/
def supportOtherPosition :
    Fin (cycle.supportCrossingOrder state.supportCycle).length :=
  (List.Nodup.getEquiv
    (cycle.supportCrossingOrder state.supportCycle)
    (cycle.supportCrossingOrder_nodup
      state.supportCycle_isCycle)).symm
    ⟨(state.otherCrossing : Sym2 V),
      state.other_mem_supportCrossingOrder⟩

/-- The unique remote-order position of the certified second
crossing. -/
def remoteOtherPosition :
    Fin (cycle.remoteSupportCrossingOrder state.supportCycle).length :=
  (List.Nodup.getEquiv
    (cycle.remoteSupportCrossingOrder state.supportCycle)
    (cycle.remoteSupportCrossingOrder_nodup state.supportCycle)).symm
    ⟨(state.otherCrossing : Sym2 V),
      state.other_mem_remoteSupportCrossingOrder⟩

@[simp] theorem get_supportTargetPosition :
    (cycle.supportCrossingOrder state.supportCycle).get
        state.supportTargetPosition =
      (targetEdge : Sym2 V) := by
  let equivalence := List.Nodup.getEquiv
    (cycle.supportCrossingOrder state.supportCycle)
    (cycle.supportCrossingOrder_nodup state.supportCycle_isCycle)
  exact congrArg Subtype.val
    (equivalence.apply_symm_apply
      ⟨(targetEdge : Sym2 V), state.target_mem_supportCrossingOrder⟩)

@[simp] theorem get_remoteTargetPosition :
    (cycle.remoteSupportCrossingOrder state.supportCycle).get
        state.remoteTargetPosition =
      (targetEdge : Sym2 V) := by
  let equivalence := List.Nodup.getEquiv
    (cycle.remoteSupportCrossingOrder state.supportCycle)
    (cycle.remoteSupportCrossingOrder_nodup state.supportCycle)
  exact congrArg Subtype.val
    (equivalence.apply_symm_apply
      ⟨(targetEdge : Sym2 V),
        state.target_mem_remoteSupportCrossingOrder⟩)

@[simp] theorem get_supportOtherPosition :
    (cycle.supportCrossingOrder state.supportCycle).get
        state.supportOtherPosition =
      (state.otherCrossing : Sym2 V) := by
  let equivalence := List.Nodup.getEquiv
    (cycle.supportCrossingOrder state.supportCycle)
    (cycle.supportCrossingOrder_nodup state.supportCycle_isCycle)
  exact congrArg Subtype.val
    (equivalence.apply_symm_apply
      ⟨(state.otherCrossing : Sym2 V),
        state.other_mem_supportCrossingOrder⟩)

@[simp] theorem get_remoteOtherPosition :
    (cycle.remoteSupportCrossingOrder state.supportCycle).get
        state.remoteOtherPosition =
      (state.otherCrossing : Sym2 V) := by
  let equivalence := List.Nodup.getEquiv
    (cycle.remoteSupportCrossingOrder state.supportCycle)
    (cycle.remoteSupportCrossingOrder_nodup state.supportCycle)
  exact congrArg Subtype.val
    (equivalence.apply_symm_apply
      ⟨(state.otherCrossing : Sym2 V),
        state.other_mem_remoteSupportCrossingOrder⟩)

/-- Support-cycle crossing order rotated to begin at the target edge. -/
def targetRootedSupportOrder : List (Sym2 V) :=
  (cycle.supportCrossingOrder state.supportCycle).rotate
    state.supportTargetPosition.val

/-- Remote facial-dual crossing order rotated to begin at the same target
edge. -/
def targetRootedRemoteOrder : List (Sym2 V) :=
  (cycle.remoteSupportCrossingOrder state.supportCycle).rotate
    state.remoteTargetPosition.val

@[simp] theorem targetRootedSupportOrder_head? :
    state.targetRootedSupportOrder.head? =
      some (targetEdge : Sym2 V) := by
  rw [targetRootedSupportOrder,
    List.head?_rotate state.supportTargetPosition.isLt,
    List.getElem?_eq_getElem state.supportTargetPosition.isLt]
  exact congrArg some state.get_supportTargetPosition

@[simp] theorem targetRootedRemoteOrder_head? :
    state.targetRootedRemoteOrder.head? =
      some (targetEdge : Sym2 V) := by
  rw [targetRootedRemoteOrder,
    List.head?_rotate state.remoteTargetPosition.isLt,
    List.getElem?_eq_getElem state.remoteTargetPosition.isLt]
  exact congrArg some state.get_remoteTargetPosition

theorem targetRootedSupportOrder_nodup :
    state.targetRootedSupportOrder.Nodup := by
  rw [targetRootedSupportOrder, List.nodup_rotate]
  exact cycle.supportCrossingOrder_nodup state.supportCycle_isCycle

theorem targetRootedRemoteOrder_nodup :
    state.targetRootedRemoteOrder.Nodup := by
  rw [targetRootedRemoteOrder, List.nodup_rotate]
  exact cycle.remoteSupportCrossingOrder_nodup state.supportCycle

/-- Rooting both cyclic orders at the target preserves their exact common
entry set. -/
theorem targetRootedSupportOrder_perm_remote :
    state.targetRootedSupportOrder.Perm
      state.targetRootedRemoteOrder := by
  exact (List.rotate_perm
      (cycle.supportCrossingOrder state.supportCycle)
      state.supportTargetPosition.val).trans
    (state.orderTransport.perm.trans
      (List.rotate_perm
        (cycle.remoteSupportCrossingOrder state.supportCycle)
        state.remoteTargetPosition.val).symm)

/-- Target-rooted identity-on-crossings transport, with the arbitrary
linear starting-point ambiguity removed. -/
def targetRootedOrderTransport :
    OrderedListTransport state.targetRootedSupportOrder
      state.targetRootedRemoteOrder where
  perm := state.targetRootedSupportOrder_perm_remote
  firstNodup := state.targetRootedSupportOrder_nodup

theorem two_le_targetRootedSupportOrder_length :
    2 ≤ state.targetRootedSupportOrder.length := by
  simpa [targetRootedSupportOrder] using
    state.two_le_supportCrossingOrder_length

theorem targetRootedSupportOrder_length_even :
    Even state.targetRootedSupportOrder.length := by
  simpa [targetRootedSupportOrder] using
    cycle.supportCrossingOrder_length_even state.supportCycle_isCycle

/-- Position zero in the target-rooted support order. -/
def targetRootedSupportEntryPosition :
    Fin state.targetRootedSupportOrder.length :=
  ⟨0, by
    have htwo := state.two_le_targetRootedSupportOrder_length
    omega⟩

/-- Position zero in the target-rooted remote order. -/
def targetRootedRemoteEntryPosition :
    Fin state.targetRootedRemoteOrder.length :=
  ⟨0, by
    have htwo := state.two_le_targetRootedSupportOrder_length
    have hlength := state.targetRootedSupportOrder_perm_remote.length_eq
    omega⟩

@[simp] theorem get_targetRootedSupportEntryPosition :
    state.targetRootedSupportOrder.get
        state.targetRootedSupportEntryPosition =
      (targetEdge : Sym2 V) := by
  rcases List.head?_eq_some_iff.mp
      state.targetRootedSupportOrder_head? with ⟨tail, htail⟩
  simp [targetRootedSupportEntryPosition, htail]

@[simp] theorem get_targetRootedRemoteEntryPosition :
    state.targetRootedRemoteOrder.get
        state.targetRootedRemoteEntryPosition =
      (targetEdge : Sym2 V) := by
  rcases List.head?_eq_some_iff.mp
      state.targetRootedRemoteOrder_head? with ⟨tail, htail⟩
  simp [targetRootedRemoteEntryPosition, htail]

/-- Rooted identity-on-crossings transport fixes the distinguished entry
position exactly. -/
theorem targetRootedOrderEquiv_entryPosition :
    state.targetRootedOrderTransport.orderEquiv
        state.targetRootedSupportEntryPosition =
      state.targetRootedRemoteEntryPosition := by
  apply state.targetRootedOrderTransport.secondNodup.get_inj_iff.mp
  calc
    state.targetRootedRemoteOrder.get
        (state.targetRootedOrderTransport.orderEquiv
          state.targetRootedSupportEntryPosition) =
        state.targetRootedSupportOrder.get
          state.targetRootedSupportEntryPosition :=
      state.targetRootedOrderTransport.orderEquiv_preserves_entry _
    _ = (targetEdge : Sym2 V) :=
      state.get_targetRootedSupportEntryPosition
    _ = state.targetRootedRemoteOrder.get
          state.targetRootedRemoteEntryPosition :=
      state.get_targetRootedRemoteEntryPosition.symm

/-- After target rooting, the crossing-order monodromy fixes position
zero.  Any nonidentity action is therefore carried by another physical
separator crossing. -/
theorem targetRootedMonodromy_entryPosition :
    state.targetRootedOrderTransport.monodromy
        state.targetRootedSupportEntryPosition =
      state.targetRootedSupportEntryPosition := by
  apply Fin.ext
  rw [OrderedListTransport.monodromy_apply_val,
    state.targetRootedOrderEquiv_entryPosition]
  rfl

/-- A target-rooted order permutation on at most two crossings is the
identity: position zero is fixed, leaving no freedom on the other
position. -/
theorem targetRootedMonodromy_eq_refl_of_length_le_two
    (hlength : state.targetRootedSupportOrder.length ≤ 2) :
    state.targetRootedOrderTransport.monodromy =
      Equiv.refl (Fin state.targetRootedSupportOrder.length) := by
  apply Equiv.ext
  intro position
  apply Fin.ext
  change
    (state.targetRootedOrderTransport.monodromy position : Nat) =
      (position : Nat)
  by_cases hentry : position = state.targetRootedSupportEntryPosition
  · rw [hentry, state.targetRootedMonodromy_entryPosition]
  · have hpositionNeZero : (position : Nat) ≠ 0 := by
      intro hzero
      apply hentry
      apply Fin.ext
      exact hzero
    have himageNeZero :
        (state.targetRootedOrderTransport.monodromy position : Nat) ≠
          0 := by
      intro hzero
      apply hentry
      apply state.targetRootedOrderTransport.monodromy.injective
      calc
        state.targetRootedOrderTransport.monodromy position =
            state.targetRootedSupportEntryPosition := by
          apply Fin.ext
          exact hzero
        _ = state.targetRootedOrderTransport.monodromy
              state.targetRootedSupportEntryPosition :=
          state.targetRootedMonodromy_entryPosition.symm
    have hpositionLt := position.isLt
    have himageLt :=
      (state.targetRootedOrderTransport.monodromy position).isLt
    omega

/-- Nontrivial target-rooted crossing monodromy needs at least four
physical crossings: the width is even, and widths two or less have no
remaining permutation freedom. -/
theorem four_le_length_of_targetRootedMonodromy_ne_refl
    (hmonodromy : state.targetRootedOrderTransport.monodromy ≠
      Equiv.refl (Fin state.targetRootedSupportOrder.length)) :
    4 ≤ state.targetRootedSupportOrder.length := by
  by_contra hfour
  have hleThree : state.targetRootedSupportOrder.length ≤ 3 := by
    omega
  rcases state.targetRootedSupportOrder_length_even with
    ⟨half, hhalf⟩
  have hleTwo : state.targetRootedSupportOrder.length ≤ 2 := by
    omega
  exact hmonodromy
    (state.targetRootedMonodromy_eq_refl_of_length_le_two hleTwo)

/-- A remote dual triangle cannot carry nontrivial target-rooted crossing
monodromy. -/
theorem targetRootedMonodromy_eq_refl_of_remote_length_le_three
    (hremote : cycle.walk.length ≤ 3) :
    state.targetRootedOrderTransport.monodromy =
      Equiv.refl (Fin state.targetRootedSupportOrder.length) := by
  by_contra hmonodromy
  have hfour :=
    state.four_le_length_of_targetRootedMonodromy_ne_refl hmonodromy
  have hwidth : state.targetRootedSupportOrder.length ≤
      cycle.walk.length := by
    simpa [targetRootedSupportOrder] using
      cycle.supportCrossingOrder_length_le_walk_length
        state.supportCycle_isCycle
  omega

/-- In the exact singleton primal-cut branch, target-rooted crossing
monodromy is necessarily trivial. -/
theorem targetRootedMonodromy_eq_refl_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile) :
    state.targetRootedOrderTransport.monodromy =
      Equiv.refl (Fin state.targetRootedSupportOrder.length) := by
  apply state.targetRootedMonodromy_eq_refl_of_remote_length_le_three
  rw [profile.length_eq_three]

/-- On a remote cycle of length at most four, any nontrivial rooted
monodromy uses exactly four crossings. -/
theorem targetRootedSupportOrder_length_eq_four_of_monodromy_ne_refl
    (hremote : cycle.walk.length ≤ 4)
    (hmonodromy : state.targetRootedOrderTransport.monodromy ≠
      Equiv.refl (Fin state.targetRootedSupportOrder.length)) :
    state.targetRootedSupportOrder.length = 4 := by
  have hfour :=
    state.four_le_length_of_targetRootedMonodromy_ne_refl hmonodromy
  have hwidth : state.targetRootedSupportOrder.length ≤
      cycle.walk.length := by
    simpa [targetRootedSupportOrder] using
      cycle.supportCrossingOrder_length_le_walk_length
        state.supportCycle_isCycle
  omega

/-- In the exact adjacent-pair primal-cut branch, nontrivial rooted
monodromy saturates all four available crossing positions. -/
theorem targetRootedSupportOrder_length_eq_four_of_adjacentPairPrimalCutProfile
    (profile : cycle.AdjacentPairPrimalCutProfile)
    (hmonodromy : state.targetRootedOrderTransport.monodromy ≠
      Equiv.refl (Fin state.targetRootedSupportOrder.length)) :
    state.targetRootedSupportOrder.length = 4 := by
  apply state.targetRootedSupportOrder_length_eq_four_of_monodromy_ne_refl
    (hmonodromy := hmonodromy)
  rw [profile.length_eq_four]

/-- Identity-on-crossings order transport sends the distinguished support
position to the distinguished remote position. -/
theorem orderEquiv_supportTargetPosition :
    state.orderTransport.orderEquiv state.supportTargetPosition =
      state.remoteTargetPosition := by
  apply state.orderTransport.secondNodup.get_inj_iff.mp
  calc
    (cycle.remoteSupportCrossingOrder state.supportCycle).get
        (state.orderTransport.orderEquiv state.supportTargetPosition) =
        (cycle.supportCrossingOrder state.supportCycle).get
          state.supportTargetPosition :=
      state.orderTransport.orderEquiv_preserves_entry _
    _ = (targetEdge : Sym2 V) := state.get_supportTargetPosition
    _ = (cycle.remoteSupportCrossingOrder state.supportCycle).get
          state.remoteTargetPosition := state.get_remoteTargetPosition.symm

/-- The same transport sends the certified second support position to its
remote position. -/
theorem orderEquiv_supportOtherPosition :
    state.orderTransport.orderEquiv state.supportOtherPosition =
      state.remoteOtherPosition := by
  apply state.orderTransport.secondNodup.get_inj_iff.mp
  calc
    (cycle.remoteSupportCrossingOrder state.supportCycle).get
        (state.orderTransport.orderEquiv state.supportOtherPosition) =
        (cycle.supportCrossingOrder state.supportCycle).get
          state.supportOtherPosition :=
      state.orderTransport.orderEquiv_preserves_entry _
    _ = (state.otherCrossing : Sym2 V) :=
      state.get_supportOtherPosition
    _ = (cycle.remoteSupportCrossingOrder state.supportCycle).get
          state.remoteOtherPosition := state.get_remoteOtherPosition.symm

theorem supportOtherPosition_ne_target :
    state.supportOtherPosition ≠ state.supportTargetPosition := by
  intro hpositions
  apply state.otherCrossing_ne_target
  apply Subtype.ext
  rw [← state.get_supportOtherPosition,
    hpositions, state.get_supportTargetPosition]

theorem remoteOtherPosition_ne_target :
    state.remoteOtherPosition ≠ state.remoteTargetPosition := by
  intro hpositions
  apply state.otherCrossing_ne_target
  apply Subtype.ext
  rw [← state.get_remoteOtherPosition,
    hpositions, state.get_remoteTargetPosition]

/-- The crossing-order monodromy compares the two linearizations on the
common finite crossing set. -/
def monodromy :
    Equiv.Perm
      (Fin (cycle.supportCrossingOrder state.supportCycle).length) :=
  state.orderTransport.monodromy

@[simp] theorem monodromy_supportTargetPosition_val :
    (state.monodromy state.supportTargetPosition : Nat) =
      (state.remoteTargetPosition : Nat) := by
  rw [monodromy, OrderedListTransport.monodromy_apply_val,
    state.orderEquiv_supportTargetPosition]

@[simp] theorem monodromy_supportOtherPosition_val :
    (state.monodromy state.supportOtherPosition : Nat) =
      (state.remoteOtherPosition : Nat) := by
  rw [monodromy, OrderedListTransport.monodromy_apply_val,
    state.orderEquiv_supportOtherPosition]

end ScalarSupportCrossingState

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
