import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortCommonDiscrepancy

/-! The finite balanced Kirchhoff-boundary state carried by an intrinsic-short
common core. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation
open scoped BigOperators

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

namespace IntrinsicShortTargetEscapeCollar

/-- Restrict the full Kirchhoff boundary operator to the named common-core
terminal interface. -/
def commonPortBoundaryLinearMap
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    (collar.commonCore.edgeSet → Color) →ₗ[F2]
      (collar.commonPortVertexFinset → Color) where
  toFun chain terminal :=
    vertexKirchhoffSum collar.commonCore chain terminal.1
  map_add' left right := by
    funext terminal
    unfold vertexKirchhoffSum
    exact Finset.sum_add_distrib
  map_smul' scalar chain := by
    funext terminal
    unfold vertexKirchhoffSum
    simp only [Pi.smul_apply]
    exact Finset.smul_sum.symm

@[simp]
theorem commonPortBoundaryLinearMap_apply
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (chain : collar.commonCore.edgeSet → Color)
    (terminal : collar.commonPortVertexFinset) :
    collar.commonPortBoundaryLinearMap chain terminal =
      vertexKirchhoffSum collar.commonCore chain terminal.1 :=
  rfl

/-- A common-core chain has no Kirchhoff boundary away from the named
terminal interface. -/
def HasCommonPortBoundary
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (chain : collar.commonCore.edgeSet → Color) : Prop :=
  ∀ vertex ∉ collar.commonPortVertexFinset,
    vertexKirchhoffSum collar.commonCore chain vertex = 0

/-- The actual intrinsic-short discrepancy has boundary only on the common
terminal interface. -/
theorem commonDiscrepancy_hasCommonPortBoundary
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.HasCommonPortBoundary
      (collar.commonDiscrepancy sourceEscape) := by
  intro vertex hvertex
  exact
    collar.vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_mem_commonPortVertexFinset
      sourceEscape vertex hvertex

/-- For chains supported at the same terminal interface, equality of the
finite boundary state is exactly the assertion that their difference is a
Kirchhoff circulation on the whole common core. -/
theorem commonPortBoundaryLinearMap_eq_iff_add_mem_kirchhoffSubmodule
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    {left right : collar.commonCore.edgeSet → Color}
    (hleft : collar.HasCommonPortBoundary left)
    (hright : collar.HasCommonPortBoundary right) :
    collar.commonPortBoundaryLinearMap left =
        collar.commonPortBoundaryLinearMap right ↔
      left + right ∈ kirchhoffSubmodule collar.commonCore Finset.univ := by
  constructor
  · intro hboundary
    rw [mem_kirchhoffSubmodule]
    intro vertex _hvertex
    unfold vertexKirchhoffSum
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    apply (add_eq_zero_iff_eq _ _).2
    change vertexKirchhoffSum collar.commonCore left vertex =
      vertexKirchhoffSum collar.commonCore right vertex
    by_cases hterminal : vertex ∈ collar.commonPortVertexFinset
    · have hvalue := congrFun hboundary
          (⟨vertex, hterminal⟩ : collar.commonPortVertexFinset)
      simpa only [commonPortBoundaryLinearMap_apply] using hvalue
    · rw [hleft vertex hterminal, hright vertex hterminal]
  · intro hflow
    funext terminal
    have hzero :=
      (mem_kirchhoffSubmodule.mp hflow) terminal.1 (Finset.mem_univ _)
    unfold vertexKirchhoffSum at hzero
    simp only [Pi.add_apply] at hzero
    rw [Finset.sum_add_distrib] at hzero
    exact (add_eq_zero_iff_eq _ _).1 hzero

/-- The affine fiber of the forced discrepancy is therefore an explicit
coset of the full common-core circulation submodule. -/
theorem commonPortBoundaryLinearMap_eq_commonDiscrepancy_iff
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    {chain : collar.commonCore.edgeSet → Color}
    (hchain : collar.HasCommonPortBoundary chain) :
    collar.commonPortBoundaryLinearMap chain =
        collar.commonPortBoundaryLinearMap
          (collar.commonDiscrepancy sourceEscape) ↔
      chain + collar.commonDiscrepancy sourceEscape ∈
        kirchhoffSubmodule collar.commonCore Finset.univ :=
  collar.commonPortBoundaryLinearMap_eq_iff_add_mem_kirchhoffSubmodule
    hchain (collar.commonDiscrepancy_hasCommonPortBoundary sourceEscape)

/-- Balanced terminal states are the finite interface words satisfying the
global parity law. -/
abbrev BalancedCommonPortBoundaryState
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :=
  {state : collar.commonPortVertexFinset → Color //
    ∑ terminal, state terminal = 0}

/-- The forced discrepancy determines a balanced finite boundary state. -/
def commonDiscrepancyBoundaryState
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.BalancedCommonPortBoundaryState := by
  refine ⟨collar.commonPortBoundaryLinearMap
      (collar.commonDiscrepancy sourceEscape), ?_⟩
  change (∑ terminal : collar.commonPortVertexFinset,
    vertexKirchhoffSum collar.commonCore
      (collar.commonDiscrepancy sourceEscape) terminal.1) = 0
  rw [← Finset.sum_subtype collar.commonPortVertexFinset
    (fun _ => Iff.rfl)]
  exact
    collar.sum_vertexKirchhoffSum_commonDiscrepancy_on_commonPortVertexFinset_eq_zero
      sourceEscape

@[simp]
theorem commonDiscrepancyBoundaryState_apply
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (terminal : collar.commonPortVertexFinset) :
    (collar.commonDiscrepancyBoundaryState sourceEscape).1 terminal =
      vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape) terminal.1 :=
  rfl

/-- The finite state is genuinely nonzero; the cross-base mismatch cannot be
absorbed into an internal circulation. -/
theorem commonDiscrepancyBoundaryState_ne_zero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    (collar.commonDiscrepancyBoundaryState sourceEscape).1 ≠ 0 := by
  rcases collar.commonDiscrepancyBoundarySupport_nonempty sourceEscape with
    ⟨vertex, hvertex⟩
  have hterminal :=
    collar.commonDiscrepancyBoundarySupport_subset_commonPortVertexFinset
      sourceEscape hvertex
  intro hzero
  have hvalue := congrFun hzero
    (⟨vertex, hterminal⟩ : collar.commonPortVertexFinset)
  simp only [commonDiscrepancyBoundaryState_apply, Pi.zero_apply] at hvalue
  have hnonzero : vertexKirchhoffSum collar.commonCore
      (collar.commonDiscrepancy sourceEscape) vertex ≠ 0 := by
    simpa only [commonDiscrepancyBoundarySupport, Finset.mem_filter,
      Finset.mem_univ, true_and] using hvertex
  exact hnonzero hvalue

/-- Global parity determines one terminal value from all the others, so the
variable-width interface has at most `4^7 = 16384` balanced color states. -/
theorem card_balancedCommonPortBoundaryState_le_16384
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Fintype.card collar.BalancedCommonPortBoundaryState ≤ 16384 := by
  classical
  have hterminalNonempty : Nonempty collar.commonPortVertexFinset :=
    Fintype.card_pos_iff.mp (by
      have hbounds := collar.commonPortVertexFinset_card_bounds
      rw [Fintype.card_coe]
      omega : 0 < Fintype.card collar.commonPortVertexFinset)
  let root : collar.commonPortVertexFinset :=
    Classical.choice hterminalNonempty
  letI : Fintype
      {terminal : collar.commonPortVertexFinset // terminal ≠ root} :=
    Subtype.fintype _
  let forgetRoot : collar.BalancedCommonPortBoundaryState →
      ({terminal : collar.commonPortVertexFinset // terminal ≠ root} →
        Color) :=
    fun state terminal => state.1 terminal.1
  have hforgetRoot : Function.Injective forgetRoot := by
    intro left right heq
    apply Subtype.ext
    funext terminal
    by_cases hroot : terminal = root
    · subst terminal
      have hleftBalance := left.2
      have hrightBalance := right.2
      rw [Fintype.sum_eq_add_sum_subtype_ne left.1 root] at hleftBalance
      rw [Fintype.sum_eq_add_sum_subtype_ne right.1 root] at hrightBalance
      have hrest :
          (∑ terminal : {terminal : collar.commonPortVertexFinset //
              terminal ≠ root}, left.1 terminal.1) =
            ∑ terminal : {terminal : collar.commonPortVertexFinset //
              terminal ≠ root}, right.1 terminal.1 := by
        exact congrArg (fun state => ∑ terminal, state terminal) heq
      exact ((add_eq_zero_iff_eq _ _).1 hleftBalance).trans
        (hrest.trans ((add_eq_zero_iff_eq _ _).1 hrightBalance).symm)
    · exact congrFun heq ⟨terminal, hroot⟩
  have hcomplementCard :
      Fintype.card {terminal : collar.commonPortVertexFinset //
        terminal ≠ root} ≤ 7 := by
    have hstrict :
        Fintype.card {terminal : collar.commonPortVertexFinset //
            terminal ≠ root} <
          Fintype.card collar.commonPortVertexFinset :=
      Fintype.card_subtype_lt (p := fun terminal => terminal ≠ root)
        (x := root) (by simp)
    have hupper := collar.card_commonPortVertexFinset_le_eight
    rw [Fintype.card_coe] at hstrict
    omega
  calc
    Fintype.card collar.BalancedCommonPortBoundaryState ≤
        Fintype.card
          ({terminal : collar.commonPortVertexFinset // terminal ≠ root} →
            Color) :=
      Fintype.card_le_of_injective forgetRoot hforgetRoot
    _ = 4 ^ Fintype.card
          {terminal : collar.commonPortVertexFinset // terminal ≠ root} := by
      simp only [Fintype.card_fun]
      have hcolor : Fintype.card Color = 4 := by decide
      rw [hcolor]
    _ ≤ 4 ^ 7 := Nat.pow_le_pow_right (by decide) hcomplementCard
    _ = 16384 := by norm_num

/-- The coarser eight-terminal count remains available for consumers that do
not use the parity coordinate elimination. -/
theorem card_balancedCommonPortBoundaryState_le_65536
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Fintype.card collar.BalancedCommonPortBoundaryState ≤ 65536 :=
  le_trans collar.card_balancedCommonPortBoundaryState_le_16384 (by norm_num)

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
