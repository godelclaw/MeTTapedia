import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarSignedSupportParity

/-!
# Orientation gauge of singleton signed-support monodromy

The scalar support cycle used by the intrinsic-collar construction is an
unoriented geometric cycle represented by an oriented walk.  Reversing that
walk preserves all support and nonvanishing data.  This file makes that gauge
change explicit before any local odd monodromy is promoted to an ambient
observable.
-/

set_option autoImplicit false

namespace List

universe u

variable {Alpha : Type u}

/-- Two two-letter words with the same first letter and the same underlying
entries are equal. -/
theorem eq_of_length_eq_two_of_perm_of_head?_eq
    {first second : List Alpha}
    (hfirstLength : first.length = 2)
    (hsecondLength : second.length = 2)
    (hperm : first.Perm second)
    (hhead : first.head? = second.head?) :
    first = second := by
  rcases List.length_eq_two.mp hfirstLength with ⟨a, b, rfl⟩
  rcases List.length_eq_two.mp hsecondLength with ⟨c, d, rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst c
  simp only [List.perm_cons] at hperm
  have : b = d := by
    simpa using hperm
  subst d
  rfl

/-- Reading an entry commutes with transporting its finite index along an
equality of lists. -/
theorem get_cast_eq_of_eq {first second : List Alpha}
    (h : first = second) (position : Fin second.length) :
    first.get (Fin.cast (congrArg List.length h).symm position) =
      second.get position := by
  subst second
  rfl

end List

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} {Graph : SimpleGraph Vertex}

/-- A trail traverses a given unoriented edge in at most one orientation. -/
theorem IsTrail.dart_eq_of_mem_darts_of_edge_eq
    {left right : Vertex} {walk : Graph.Walk left right}
    (htrail : walk.IsTrail)
    {first second : Graph.Dart}
    (hfirst : first ∈ walk.darts)
    (hsecond : second ∈ walk.darts)
    (hedge : first.edge = second.edge) :
    first = second := by
  rcases List.mem_iff_get.mp hfirst with ⟨firstPosition, hfirstGet⟩
  rcases List.mem_iff_get.mp hsecond with ⟨secondPosition, hsecondGet⟩
  rw [← hfirstGet, ← hsecondGet] at hedge
  have hedgeGet :
      walk.edges.get (Fin.cast (by simp) firstPosition) =
        walk.edges.get (Fin.cast (by simp) secondPosition) := by
    simpa [SimpleGraph.Walk.edges] using hedge
  have hpositions :
      (Fin.cast (by simp) firstPosition : Fin walk.edges.length) =
        Fin.cast (by simp) secondPosition :=
    htrail.edges_nodup.get_inj_iff.mp hedgeGet
  have : firstPosition = secondPosition := by
    apply Fin.ext
    simpa using congrArg Fin.val hpositions
  subst secondPosition
  exact hfirstGet.symm.trans hsecondGet

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalFaceIntersections
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24TwoEdgeCutMinimality
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

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
namespace IntrinsicShortTargetEscapeCollar
namespace ScalarSupportCrossingState

variable
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}
  {rebaseCircuit :
    CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
  {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}

variable (state : ScalarSupportCrossingState collar sourceEscape)

/-- Reversing the arbitrarily oriented scalar support cycle preserves the
complete crossing-state certificate. -/
def reverseSupport : ScalarSupportCrossingState collar sourceEscape where
  coordinate := state.coordinate
  root := state.root
  supportCycle := state.supportCycle.reverse
  supportCycle_isCycle := state.supportCycle_isCycle.reverse
  target_mem := by
    simpa using state.target_mem
  otherCrossing := state.otherCrossing
  otherCrossing_mem_remote := state.otherCrossing_mem_remote
  otherCrossing_ne_target := state.otherCrossing_ne_target
  otherCrossing_mem_support := by
    simpa using state.otherCrossing_mem_support
  support_nonzero := by
    intro edge hedge
    apply state.support_nonzero edge
    simpa using hedge

@[simp] theorem reverseSupport_supportCycle :
    state.reverseSupport.supportCycle = state.supportCycle.reverse :=
  rfl

@[simp] theorem reverseSupport_otherCrossing :
    state.reverseSupport.otherCrossing = state.otherCrossing :=
  rfl

/-- Reversal reverses the order in which the support cycle meets the
remote separator. -/
@[simp] theorem supportCrossingOrder_reverseSupport :
    cycle.supportCrossingOrder state.reverseSupport.supportCycle =
      (cycle.supportCrossingOrder state.supportCycle).reverse := by
  change
    state.supportCycle.reverse.edges.filter
        (fun edge => edge ∈ cycle.crossingSym2Finset) =
      (state.supportCycle.edges.filter
        (fun edge => edge ∈ cycle.crossingSym2Finset)).reverse
  rw [SimpleGraph.Walk.edges_reverse, List.filter_reverse]

/-- The remote order only uses the unoriented edge set of the support
cycle, so reversing the support orientation leaves it unchanged. -/
@[simp] theorem remoteSupportCrossingOrder_reverseSupport :
    cycle.remoteSupportCrossingOrder state.reverseSupport.supportCycle =
      cycle.remoteSupportCrossingOrder state.supportCycle := by
  change
    cycle.remoteCrossingWord.filter
        (fun edge => edge ∈ state.supportCycle.reverse.edges) =
      cycle.remoteCrossingWord.filter
        (fun edge => edge ∈ state.supportCycle.edges)
  rw [SimpleGraph.Walk.edges_reverse]
  simp only [List.mem_reverse]

/-- Reversing the support orientation preserves the unordered set of
target-rooted crossing entries. -/
theorem targetRootedSupportOrder_perm_reverseSupport :
    state.reverseSupport.targetRootedSupportOrder.Perm
      state.targetRootedSupportOrder := by
  apply (List.rotate_perm
    (cycle.supportCrossingOrder state.reverseSupport.supportCycle)
    state.reverseSupport.supportTargetPosition.val).trans
  rw [state.supportCrossingOrder_reverseSupport]
  exact (List.reverse_perm _).trans
    (List.rotate_perm
      (cycle.supportCrossingOrder state.supportCycle)
      state.supportTargetPosition.val).symm

/-- In the singleton branch there are only two crossings, so rooting at the
target removes the residual reversal of their cyclic order. -/
theorem targetRootedSupportOrder_reverseSupport_eq_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile) :
    state.reverseSupport.targetRootedSupportOrder =
      state.targetRootedSupportOrder := by
  apply List.eq_of_length_eq_two_of_perm_of_head?_eq
    (state.reverseSupport.targetRootedSupportOrder_length_eq_two_of_singletonPrimalCutProfile
      profile)
    (state.targetRootedSupportOrder_length_eq_two_of_singletonPrimalCutProfile
      profile)
    state.targetRootedSupportOrder_perm_reverseSupport
  rw [state.reverseSupport.targetRootedSupportOrder_head?,
    state.targetRootedSupportOrder_head?]

/-- The position on the reversed support orientation corresponding to a
position in the original target-rooted two-crossing order. -/
def reverseTargetRootedPosition
    (profile : cycle.SingletonPrimalCutProfile)
    (position : Fin state.targetRootedSupportOrder.length) :
    Fin state.reverseSupport.targetRootedSupportOrder.length :=
  Fin.cast
    (congrArg List.length
      (state.targetRootedSupportOrder_reverseSupport_eq_of_singletonPrimalCutProfile
        profile)).symm
    position

@[simp] theorem reverseTargetRootedPosition_val
    (profile : cycle.SingletonPrimalCutProfile)
    (position : Fin state.targetRootedSupportOrder.length) :
    (state.reverseTargetRootedPosition profile position).val = position.val :=
  rfl

/-- Corresponding rooted positions denote the same physical crossing. -/
theorem targetRootedCrossingValue_reverseSupport
    (profile : cycle.SingletonPrimalCutProfile)
    (position : Fin state.targetRootedSupportOrder.length) :
    state.reverseSupport.targetRootedCrossingValue
        (state.reverseTargetRootedPosition profile position) =
      state.targetRootedCrossingValue position := by
  unfold targetRootedCrossingValue reverseTargetRootedPosition
  exact List.get_cast_eq_of_eq
    (state.targetRootedSupportOrder_reverseSupport_eq_of_singletonPrimalCutProfile
      profile)
    position

/-- At a corresponding physical crossing, reversing the support cycle
reverses its oriented dart. -/
theorem supportDartAt_reverseSupport
    (profile : cycle.SingletonPrimalCutProfile)
    (position : Fin state.targetRootedSupportOrder.length) :
    state.reverseSupport.supportDartAt
        (state.reverseTargetRootedPosition profile position) =
      (state.supportDartAt position).symm := by
  let reversePosition := state.reverseTargetRootedPosition profile position
  have horiginalMem :
      state.supportDartAt position ∈ state.supportCycle.darts := by
    exact List.get_mem _ _
  have hreverseMem :
      state.reverseSupport.supportDartAt reversePosition ∈
        state.supportCycle.reverse.darts := by
    exact List.get_mem _ _
  have hreverseSymmMem :
      (state.reverseSupport.supportDartAt reversePosition).symm ∈
        state.supportCycle.darts :=
    (SimpleGraph.Walk.mem_darts_reverse).1 hreverseMem
  have hedge :
      (state.reverseSupport.supportDartAt reversePosition).symm.edge =
        (state.supportDartAt position).edge := by
    rw [SimpleGraph.Dart.edge_symm,
      state.reverseSupport.supportDartAt_edge,
      state.supportDartAt_edge]
    exact state.targetRootedCrossingValue_reverseSupport profile position
  have hsymm := state.supportCycle_isCycle.isTrail
    |>.dart_eq_of_mem_darts_of_edge_eq hreverseSymmMem horiginalMem hedge
  have := congrArg SimpleGraph.Dart.symm hsymm
  simpa [reversePosition] using this

/-- Corresponding positions also define equal ambient graph edges. -/
theorem targetRootedCrossingEdge_reverseSupport
    (profile : cycle.SingletonPrimalCutProfile)
    (position : Fin state.targetRootedSupportOrder.length) :
    state.reverseSupport.targetRootedCrossingEdge
        (state.reverseTargetRootedPosition profile position) =
      state.targetRootedCrossingEdge position := by
  apply Subtype.ext
  exact state.targetRootedCrossingValue_reverseSupport profile position

/-- The facial-dual step is independent of the chosen orientation of the
primal support cycle. -/
theorem remoteStepAt_reverseSupport
    (profile : cycle.SingletonPrimalCutProfile)
    (position : Fin state.targetRootedSupportOrder.length) :
    state.reverseSupport.remoteStepAt
        (state.reverseTargetRootedPosition profile position) =
      state.remoteStepAt position := by
  apply dualWalkCrossingEdge_injective_of_isCycle
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
    (orbitFace_incidence_le_two graphData.toRotationSystem)
    (pairwiseUniqueSharedInteriorEdges graphData minimal)
    cycle.walk cycle.isCycle
  change cycle.crossingAt
      (state.reverseSupport.remoteStepAt
        (state.reverseTargetRootedPosition profile position)) =
    cycle.crossingAt (state.remoteStepAt position)
  rw [state.reverseSupport.crossingAt_remoteStepAt,
    state.crossingAt_remoteStepAt,
    state.targetRootedCrossingEdge_reverseSupport profile position]

/-- The remote-cycle dart is fixed when only the primal support orientation
is reversed. -/
theorem remoteDartAt_reverseSupport
    (profile : cycle.SingletonPrimalCutProfile)
    (position : Fin state.targetRootedSupportOrder.length) :
    state.reverseSupport.remoteDartAt
        (state.reverseTargetRootedPosition profile position) =
      state.remoteDartAt position := by
  unfold remoteDartAt
  rw [state.remoteStepAt_reverseSupport profile position]

/-- Reversing the support orientation toggles the chirality at every
physical crossing. -/
theorem targetRootedCrossingChirality_reverseSupport
    (profile : cycle.SingletonPrimalCutProfile)
    (position : Fin state.targetRootedSupportOrder.length) :
    state.reverseSupport.targetRootedCrossingChirality
        (state.reverseTargetRootedPosition profile position) =
      !state.targetRootedCrossingChirality position := by
  let reversePosition := state.reverseTargetRootedPosition profile position
  cases hchirality : state.targetRootedCrossingChirality position with
  | false =>
      have horiginalReverse : state.remoteDartAt position =
          (state.supportDartAt position).symm :=
        (state.targetRootedCrossingChirality_eq_false_iff position).1
          hchirality
      have hreverseSame : state.reverseSupport.remoteDartAt reversePosition =
          state.reverseSupport.supportDartAt reversePosition := by
        rw [state.remoteDartAt_reverseSupport profile position,
          state.supportDartAt_reverseSupport profile position]
        exact horiginalReverse
      have hnew :=
        (state.reverseSupport.targetRootedCrossingChirality_eq_true_iff
          reversePosition).2 hreverseSame
      simpa [hchirality, reversePosition] using hnew
  | true =>
      have horiginalSame : state.remoteDartAt position =
          state.supportDartAt position :=
        (state.targetRootedCrossingChirality_eq_true_iff position).1
          hchirality
      have hreverseOpposite :
          state.reverseSupport.remoteDartAt reversePosition =
            (state.reverseSupport.supportDartAt reversePosition).symm := by
        rw [state.remoteDartAt_reverseSupport profile position,
          state.supportDartAt_reverseSupport profile position,
          horiginalSame]
        simp
      have hnew :=
        (state.reverseSupport.targetRootedCrossingChirality_eq_false_iff
          reversePosition).2 hreverseOpposite
      simpa [hchirality, reversePosition] using hnew

/-- The unique negative crossing is not an unoriented ambient-edge charge:
reversing the same support cycle moves it to the other physical crossing. -/
theorem exists_distinct_negative_crossing_edges_of_orientation_reversal
    (profile : cycle.SingletonPrimalCutProfile) :
    ∃ originalNegative : Fin state.targetRootedSupportOrder.length,
      ∃ reversedNegative :
          Fin state.reverseSupport.targetRootedSupportOrder.length,
        state.targetRootedCrossingChirality originalNegative = false ∧
        state.reverseSupport.targetRootedCrossingChirality
            reversedNegative = false ∧
        state.reverseSupport.targetRootedCrossingEdge reversedNegative ≠
          state.targetRootedCrossingEdge originalNegative := by
  rcases
      state.exists_unique_targetRootedCrossingChirality_eq_false_of_singletonPrimalCutProfile
        profile with
    ⟨originalNegative, horiginalNegative, _horiginalUnique⟩
  rcases
      state.reverseSupport.exists_unique_targetRootedCrossingChirality_eq_false_of_singletonPrimalCutProfile
        profile with
    ⟨reversedNegative, hreversedNegative, _hreversedUnique⟩
  refine ⟨originalNegative, reversedNegative, horiginalNegative,
    hreversedNegative, ?_⟩
  intro hedges
  let corresponding :=
    state.reverseTargetRootedPosition profile originalNegative
  have hcorrespondingPositive :
      state.reverseSupport.targetRootedCrossingChirality corresponding =
        true := by
    have htoggle :=
      state.targetRootedCrossingChirality_reverseSupport
        profile originalNegative
    simpa [corresponding, horiginalNegative] using htoggle
  have hvalues :
      state.reverseSupport.targetRootedCrossingValue reversedNegative =
        state.reverseSupport.targetRootedCrossingValue corresponding := by
    have hphysical := congrArg Subtype.val hedges
    exact hphysical.trans
      (state.targetRootedCrossingValue_reverseSupport
        profile originalNegative).symm
  have hpositions : reversedNegative = corresponding :=
    state.reverseSupport.targetRootedSupportOrder_nodup.get_inj_iff.mp
      hvalues
  rw [hpositions, hcorrespondingPositive] at hreversedNegative
  exact Bool.noConfusion hreversedNegative

end ScalarSupportCrossingState
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

namespace GoertzelV24AllFaceIntrinsicCollarSignedSupportGauge

variable
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G}
  {rebaseCircuit :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.CrossCentralExactFaceCertifiedRebaseCircuit
      graphData minimal baseData}
  {cycle :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
      rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}

/-- Consumer-facing form of the orientation-gauge obstruction. -/
theorem negative_crossing_edge_depends_on_support_orientation
    (state : collar.ScalarSupportCrossingState sourceEscape)
    (profile : cycle.SingletonPrimalCutProfile) :
    ∃ originalNegative : Fin state.targetRootedSupportOrder.length,
      ∃ reversedNegative :
          Fin state.reverseSupport.targetRootedSupportOrder.length,
        state.targetRootedCrossingChirality originalNegative = false ∧
        state.reverseSupport.targetRootedCrossingChirality
            reversedNegative = false ∧
        state.reverseSupport.targetRootedCrossingEdge reversedNegative ≠
          state.targetRootedCrossingEdge originalNegative :=
  state.exists_distinct_negative_crossing_edges_of_orientation_reversal profile

end GoertzelV24AllFaceIntrinsicCollarSignedSupportGauge

end
end Mettapedia.GraphTheory.FourColor
