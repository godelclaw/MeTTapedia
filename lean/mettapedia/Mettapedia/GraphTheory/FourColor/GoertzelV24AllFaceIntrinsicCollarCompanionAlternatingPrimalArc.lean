import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingOrbit

/-! Oriented common-core arcs underlying exact alternating turn steps. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CorridorPumping
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

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

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}
  {coordinate : Bool}
  {turn : collar.ScalarCompanionTurn sourceEscape coordinate}
  {corner : turn.ComplementarySupportCorner}
  {route : corner.ClosedSupportRoute}

/-- Proof-independent companion label of a common-core edge in one scalar
coordinate. On a support edge this is the companion color of its exact
discrepancy state. -/
def commonCoreEdgeCompanionColor
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : Bool) (edge : collar.commonCore.edgeSet) : Color :=
  if collar.sourceCommonColoring sourceEscape edge =
      crossFaceZeroColor coordinate then
    collar.targetCommonColoring edge
  else
    collar.sourceCommonColoring sourceEscape edge

theorem ScalarCompanionTurn.ComplementarySupportCorner.supportEdgeColorState_companionColor
    (corner : turn.ComplementarySupportCorner)
    (edge : corner.complementarySupportGraph.edgeSet) :
    (corner.supportEdgeColorState edge).companionColor =
      collar.commonCoreEdgeCompanionColor sourceEscape (!coordinate)
        (corner.supportEdgeAmbientEdge edge) := rfl

namespace ScalarCompanionTurn.ComplementarySupportCorner.ClosedSupportRoute.FirstInteriorTransverseTurn

variable (firstTurn : route.FirstInteriorTransverseTurn)

/-- Number of primal edges traversed before the normalized first turn. -/
def turnPosition : Nat := firstTurn.interior.before.length + 1

/-- The normalized first turn occurs strictly before the rooted cycle
closes. -/
theorem turnPosition_lt_cycleLength :
    firstTurn.turnPosition < route.rootedAtLaunch.cycle.length := by
  have hlength := congrArg List.length firstTurn.interior.word_eq
  rw [route.rootedAtLaunch.cycle.edgeSubtypeSupport_length] at hlength
  simp only [List.length_append, List.length_cons] at hlength
  unfold turnPosition
  omega

/-- Initial support-graph walk from the launch junction to the normalized
first-turn junction. -/
noncomputable def supportArc :
    corner.complementarySupportGraph.Walk
      corner.complementarySupportJunction firstTurn.finishJunction :=
  (route.rootedAtLaunch.cycle.take firstTurn.turnPosition).copy rfl
    firstTurn.finishJunction_eq_getVert_and_ne_launch.1.symm

@[simp]
theorem supportArc_length :
    firstTurn.supportArc.length = firstTurn.turnPosition := by
  rw [supportArc, SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.take_length,
    min_eq_left (Nat.le_of_lt firstTurn.turnPosition_lt_cycleLength)]

theorem supportArc_positive : 0 < firstTurn.supportArc.length := by
  rw [firstTurn.supportArc_length]
  unfold turnPosition
  omega

/-- The edge word of the typed support arc is exactly the normalized
straight prefix selected at the first change. -/
theorem supportArc_edgeSubtypeSupport :
    firstTurn.supportArc.edgeSubtypeSupport =
      firstTurn.straightEdgeWord := by
  simp only [supportArc, SimpleGraph.Walk.edgeSubtypeSupport,
    SimpleGraph.Walk.darts_copy, SimpleGraph.Walk.darts_take,
    List.map_take]
  change List.take firstTurn.turnPosition
      route.rootedAtLaunch.cycle.edgeSubtypeSupport =
    firstTurn.straightEdgeWord
  rw [firstTurn.interior.word_eq]
  unfold turnPosition straightEdgeWord
  rw [List.take_length_add_append]
  change firstTurn.interior.before ++
      List.take (0 + 1)
        (firstTurn.interior.first :: firstTurn.interior.second ::
          firstTurn.interior.after) =
    firstTurn.interior.before ++ [firstTurn.interior.first]
  rw [List.take_succ_cons]
  rw [List.take_zero]

/-- The initial arc of the rooted simple support cycle is a simple path. -/
theorem supportArc_isPath : firstTurn.supportArc.IsPath := by
  rw [supportArc, SimpleGraph.Walk.isPath_copy]
  apply SimpleGraph.Walk.IsCycle.isPath_of_append_left
  · apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
    rw [SimpleGraph.Walk.drop_length]
    exact Nat.sub_pos_of_lt firstTurn.turnPosition_lt_cycleLength
  · simpa only [SimpleGraph.Walk.append_take_drop_eq] using
      route.rootedAtLaunch.cycle_isCycle

/-- The same oriented arc after forgetting the scalar-support predicate,
with endpoints rewritten as the canonical source and target turn
junctions. -/
noncomputable def primalArc :
    collar.commonCore.Walk turn.junction
      firstTurn.toScalarCompanionTurn.junction :=
  (firstTurn.supportArc.mapLe (scalarSupportGraph_le (fun edge =>
      crossFaceCoordinate (!coordinate)
        (collar.commonDiscrepancy sourceEscape edge)))).copy
    corner.complementarySupportJunction_eq_junction
    firstTurn.toScalarCompanionTurn_junction_eq_finishJunction.symm

@[simp]
theorem primalArc_length :
    firstTurn.primalArc.length = firstTurn.turnPosition := by
  calc
    firstTurn.primalArc.length = firstTurn.supportArc.length := by
      rw [primalArc, SimpleGraph.Walk.length_copy]
      calc
        (firstTurn.supportArc.mapLe _).length =
            (firstTurn.supportArc.mapLe _).edges.length :=
          (firstTurn.supportArc.mapLe _).length_edges.symm
        _ = firstTurn.supportArc.edges.length := congrArg List.length
          (SimpleGraph.Walk.edges_mapLe_eq_edges _ _)
        _ = firstTurn.supportArc.length := firstTurn.supportArc.length_edges
    _ = firstTurn.turnPosition := firstTurn.supportArc_length

theorem primalArc_positive : 0 < firstTurn.primalArc.length := by
  rw [firstTurn.primalArc_length]
  unfold turnPosition
  omega

theorem primalArc_isPath : firstTurn.primalArc.IsPath := by
  rw [primalArc, SimpleGraph.Walk.isPath_copy]
  exact firstTurn.supportArc_isPath.mapLe
    (scalarSupportGraph_le (fun edge =>
      crossFaceCoordinate (!coordinate)
        (collar.commonDiscrepancy sourceEscape edge)))

/-- Every edge of the primal arc remains in the complementary scalar
discrepancy support. -/
theorem primalArc_support :
    ∀ edge ∈ firstTurn.primalArc.edgeSubtypeSupport,
      crossFaceCoordinate (!coordinate)
        (collar.commonDiscrepancy sourceEscape edge) ≠ 0 := by
  intro edge hedge
  apply scalarSupportWalk_support
    (fun current => crossFaceCoordinate (!coordinate)
      (collar.commonDiscrepancy sourceEscape current))
    firstTurn.supportArc edge
  simpa only [primalArc, SimpleGraph.Walk.edgeSubtypeSupport,
    SimpleGraph.Walk.darts_copy]
    using hedge

/-- Forgetting the support predicate maps the exact support edge word to
the common-core edge word of the primal arc. -/
theorem primalArc_edgeSubtypeSupport :
    firstTurn.primalArc.edgeSubtypeSupport =
      firstTurn.supportArc.edgeSubtypeSupport.map
        corner.supportEdgeAmbientEdge := by
  apply (List.map_injective_iff.mpr Subtype.val_injective)
  calc
    firstTurn.primalArc.edgeSubtypeSupport.map Subtype.val =
        firstTurn.primalArc.edges :=
      firstTurn.primalArc.edgeSubtypeSupport_map_val
    _ = firstTurn.supportArc.edges := by
      simp only [primalArc, SimpleGraph.Walk.edges_copy,
        SimpleGraph.Walk.edges_mapLe_eq_edges]
    _ = firstTurn.supportArc.edgeSubtypeSupport.map Subtype.val :=
      firstTurn.supportArc.edgeSubtypeSupport_map_val.symm
    _ = (firstTurn.supportArc.edgeSubtypeSupport.map
          corner.supportEdgeAmbientEdge).map Subtype.val := by
      rw [List.map_map]
      apply List.map_congr_left
      intro edge _hedge
      exact supportEdgeAmbientEdge_val corner edge |>.symm

/-- The proof-independent companion label is constant along every
internal adjacency of the oriented primal arc. -/
theorem primalArc_companionColor_isChain :
    firstTurn.primalArc.edgeSubtypeSupport.IsChain
      (fun first second =>
        collar.commonCoreEdgeCompanionColor sourceEscape (!coordinate)
            first =
          collar.commonCoreEdgeCompanionColor sourceEscape (!coordinate)
            second) := by
  rw [firstTurn.primalArc_edgeSubtypeSupport,
    firstTurn.supportArc_edgeSubtypeSupport]
  rw [List.isChain_map]
  apply firstTurn.straightEdgeWord_isChain.imp
  intro first second heq
  simpa only [ScalarCompanionTurn.ComplementarySupportCorner.supportEdgeColorState_companionColor]
    using heq

end ScalarCompanionTurn.ComplementarySupportCorner.ClosedSupportRoute.FirstInteriorTransverseTurn

namespace ScalarCompanionTurnState

/-- Geometric content of one exact finite-state transition, expressed
entirely in the common core. -/
structure ExactPrimalArc
    (source target : collar.ScalarCompanionTurnState sourceEscape) where
  path : collar.commonCore.Walk source.junction target.junction
  path_isPath : path.IsPath
  path_positive : 0 < path.length
  junction_ne : target.junction ≠ source.junction
  coordinateSupport : ∀ edge ∈ path.edgeSubtypeSupport,
    crossFaceCoordinate (!source.1.coordinate)
      (collar.commonDiscrepancy sourceEscape edge) ≠ 0
  companionColor_isChain : path.edgeSubtypeSupport.IsChain
    (fun first second =>
      collar.commonCoreEdgeCompanionColor sourceEscape
          (!source.1.coordinate) first =
        collar.commonCoreEdgeCompanionColor sourceEscape
          (!source.1.coordinate) second)

/-- Every exact next-state proof contains a positive straight primal arc. -/
theorem IsExactNext.nonempty_exactPrimalArc
    {source target : collar.ScalarCompanionTurnState sourceEscape}
    (hexact : source.IsExactNext target) :
    Nonempty (ExactPrimalArc source target) := by
  rcases hexact with ⟨witness, rfl⟩
  let path : collar.commonCore.Walk source.junction
      (ofTurn witness.nextTurn).junction :=
    witness.interior.primalArc.copy rfl
      (ofTurn_junction witness.nextTurn).symm
  have hexact' : source.IsExactNext (ofTurn witness.nextTurn) :=
    ⟨witness, rfl⟩
  refine ⟨{
    path := path
    path_isPath := ?_
    path_positive := ?_
    junction_ne := hexact'.junction_ne
    coordinateSupport := ?_
    companionColor_isChain := ?_ }⟩
  · simp only [path, SimpleGraph.Walk.isPath_copy]
    exact witness.interior.primalArc_isPath
  · simp only [path, SimpleGraph.Walk.length_copy]
    exact witness.interior.primalArc_positive
  · intro edge hedge
    apply witness.interior.primalArc_support edge
    simpa only [path, SimpleGraph.Walk.edgeSubtypeSupport,
      SimpleGraph.Walk.darts_copy] using hedge
  · simpa only [path, SimpleGraph.Walk.edgeSubtypeSupport,
      SimpleGraph.Walk.darts_copy] using
      witness.interior.primalArc_companionColor_isChain

/-- A chosen geometric representative of an exact finite-state step. -/
noncomputable def IsExactNext.exactPrimalArc
    {source target : collar.ScalarCompanionTurnState sourceEscape}
    (hexact : source.IsExactNext target) : ExactPrimalArc source target :=
  Classical.choice hexact.nonempty_exactPrimalArc

/-- An exact relational transfer with every step replaced by its oriented
common-core primal arc. -/
inductive ExactPrimalArcTransfer :
    Nat → collar.ScalarCompanionTurnState sourceEscape →
      collar.ScalarCompanionTurnState sourceEscape → Prop where
  | zero (state : collar.ScalarCompanionTurnState sourceEscape) :
      ExactPrimalArcTransfer 0 state state
  | succ {length : Nat}
      {start next finish : collar.ScalarCompanionTurnState sourceEscape} :
      ExactPrimalArc start next →
      ExactPrimalArcTransfer length next finish →
      ExactPrimalArcTransfer (length + 1) start finish

/-- Exact next-state chains lift stepwise to oriented primal-arc chains. -/
theorem exactRelationalTransfer_toExactPrimalArcTransfer
    {length : Nat}
    {start finish : collar.ScalarCompanionTurnState sourceEscape}
    (transfer : ExactRelationalTransfer IsExactNext length start finish) :
    ExactPrimalArcTransfer length start finish := by
  induction transfer with
  | zero state => exact .zero state
  | succ hstep _htail ih =>
      exact .succ hstep.exactPrimalArc ih

/-- Concatenating a primal-arc transfer yields a typed common-core walk;
its length is at least the number of nonempty constituent arcs. -/
theorem ExactPrimalArcTransfer.exists_walk_length_ge
    {length : Nat}
    {start finish : collar.ScalarCompanionTurnState sourceEscape}
    (transfer : ExactPrimalArcTransfer length start finish) :
    ∃ walk : collar.commonCore.Walk start.junction finish.junction,
      length ≤ walk.length := by
  induction transfer with
  | zero state =>
      exact ⟨SimpleGraph.Walk.nil, Nat.le_refl 0⟩
  | @succ length start next finish first rest ih =>
      rcases ih with ⟨tail, htail⟩
      refine ⟨first.path.append tail, ?_⟩
      rw [SimpleGraph.Walk.length_append]
      have hfirst : 1 ≤ first.path.length := first.path_positive
      omega

/-- A recurrent alternating orbit therefore carries an exact even closed
primal junction itinerary of positive total length. -/
theorem AlternatingOrbitCertificate.exists_exact_even_primalJunctionItinerary
    {hnoAction : ¬ collar.HasChargedKempeReentry sourceEscape}
    {start : collar.ScalarCompanionTurnState sourceEscape}
    (certificate : AlternatingOrbitCertificate hnoAction start) :
    ∃ (entry : collar.ScalarCompanionTurnState sourceEscape)
        (period : Nat),
      2 ≤ period ∧ Even period ∧
        ExactPrimalArcTransfer period entry entry ∧
        ∃ walk : collar.commonCore.Walk entry.junction entry.junction,
          period ≤ walk.length ∧ ¬walk.Nil := by
  rcases certificate.exists_exact_even_return with
    ⟨entry, period, hperiod, heven, hreturn⟩
  let transfer := exactRelationalTransfer_toExactPrimalArcTransfer hreturn
  rcases transfer.exists_walk_length_ge with ⟨walk, hlength⟩
  refine ⟨entry, period, hperiod, heven, transfer, walk, hlength, ?_⟩
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
  omega

end ScalarCompanionTurnState

namespace ScalarCompanionTurn

/-- Global geometric dichotomy from a signed turn: either a charged Kempe
reentry is available, or the non-action dynamics produces a positive even
closed primal junction itinerary. -/
theorem hasChargedKempeReentry_or_exactEvenPrimalJunctionItinerary
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    collar.HasChargedKempeReentry sourceEscape ∨
      ∃ (entry : collar.ScalarCompanionTurnState sourceEscape)
          (period : Nat),
        2 ≤ period ∧ Even period ∧
          ScalarCompanionTurnState.ExactPrimalArcTransfer
            period entry entry ∧
          ∃ walk : collar.commonCore.Walk entry.junction entry.junction,
            period ≤ walk.length ∧ ¬walk.Nil := by
  rcases turn.hasChargedKempeReentry_or_alternatingOrbitCertificate with
    haction | ⟨_hnoAction, certificate⟩
  · exact Or.inl haction
  · exact Or.inr certificate.exists_exact_even_primalJunctionItinerary

end ScalarCompanionTurn
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
