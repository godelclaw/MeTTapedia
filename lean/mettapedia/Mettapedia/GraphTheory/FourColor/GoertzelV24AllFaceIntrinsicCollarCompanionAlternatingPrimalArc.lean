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

variable {W : Type*} {H : SimpleGraph W}

/-- The first member of a positive walk's edge word is its first edge-set
member. -/
theorem edgeSubtypeSupport_head_eq_firstEdgeSet
    {start finish : W} (path : H.Walk start finish)
    (hpositive : 0 < path.length) :
    path.edgeSubtypeSupport.head
        (edgeSubtypeSupport_ne_nil_of_length_pos path hpositive) =
      path.firstEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive) := by
  cases path with
  | nil => simp at hpositive
  | cons edge tail =>
      simp [SimpleGraph.Walk.edgeSubtypeSupport,
        SimpleGraph.Walk.firstEdgeSet,
        SimpleGraph.Walk.firstDart]

/-- Copying only the endpoints of a positive walk preserves its first
edge-set member. -/
theorem firstEdgeSet_copy_eq
    {start finish start' finish' : W}
    (path : H.Walk start finish) (hstart : start = start')
    (hfinish : finish = finish') (hpositive : 0 < path.length) :
    (path.copy hstart hfinish).firstEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr (by
          simpa using hpositive)) =
      path.firstEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive) := by
  rw [← edgeSubtypeSupport_head_eq_firstEdgeSet
      (path.copy hstart hfinish) (by simpa using hpositive),
    ← edgeSubtypeSupport_head_eq_firstEdgeSet path hpositive]
  simp only [SimpleGraph.Walk.edgeSubtypeSupport,
    SimpleGraph.Walk.darts_copy]

/-- Copying only the endpoints of a positive walk preserves its last
edge-set member. -/
theorem lastEdgeSet_copy_eq
    {start finish start' finish' : W}
    (path : H.Walk start finish) (hstart : start = start')
    (hfinish : finish = finish') (hpositive : 0 < path.length) :
    (path.copy hstart hfinish).lastEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr (by
          simpa using hpositive)) =
      path.lastEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive) := by
  rw [← edgeSubtypeSupport_getLast_eq_lastEdgeSet
      (path.copy hstart hfinish) (by simpa using hpositive),
    ← edgeSubtypeSupport_getLast_eq_lastEdgeSet path hpositive]
  simp only [SimpleGraph.Walk.edgeSubtypeSupport,
    SimpleGraph.Walk.darts_copy]

/-- Option-valued first-edge form, avoiding any dependence on the proof of
positivity. -/
theorem edgeSubtypeSupport_head?_eq_some_firstEdgeSet
    {start finish : W} (path : H.Walk start finish)
    (hpositive : 0 < path.length) :
    path.edgeSubtypeSupport.head? =
      some (path.firstEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive)) := by
  calc
    path.edgeSubtypeSupport.head? =
        some (path.edgeSubtypeSupport.head
          (edgeSubtypeSupport_ne_nil_of_length_pos path hpositive)) :=
      List.head?_eq_some_head _
    _ = some (path.firstEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive)) :=
      congrArg some (edgeSubtypeSupport_head_eq_firstEdgeSet path hpositive)

/-- Option-valued last-edge form, avoiding any dependence on the proof of
positivity. -/
theorem edgeSubtypeSupport_getLast?_eq_some_lastEdgeSet
    {start finish : W} (path : H.Walk start finish)
    (hpositive : 0 < path.length) :
    path.edgeSubtypeSupport.getLast? =
      some (path.lastEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive)) := by
  calc
    path.edgeSubtypeSupport.getLast? =
        some (path.edgeSubtypeSupport.getLast
          (edgeSubtypeSupport_ne_nil_of_length_pos path hpositive)) :=
      List.getLast?_eq_some_getLast _
    _ = some (path.lastEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive)) :=
      congrArg some
        (edgeSubtypeSupport_getLast_eq_lastEdgeSet path hpositive)

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

/-- The normalized arc terminates through the first edge of its emitted
turn. -/
theorem primalArc_lastEdgeSet_eq_nextFirst :
    firstTurn.primalArc.lastEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr
          firstTurn.primalArc_positive) =
      firstTurn.toScalarCompanionTurn.first := by
  rw [← edgeSubtypeSupport_getLast_eq_lastEdgeSet
    firstTurn.primalArc firstTurn.primalArc_positive]
  simp only [firstTurn.primalArc_edgeSubtypeSupport,
    firstTurn.supportArc_edgeSubtypeSupport]
  unfold straightEdgeWord
  simp only [List.map_append, List.map_singleton,
    List.getLast_append_singleton]
  rfl

/-- The normalized arc launches through the continuing old edge or the
transverse edge of its source turn. -/
theorem primalArc_firstEdgeSet_eq_incoming_or_third :
    firstTurn.primalArc.firstEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr
          firstTurn.primalArc_positive) = corner.incoming ∨
      firstTurn.primalArc.firstEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr
          firstTurn.primalArc_positive) = turn.third := by
  let strand := route.rootedAtLaunch
  have hstraight := firstTurn.straightEdgeWord_ne_nil
  have hcycle := strand.cycleEdgeWord_ne_nil
  have hhead : firstTurn.straightEdgeWord.head hstraight =
      strand.rootFirstSupportEdge := by
    rcases firstTurn.straightEdgeWord_isPrefix with ⟨suffix, heq⟩
    change firstTurn.straightEdgeWord.head hstraight =
      route.rootedAtLaunch.cycle.edgeSubtypeSupport.head _
    apply (List.head_eq_iff_head?_eq_some hstraight).2
    calc
      firstTurn.straightEdgeWord.head? =
          (firstTurn.straightEdgeWord ++ suffix).head? := by
        exact (List.head?_append_of_ne_nil _ hstraight).symm
      _ = route.rootedAtLaunch.cycle.edgeSubtypeSupport.head? :=
        congrArg List.head? heq
      _ = some (route.rootedAtLaunch.cycle.edgeSubtypeSupport.head _) :=
        List.head?_eq_some_head _
  have hfirst : firstTurn.primalArc.firstEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr
          firstTurn.primalArc_positive) =
      corner.supportEdgeAmbientEdge strand.rootFirstSupportEdge := by
    rw [← edgeSubtypeSupport_head_eq_firstEdgeSet
      firstTurn.primalArc firstTurn.primalArc_positive]
    simp only [firstTurn.primalArc_edgeSubtypeSupport,
      firstTurn.supportArc_edgeSubtypeSupport]
    rw [List.head_map]
    exact congrArg corner.supportEdgeAmbientEdge hhead
  have hroot : strand.rootFirstSupportEdge =
        corner.incomingSupportEdge ∨
      strand.rootFirstSupportEdge = corner.transverseSupportEdge := by
    have hmem : strand.rootFirstSupportEdge ∈
        ({strand.rootFirstSupportEdge, strand.rootLastSupportEdge} :
          Finset corner.complementarySupportGraph.edgeSet) :=
      Finset.mem_insert_self _ _
    rw [strand.rootEdges_pair_eq_launchEdges] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hroot with hroot | hroot
  · left
    rw [hfirst, hroot]
    rfl
  · right
    rw [hfirst, hroot]
    rfl

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
  witness : source.realizedTurn.NextTurnWitness
  target_eq_ofTurn : target = ofTurn witness.nextTurn
  path : collar.commonCore.Walk source.junction target.junction
  path_edgeSubtypeSupport_eq_witness :
    path.edgeSubtypeSupport = witness.interior.primalArc.edgeSubtypeSupport
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
  firstEdge_eq_sourceFirst_or_second_or_third :
    path.edgeSubtypeSupport.head? = some source.1.first ∨
      path.edgeSubtypeSupport.head? = some source.1.second ∨
      path.edgeSubtypeSupport.head? = some source.1.third
  lastEdge_eq_targetFirst :
    path.edgeSubtypeSupport.getLast? = some target.1.first

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
    witness := witness
    target_eq_ofTurn := rfl
    path := path
    path_edgeSubtypeSupport_eq_witness := ?_
    path_isPath := ?_
    path_positive := ?_
    junction_ne := hexact'.junction_ne
    coordinateSupport := ?_
    companionColor_isChain := ?_
    firstEdge_eq_sourceFirst_or_second_or_third := ?_
    lastEdge_eq_targetFirst := ?_ }⟩
  · simp only [path, SimpleGraph.Walk.edgeSubtypeSupport,
      SimpleGraph.Walk.darts_copy]
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
  · have hword : path.edgeSubtypeSupport =
        witness.interior.primalArc.edgeSubtypeSupport := by
      simp only [path, SimpleGraph.Walk.edgeSubtypeSupport,
        SimpleGraph.Walk.darts_copy]
    have hpathHead := congrArg List.head? hword
    have hhead := edgeSubtypeSupport_head?_eq_some_firstEdgeSet
      witness.interior.primalArc witness.interior.primalArc_positive
    rcases witness.interior.primalArc_firstEdgeSet_eq_incoming_or_third with
      hincoming | hthird
    · rcases witness.corner.orientation with horientation | horientation
      · left
        calc
          path.edgeSubtypeSupport.head? =
              witness.interior.primalArc.edgeSubtypeSupport.head? := hpathHead
          _ = some (witness.interior.primalArc.firstEdgeSet _) := hhead
          _ = some source.1.first := congrArg some <|
            hincoming.trans <| horientation.1.trans source.realizedTurn_first
      · right
        left
        calc
          path.edgeSubtypeSupport.head? =
              witness.interior.primalArc.edgeSubtypeSupport.head? := hpathHead
          _ = some (witness.interior.primalArc.firstEdgeSet _) := hhead
          _ = some source.1.second := congrArg some <|
            hincoming.trans <| horientation.1.trans source.realizedTurn_second
    · right
      right
      calc
        path.edgeSubtypeSupport.head? =
            witness.interior.primalArc.edgeSubtypeSupport.head? := hpathHead
        _ = some (witness.interior.primalArc.firstEdgeSet _) := hhead
        _ = some source.1.third := congrArg some <|
          hthird.trans source.realizedTurn_third
  · have hword : path.edgeSubtypeSupport =
        witness.interior.primalArc.edgeSubtypeSupport := by
      simp only [path, SimpleGraph.Walk.edgeSubtypeSupport,
        SimpleGraph.Walk.darts_copy]
    have hpathLast := congrArg List.getLast? hword
    have hlast := edgeSubtypeSupport_getLast?_eq_some_lastEdgeSet
      witness.interior.primalArc witness.interior.primalArc_positive
    calc
      path.edgeSubtypeSupport.getLast? =
          witness.interior.primalArc.edgeSubtypeSupport.getLast? := hpathLast
      _ = some (witness.interior.primalArc.lastEdgeSet _) := hlast
      _ = some witness.nextTurn.first := congrArg some
        witness.interior.primalArc_lastEdgeSet_eq_nextFirst
      _ = some (ofTurn witness.nextTurn).1.first := rfl

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
