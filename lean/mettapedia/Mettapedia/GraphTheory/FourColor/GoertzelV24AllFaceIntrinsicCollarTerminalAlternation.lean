import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarTerminalTrail

/-! Alternating-matching structure of the scalar discrepancy trail forced by
an intrinsic singleton collar. -/

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

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- The unique nonzero color whose selected binary coordinate vanishes. -/
def crossFaceZeroColor (coordinate : Bool) : Color :=
  if coordinate then red else blue

@[simp]
theorem crossFaceZeroColor_false : crossFaceZeroColor false = blue := by
  rfl

@[simp]
theorem crossFaceZeroColor_true : crossFaceZeroColor true = red := by
  rfl

theorem crossFaceZeroColor_ne_zero (coordinate : Bool) :
    crossFaceZeroColor coordinate ≠ 0 := by
  cases coordinate <;> simp [crossFaceZeroColor, red, blue]

/-- Among the three Tait colors, a coordinate vanishes precisely at its
distinguished zero-coordinate color. -/
theorem crossFaceCoordinate_eq_zero_iff_eq_crossFaceZeroColor
    (coordinate : Bool) (value : Color) (hvalue : value ≠ 0) :
    crossFaceCoordinate coordinate value = 0 ↔
      value = crossFaceZeroColor coordinate := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero value hvalue with
      rfl | rfl | rfl <;>
    cases coordinate <;>
      simp [crossFaceZeroColor, crossFaceCoordinate, red, blue, purple]

/-- A nonzero scalar discrepancy says exactly that one of two Tait colors,
but not the other, is the distinguished zero-coordinate color. -/
theorem crossFaceCoordinate_add_ne_zero_iff_exactlyOne_zeroColor
    (coordinate : Bool) (left right : Color)
    (hleft : left ≠ 0) (hright : right ≠ 0) :
    crossFaceCoordinate coordinate (left + right) ≠ 0 ↔
      (left = crossFaceZeroColor coordinate ∧
          right ≠ crossFaceZeroColor coordinate) ∨
        (left ≠ crossFaceZeroColor coordinate ∧
          right = crossFaceZeroColor coordinate) := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero left hleft with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero right hright with
      rfl | rfl | rfl <;>
      cases coordinate <;>
        simp [crossFaceZeroColor, crossFaceCoordinate, red, blue, purple]

omit [Fintype W] [DecidableEq W] [DecidableRel H.Adj] in
/-- Adjacent scalar-discrepancy edges alternate between the distinguished
color matching of the first coloring and that of the second coloring. -/
theorem discrepancySupport_adjacent_edges_alternate
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) {firstEdge secondEdge : H.edgeSet}
    (hadjacent : H.lineGraph.Adj firstEdge secondEdge)
    (hfirstSupport : crossFaceCoordinate coordinate
      (firstColoring firstEdge + secondColoring firstEdge) ≠ 0)
    (hsecondSupport : crossFaceCoordinate coordinate
      (firstColoring secondEdge + secondColoring secondEdge) ≠ 0) :
    (firstColoring firstEdge = crossFaceZeroColor coordinate ∧
        secondColoring firstEdge ≠ crossFaceZeroColor coordinate ∧
        firstColoring secondEdge ≠ crossFaceZeroColor coordinate ∧
        secondColoring secondEdge = crossFaceZeroColor coordinate) ∨
      (firstColoring firstEdge ≠ crossFaceZeroColor coordinate ∧
        secondColoring firstEdge = crossFaceZeroColor coordinate ∧
        firstColoring secondEdge = crossFaceZeroColor coordinate ∧
        secondColoring secondEdge ≠ crossFaceZeroColor coordinate) := by
  have hfirstClass :=
    (crossFaceCoordinate_add_ne_zero_iff_exactlyOne_zeroColor coordinate
      (firstColoring firstEdge) (secondColoring firstEdge)
      (hfirstTait firstEdge) (hsecondTait firstEdge)).1 hfirstSupport
  have hsecondClass :=
    (crossFaceCoordinate_add_ne_zero_iff_exactlyOne_zeroColor coordinate
      (firstColoring secondEdge) (secondColoring secondEdge)
      (hfirstTait secondEdge) (hsecondTait secondEdge)).1 hsecondSupport
  rcases hfirstClass with hfirstSource | hfirstTarget
  · rcases hsecondClass with hsecondSource | hsecondTarget
    · exact False.elim
        ((firstColoring.valid hadjacent)
          (hfirstSource.1.trans hsecondSource.1.symm))
    · exact Or.inl ⟨hfirstSource.1, hfirstSource.2,
        hsecondTarget.1, hsecondTarget.2⟩
  · rcases hsecondClass with hsecondSource | hsecondTarget
    · exact Or.inr ⟨hfirstTarget.1, hfirstTarget.2,
        hsecondSource.1, hsecondSource.2⟩
    · exact False.elim
        ((secondColoring.valid hadjacent)
          (hfirstTarget.2.trans hsecondTarget.2.symm))

/-- If an ambient vertex has degree at most three and a scalar chain obeys
Kirchhoff whenever that degree is three, its support has degree at most two. -/
theorem scalarSupportGraph_incidentCard_le_two
    (chain : H.edgeSet → F2) (vertex : W)
    (hambient : (incidentEdgeFinset H vertex).card ≤ 3)
    (hkirchhoff : (incidentEdgeFinset H vertex).card = 3 →
      scalarVertexKirchhoffSum H chain vertex = 0) :
    (incidentEdgeFinset (scalarSupportGraph chain) vertex).card ≤ 2 := by
  rw [scalarSupportGraph_incidentEdgeFinset_card]
  by_cases hsmall : (incidentEdgeFinset H vertex).card ≤ 2
  · exact le_trans (Finset.card_filter_le _ _) hsmall
  · have hcubic : (incidentEdgeFinset H vertex).card = 3 := by
      omega
    have heven : Even
        (((incidentEdgeFinset H vertex).filter
          fun edge => chain edge ≠ 0).card) := by
      apply filter_ne_zero_card_even_of_f2_sum_eq_zero
      exact hkirchhoff hcubic
    have hle :
        ((incidentEdgeFinset H vertex).filter
          fun edge => chain edge ≠ 0).card ≤ 3 := by
      exact le_trans (Finset.card_filter_le _ _) hambient
    rcases heven with ⟨multiple, hmultiple⟩
    omega

/-- A scalar coordinate of the discrepancy of two Tait colorings has
support degree at most two on every subcubic vertex. -/
theorem taitDiscrepancySupport_incidentCard_le_two
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) (vertex : W)
    (hsubcubic : (incidentEdgeFinset H vertex).card ≤ 3) :
    (incidentEdgeFinset
      (scalarSupportGraph (fun edge => crossFaceCoordinate coordinate
        (firstColoring edge + secondColoring edge))) vertex).card ≤ 2 := by
  apply scalarSupportGraph_incidentCard_le_two _ vertex hsubcubic
  intro hcubic
  have hfirstZero :=
    GoertzelV24TwoDefectParity.vertexKirchhoffSum_eq_zero_of_card_three
      firstColoring hfirstTait vertex hcubic
  have hsecondZero :=
    GoertzelV24TwoDefectParity.vertexKirchhoffSum_eq_zero_of_card_three
      secondColoring hsecondTait vertex hcubic
  rw [scalarVertexKirchhoffSum_crossFaceCoordinate]
  have hsum : vertexKirchhoffSum H
      (fun edge => firstColoring edge + secondColoring edge) vertex = 0 := by
    calc
      vertexKirchhoffSum H
          (fun edge => firstColoring edge + secondColoring edge) vertex =
          vertexKirchhoffSum H firstColoring vertex +
            vertexKirchhoffSum H secondColoring vertex := by
        unfold vertexKirchhoffSum
        exact Finset.sum_add_distrib
      _ = 0 := by rw [hfirstZero, hsecondZero, add_zero]
  rw [hsum]
  cases coordinate <;> rfl

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

/-- Every vertex of the exact four-vertex common deletion is subcubic. -/
theorem commonCore_incidentEdgeFinset_card_le_three
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (vertex : collar.commonCoreVertex) :
    (incidentEdgeFinset collar.commonCore vertex).card ≤ 3 := by
  by_cases hsource : ∃ sourcePort : Fin 4,
      vertex = collar.sourcePortInCommonCore sourcePort
  · rcases hsource with ⟨sourcePort, rfl⟩
    rw [collar.card_incidentEdgeFinset_sourcePortInCommonCore sourcePort]
    split <;> omega
  · by_cases htarget : ∃ targetPort : Fin 4,
        vertex = collar.targetPortInCommonCore targetPort
    · rcases htarget with ⟨targetPort, rfl⟩
      rw [collar.card_incidentEdgeFinset_targetPortInCommonCore targetPort]
      split <;> omega
    · have hsource' : ∀ sourcePort : Fin 4,
          vertex ≠ collar.sourcePortInCommonCore sourcePort := by
        intro sourcePort heq
        exact hsource ⟨sourcePort, heq⟩
      have htarget' : ∀ targetPort : Fin 4,
          vertex ≠ collar.targetPortInCommonCore targetPort := by
        intro targetPort heq
        exact htarget ⟨targetPort, heq⟩
      rw [collar.card_incidentEdgeFinset_commonCore_eq_three_of_not_ports
        vertex hsource' htarget']

/-- The coordinate support graph of the exact source/target discrepancy. -/
abbrev coordinateDiscrepancySupportGraph
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : Bool) : SimpleGraph collar.commonCoreVertex :=
  scalarSupportGraph (fun edge => crossFaceCoordinate coordinate
    (collar.commonDiscrepancy sourceEscape edge))

/-- The forced singleton terminal lies on a genuine alternating path between
the distinguished color matchings of the two exact common-core colorings.
Both endpoints have support degree one, every support vertex has degree at
most two, and adjacent path edges alternate between the two matchings. -/
theorem exists_singletonTerminal_alternatingSupportPath
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    ∃ (coordinate : Bool) (targetPort : Fin 4)
        (finish : collar.commonPortVertexFinset)
        (path : collar.commonCore.Walk
          (collar.targetPortInCommonCore targetPort) finish.1),
      boundaryDeletedVertex collar.targetData targetPort ∈
          collar.singletonCutProfile.component.supp ∧
        finish ≠ collar.targetPortCommonTerminal targetPort ∧
        path.IsPath ∧
        (incidentEdgeFinset
          (collar.coordinateDiscrepancySupportGraph sourceEscape coordinate)
          (collar.targetPortInCommonCore targetPort)).card = 1 ∧
        (incidentEdgeFinset
          (collar.coordinateDiscrepancySupportGraph sourceEscape coordinate)
          finish.1).card = 1 ∧
        (∀ vertex : collar.commonCoreVertex,
          (incidentEdgeFinset
            (collar.coordinateDiscrepancySupportGraph sourceEscape coordinate)
            vertex).card ≤ 2) ∧
        (∀ edge : collar.commonCore.edgeSet,
          (edge : Sym2 collar.commonCoreVertex) ∈ path.edges →
            (collar.sourceCommonColoring sourceEscape edge =
                crossFaceZeroColor coordinate ∧
              collar.targetCommonColoring edge ≠
                crossFaceZeroColor coordinate) ∨
            (collar.sourceCommonColoring sourceEscape edge ≠
                crossFaceZeroColor coordinate ∧
              collar.targetCommonColoring edge =
                crossFaceZeroColor coordinate)) ∧
        ∀ firstEdge secondEdge : collar.commonCore.edgeSet,
          (firstEdge : Sym2 collar.commonCoreVertex) ∈ path.edges →
          (secondEdge : Sym2 collar.commonCoreVertex) ∈ path.edges →
          collar.commonCore.lineGraph.Adj firstEdge secondEdge →
            (collar.sourceCommonColoring sourceEscape firstEdge =
                crossFaceZeroColor coordinate ∧
              collar.targetCommonColoring firstEdge ≠
                crossFaceZeroColor coordinate ∧
              collar.sourceCommonColoring sourceEscape secondEdge ≠
                crossFaceZeroColor coordinate ∧
              collar.targetCommonColoring secondEdge =
                crossFaceZeroColor coordinate) ∨
            (collar.sourceCommonColoring sourceEscape firstEdge ≠
                crossFaceZeroColor coordinate ∧
              collar.targetCommonColoring firstEdge =
                crossFaceZeroColor coordinate ∧
              collar.sourceCommonColoring sourceEscape secondEdge =
                crossFaceZeroColor coordinate ∧
              collar.targetCommonColoring secondEdge ≠
                crossFaceZeroColor coordinate) := by
  rcases collar.exists_singletonTerminal_coordinateSupportPath sourceEscape with
    ⟨coordinate, targetPort, finish, path, hinside, hfinishNe,
      hstartBoundary, hfinishBoundary, hpath, hpathSupport⟩
  let supportGraph :=
    collar.coordinateDiscrepancySupportGraph sourceEscape coordinate
  have hdegreeBound : ∀ vertex : collar.commonCoreVertex,
      (incidentEdgeFinset supportGraph vertex).card ≤ 2 := by
    intro vertex
    apply taitDiscrepancySupport_incidentCard_le_two
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait coordinate vertex
      (collar.commonCore_incidentEdgeFinset_card_le_three vertex)
  have hstartScalarBoundary : scalarVertexKirchhoffSum collar.commonCore
      (fun edge => crossFaceCoordinate coordinate
        (collar.commonDiscrepancy sourceEscape edge))
      (collar.targetPortInCommonCore targetPort) ≠ 0 := by
    rw [scalarVertexKirchhoffSum_crossFaceCoordinate]
    simpa only [commonDiscrepancyBoundaryState_apply,
      targetPortCommonTerminal] using hstartBoundary
  have hfinishScalarBoundary : scalarVertexKirchhoffSum collar.commonCore
      (fun edge => crossFaceCoordinate coordinate
        (collar.commonDiscrepancy sourceEscape edge)) finish.1 ≠ 0 := by
    rw [scalarVertexKirchhoffSum_crossFaceCoordinate]
    simpa only [commonDiscrepancyBoundaryState_apply] using hfinishBoundary
  have hstartOdd : Odd (supportGraph.degree
      (collar.targetPortInCommonCore targetPort)) := by
    exact (scalarSupportGraph_degree_odd_iff _ _).2 hstartScalarBoundary
  have hfinishOdd : Odd (supportGraph.degree finish.1) := by
    exact (scalarSupportGraph_degree_odd_iff _ _).2 hfinishScalarBoundary
  have hstartDegree : (incidentEdgeFinset supportGraph
      (collar.targetPortInCommonCore targetPort)).card = 1 := by
    rw [incidentEdgeFinset_card_eq_degree]
    rcases hstartOdd with ⟨multiple, hmultiple⟩
    have hle := hdegreeBound (collar.targetPortInCommonCore targetPort)
    rw [incidentEdgeFinset_card_eq_degree] at hle
    omega
  have hfinishDegree :
      (incidentEdgeFinset supportGraph finish.1).card = 1 := by
    rw [incidentEdgeFinset_card_eq_degree]
    rcases hfinishOdd with ⟨multiple, hmultiple⟩
    have hle := hdegreeBound finish.1
    rw [incidentEdgeFinset_card_eq_degree] at hle
    omega
  have hedgeClass : ∀ edge : collar.commonCore.edgeSet,
      (edge : Sym2 collar.commonCoreVertex) ∈ path.edges →
        (collar.sourceCommonColoring sourceEscape edge =
            crossFaceZeroColor coordinate ∧
          collar.targetCommonColoring edge ≠ crossFaceZeroColor coordinate) ∨
        (collar.sourceCommonColoring sourceEscape edge ≠
            crossFaceZeroColor coordinate ∧
          collar.targetCommonColoring edge = crossFaceZeroColor coordinate) := by
    intro edge hedge
    apply (crossFaceCoordinate_add_ne_zero_iff_exactlyOne_zeroColor
      coordinate (collar.sourceCommonColoring sourceEscape edge)
      (collar.targetCommonColoring edge)
      (collar.sourceCommonColoring_isTait sourceEscape edge)
      (collar.targetCommonColoring_isTait edge)).1
    simpa only [commonDiscrepancy_apply] using hpathSupport edge hedge
  refine ⟨coordinate, targetPort, finish, path, hinside, hfinishNe,
    hpath, hstartDegree, hfinishDegree, hdegreeBound, hedgeClass, ?_⟩
  intro firstEdge secondEdge hfirstPath hsecondPath hadjacent
  apply discrepancySupport_adjacent_edges_alternate
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait coordinate hadjacent
  · simpa only [commonDiscrepancy_apply] using
      hpathSupport firstEdge hfirstPath
  · simpa only [commonDiscrepancy_apply] using
      hpathSupport secondEdge hsecondPath

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
