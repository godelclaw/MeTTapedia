import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionTargetCollarColorContact
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionSupportComponent
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionChargedKempeReentry
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionResolvedKempeReentry
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionTransferMonoid

set_option autoImplicit false

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

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]

/-- In a finite graph of maximum degree two, every edge either shares its
component with an odd vertex or lies on a simple cycle.  In the cycle branch
the displayed cycle contains the chosen edge itself. -/
theorem exists_odd_reachable_from_edge_or_cycle_through_edge_of_degree_le_two
    (edge : H.edgeSet) (hdegree : ∀ vertex : W, H.degree vertex ≤ 2) :
    (∃ start finish : W,
        start ∈ edge.1 ∧ Odd (H.degree finish) ∧ H.Reachable start finish) ∨
      ∃ (root : W) (cycle : H.Walk root root),
        root ∈ edge.1 ∧ cycle.IsCycle ∧ edge.1 ∈ cycle.edges := by
  classical
  rcases Sym2.mk_surjective (edge.1 : Sym2 W) with
    ⟨⟨first, second⟩, hedgeValue⟩
  have hedgeValue' : s(first, second) = edge.1 := hedgeValue
  have hadjacent : H.Adj first second := by
    apply (SimpleGraph.mem_edgeSet H).mp
    rw [hedgeValue']
    exact edge.2
  have hfirstMem : first ∈ edge.1 := by
    rw [← hedgeValue']
    exact Sym2.mem_mk_left first second
  have hpositive : 0 < H.degree first :=
    SimpleGraph.degree_pos_iff_nonempty.mpr ⟨second, hadjacent⟩
  have hdegreeCases : H.degree first = 1 ∨ H.degree first = 2 := by
    have hupper := hdegree first
    omega
  rcases hdegreeCases with hdegreeOne | hdegreeTwo
  · apply Or.inl
    exact ⟨first, first, hfirstMem, by simp [hdegreeOne],
      SimpleGraph.Reachable.refl first⟩
  · rcases exists_reachable_odd_or_cycle_of_degree_eq_two_of_degree_le_two
        first hdegreeTwo hdegree with hodd | hcycle
    · rcases hodd with ⟨finish, _hfinishNe, hfinishOdd, hreachable⟩
      exact Or.inl ⟨first, finish, hfirstMem, hfinishOdd, hreachable⟩
    · rcases hcycle with ⟨cycle, cycleIsCycle⟩
      exact Or.inr ⟨first, cycle, hfirstMem, cycleIsCycle,
        edge_mem_rooted_isCycle_of_degree_eq_two
          cycleIsCycle hdegreeTwo edge hfirstMem⟩

variable {V : Type u} [Fintype V] [DecidableEq V]
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

/-- A nonzero discrepancy contact routed through one scalar support
component to a named source or target port. -/
structure CommonDiscrepancyContactRoute
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet) where
  coordinate : Bool
  coordinate_support : crossFaceCoordinate coordinate
    (collar.commonDiscrepancy sourceEscape edge) ≠ 0
  start : collar.commonCoreVertex
  start_mem_edge : start ∈ edge.1
  finish : collar.commonCoreVertex
  finish_mem_boundarySupport : finish ∈
    collar.commonDiscrepancyBoundarySupport sourceEscape
  finish_coordinate_boundary_ne_zero :
    crossFaceCoordinate coordinate
      (vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape) finish) ≠ 0
  reachable : (collar.coordinateDiscrepancySupportGraph
    sourceEscape coordinate).Reachable start finish

namespace CommonDiscrepancyContactRoute

variable {edge : collar.commonCore.edgeSet}
  (route : CommonDiscrepancyContactRoute collar sourceEscape edge)

/-- A charged discrepancy endpoint is one of the at-most-eight named collar
ports. -/
theorem finish_mem_commonPort :
    route.finish ∈ collar.commonPortVertexFinset :=
  collar.commonDiscrepancyBoundarySupport_subset_commonPortVertexFinset
    sourceEscape route.finish_mem_boundarySupport

/-- The charged endpoint as an element of the deduplicated terminal
interface. -/
noncomputable def finishTerminal : collar.commonPortVertexFinset :=
  ⟨route.finish, route.finish_mem_commonPort⟩

/-- The canonical source occurrence or unmatched target occurrence naming
the contacted component's charged endpoint. -/
noncomputable def finishRepresentative :
    IntrinsicCollarTerminalRepresentative
      collar.intrinsicCollarPortOverlapProfile :=
  collar.intrinsicCollarTerminalRepresentativeEquiv.symm
    route.finishTerminal

@[simp]
theorem finishRepresentative_apply :
    collar.intrinsicCollarTerminalRepresentativeEquiv
        route.finishRepresentative = route.finishTerminal :=
  Equiv.apply_symm_apply _ _

/-- The charged endpoint is read exactly from the fixed finite collar word. -/
theorem finishBoundaryWord_eq :
    intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (intrinsicCollarTerminalCoordinateOfRepresentative
          route.finishRepresentative) =
      (collar.commonDiscrepancyBoundaryState sourceEscape).1
        route.finishTerminal := by
  simpa only [route.finishRepresentative_apply] using
    (collar.intrinsicCollarTerminalBoundaryWord_representative_eq_boundaryState
      sourceEscape route.finishRepresentative)

/-- The same scalar coordinate that carries the contacted component is
nonzero in its canonical finite collar word. -/
theorem finishBoundaryWord_coordinate_ne_zero :
    crossFaceCoordinate route.coordinate
      (intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (intrinsicCollarTerminalCoordinateOfRepresentative
          route.finishRepresentative)) ≠ 0 := by
  rw [route.finishBoundaryWord_eq,
    commonDiscrepancyBoundaryState_apply]
  exact route.finish_coordinate_boundary_ne_zero

/-- A routed contact therefore ends in one of the three exact local collar
color witnesses: unmatched source, matched stem, or unmatched target. -/
theorem finishColorWitness :
    ChargedTerminalColorWitness collar sourceEscape route.coordinate
      route.finishRepresentative := by
  apply collar.chargedTerminalColorWitness_of_coordinate_ne_zero
    sourceEscape route.coordinate route.finishRepresentative
  exact route.finishBoundaryWord_coordinate_ne_zero

/-- The charged endpoint enters the existing resolved source-or-target
same-base continuation, retaining all-equal fusion lenses where necessary. -/
theorem nonempty_finishResolvedKempeReentry
    (contactRoute : CommonDiscrepancyContactRoute collar sourceEscape edge) :
    Nonempty (ResolvedChargedKempeReentry collar sourceEscape) := by
  let action := ChargedTerminalColorWitness.nonempty_kempeAction
    (finishColorWitness contactRoute)
  have reentry : collar.HasChargedKempeReentry sourceEscape :=
    ⟨contactRoute.coordinate, contactRoute.finishRepresentative, action,
      action.sameBaseReentry⟩
  exact reentry.nonempty_resolved

end CommonDiscrepancyContactRoute

/-- A nonzero discrepancy contact lying on a closed scalar support
component.  The simple support cycle contains the contacted edge. -/
structure CommonDiscrepancyContactCycle
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet) where
  coordinate : Bool
  coordinate_support : crossFaceCoordinate coordinate
    (collar.commonDiscrepancy sourceEscape edge) ≠ 0
  root : collar.commonCoreVertex
  root_mem_edge : root ∈ edge.1
  supportCycle : (collar.coordinateDiscrepancySupportGraph
    sourceEscape coordinate).Walk root root
  supportCycle_isCycle : supportCycle.IsCycle
  edge_mem_supportCycle : edge.1 ∈ supportCycle.edges

namespace CommonDiscrepancyContactCycle

variable {edge : collar.commonCore.edgeSet}
  (contact : CommonDiscrepancyContactCycle collar sourceEscape edge)

/-- The contacted scalar-support cycle after forgetting the support
subgraph. -/
def ambientCycle : collar.commonCore.Walk contact.root contact.root :=
  contact.supportCycle.mapLe (scalarSupportGraph_le (fun current =>
    crossFaceCoordinate contact.coordinate
      (collar.commonDiscrepancy sourceEscape current)))

@[simp]
theorem ambientCycle_length :
    contact.ambientCycle.length = contact.supportCycle.length := by
  calc
    contact.ambientCycle.length = contact.ambientCycle.edges.length :=
      contact.ambientCycle.length_edges.symm
    _ = contact.supportCycle.edges.length := by
      exact congrArg List.length
        (SimpleGraph.Walk.edges_mapLe_eq_edges _ _)
    _ = contact.supportCycle.length := contact.supportCycle.length_edges

theorem ambientCycle_isCycle : contact.ambientCycle.IsCycle := by
  exact contact.supportCycle_isCycle.mapLe
    (scalarSupportGraph_le (fun current =>
      crossFaceCoordinate contact.coordinate
        (collar.commonDiscrepancy sourceEscape current)))

theorem ambientCycle_positive : 0 < contact.ambientCycle.length := by
  exact lt_of_lt_of_le (by omega)
    contact.ambientCycle_isCycle.three_le_length

/-- Forgetting the support subgraph preserves the exact contacted edge. -/
theorem edge_mem_ambientCycle : edge.1 ∈ contact.ambientCycle.edges := by
  rw [ambientCycle, SimpleGraph.Walk.edges_mapLe_eq_edges]
  exact contact.edge_mem_supportCycle

/-- Every edge of the ambient cycle retains nonzero discrepancy in the
selected scalar coordinate. -/
theorem support : ∀ current ∈ contact.ambientCycle.edgeSubtypeSupport,
    crossFaceCoordinate contact.coordinate
      (collar.sourceCommonColoring sourceEscape current +
        collar.targetCommonColoring current) ≠ 0 := by
  simpa only [ambientCycle, commonDiscrepancy_apply] using
    (scalarSupportWalk_support (fun current =>
      crossFaceCoordinate contact.coordinate
        (collar.commonDiscrepancy sourceEscape current))
      contact.supportCycle)

/-- The canonical four-state word obtained by cutting the contacted support
cycle at its chosen root. -/
noncomputable def stateWord :
    List (ScalarDiscrepancyColorState contact.coordinate) :=
  scalarDiscrepancyColorStateWord
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    contact.coordinate contact.ambientCycle contact.support

@[simp]
theorem stateWord_length :
    contact.stateWord.length = contact.supportCycle.length := by
  rw [stateWord, scalarDiscrepancyColorStateWord_length,
    contact.ambientCycle_length]

theorem stateWord_ne_nil : contact.stateWord ≠ [] := by
  apply List.length_pos_iff.mp
  rw [contact.stateWord_length]
  exact lt_of_lt_of_le (by omega)
    contact.supportCycle_isCycle.three_le_length

/-- Cutting the cycle gives the exact linear transfer between its first and
last edge states. -/
theorem linearizedExactTransfer :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
      (contact.supportCycle.length - 1)
      (contact.stateWord.head contact.stateWord_ne_nil)
      (contact.stateWord.getLast contact.stateWord_ne_nil) := by
  simpa only [stateWord, contact.ambientCycle_length] using
    (scalarDiscrepancyColorStateWord_exactTransfer
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      contact.coordinate contact.ambientCycle_isCycle.isTrail
      contact.ambientCycle_positive contact.support)

/-- The last edge state transitions back to the first at the cycle root. -/
theorem closingTransition :
    ScalarDiscrepancyColorTransition
      (contact.stateWord.getLast contact.stateWord_ne_nil)
      (contact.stateWord.head contact.stateWord_ne_nil) := by
  simpa only [stateWord] using
    (scalarDiscrepancyColorStateWord_closingTransition
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      contact.coordinate contact.ambientCycle_isCycle contact.support)

/-- The exact cycle through the discrepancy contact is a positive-period
return in the four-state transfer monoid. -/
theorem exactReturn :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
      contact.supportCycle.length
      (contact.stateWord.head contact.stateWord_ne_nil)
      (contact.stateWord.head contact.stateWord_ne_nil) := by
  have hclosingStep :
      ExactRelationalTransfer ScalarDiscrepancyColorTransition 1
        (contact.stateWord.getLast contact.stateWord_ne_nil)
        (contact.stateWord.head contact.stateWord_ne_nil) := by
    simpa using ExactRelationalTransfer.succ contact.closingTransition
      (ExactRelationalTransfer.zero
        (oneStep := ScalarDiscrepancyColorTransition)
        (contact.stateWord.head contact.stateWord_ne_nil))
  have hreturn := contact.linearizedExactTransfer.comp hclosingStep
  have hlength : contact.supportCycle.length - 1 + 1 =
      contact.supportCycle.length := by
    have hpositive : 0 < contact.supportCycle.length :=
      lt_of_lt_of_le (by omega)
        contact.supportCycle_isCycle.three_le_length
    omega
  rw [hlength] at hreturn
  exact hreturn

/-- Hence every contacted closed support cycle has even length. -/
theorem period_even : Even contact.supportCycle.length :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.ExactRelationalTransfer.scalarDiscrepancy_even_of_return
    contact.exactReturn

end CommonDiscrepancyContactCycle

/-- The finite-transfer data of a closed scalar component through the exact
discrepancy contact. -/
structure CommonDiscrepancyContactMonodromy
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet) where
  contactCycle : CommonDiscrepancyContactCycle collar sourceEscape edge
  state : ScalarDiscrepancyColorState contactCycle.coordinate
  contact_edge_mem : edge.1 ∈ contactCycle.ambientCycle.edges
  period_positive : 0 < contactCycle.supportCycle.length
  period_even : Even contactCycle.supportCycle.length
  exactReturn : ExactRelationalTransfer ScalarDiscrepancyColorTransition
    contactCycle.supportCycle.length state state

namespace CommonDiscrepancyContactCycle

/-- Every contacted support cycle canonically realizes its exact positive,
even transfer-monoid return. -/
noncomputable def toMonodromy
    {edge : collar.commonCore.edgeSet}
    (contact : CommonDiscrepancyContactCycle collar sourceEscape edge) :
    CommonDiscrepancyContactMonodromy collar sourceEscape edge := {
  contactCycle := contact
  state := contact.stateWord.head contact.stateWord_ne_nil
  contact_edge_mem := contact.edge_mem_ambientCycle
  period_positive := lt_of_lt_of_le (by omega)
    contact.supportCycle_isCycle.three_le_length
  period_even := contact.period_even
  exactReturn := contact.exactReturn }

end CommonDiscrepancyContactCycle

/-- Every nonzero common-core discrepancy contact reaches the finite named
port interface in one scalar coordinate, or belongs to a closed simple
support cycle in that coordinate. -/
theorem nonempty_commonDiscrepancyContactRoute_or_cycle
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet)
    (hdiscrepancy : collar.commonDiscrepancy sourceEscape edge ≠ 0) :
    Nonempty (CommonDiscrepancyContactRoute collar sourceEscape edge) ∨
      Nonempty (CommonDiscrepancyContactCycle collar sourceEscape edge) := by
  rcases exists_crossFaceCoordinate_ne_zero
      (collar.commonDiscrepancy sourceEscape edge) hdiscrepancy with
    ⟨coordinate, hcoordinate⟩
  let supportGraph := collar.coordinateDiscrepancySupportGraph
    sourceEscape coordinate
  let supportEdge := collar.coordinateDiscrepancySupportEdge
    sourceEscape coordinate edge hcoordinate
  have hdegree : ∀ vertex : collar.commonCoreVertex,
      supportGraph.degree vertex ≤ 2 := by
    intro vertex
    rw [← incidentEdgeFinset_card_eq_degree]
    exact taitDiscrepancySupport_incidentCard_le_two
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait coordinate vertex
      (collar.commonCore_incidentEdgeFinset_card_le_three vertex)
  have hoddBoundarySupport : ∀ vertex : collar.commonCoreVertex,
      Odd (supportGraph.degree vertex) →
        vertex ∈ collar.commonDiscrepancyBoundarySupport sourceEscape := by
    intro vertex hodd
    have hscalarBoundary :
        scalarVertexKirchhoffSum collar.commonCore
          (fun current => crossFaceCoordinate coordinate
            (collar.commonDiscrepancy sourceEscape current)) vertex ≠ 0 :=
      (scalarSupportGraph_degree_odd_iff _ vertex).1 hodd
    have hboundary : vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape) vertex ≠ 0 := by
      intro hzero
      apply hscalarBoundary
      rw [scalarVertexKirchhoffSum_crossFaceCoordinate, hzero]
      cases coordinate <;> rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ vertex, hboundary⟩
  rcases
      exists_odd_reachable_from_edge_or_cycle_through_edge_of_degree_le_two
        supportEdge hdegree with hroute | hcycle
  · rcases hroute with
      ⟨start, finish, hstart, hfinishOdd, hreachable⟩
    apply Or.inl
    refine ⟨{
      coordinate := coordinate
      coordinate_support := hcoordinate
      start := start
      start_mem_edge := ?_
      finish := finish
      finish_mem_boundarySupport :=
        hoddBoundarySupport finish hfinishOdd
      finish_coordinate_boundary_ne_zero := by
        have hscalarBoundary :
            scalarVertexKirchhoffSum collar.commonCore
              (fun current => crossFaceCoordinate coordinate
                (collar.commonDiscrepancy sourceEscape current)) finish ≠ 0 :=
          (scalarSupportGraph_degree_odd_iff _ finish).1 hfinishOdd
        rw [scalarVertexKirchhoffSum_crossFaceCoordinate] at hscalarBoundary
        exact hscalarBoundary
      reachable := hreachable }⟩
    exact hstart
  · rcases hcycle with
      ⟨root, supportCycle, hroot, supportCycleIsCycle, hedgeCycle⟩
    apply Or.inr
    refine ⟨{
      coordinate := coordinate
      coordinate_support := hcoordinate
      root := root
      root_mem_edge := ?_
      supportCycle := supportCycle
      supportCycle_isCycle := supportCycleIsCycle
      edge_mem_supportCycle := ?_ }⟩
    · exact hroot
    · exact hedgeCycle

/-- Every nonzero contact is now handed either to the finite charged-terminal
color classification or to a closed scalar support cycle through that exact
contact. -/
theorem exists_commonDiscrepancyContactColorWitness_or_cycle
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet)
    (hdiscrepancy : collar.commonDiscrepancy sourceEscape edge ≠ 0) :
    (∃ route : CommonDiscrepancyContactRoute collar sourceEscape edge,
      ChargedTerminalColorWitness collar sourceEscape route.coordinate
        route.finishRepresentative) ∨
      Nonempty (CommonDiscrepancyContactCycle collar sourceEscape edge) := by
  rcases collar.nonempty_commonDiscrepancyContactRoute_or_cycle
      sourceEscape edge hdiscrepancy with hroute | hcycle
  · rcases hroute with ⟨route⟩
    exact Or.inl ⟨route, route.finishColorWitness⟩
  · exact Or.inr hcycle

/-- Equivalently, the charged branch enters the established resolved
adjacent-escape recurrence, while the only remaining alternative is the
closed scalar support cycle through the contacted edge. -/
theorem exists_commonDiscrepancyContactResolvedKempeReentry_or_cycle
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet)
    (hdiscrepancy : collar.commonDiscrepancy sourceEscape edge ≠ 0) :
    (Nonempty (CommonDiscrepancyContactRoute collar sourceEscape edge) ∧
      Nonempty (ResolvedChargedKempeReentry collar sourceEscape)) ∨
      Nonempty (CommonDiscrepancyContactCycle collar sourceEscape edge) := by
  rcases collar.nonempty_commonDiscrepancyContactRoute_or_cycle
      sourceEscape edge hdiscrepancy with hroute | hcycle
  · rcases hroute with ⟨route⟩
    exact Or.inl ⟨⟨route⟩, route.nonempty_finishResolvedKempeReentry⟩
  · exact Or.inr hcycle

/-- Thus every nonzero contact enters either the resolved adjacent-escape
recurrence or an exact positive even return in the finite transfer monoid. -/
theorem exists_commonDiscrepancyContactResolvedKempeReentry_or_monodromy
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet)
    (hdiscrepancy : collar.commonDiscrepancy sourceEscape edge ≠ 0) :
    (Nonempty (CommonDiscrepancyContactRoute collar sourceEscape edge) ∧
      Nonempty (ResolvedChargedKempeReentry collar sourceEscape)) ∨
      Nonempty (CommonDiscrepancyContactMonodromy collar sourceEscape edge) := by
  rcases collar.exists_commonDiscrepancyContactResolvedKempeReentry_or_cycle
      sourceEscape edge hdiscrepancy with hreentry | hcycle
  · exact Or.inl hreentry
  · rcases hcycle with ⟨contact⟩
    exact Or.inr ⟨contact.toMonodromy⟩

namespace CompanionCrossPairFusionTargetCollarTraversal

variable {start : sourceNormal.KempeOrbitAdjacentEscape}
  (traversal : CompanionCrossPairFusionTargetCollarTraversal collar start)

/-- The resolved color status of one edge of a rerouted target path.  A
discrepancy is retained only with its resolved charged recurrence or with an
exact positive even monodromy return containing the contacted common edge. -/
def TargetPathEdgeColorResolution
    (edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).edgeSet) : Prop :=
  edge ∈ collar.targetEscape.coloring.bicoloredSet
      collar.targetOwnFirstColor collar.targetOwnSecondColor ∨
    ∃ commonEdge : collar.commonCore.edgeSet,
      collar.commonEdgeInTarget commonEdge = edge ∧
        (edge ∈ collar.targetEscape.coloring.bicoloredSet
            (traversal.contact.fusion.lineFusion.normal.returnData.lastOverlap.overlap.fixedColor)
            (traversal.contact.fusion.lineFusion.normal.returnData.lastOverlap.overlap.breakOuterColor) ∨
          edge ∈ collar.targetEscape.coloring.bicoloredSet
            (crossFaceZeroColor
              (traversal.contact.fusion.lineFusion.normal.step.firstHit.transfer.coordinate))
            (traversal.contact.fusion.lineFusion.normal.step.reentry.realization.companion) ∨
          (Nonempty (CommonDiscrepancyContactRoute collar
              traversal.contact.fusion.lineFusion.normal.canonicalState
                commonEdge) ∧
            Nonempty (ResolvedChargedKempeReentry collar
              traversal.contact.fusion.lineFusion.normal.canonicalState)) ∨
          Nonempty (CommonDiscrepancyContactMonodromy collar
            traversal.contact.fusion.lineFusion.normal.canonicalState
              commonEdge))

/-- Every noncentral collar traversal now has a simple target path whose
every edge has a resolved local color status. -/
theorem exists_targetKempeReroutedPath_with_colorResolution_of_noncentral
    (hclass : traversal.traversalClass = .firstBoundaryPair ∨
      traversal.traversalClass = .secondBoundaryPair ∨
      traversal.traversalClass = .bothBoundaryPairs) :
    ∃ targetPath : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        ⟨traversal.contact.fusion.startVertex.1,
          traversal.contact.fusion.startVertex_mem_targetRetainedVertexSet⟩
        ⟨traversal.contact.fusion.endVertex.1,
          traversal.contact.fusion.endVertex_mem_targetRetainedVertexSet⟩,
      targetPath.IsPath ∧
        ∀ edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
          collar.targetData.secondVertex).edgeSet,
          edge.1 ∈ targetPath.edges →
            traversal.TargetPathEdgeColorResolution edge := by
  rcases
      traversal.exists_targetKempeReroutedPath_with_colorTransport_or_discrepancy_of_noncentral
        hclass with ⟨targetPath, targetPathIsPath, edgeStatus⟩
  refine ⟨targetPath, targetPathIsPath, ?_⟩
  intro edge hedge
  rcases edgeStatus edge hedge with htargetOwn |
      ⟨commonEdge, htargetEdge, hreturn | hselected | hdiscrepancy⟩
  · exact Or.inl htargetOwn
  · exact Or.inr ⟨commonEdge, htargetEdge, Or.inl hreturn⟩
  · exact Or.inr ⟨commonEdge, htargetEdge,
      Or.inr (Or.inl hselected)⟩
  · rcases collar.exists_commonDiscrepancyContactResolvedKempeReentry_or_monodromy
        traversal.contact.fusion.lineFusion.normal.canonicalState
          commonEdge hdiscrepancy with hreentry | hmonodromy
    · exact Or.inr ⟨commonEdge, htargetEdge,
        Or.inr (Or.inr (Or.inl hreentry))⟩
    · exact Or.inr ⟨commonEdge, htargetEdge,
        Or.inr (Or.inr (Or.inr hmonodromy))⟩

/-- Across all seven collar classes, either a target path has fully routed
edgewise color status, or the traversal is one of the four exact central
cross-arm obstructions. -/
theorem exists_targetKempeReroutedPath_with_colorResolution_or_crossObstruction :
    (∃ targetPath : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        ⟨traversal.contact.fusion.startVertex.1,
          traversal.contact.fusion.startVertex_mem_targetRetainedVertexSet⟩
        ⟨traversal.contact.fusion.endVertex.1,
          traversal.contact.fusion.endVertex_mem_targetRetainedVertexSet⟩,
      targetPath.IsPath ∧
        ∀ edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
          collar.targetData.secondVertex).edgeSet,
          edge.1 ∈ targetPath.edges →
            traversal.TargetPathEdgeColorResolution edge) ∨
      ∃ firstUsesOne secondUsesThree,
        traversal.traversalClass = .cross firstUsesOne secondUsesThree ∧
        ¬ collar.targetData.degreeTwoBoundaryData.KempePortsConnected
          collar.targetEscape.coloring collar.targetOwnFirstColor
            collar.targetOwnSecondColor
            (TargetCollarTraversalClass.firstCrossPort firstUsesOne)
            (TargetCollarTraversalClass.secondCrossPort secondUsesThree) := by
  cases hclass : traversal.traversalClass with
  | firstBoundaryPair =>
      exact Or.inl <|
        traversal.exists_targetKempeReroutedPath_with_colorResolution_of_noncentral
          (Or.inl hclass)
  | secondBoundaryPair =>
      exact Or.inl <|
        traversal.exists_targetKempeReroutedPath_with_colorResolution_of_noncentral
          (Or.inr (Or.inl hclass))
  | bothBoundaryPairs =>
      exact Or.inl <|
        traversal.exists_targetKempeReroutedPath_with_colorResolution_of_noncentral
          (Or.inr (Or.inr hclass))
  | cross firstUsesOne secondUsesThree =>
      exact Or.inr ⟨firstUsesOne, secondUsesThree, rfl,
        collar.not_targetOwnKempePortsConnected_cross
          firstUsesOne secondUsesThree⟩

end CompanionCrossPairFusionTargetCollarTraversal

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
