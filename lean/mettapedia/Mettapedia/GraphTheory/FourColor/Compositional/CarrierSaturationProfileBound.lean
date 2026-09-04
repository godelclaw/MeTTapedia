import Mettapedia.GraphTheory.FourColor.Compositional.CarrierSaturationRootedNesting
import Mettapedia.GraphTheory.FourColor.CyclicCutConnectedShore
import Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixConnectedCutProfileBound

/-!
# Complete-profile bounds for saturated carrier prefixes

A finite family of component-saturated carrier prefixes with one uniform
boundary bound can be rooted coherently at the exterior component of its last
member.  The resulting connected cuts are strictly nested.  Their complete
phased Count states must therefore all be distinct in a vertex-minimal
counterexample.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CarrierSaturationProfileBound

open CarrierSaturationBoundaryDecomposition
open CarrierSaturationConnected
open CarrierSaturationCyclicCut
open CarrierSaturationRootedNesting
open CyclicEdgeCutRealization
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24MajorityShoreStateDescent
open GoertzelV24NormalizedShoreDescent
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory
open PathPrefixConnectedCutProfileBound
open ResidualReturnComponentSaturation
open RootedCutSaturation
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Saturate one carrier prefix at a prescribed common exterior root and
cycle. -/
theorem exists_connectedCarrierCut_at_commonRoot
    (hconnected : G.Connected)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) (hcut : 0 < cut.val)
    (bound : Nat)
    (hboundary : Nat.card (AmbientExitDart hG sigma hSigma site cut) ≤ bound)
    (hprefixLarge : bound < cut.val + 2)
    (hsuffixLarge : bound <
      (Fintype.card (CyclePosition sigma site) - cut.val) + 2)
    (anchor : CyclePosition sigma site) (hcutAnchor : cut ≤ anchor)
    (outsideRoot : V)
    (hrootAnchor : carrierPrefixExteriorComponent hG sigma hSigma site anchor
      outsideRoot)
    (outsideCycle : G.Walk outsideRoot outsideRoot)
    (hcycle : outsideCycle.IsCycle)
    (hsupportAnchor : ∀ vertex, vertex ∈ outsideCycle.support →
      carrierPrefixExteriorComponent hG sigma hSigma site anchor vertex) :
    ∃ connected : ConnectedAtWidth G bound,
      ∀ vertex, connected.realization.side vertex ↔
        closureSide (G := G)
          (carrierPrefixReturnSaturation hG sigma hSigma site cut)
          outsideRoot
          (carrierPrefixExteriorComponent_mono hG sigma hSigma site
            hcutAnchor outsideRoot hrootAnchor).choose vertex := by
  let raw := carrierPrefixCyclicEdgeCutRealization hG sigma hSigma site cut
    hcut bound hboundary hprefixLarge hsuffixLarge
  have hrootCut := carrierPrefixExteriorComponent_mono hG sigma hSigma site
    hcutAnchor outsideRoot hrootAnchor
  have hsideConnected : (G.induce raw.side).Connected := by
    change (G.induce
      (carrierPrefixReturnSaturation hG sigma hSigma site cut)).Connected
    exact induce_carrierPrefixReturnSaturation_connected
      hG sigma hSigma site cut hcut
  have hsupportCut : ∀ vertex, vertex ∈ outsideCycle.support →
      ¬raw.side vertex := by
    intro vertex hvertex
    change ¬carrierPrefixReturnSaturation hG sigma hSigma site cut vertex
    exact (carrierPrefixExteriorComponent_mono hG sigma hSigma site
      hcutAnchor vertex (hsupportAnchor vertex hvertex)).choose
  have hrootOutside : ¬raw.side outsideRoot := by
    change ¬carrierPrefixReturnSaturation hG sigma hSigma site cut outsideRoot
    exact hrootCut.choose
  have hrawBoundary :
      (crossingEdgeFinset G
        (carrierPrefixReturnSaturation hG sigma hSigma site cut)).card ≤
          bound := by
    rw [card_crossingEdgeFinset_carrierPrefixReturnSaturation]
    exact hboundary
  rcases RootedCutSaturation.exists_connectedAtWidth hconnected raw
      hsideConnected outsideRoot hrootOutside outsideCycle hcycle hsupportCut
      bound hrawBoundary with ⟨connected, _hedges, hside⟩
  refine ⟨connected, ?_⟩
  intro vertex
  change connected.realization.side vertex ↔
    closureSide raw.side outsideRoot hrootOutside vertex
  exact hside vertex

/-- Any finite family of uniformly bounded, two-margin saturated carrier
prefixes has at most as many members as the complete phased profile carrier. -/
theorem card_carrierPrefixFamily_le_profileStateCount
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (bound : Nat) (positions : Finset (CyclePosition sigma site))
    (hpositive : ∀ cut ∈ positions, 0 < cut.val)
    (hboundary : ∀ cut ∈ positions,
      Nat.card (AmbientExitDart hG sigma hSigma site cut) ≤ bound)
    (hmargins : ∀ cut ∈ positions,
      bound ≤ cut.val ∧
        bound ≤ Fintype.card (CyclePosition sigma site) - cut.val) :
    positions.card ≤ pathPrefixProfileStateCount bound := by
  classical
  by_cases hpositions : positions.Nonempty
  · let anchor := positions.max' hpositions
    have hanchorMem : anchor ∈ positions :=
      Finset.max'_mem positions hpositions
    have hanchorBoundary := hboundary anchor hanchorMem
    have hanchorMargins := hmargins anchor hanchorMem
    have hanchorExteriorCycle : HasCycleOnSide G
        (carrierPrefixExteriorComponent hG sigma hSigma site anchor) := by
      have hsuffixLarge : bound <
          (Fintype.card (CyclePosition sigma site) - anchor.val) + 2 := by
        omega
      exact hasCycleOnSide_carrierPrefixExteriorComponent hG sigma hSigma
        site anchor bound hanchorBoundary hsuffixLarge
    rcases hanchorExteriorCycle with
      ⟨outsideRoot, hrootAnchor, outsideCycle, hcycle, hsupportAnchor⟩
    have hconnected : G.Connected := by
      rw [← rotationPrimalGraph_toRotationSystem_eq G rotation]
      exact minimal.primalConnected
    have hexists (cut : positions) :
        ∃ connected : ConnectedAtWidth G bound,
          ∀ vertex, connected.realization.side vertex ↔
            closureSide (G := G)
              (carrierPrefixReturnSaturation hG sigma hSigma site cut.1)
              outsideRoot
              (carrierPrefixExteriorComponent_mono hG sigma hSigma site
                (Finset.le_max' positions cut.1 cut.2) outsideRoot
                hrootAnchor).choose vertex := by
      have hcutPositive := hpositive cut.1 cut.2
      have hcutBoundary := hboundary cut.1 cut.2
      have hcutMargins := hmargins cut.1 cut.2
      have hprefixLarge : bound < cut.1.val + 2 := by omega
      have hsuffixLarge : bound <
          (Fintype.card (CyclePosition sigma site) - cut.1.val) + 2 := by omega
      exact exists_connectedCarrierCut_at_commonRoot hconnected hG sigma
        hSigma site cut.1 hcutPositive bound hcutBoundary hprefixLarge
        hsuffixLarge anchor (Finset.le_max' positions cut.1 cut.2)
        outsideRoot hrootAnchor outsideCycle hcycle hsupportAnchor
    choose connected hside using hexists
    let nodes : positions → LiteralShoreNode rotation bound bound := fun cut =>
      ((connected cut).toConnectedShoreNode rotation minimal).toLiteral
        rotation minimal
    let state : positions → Fin (6 * bound + 1) × StateAtBound.{u} bound :=
      fun cut => (nodes cut).cardPhasedState
    have hstateInjective : Function.Injective state := by
      intro firstPosition secondPosition heq
      by_contra hne
      have hvaluesNe : firstPosition.1 ≠ secondPosition.1 := by
        intro hvalues
        apply hne
        exact Subtype.ext hvalues
      rcases lt_or_gt_of_ne hvaluesNe with hfirstSecond | hsecondFirst
      · have hfirstSide : (connected firstPosition).realization.side =
            closureSide (G := G)
              (carrierPrefixReturnSaturation hG sigma hSigma site
                firstPosition.1)
              outsideRoot
              (carrierPrefixExteriorComponent_mono hG sigma hSigma site
                (Finset.le_max' positions firstPosition.1 firstPosition.2)
                outsideRoot hrootAnchor).choose := by
          funext vertex
          exact propext (hside firstPosition vertex)
        have hsecondSide : (connected secondPosition).realization.side =
            closureSide (G := G)
              (carrierPrefixReturnSaturation hG sigma hSigma site
                secondPosition.1)
              outsideRoot
              (carrierPrefixExteriorComponent_mono hG sigma hSigma site
                (Finset.le_max' positions secondPosition.1 secondPosition.2)
                outsideRoot hrootAnchor).choose := by
          funext vertex
          exact propext (hside secondPosition vertex)
        have hproper := incidentEdgeShore_carrierClosureSide_ssubset
          hG sigma hSigma site hfirstSecond
          (Finset.le_max' positions secondPosition.1 secondPosition.2)
          outsideRoot hrootAnchor
        have hnodesProper : (nodes firstPosition).shore ⊂
            (nodes secondPosition).shore := by
          simpa only [nodes, ConnectedShoreNode.toLiteral_shore,
            ConnectedAtWidth.toConnectedShoreNode_shore,
            hfirstSide, hsecondSide] using hproper
        exact cardPhasedState_ne_of_ssubset rotation minimal
          (nodes secondPosition) (nodes firstPosition) hnodesProper (by
            simpa only [state] using heq.symm)
      · have hfirstSide : (connected firstPosition).realization.side =
            closureSide (G := G)
              (carrierPrefixReturnSaturation hG sigma hSigma site
                firstPosition.1)
              outsideRoot
              (carrierPrefixExteriorComponent_mono hG sigma hSigma site
                (Finset.le_max' positions firstPosition.1 firstPosition.2)
                outsideRoot hrootAnchor).choose := by
          funext vertex
          exact propext (hside firstPosition vertex)
        have hsecondSide : (connected secondPosition).realization.side =
            closureSide (G := G)
              (carrierPrefixReturnSaturation hG sigma hSigma site
                secondPosition.1)
              outsideRoot
              (carrierPrefixExteriorComponent_mono hG sigma hSigma site
                (Finset.le_max' positions secondPosition.1 secondPosition.2)
                outsideRoot hrootAnchor).choose := by
          funext vertex
          exact propext (hside secondPosition vertex)
        have hproper := incidentEdgeShore_carrierClosureSide_ssubset
          hG sigma hSigma site hsecondFirst
          (Finset.le_max' positions firstPosition.1 firstPosition.2)
          outsideRoot hrootAnchor
        have hnodesProper : (nodes secondPosition).shore ⊂
            (nodes firstPosition).shore := by
          simpa only [nodes, ConnectedShoreNode.toLiteral_shore,
            ConnectedAtWidth.toConnectedShoreNode_shore,
            hfirstSide, hsecondSide] using hproper
        exact cardPhasedState_ne_of_ssubset rotation minimal
          (nodes firstPosition) (nodes secondPosition) hnodesProper (by
            simpa only [state] using heq)
    have hcard := Fintype.card_le_of_injective state hstateInjective
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin,
      card_stateAtBound, pathPrefixProfileStateCount] using hcard
  · have hempty : positions = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hpositions
    simp [hempty]

end

end CarrierSaturationProfileBound

end Mettapedia.GraphTheory.FourColor.Compositional
