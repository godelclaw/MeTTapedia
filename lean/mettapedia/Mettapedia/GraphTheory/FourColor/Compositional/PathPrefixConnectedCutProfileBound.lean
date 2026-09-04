import Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixRootedNesting
import Mettapedia.GraphTheory.FourColor.CyclicCutConnectedShore

/-!
# Complete-profile bounds for bounded cubic path prefixes

This is the path-generic semantic core of the sweep argument.  A finite
family of strict path prefixes has a common boundary bound and enough path
material on both sides.  The last prefix supplies a suffix cycle and a
common exterior root.  Rooted saturation then gives strictly nested actual
connected cuts, whose complete phased Count profiles must be distinct in a
vertex-minimal counterexample.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace PathPrefixConnectedCutProfileBound

open CyclicEdgeCutRealization
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24MajorityShoreStateDescent
open GoertzelV24NormalizedShoreDescent
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open Mettapedia.GraphTheory
open PathPrefixBoundary
open PathPrefixCyclicCut
open PathPrefixRootedNesting
open RootedCutSaturation
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Cardinality of the complete phased interface carrier at width `bound`. -/
def pathPrefixProfileStateCount (bound : Nat) : Nat :=
  (6 * bound + 1) *
    (∑ j : Fin (bound + 1),
      Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat)))

/-- Saturate one prefix at a prescribed exterior root and cycle.  The
resulting side is characterized as the rooted closure of the raw prefix. -/
theorem exists_connectedCut_at_commonRoot
    (hconnected : G.Connected)
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (cut : Fin (path.length + 1)) (hcut : 0 < cut.val)
    (bound : Nat)
    (hboundary : (crossingEdgeFinset G (pathPrefixSide path cut)).card ≤ bound)
    (hprefixLarge : bound < cut.val + 2)
    (hsuffixLarge : bound < path.length + 1 - cut.val + 2)
    (anchor : Fin (path.length + 1)) (hcutAnchor : cut ≤ anchor)
    (outsideRoot : V)
    (hrootAnchor : prefixExteriorComponent hpath anchor outsideRoot)
    (outsideCycle : G.Walk outsideRoot outsideRoot)
    (hcycle : outsideCycle.IsCycle)
    (hsupportAnchor : ∀ vertex, vertex ∈ outsideCycle.support →
      prefixExteriorComponent hpath anchor vertex) :
    ∃ connected : ConnectedAtWidth G bound,
      ∀ vertex, connected.realization.side vertex ↔
        closureSide (G := G) (pathPrefixSide path cut) outsideRoot
          (prefixExteriorComponent_mono hpath hcutAnchor outsideRoot
            hrootAnchor).choose vertex := by
  let raw := pathPrefixCyclicEdgeCutRealization hpath hregular cut hcut bound
    hboundary hprefixLarge hsuffixLarge
  have hrootCut := prefixExteriorComponent_mono hpath hcutAnchor outsideRoot
    hrootAnchor
  have hsideConnected : (G.induce raw.side).Connected := by
    change (G.induce (pathPrefixSide path cut)).Connected
    exact induce_pathPrefixSide_connected hpath cut hcut
  have hsupportCut : ∀ vertex, vertex ∈ outsideCycle.support →
      ¬raw.side vertex := by
    intro vertex hvertex
    change ¬pathPrefixSide path cut vertex
    exact (prefixExteriorComponent_mono hpath hcutAnchor vertex
      (hsupportAnchor vertex hvertex)).choose
  have hrootOutside : ¬raw.side outsideRoot := by
    change ¬pathPrefixSide path cut outsideRoot
    exact hrootCut.choose
  rcases RootedCutSaturation.exists_connectedAtWidth hconnected raw
      hsideConnected outsideRoot hrootOutside outsideCycle hcycle hsupportCut
      bound hboundary with ⟨connected, _hedges, hside⟩
  refine ⟨connected, ?_⟩
  intro vertex
  change connected.realization.side vertex ↔
    closureSide raw.side outsideRoot hrootOutside vertex
  exact hside vertex

/-- Any finite family of bounded two-margin prefixes of one cubic simple
path has at most as many members as the complete phased profile carrier. -/
theorem card_prefixFamily_le_profileStateCount
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (bound : Nat) (positions : Finset (Fin (path.length + 1)))
    (hpositive : ∀ cut ∈ positions, 0 < cut.val)
    (hboundary : ∀ cut ∈ positions,
      (crossingEdgeFinset G (pathPrefixSide path cut)).card ≤ bound)
    (hmargins : ∀ cut ∈ positions,
      bound ≤ cut.val ∧ bound ≤ path.length + 1 - cut.val) :
    positions.card ≤ pathPrefixProfileStateCount bound := by
  classical
  by_cases hpositions : positions.Nonempty
  · let anchor := positions.max' hpositions
    have hanchorMem : anchor ∈ positions :=
      Finset.max'_mem positions hpositions
    have hanchorBoundary := hboundary anchor hanchorMem
    have hanchorMargins := hmargins anchor hanchorMem
    have hanchorExteriorCycle :
        HasCycleOnSide G (prefixExteriorComponent hpath anchor) := by
      have hsuffixLarge : bound < path.length + 1 - anchor.val + 2 := by
        omega
      exact hasCycleOnSide_prefixExteriorComponent hpath hregular anchor bound
        hanchorBoundary hsuffixLarge
    rcases hanchorExteriorCycle with
      ⟨outsideRoot, hrootAnchor, outsideCycle, hcycle, hsupportAnchor⟩
    have hconnected : G.Connected := by
      rw [← rotationPrimalGraph_toRotationSystem_eq G rotation]
      exact minimal.primalConnected
    have hexists (cut : positions) :
        ∃ connected : ConnectedAtWidth G bound,
          ∀ vertex, connected.realization.side vertex ↔
            closureSide (G := G) (pathPrefixSide path cut.1) outsideRoot
              (prefixExteriorComponent_mono hpath
                (Finset.le_max' positions cut.1 cut.2) outsideRoot
                  hrootAnchor).choose vertex := by
      have hcutPositive := hpositive cut.1 cut.2
      have hcutBoundary := hboundary cut.1 cut.2
      have hcutMargins := hmargins cut.1 cut.2
      have hprefixLarge : bound < cut.1.val + 2 := by omega
      have hsuffixLarge : bound < path.length + 1 - cut.1.val + 2 := by omega
      exact exists_connectedCut_at_commonRoot hconnected hpath hregular cut.1
        hcutPositive bound hcutBoundary hprefixLarge hsuffixLarge anchor
        (Finset.le_max' positions cut.1 cut.2) outsideRoot hrootAnchor
        outsideCycle hcycle hsupportAnchor
    choose connected hside using hexists
    let nodes : positions → LiteralShoreNode rotation bound bound := fun cut =>
      ((connected cut).toConnectedShoreNode rotation minimal).toLiteral
        rotation minimal
    let state : positions → Fin (6 * bound + 1) × StateAtBound.{u} bound :=
      fun cut => (nodes cut).cardPhasedState
    have hstateInjective : Function.Injective state := by
      intro first second heq
      by_contra hne
      have hvaluesNe : first.1 ≠ second.1 := by
        intro hvalues
        apply hne
        exact Subtype.ext hvalues
      rcases lt_or_gt_of_ne hvaluesNe with hfirstSecond | hsecondFirst
      · have hfirstSide : (connected first).realization.side =
            closureSide (G := G) (pathPrefixSide path first.1) outsideRoot
              (prefixExteriorComponent_mono hpath
                (Finset.le_max' positions first.1 first.2) outsideRoot
                  hrootAnchor).choose := by
          funext vertex
          exact propext (hside first vertex)
        have hsecondSide : (connected second).realization.side =
            closureSide (G := G) (pathPrefixSide path second.1) outsideRoot
              (prefixExteriorComponent_mono hpath
                (Finset.le_max' positions second.1 second.2) outsideRoot
                  hrootAnchor).choose := by
          funext vertex
          exact propext (hside second vertex)
        have hproper := incidentEdgeShore_closureSide_ssubset hpath hfirstSecond
          (Finset.le_max' positions second.1 second.2) outsideRoot hrootAnchor
        have hnodesProper : (nodes first).shore ⊂ (nodes second).shore := by
          simpa only [nodes, ConnectedShoreNode.toLiteral_shore,
            ConnectedAtWidth.toConnectedShoreNode_shore,
            hfirstSide, hsecondSide] using hproper
        exact cardPhasedState_ne_of_ssubset rotation minimal
          (nodes second) (nodes first) hnodesProper (by
            simpa only [state] using heq.symm)
      · have hfirstSide : (connected first).realization.side =
            closureSide (G := G) (pathPrefixSide path first.1) outsideRoot
              (prefixExteriorComponent_mono hpath
                (Finset.le_max' positions first.1 first.2) outsideRoot
                  hrootAnchor).choose := by
          funext vertex
          exact propext (hside first vertex)
        have hsecondSide : (connected second).realization.side =
            closureSide (G := G) (pathPrefixSide path second.1) outsideRoot
              (prefixExteriorComponent_mono hpath
                (Finset.le_max' positions second.1 second.2) outsideRoot
                  hrootAnchor).choose := by
          funext vertex
          exact propext (hside second vertex)
        have hproper := incidentEdgeShore_closureSide_ssubset hpath hsecondFirst
          (Finset.le_max' positions first.1 first.2) outsideRoot hrootAnchor
        have hnodesProper : (nodes second).shore ⊂ (nodes first).shore := by
          simpa only [nodes, ConnectedShoreNode.toLiteral_shore,
            ConnectedAtWidth.toConnectedShoreNode_shore,
            hfirstSide, hsecondSide] using hproper
        exact cardPhasedState_ne_of_ssubset rotation minimal
          (nodes first) (nodes second) hnodesProper (by
            simpa only [state] using heq)
    have hcard := Fintype.card_le_of_injective state hstateInjective
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin,
      card_stateAtBound, pathPrefixProfileStateCount] using hcard
  · have hempty : positions = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpositions
    simp [hempty]

end

end PathPrefixConnectedCutProfileBound

end Mettapedia.GraphTheory.FourColor.Compositional
