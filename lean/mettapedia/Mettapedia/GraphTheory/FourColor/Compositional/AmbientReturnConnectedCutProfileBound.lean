import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnCentralCutFamily
import Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixRootedNesting
import Mettapedia.GraphTheory.FourColor.CyclicCutConnectedShore

/-!
# Full-profile bound for shallow ambient-return cuts

Many shallow middle positions are first promoted to actual cyclic cuts.  A
cycle in the suffix component of the last position then anchors a common
rooted saturation of every cut.  These saturated shores are strictly nested,
so the physical replacement theorem makes their complete phased profiles
pairwise distinct in a vertex-minimal counterexample.  Their number is
therefore bounded by the exact finite profile carrier.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace AmbientReturnConnectedCutProfileBound

open AmbientReturnCentralCutFamily
open AmbientReturnSweepBoundedRepeat
open AmbientReturnSweepInterface
open CubicPathChordDiagram
open CyclicEdgeCutRealization
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24MajorityShoreStateDescent
open GoertzelV24NoncrossingSweepLifo
open GoertzelV24NormalizedShoreDescent
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory
open PathPrefixBoundary
open PathPrefixCyclicCut
open PathPrefixRootedNesting
open ResidualReturnPathAttachment
open RootedCutSaturation
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Cardinality of the complete phased interface carrier at width `bound`. -/
def connectedCutProfileStateCount (bound : Nat) : Nat :=
  (6 * bound + 1) *
    (∑ j : Fin (bound + 1),
      Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat)))

/-- Saturate one prefix at a prescribed exterior root and cycle.  The
resulting side is definitionally characterized as the rooted closure of the
raw prefix side. -/
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

/-- A shallow central family in a least counterexample has at most the exact
number of complete phased connected-shore profiles. -/
theorem ShallowCentralCutFamilyReceipt.card_le_profileStateCount
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (depth target : Nat)
    (receipt : ShallowCentralCutFamilyReceipt rotation minimal hG sigma hSigma
      site returnChord closure depth target) :
    (centralSweepPositions hG sigma hSigma site returnChord depth).card ≤
      connectedCutProfileStateCount (physicalSweepBound depth) := by
  classical
  let path := orderedChordAmbientPath hG sigma hSigma site returnChord
  let hpath := orderedChordAmbientPath_isPath hG sigma hSigma site returnChord
  let hregular := regularOfDegreeThree_of_cubicIncidentTriples hG
  let bound := physicalSweepBound depth
  let positions := centralSweepPositions hG sigma hSigma site returnChord depth
  have hpositionsNonempty : positions.Nonempty := by
    apply Finset.card_pos.mp
    have hm : target < positions.card := by
      simpa only [positions] using receipt.many
    exact lt_of_le_of_lt (Nat.zero_le target) hm
  let anchor := positions.max' hpositionsNonempty
  have hanchorMem : anchor ∈ positions := Finset.max'_mem positions hpositionsNonempty
  have hanchorBoundary :
      (crossingEdgeFinset G (pathPrefixSide path anchor)).card ≤ bound := by
    simpa only [path, bound] using
      ShallowCentralCutFamilyReceipt.boundaryWidth rotation minimal hG sigma
        hSigma site returnChord closure depth target receipt hanchorMem
  have hanchorMargins : bound ≤ anchor.val ∧
      bound ≤ path.length + 1 - anchor.val := by
    simpa only [path, bound] using
      ShallowCentralCutFamilyReceipt.margins rotation minimal hG sigma hSigma
        site returnChord closure depth target receipt hanchorMem
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
    have hcutEligible :=
      ShallowCentralCutFamilyReceipt.mem_eligible rotation minimal hG sigma
        hSigma site returnChord closure depth target receipt cut.2
    have hcutPositive :=
      positive_of_mem_eligibleAmbientReturnSweepPositions hG sigma hSigma site
        returnChord cut.1 hcutEligible
    have hcutBoundary :
        (crossingEdgeFinset G (pathPrefixSide path cut.1)).card ≤ bound := by
      simpa only [path, bound] using
        ShallowCentralCutFamilyReceipt.boundaryWidth rotation minimal hG sigma
          hSigma site returnChord closure depth target receipt cut.2
    have hcutMargins : bound ≤ cut.1.val ∧
        bound ≤ path.length + 1 - cut.1.val := by
      simpa only [path, bound] using
        ShallowCentralCutFamilyReceipt.margins rotation minimal hG sigma hSigma
          site returnChord closure depth target receipt cut.2
    have hprefixLarge : bound < cut.1.val + 2 := by
      omega
    have hsuffixLarge : bound < path.length + 1 - cut.1.val + 2 := by
      omega
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
    card_stateAtBound, positions, bound, connectedCutProfileStateCount] using
      hcard

end

end AmbientReturnConnectedCutProfileBound

end Mettapedia.GraphTheory.FourColor.Compositional
