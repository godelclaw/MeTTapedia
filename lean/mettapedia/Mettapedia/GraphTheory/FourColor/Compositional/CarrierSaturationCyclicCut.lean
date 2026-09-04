import Mettapedia.GraphTheory.FourColor.Compositional.CarrierSaturationConnected
import Mettapedia.GraphTheory.FourColor.Compositional.CarrierBoundaryDeepAlternative
import Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixCyclicCut

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CarrierSaturationCyclicCut

open CarrierSaturationBoundaryDecomposition
open CarrierSaturationConnected
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24CyclicThreeCutConnectedSides
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open MatchingParity
open Mettapedia.GraphTheory
open PathPrefixBoundary
open PathPrefixCyclicCut
open ResidualReturnComponentSaturation
open ResidualReturnPathAttachment
open RootedCutSaturation
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Convert an ordinary coordinate on the opened carrier path back to the
cyclic coordinate with the same numerical value. -/
def carrierCyclePositionOfPathCoordinate
    {sigma : Pairing V} {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (coordinate : Fin (site.cycle.tail.length + 1)) :
    CyclePosition sigma site :=
  ⟨coordinate.val, by
    simpa only [SimpleGraph.Walk.length_support] using coordinate.isLt⟩

@[simp] theorem carrierCyclePositionOfPathCoordinate_val
    {sigma : Pairing V} {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (coordinate : Fin (site.cycle.tail.length + 1)) :
    (carrierCyclePositionOfPathCoordinate site coordinate).val = coordinate.val :=
  rfl

theorem cycleVertexOrder_carrierCyclePositionOfPathCoordinate
    {sigma : Pairing V} {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (coordinate : Fin (site.cycle.tail.length + 1)) :
    (cycleVertexOrder sigma site
      (carrierCyclePositionOfPathCoordinate site coordinate)).1 =
        site.cycle.tail.getVert coordinate := by
  rw [cycleVertexOrder_apply_val]
  rw [List.get_eq_getElem,
    site.cycle.tail.support_getElem_eq_getVert]
  rfl

@[simp] theorem carrierCyclePositionOfPathCut
    {sigma : Pairing V} {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    carrierCyclePositionOfPathCoordinate site (carrierPrefixPathCut site cut) =
      cut := by
  apply Fin.ext
  rfl

/-- The first omitted carrier vertex is outside the component-saturated
prefix. -/
theorem not_carrierPrefixReturnSaturation_cycleVertex_cut
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    ¬carrierPrefixReturnSaturation hG sigma hSigma site cut
      (cycleVertexOrder sigma site cut).1 := by
  rw [cycleVertex_mem_carrierPrefixReturnSaturation_iff]
  exact lt_irrefl cut

/-- The complementary component rooted at the first omitted carrier vertex. -/
def carrierPrefixExteriorComponent
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) : V → Prop :=
  inducedReachableSide G
    (fun vertex =>
      ¬carrierPrefixReturnSaturation hG sigma hSigma site cut vertex)
    (cycleVertexOrder sigma site cut).1
    (not_carrierPrefixReturnSaturation_cycleVertex_cut
      hG sigma hSigma site cut)

/-- Every carrier vertex at or after the cut lies in the rooted exterior
component of the saturated prefix. -/
theorem cycleVertex_mem_carrierPrefixExteriorComponent
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut position : CyclePosition sigma site) (horder : cut ≤ position) :
    carrierPrefixExteriorComponent hG sigma hSigma site cut
      (cycleVertexOrder sigma site position).1 := by
  let pathCut := carrierPrefixPathCut site cut
  let coordinate : Fin (site.cycle.tail.length + 1) :=
    ⟨position.val, by
      simpa only [SimpleGraph.Walk.length_support] using position.isLt⟩
  have hpathOrder : pathCut.val ≤ coordinate.val := by
    simpa only [pathCut, coordinate, carrierPrefixPathCut_val] using
      (Fin.mk_le_mk.mp horder)
  let interval := walkInterval site.cycle.tail pathCut.val coordinate.val
    hpathOrder
  have hcoordinateBound : coordinate.val ≤ site.cycle.tail.length :=
    Nat.lt_succ_iff.mp coordinate.isLt
  have hintervalLength : interval.length = coordinate.val - pathCut.val := by
    exact walkInterval_length site.cycle.tail pathCut.val coordinate.val
      hpathOrder hcoordinateBound
  have hsupport : ∀ vertex, vertex ∈ interval.support →
      ¬carrierPrefixReturnSaturation hG sigma hSigma site cut vertex := by
    intro vertex hvertex
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hvertex
    rcases hvertex with ⟨offset, hoffsetVertex, hoffsetBound⟩
    rw [hintervalLength] at hoffsetBound
    have htranslatedBound : pathCut.val + offset ≤ site.cycle.tail.length := by
      omega
    let translated : Fin (site.cycle.tail.length + 1) :=
      ⟨pathCut.val + offset, Nat.lt_succ_iff.mpr htranslatedBound⟩
    have htranslatedVertex : site.cycle.tail.getVert translated = vertex := by
      change site.cycle.tail.getVert (pathCut.val + offset) = vertex
      rw [← hoffsetVertex]
      exact (walkInterval_getVert site.cycle.tail pathCut.val coordinate.val
        offset hpathOrder hoffsetBound).symm
    rw [← htranslatedVertex,
      ← cycleVertexOrder_carrierCyclePositionOfPathCoordinate]
    rw [cycleVertex_mem_carrierPrefixReturnSaturation_iff]
    change ¬pathCut.val + offset < cut.val
    simp only [pathCut, carrierPrefixPathCut_val]
    omega
  refine ⟨?_, ?_⟩
  · change ¬carrierPrefixReturnSaturation hG sigma hSigma site cut
      (cycleVertexOrder sigma site position).1
    rw [cycleVertex_mem_carrierPrefixReturnSaturation_iff]
    exact not_lt_of_ge horder
  · let inside := interval.induce
      (fun vertex =>
        ¬carrierPrefixReturnSaturation hG sigma hSigma site cut vertex)
      hsupport
    have hreach :
        (G.induce (fun vertex =>
          ¬carrierPrefixReturnSaturation hG sigma hSigma site cut vertex)).Reachable
          ⟨site.cycle.tail.getVert pathCut, by
            rw [← cycleVertexOrder_carrierCyclePositionOfPathCoordinate,
              carrierCyclePositionOfPathCut]
            exact not_carrierPrefixReturnSaturation_cycleVertex_cut
              hG sigma hSigma site cut⟩
          ⟨site.cycle.tail.getVert coordinate, by
            rw [← cycleVertexOrder_carrierCyclePositionOfPathCoordinate]
            change ¬carrierPrefixReturnSaturation hG sigma hSigma site cut
              (cycleVertexOrder sigma site
                (carrierCyclePositionOfPathCoordinate site coordinate)).1
            rw [cycleVertex_mem_carrierPrefixReturnSaturation_iff]
            have heq : carrierCyclePositionOfPathCoordinate site coordinate =
                position := by
              apply Fin.ext
              rfl
            rw [heq]
            exact not_lt_of_ge horder⟩ := by
      exact ⟨inside⟩
    change (G.induce (fun vertex =>
      ¬carrierPrefixReturnSaturation hG sigma hSigma site cut vertex)).Reachable
        ⟨(cycleVertexOrder sigma site cut).1, _⟩
        ⟨(cycleVertexOrder sigma site position).1, _⟩
    convert hreach using 1
    · apply Subtype.ext
      change (cycleVertexOrder sigma site cut).1 =
        site.cycle.tail.getVert pathCut
      calc
        (cycleVertexOrder sigma site cut).1 =
            (cycleVertexOrder sigma site
              (carrierCyclePositionOfPathCoordinate site pathCut)).1 := by
          rw [carrierCyclePositionOfPathCut]
        _ = site.cycle.tail.getVert pathCut :=
          cycleVertexOrder_carrierCyclePositionOfPathCoordinate site pathCut
    · apply Subtype.ext
      change (cycleVertexOrder sigma site position).1 =
        site.cycle.tail.getVert coordinate
      have heq : carrierCyclePositionOfPathCoordinate site coordinate =
          position := by
        apply Fin.ext
        rfl
      calc
        (cycleVertexOrder sigma site position).1 =
            (cycleVertexOrder sigma site
              (carrierCyclePositionOfPathCoordinate site coordinate)).1 := by
          rw [heq]
        _ = site.cycle.tail.getVert coordinate :=
          cycleVertexOrder_carrierCyclePositionOfPathCoordinate site coordinate

/-- The rooted exterior component contains every distinct carrier vertex in
the displayed suffix. -/
theorem suffixLength_le_natCard_carrierPrefixExteriorComponent
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    Fintype.card (CyclePosition sigma site) - cut.val ≤
      Fintype.card {vertex : V //
        carrierPrefixExteriorComponent hG sigma hSigma site cut vertex} := by
  let suffixVertex : Fin (Fintype.card (CyclePosition sigma site) - cut.val) →
      {vertex : V //
        carrierPrefixExteriorComponent hG sigma hSigma site cut vertex} :=
    fun index =>
      let position : CyclePosition sigma site :=
        ⟨cut.val + index.val, by
          have hcard : Fintype.card (CyclePosition sigma site) =
              site.cycle.tail.support.length := by simp
          have := index.isLt
          omega⟩
      ⟨(cycleVertexOrder sigma site position).1,
        cycleVertex_mem_carrierPrefixExteriorComponent hG sigma hSigma site
          cut position (by
            apply Fin.mk_le_mk.mpr
            omega)⟩
  have hinjective : Function.Injective suffixVertex := by
    intro left right heq
    apply Fin.ext
    have hvertices := congrArg (fun vertex => vertex.1) heq
    have hpositions :
        (⟨cut.val + left.val, by
          have hcard : Fintype.card (CyclePosition sigma site) =
              site.cycle.tail.support.length := by simp
          have := left.isLt
          omega⟩ : CyclePosition sigma site) =
        ⟨cut.val + right.val, by
          have hcard : Fintype.card (CyclePosition sigma site) =
              site.cycle.tail.support.length := by simp
          have := right.isLt
          omega⟩ := by
      apply (cycleVertexOrder sigma site).injective
      apply Subtype.ext
      exact hvertices
    have hvalues := congrArg Fin.val hpositions
    exact Nat.add_left_cancel hvalues
  simpa using Fintype.card_le_of_injective suffixVertex hinjective

/-- Outgoing darts of the saturated prefix are exactly the usual oriented
crossing darts, so their cardinality is the cardinality of its crossing-edge
finset. -/
theorem card_crossingEdgeFinset_carrierPrefixReturnSaturation
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    (crossingEdgeFinset G
      (carrierPrefixReturnSaturation hG sigma hSigma site cut)).card =
        Nat.card (AmbientExitDart hG sigma hSigma site cut) := by
  rw [card_crossingEdgeFinset_eq_card_crossingSideDart]
  calc
    Fintype.card (CrossingSideDart G
        (carrierPrefixReturnSaturation hG sigma hSigma site cut)) =
        Nat.card (CrossingSideDart G
          (carrierPrefixReturnSaturation hG sigma hSigma site cut)) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (AmbientExitDart hG sigma hSigma site cut) := by
      rfl

/-- The saturated prefix contains at least the selected carrier coordinates. -/
theorem cut_le_natCard_carrierPrefixReturnSaturation
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) (hcut : 0 < cut.val) :
    cut.val ≤ Fintype.card {vertex : V //
      carrierPrefixReturnSaturation hG sigma hSigma site cut vertex} := by
  let inclusion :
      {vertex : V // pathPrefixSide site.cycle.tail
        (carrierPrefixPathCut site cut) vertex} →
      {vertex : V //
        carrierPrefixReturnSaturation hG sigma hSigma site cut vertex} :=
    fun vertex => ⟨vertex.1, by
      have hboundary : ∃ position : CyclePosition sigma site,
          carrierPrefixSelected cut position ∧
            (cycleVertexOrder sigma site position).1 = vertex.1 := by
        exact (congrFun
          (carrierPrefixBoundarySide_eq_pathPrefixSide site cut)
          vertex.1).mpr vertex.2
      exact Or.inl hboundary⟩
  have hinjective : Function.Injective inclusion := by
    intro left right heq
    apply Subtype.ext
    simpa [inclusion] using congrArg Subtype.val heq
  calc
    cut.val = Nat.card {vertex : V // pathPrefixSide site.cycle.tail
        (carrierPrefixPathCut site cut) vertex} := by
      symm
      exact natCard_pathPrefixSide_eq site.cycle_isCycle.isPath_tail
        (carrierPrefixPathCut site cut) hcut
    _ ≤ Nat.card {vertex : V //
        carrierPrefixReturnSaturation hG sigma hSigma site cut vertex} :=
      Nat.card_le_card_of_injective inclusion hinjective
    _ = Fintype.card {vertex : V //
        carrierPrefixReturnSaturation hG sigma hSigma site cut vertex} :=
      Nat.card_eq_fintype_card

/-- The component of the complement rooted at the first omitted carrier
vertex is connected. -/
theorem induce_carrierPrefixExteriorComponent_connected
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    (G.induce
      (carrierPrefixExteriorComponent hG sigma hSigma site cut)).Connected := by
  exact induce_inducedReachableSide_connected
    (fun vertex =>
      ¬carrierPrefixReturnSaturation hG sigma hSigma site cut vertex)
    (cycleVertexOrder sigma site cut).1
    (not_carrierPrefixReturnSaturation_cycleVertex_cut
      hG sigma hSigma site cut)

/-- The boundary of the rooted exterior component is no larger than the
boundary of the saturated prefix it complements. -/
theorem card_crossingEdgeFinset_carrierPrefixExteriorComponent_le
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    (crossingEdgeFinset G
      (carrierPrefixExteriorComponent hG sigma hSigma site cut)).card ≤
        Nat.card (AmbientExitDart hG sigma hSigma site cut) := by
  calc
    (crossingEdgeFinset G
        (carrierPrefixExteriorComponent hG sigma hSigma site cut)).card ≤
        (crossingEdgeFinset G
          (carrierPrefixReturnSaturation hG sigma hSigma site cut)).card := by
      apply Finset.card_le_card
      intro edge hedge
      apply (mem_crossingEdgeFinset_iff
        (carrierPrefixReturnSaturation hG sigma hSigma site cut) edge).2
      have hcrossExterior :=
        (mem_crossingEdgeFinset_iff
          (carrierPrefixExteriorComponent hG sigma hSigma site cut) edge).1
            hedge
      have hcrossComplement : EdgeCrossesVertexSide G
          (fun vertex =>
            ¬carrierPrefixReturnSaturation hG sigma hSigma site cut vertex)
          edge := by
        exact edgeCrossesVertexSide_of_inducedReachableSide
          (fun vertex =>
            ¬carrierPrefixReturnSaturation hG sigma hSigma site cut vertex)
          (cycleVertexOrder sigma site cut).1
          (not_carrierPrefixReturnSaturation_cycleVertex_cut
            hG sigma hSigma site cut)
          edge hcrossExterior
      exact (edgeCrossesVertexSide_compl G
        (carrierPrefixReturnSaturation hG sigma hSigma site cut) edge).1
          hcrossComplement
    _ = Nat.card (AmbientExitDart hG sigma hSigma site cut) :=
      card_crossingEdgeFinset_carrierPrefixReturnSaturation
        hG sigma hSigma site cut

/-- The rooted exterior of a saturated carrier prefix contains a cycle once
the displayed carrier suffix exceeds the cubic-tree boundary budget. -/
theorem hasCycleOnSide_carrierPrefixExteriorComponent
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site)
    (bound : Nat)
    (hboundary : Nat.card (AmbientExitDart hG sigma hSigma site cut) ≤ bound)
    (hsuffixLarge : bound <
      (Fintype.card (CyclePosition sigma site) - cut.val) + 2) :
    HasCycleOnSide G
      (carrierPrefixExteriorComponent hG sigma hSigma site cut) := by
  let exterior := carrierPrefixExteriorComponent hG sigma hSigma site cut
  have hexteriorConnected : (G.induce exterior).Connected :=
    induce_carrierPrefixExteriorComponent_connected hG sigma hSigma site cut
  have hexteriorNonempty : ∃ vertex, exterior vertex := by
    refine ⟨(cycleVertexOrder sigma site cut).1, ?_⟩
    exact inducedReachableSide_root
      (fun vertex =>
        ¬carrierPrefixReturnSaturation hG sigma hSigma site cut vertex)
      (cycleVertexOrder sigma site cut).1
      (not_carrierPrefixReturnSaturation_cycleVertex_cut
        hG sigma hSigma site cut)
  have hexteriorBoundary : (crossingEdgeFinset G exterior).card ≤ bound :=
    (card_crossingEdgeFinset_carrierPrefixExteriorComponent_le
      hG sigma hSigma site cut).trans hboundary
  apply hasCycleOnSide_of_connected_cubic_of_boundary_lt_card_add_two
    (regularOfDegreeThree_of_cubicIncidentTriples hG)
    exterior hexteriorNonempty hexteriorConnected bound hexteriorBoundary
  have hcard := suffixLength_le_natCard_carrierPrefixExteriorComponent
    hG sigma hSigma site cut
  exact hsuffixLarge.trans_le (Nat.add_le_add_right hcard 2)

/-- With two margins beyond the cubic tree budget, a bounded saturated
carrier prefix is a genuine cyclic edge cut. -/
def carrierPrefixCyclicEdgeCutRealization
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) (hcut : 0 < cut.val)
    (bound : Nat)
    (hboundary : Nat.card (AmbientExitDart hG sigma hSigma site cut) ≤ bound)
    (hprefixLarge : bound < cut.val + 2)
    (hsuffixLarge : bound <
      (Fintype.card (CyclePosition sigma site) - cut.val) + 2) :
    CyclicEdgeCutRealization G
      (crossingEdgeFinset G
        (carrierPrefixReturnSaturation hG sigma hSigma site cut)) := by
  let side := carrierPrefixReturnSaturation hG sigma hSigma site cut
  let exterior := carrierPrefixExteriorComponent hG sigma hSigma site cut
  have hsideConnected : (G.induce side).Connected := by
    exact induce_carrierPrefixReturnSaturation_connected
      hG sigma hSigma site cut hcut
  have hsideNonempty : ∃ vertex, side vertex := by
    rcases hsideConnected.nonempty with ⟨vertex⟩
    exact ⟨vertex.1, vertex.2⟩
  have hsideBoundary : (crossingEdgeFinset G side).card ≤ bound := by
    rw [card_crossingEdgeFinset_carrierPrefixReturnSaturation]
    exact hboundary
  have hsideCycle : HasCycleOnSide G side := by
    apply hasCycleOnSide_of_connected_cubic_of_boundary_lt_card_add_two
      (regularOfDegreeThree_of_cubicIncidentTriples hG)
      side hsideNonempty hsideConnected bound hsideBoundary
    have hcard := cut_le_natCard_carrierPrefixReturnSaturation
      hG sigma hSigma site cut hcut
    exact hprefixLarge.trans_le (Nat.add_le_add_right hcard 2)
  have hexteriorConnected : (G.induce exterior).Connected :=
    induce_carrierPrefixExteriorComponent_connected hG sigma hSigma site cut
  have hexteriorNonempty : ∃ vertex, exterior vertex := by
    refine ⟨(cycleVertexOrder sigma site cut).1, ?_⟩
    exact inducedReachableSide_root
      (fun vertex => ¬side vertex)
      (cycleVertexOrder sigma site cut).1
      (not_carrierPrefixReturnSaturation_cycleVertex_cut
        hG sigma hSigma site cut)
  have hexteriorBoundary : (crossingEdgeFinset G exterior).card ≤ bound :=
    (card_crossingEdgeFinset_carrierPrefixExteriorComponent_le
      hG sigma hSigma site cut).trans hboundary
  have hexteriorCycle : HasCycleOnSide G exterior := by
    apply hasCycleOnSide_of_connected_cubic_of_boundary_lt_card_add_two
      (regularOfDegreeThree_of_cubicIncidentTriples hG)
      exterior hexteriorNonempty hexteriorConnected bound hexteriorBoundary
    have hcard := suffixLength_le_natCard_carrierPrefixExteriorComponent
      hG sigma hSigma site cut
    exact hsuffixLarge.trans_le (Nat.add_le_add_right hcard 2)
  refine
    { side := side
      hcut_eq := fun edge => mem_crossingEdgeFinset_iff _ _
      hinside_cycle := hsideCycle
      houtside_cycle := ?_ }
  apply HasCycleOnSide.mono
      (side₁ := exterior) (side₂ := fun vertex => ¬side vertex)
  · intro _ hcomponent
    simpa [exterior, carrierPrefixExteriorComponent] using hcomponent.choose
  · exact hexteriorCycle

/-- Rooted saturation turns the preceding raw cyclic cut into connected
complementary shores without increasing the explicit width. -/
theorem exists_connectedAtWidth_carrierPrefix
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
      (Fintype.card (CyclePosition sigma site) - cut.val) + 2) :
    Nonempty (CyclicEdgeCutRealization.ConnectedAtWidth G bound) := by
  let raw := carrierPrefixCyclicEdgeCutRealization hG sigma hSigma site cut
    hcut bound hboundary hprefixLarge hsuffixLarge
  have hrawBoundary :
      (crossingEdgeFinset G
        (carrierPrefixReturnSaturation hG sigma hSigma site cut)).card ≤
          bound := by
    rw [card_crossingEdgeFinset_carrierPrefixReturnSaturation]
    exact hboundary
  rcases raw.houtside_cycle with
    ⟨outsideRoot, houtsideRoot, outsideCycle, hcycle, hsupport⟩
  have hrawConnected : (G.induce raw.side).Connected := by
    change (G.induce
      (carrierPrefixReturnSaturation hG sigma hSigma site cut)).Connected
    exact induce_carrierPrefixReturnSaturation_connected
      hG sigma hSigma site cut hcut
  rcases RootedCutSaturation.exists_connectedAtWidth hconnected raw
      hrawConnected outsideRoot houtsideRoot outsideCycle hcycle hsupport
      bound hrawBoundary with ⟨connected, _hedges, _hside⟩
  exact ⟨connected⟩

end

end CarrierSaturationCyclicCut

end Mettapedia.GraphTheory.FourColor.Compositional
