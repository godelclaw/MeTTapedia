import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualReturnArc
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkFaceCut

/-!
# Two-sector noncrossing for physical residual returns

The cyclic coordinate and the literal return paths reduce the remaining
geometry to one spherical separation argument.  This file first constructs
the actual cycle interval between the ordered endpoints of a return chord and
the simple closed separator obtained by adjoining that interval to the return
path.  The eventual consumer is the statement that two interleaving residual
returns cannot occupy the same facial shore.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ResidualReturnSectorNoncrossing

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnArc
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnShore
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkFaceCut
open GoertzelV24WalkCycleParity
open MatchingParity
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## The literal interval and separator -/

/-- The cyclic coordinate really is vertex lookup in the tail walk. -/
theorem cycleVertexOrder_val_eq_getVert
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (cycleVertexOrder sigma site position).1 =
      site.cycle.tail.getVert position.val := by
  rw [cycleVertexOrder_apply_val]
  simpa only [List.get_eq_getElem] using
    site.cycle.tail.support_getElem_eq_getVert position.isLt

/-- The oriented subwalk of the operated cycle between the two linearly
ordered endpoints of a canonical return chord. -/
def residualCycleInterval
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) :
    G.Walk (cycleVertexOrder sigma site chord.left).1
      (cycleVertexOrder sigma site chord.right).1 :=
  ((site.cycle.tail.drop chord.left.val).take
      (chord.right.val - chord.left.val)).copy (by
    exact (cycleVertexOrder_val_eq_getVert sigma site chord.left).symm) (by
    calc
      (site.cycle.tail.drop chord.left.val).getVert
          (chord.right.val - chord.left.val) =
          site.cycle.tail.getVert
            (chord.left.val + (chord.right.val - chord.left.val)) := by
        rw [SimpleGraph.Walk.drop_getVert]
      _ = site.cycle.tail.getVert chord.right.val := by
        rw [Nat.add_sub_of_le chord.left_lt_right.le]
      _ = (cycleVertexOrder sigma site chord.right).1 :=
        (cycleVertexOrder_val_eq_getVert sigma site chord.right).symm)

/-- A cycle interval is a simple path. -/
theorem residualCycleInterval_isPath
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) :
    (residualCycleInterval sigma site chord).IsPath := by
  simpa [residualCycleInterval] using
    (site.cycle_isCycle.isPath_tail.drop chord.left.val).take
      (chord.right.val - chord.left.val)

/-- The interval has exactly the difference of its endpoint coordinates as
its edge length. -/
theorem residualCycleInterval_length
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) :
    (residualCycleInterval sigma site chord).length =
      chord.right.val - chord.left.val := by
  simp only [residualCycleInterval, SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length]
  rw [Nat.min_eq_left]
  have hright : chord.right.val ≤ site.cycle.tail.length := by
    have hlt := chord.right.isLt
    have hlength : site.cycle.tail.support.length =
        site.cycle.tail.length + 1 := site.cycle.tail.length_support
    omega
  omega

/-- Vertex lookup inside the interval is lookup at the translated cycle
coordinate. -/
theorem residualCycleInterval_getVert
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) (offset : Nat)
    (hoffset : offset ≤ chord.right.val - chord.left.val) :
    (residualCycleInterval sigma site chord).getVert offset =
      site.cycle.tail.getVert (chord.left.val + offset) := by
  simp only [residualCycleInterval, SimpleGraph.Walk.getVert_copy]
  rw [SimpleGraph.Walk.take_getVert, Nat.min_eq_right hoffset,
    SimpleGraph.Walk.drop_getVert]

/-- Every vertex of the interval lies on the operated cycle. -/
theorem mem_carrier_of_mem_residualCycleInterval_support
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) {vertex : V}
    (hvertex : vertex ∈ (residualCycleInterval sigma site chord).support) :
    vertex ∈ site.carrier := by
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvertex with
    ⟨offset, hvalue, hoffset⟩
  have hoffset' : offset ≤ chord.right.val - chord.left.val := by
    rwa [residualCycleInterval_length sigma site chord] at hoffset
  have hget := residualCycleInterval_getVert sigma site chord offset hoffset'
  apply (mem_cycle_tail_support_iff sigma site).1
  rw [← hvalue, hget]
  exact SimpleGraph.Walk.getVert_mem_support _ _

/-- The chosen ambient return, retyped so that its endpoint is the canonical
right endpoint rather than the definitionally equal partner of the left. -/
def orderedChordAmbientPath
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) :
    G.Walk (cycleVertexOrder sigma site chord.left).1
      (cycleVertexOrder sigma site chord.right).1 :=
  (orderedAmbientReturnPath hG sigma hSigma site chord.left).copy rfl (by
    rw [chord.partner_left])

/-- The chord-typed ambient return remains a simple path. -/
theorem orderedChordAmbientPath_isPath
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) :
    (orderedChordAmbientPath hG sigma hSigma site chord).IsPath := by
  simpa [orderedChordAmbientPath] using
    orderedAmbientReturnPath_isPath hG sigma hSigma site chord.left

/-- A chord-typed ambient return is nonempty. -/
theorem orderedChordAmbientPath_not_nil
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) :
    ¬(orderedChordAmbientPath hG sigma hSigma site chord).Nil := by
  simpa [orderedChordAmbientPath] using
    orderedAmbientReturnPath_not_nil hG sigma hSigma site chord.left

/-- A chord-typed ambient return meets the operated cycle only at its two
ordered endpoints. -/
theorem eq_left_or_eq_right_of_mem_orderedChordAmbientPath_support_of_mem_carrier
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    {vertex : V}
    (hpath : vertex ∈
      (orderedChordAmbientPath hG sigma hSigma site chord).support)
    (hcarrier : vertex ∈ site.carrier) :
    vertex = (cycleVertexOrder sigma site chord.left).1 ∨
      vertex = (cycleVertexOrder sigma site chord.right).1 := by
  have hpath' : vertex ∈
      (orderedAmbientReturnPath hG sigma hSigma site chord.left).support := by
    simpa [orderedChordAmbientPath] using hpath
  rcases
      eq_start_or_eq_finish_of_mem_orderedAmbientReturnPath_support_of_mem_carrier
        hG sigma hSigma site chord.left hpath' hcarrier with hleft | hright
  · exact Or.inl hleft
  · exact Or.inr (by simpa only [chord.partner_left] using hright)

/-- Close one physical return with the reverse operated-cycle interval. -/
def orderedReturnSeparator
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) :
    G.Walk (cycleVertexOrder sigma site chord.left).1
      (cycleVertexOrder sigma site chord.left).1 :=
  (orderedChordAmbientPath hG sigma hSigma site chord).append
    (residualCycleInterval sigma site chord).reverse

/-- If the chosen cycle interval has an interior edge, adjoining its reverse
to the physical return gives a literal simple closed separator.  Interleaving
with another chord will supply this strict length hypothesis. -/
theorem orderedReturnSeparator_isCycle
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hlong : 1 < chord.right.val - chord.left.val) :
    (orderedReturnSeparator hG sigma hSigma site chord).IsCycle := by
  let path := orderedChordAmbientPath hG sigma hSigma site chord
  let interval := residualCycleInterval sigma site chord
  have hpath : path.IsPath :=
    orderedChordAmbientPath_isPath hG sigma hSigma site chord
  have hinterval : interval.IsPath :=
    residualCycleInterval_isPath sigma site chord
  have hreverse : interval.reverse.IsPath :=
    SimpleGraph.Walk.isPath_reverse_iff interval |>.2 hinterval
  unfold orderedReturnSeparator
  apply hpath.isCycle_append hreverse
  · rw [List.disjoint_left]
    intro vertex hpathTail hreverseTail
    have hpathSupport : vertex ∈ path.support :=
      List.mem_of_mem_tail hpathTail
    have hreverseSupport : vertex ∈ interval.reverse.support :=
      List.mem_of_mem_tail hreverseTail
    have hintervalSupport : vertex ∈ interval.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
        hreverseSupport
    have hcarrier : vertex ∈ site.carrier :=
      mem_carrier_of_mem_residualCycleInterval_support
        sigma site chord hintervalSupport
    rcases
        eq_left_or_eq_right_of_mem_orderedChordAmbientPath_support_of_mem_carrier
          hG sigma hSigma site chord hpathSupport hcarrier with hleft | hright
    · have hleftNot :
          (cycleVertexOrder sigma site chord.left).1 ∉ path.support.tail := by
        have hnodup := hpath.support_nodup
        rw [← path.cons_tail_support] at hnodup
        exact (List.nodup_cons.mp hnodup).1
      exact hleftNot (hleft ▸ hpathTail)
    · have hrightNot :
          (cycleVertexOrder sigma site chord.right).1 ∉
            interval.reverse.support.tail := by
        have hnodup := hreverse.support_nodup
        rw [← interval.reverse.cons_tail_support] at hnodup
        exact (List.nodup_cons.mp hnodup).1
      exact hrightNot (hright ▸ hreverseTail)
  · exact Or.inr (by
      rw [SimpleGraph.Walk.length_reverse,
        residualCycleInterval_length sigma site chord]
      exact hlong)

/-! ## Exact facial cut carried by the separator -/

/-- In a graph-backed least counterexample, the literal return separator has
an exact binary face labeling: precisely its primal edges change the label.
This is the combinatorial Jordan separator used by the noncrossing argument. -/
theorem exists_orderedReturnSeparator_exactFaceCut_of_minimal
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hlong : 1 < chord.right.val - chord.left.val) :
    ∃ labels : OrbitFace rotation.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap rotation.toRotationSystem labels =
          walkEdgeParity
            (orderedReturnSeparator hG sigma hSigma site chord) ∧
        ∀ dart : rotation.toRotationSystem.D,
          labels (dartOrbitFace rotation.toRotationSystem dart) ≠
              labels (dartOrbitFace rotation.toRotationSystem
                (rotation.toRotationSystem.alpha dart)) ↔
            (rotation.toRotationSystem.edgeOf dart).1 ∈
              (orderedReturnSeparator hG sigma hSigma site chord).edges := by
  have hconnected : G.Connected := by
    rw [←
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
        G rotation]
    exact minimal.primalConnected
  have hdual := orbitFaceInteriorDual_connected rotation.toRotationSystem
    minimal.spherical.cubic minimal.primalConnected
      minimal.vertexRotationCyclic
  exact exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
    rotation minimal.facesTwoSided hdual hconnected minimal.spherical
      (orderedReturnSeparator hG sigma hSigma site chord)
      (orderedReturnSeparator_isCycle hG sigma hSigma site chord hlong).isTrail

/-! ## A distinct return avoids the first separator -/

/-- An ordered chord is recovered by canonicalizing its left endpoint. -/
theorem orderedReturnChord_left_eq
    {n : Nat} {pairing : Pairing (Fin n)}
    (chord : OrderedReturnChord pairing) :
    orderedReturnChord pairing chord.left = chord := by
  apply OrderedReturnChord.ext
  · simp [orderedReturnChord, chord.partner_left,
      min_eq_left chord.left_lt_right.le]
  · simp [orderedReturnChord, chord.partner_left,
      max_eq_right chord.left_lt_right.le]

/-- Canonical ambient paths belonging to distinct return components have
disjoint vertex supports. -/
theorem orderedChordAmbientPath_support_disjoint_of_ne
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (left right : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hne : left ≠ right) :
    (orderedChordAmbientPath hG sigma hSigma site left).support.Disjoint
      (orderedChordAmbientPath hG sigma hSigma site right).support := by
  have hchordNe :
      orderedReturnChord
          (orderedSiteReturnPairing hG sigma hSigma site) left.left ≠
        orderedReturnChord
          (orderedSiteReturnPairing hG sigma hSigma site) right.left := by
    simpa only [orderedReturnChord_left_eq] using hne
  have hdisjoint := orderedReturnPath_support_disjoint_of_chord_ne
    hG sigma hSigma site left.left right.left hchordNe
  simpa [orderedChordAmbientPath, orderedAmbientReturnPath,
    SimpleGraph.Walk.support_mapLe_eq_support] using hdisjoint

/-- Disjoint vertex supports force disjoint edge lists. -/
theorem orderedChordAmbientPath_edges_disjoint_of_ne
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (left right : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hne : left ≠ right) :
    (orderedChordAmbientPath hG sigma hSigma site left).edges.Disjoint
      (orderedChordAmbientPath hG sigma hSigma site right).edges := by
  have hsupport := orderedChordAmbientPath_support_disjoint_of_ne
    hG sigma hSigma site left right hne
  rw [List.disjoint_left] at hsupport ⊢
  intro edge hleft hright
  induction edge using Sym2.inductionOn with
  | _ firstVertex secondVertex =>
      exact hsupport
        ((orderedChordAmbientPath hG sigma hSigma site left).fst_mem_support_of_mem_edges
          hleft)
        ((orderedChordAmbientPath hG sigma hSigma site right).fst_mem_support_of_mem_edges
          hright)

/-- Every edge of the literal cycle interval is an edge of the full operated
cycle. -/
theorem mem_cycle_edges_of_mem_residualCycleInterval_edges
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) {edge : Sym2 V}
    (hedge : edge ∈ (residualCycleInterval sigma site chord).edges) :
    edge ∈ site.cycle.edges := by
  have hintervalTail : edge ∈ site.cycle.tail.edges := by
    have hsubwalk :
        ((site.cycle.tail.drop chord.left.val).take
            (chord.right.val - chord.left.val)).IsSubwalk site.cycle.tail :=
      (SimpleGraph.Walk.isSubwalk_take _ _).trans
        (SimpleGraph.Walk.isSubwalk_drop _ _)
    apply hsubwalk.edges_subset
    simpa [residualCycleInterval] using hedge
  exact (site.cycle.isSubwalk_rfl.tail.edges_subset) hintervalTail

/-- The separator edge list is exactly the union of the physical return and
the selected cycle interval. -/
theorem mem_orderedReturnSeparator_edges_iff
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (edge : Sym2 V) :
    edge ∈ (orderedReturnSeparator hG sigma hSigma site chord).edges ↔
      edge ∈ (orderedChordAmbientPath hG sigma hSigma site chord).edges ∨
        edge ∈ (residualCycleInterval sigma site chord).edges := by
  simp [orderedReturnSeparator, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_reverse]

/-- A second return component avoids every edge of the separator formed from
a distinct first return. -/
theorem orderedChordAmbientPath_edge_not_orderedReturnSeparator_of_ne
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (separatorChord otherChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hne : separatorChord ≠ otherChord)
    {edge : Sym2 V}
    (hedge : edge ∈
      (orderedChordAmbientPath hG sigma hSigma site otherChord).edges) :
    edge ∉
      (orderedReturnSeparator hG sigma hSigma site separatorChord).edges := by
  intro hseparator
  rcases (mem_orderedReturnSeparator_edges_iff hG sigma hSigma site
      separatorChord edge).1 hseparator with hreturn | hinterval
  · have hdisjoint := orderedChordAmbientPath_edges_disjoint_of_ne
      hG sigma hSigma site separatorChord otherChord hne
    exact (List.disjoint_left.mp hdisjoint hreturn) hedge
  · have hcycle := mem_cycle_edges_of_mem_residualCycleInterval_edges
      sigma site separatorChord hinterval
    have hedgeReturn : edge ∈
        (orderedReturnPath hG sigma hSigma site otherChord.left).edges := by
      simpa [orderedChordAmbientPath, orderedAmbientReturnPath,
        SimpleGraph.Walk.edges_mapLe_eq_edges] using hedge
    exact (orderedReturnPath_edge_not_cycle hG sigma hSigma site
      otherChord.left hedgeReturn) hcycle

/-- Any exact face-cut labeling of one return separator is transported
unchanged between the two canonical third darts of a distinct return. -/
theorem separatorLabels_eq_otherChord_thirdDarts
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (separatorChord otherChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hne : separatorChord ≠ otherChord)
    {A : Type*}
    (labels : OrbitFace rotation.toRotationSystem → A)
    (hexact : ∀ dart : rotation.toRotationSystem.D,
      labels (dartOrbitFace rotation.toRotationSystem dart) ≠
          labels (dartOrbitFace rotation.toRotationSystem
            (rotation.toRotationSystem.alpha dart)) ↔
        (rotation.toRotationSystem.edgeOf dart).1 ∈
          (orderedReturnSeparator hG sigma hSigma site separatorChord).edges) :
    labels (dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site otherChord.left))) =
      labels (dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site otherChord.right))) := by
  let path :=
    orderedAmbientReturnPath hG sigma hSigma site otherChord.left
  have hnil : ¬path.Nil :=
    orderedAmbientReturnPath_not_nil hG sigma hSigma site otherChord.left
  have htransport :=
    rotation.trail_labels_eq_firstDart_alpha_lastDart_of_walk_edges_not_cut
      hcubic hrotation labels
        (fun edge : G.edgeSet => edge.1 ∈
          (orderedReturnSeparator hG sigma hSigma site separatorChord).edges)
        hexact path hnil
        (orderedAmbientReturnPath_isPath
          hG sigma hSigma site otherChord.left).isTrail
        (by
          intro edge hedge
          apply orderedChordAmbientPath_edge_not_orderedReturnSeparator_of_ne
            hG sigma hSigma site separatorChord otherChord hne
          simpa [path, orderedChordAmbientPath] using hedge)
  have hfirst :
      path.firstDart hnil =
        siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site otherChord.left) := by
    simpa [path] using
      orderedAmbientReturnPath_firstDart
        hG sigma hSigma site otherChord.left
  have hlast :
      rotation.toRotationSystem.alpha (path.lastDart hnil) =
        siteThirdDart hG sigma hSigma site
          (cycleVertexOrder sigma site
            ((orderedSiteReturnPairing hG sigma hSigma site).partner
              otherChord.left)) := by
    change (path.lastDart hnil).symm = _
    simpa [path] using
      orderedAmbientReturnPath_alpha_lastDart
        hG sigma hSigma site otherChord.left
  rw [hfirst, hlast] at htransport
  simpa only [otherChord.partner_left] using htransport

/-- Either interleaving order supplies an interior point of each chord's
linear interval. -/
theorem OrderedReturnChord.interval_long_of_crosses
    {n : Nat} {pairing : Pairing (Fin n)}
    {left right : OrderedReturnChord pairing}
    (hcrosses : left.Crosses right) :
    1 < left.right.val - left.left.val ∧
      1 < right.right.val - right.left.val := by
  rcases hcrosses with hforward | hreverse <;> omega

end

end GoertzelV24ResidualReturnSectorNoncrossing

end Mettapedia.GraphTheory.FourColor
