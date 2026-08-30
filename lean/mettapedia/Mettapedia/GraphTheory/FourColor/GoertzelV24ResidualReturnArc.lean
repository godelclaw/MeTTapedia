import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualReturnCycleOrder

/-!
# Literal arcs for residual return chords

The common residual graph supplies more than an abstract endpoint involution.
Each ordered return chord has a chosen simple witnessing path.  Its edges avoid
the operated alternating cycle, its only cycle vertices are its two endpoints,
and paths belonging to distinct chords are vertex-disjoint.

These are the exact graph-theoretic inputs for the remaining spherical
Jordan-arc argument.  No noncrossing conclusion is assumed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ResidualReturnArc

open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnShore
open MatchingParity
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A canonical simple path witnessing one ordered residual return chord. -/
def orderedReturnPath
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (commonResidualGraph G sigma site).Walk
      (cycleVertexOrder sigma site position).1
      (cycleVertexOrder sigma site
        ((orderedSiteReturnPairing hG sigma hSigma site).partner position)).1 :=
  Classical.choose
    (orderedSiteReturnPairing_reachable hG sigma hSigma site position).exists_isPath

/-- The chosen return witness is simple. -/
theorem orderedReturnPath_isPath
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (orderedReturnPath hG sigma hSigma site position).IsPath :=
  Classical.choose_spec
    (orderedSiteReturnPairing_reachable hG sigma hSigma site position).exists_isPath

/-- The chosen return path is nonempty because the return pairing is
fixed-point-free. -/
theorem orderedReturnPath_not_nil
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    ¬(orderedReturnPath hG sigma hSigma site position).Nil := by
  apply SimpleGraph.Walk.not_nil_of_ne
  intro hvalue
  apply (orderedSiteReturnPairing hG sigma hSigma site).partner_ne position
  apply (cycleVertexOrder sigma site).injective
  apply Subtype.ext
  exact hvalue.symm

/-- Every edge of a return arc avoids the operated alternating cycle. -/
theorem orderedReturnPath_edge_not_cycle
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site)
    {edge : Sym2 V}
    (hedge : edge ∈
      (orderedReturnPath hG sigma hSigma site position).edges) :
    edge ∉ site.cycle.edges := by
  have hedgeCommon : edge ∈ (commonResidualGraph G sigma site).edgeSet :=
    (orderedReturnPath hG sigma hSigma site position).edges_subset_edgeSet hedge
  induction edge using Sym2.inductionOn with
  | _ left right =>
      exact commonResidualGraph_adj_not_cycle sigma site
        ((commonResidualGraph G sigma site).mem_edgeSet.mp hedgeCommon)

/-- The only operated-cycle vertices on a return arc are its two endpoints. -/
theorem eq_start_or_eq_finish_of_mem_orderedReturnPath_support_of_mem_carrier
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site)
    {vertex : V}
    (hpath : vertex ∈
      (orderedReturnPath hG sigma hSigma site position).support)
    (hcarrier : vertex ∈ site.carrier) :
    vertex = (cycleVertexOrder sigma site position).1 ∨
      vertex = (cycleVertexOrder sigma site
        ((orderedSiteReturnPairing hG sigma hSigma site).partner position)).1 := by
  let start := cycleVertexOrder sigma site position
  let finish := cycleVertexOrder sigma site
    ((orderedSiteReturnPairing hG sigma hSigma site).partner position)
  by_cases hstart : vertex = start.1
  · exact Or.inl hstart
  · let boundaryVertex : BoundaryVertex site.carrier :=
      ⟨vertex, hcarrier⟩
    have hboundaryNe : boundaryVertex ≠ start := by
      intro heq
      apply hstart
      exact congrArg Subtype.val heq
    have hreach : (commonResidualGraph G sigma site).Reachable
        start.1 boundaryVertex.1 :=
      ((orderedReturnPath hG sigma hSigma site position).takeUntil
        vertex hpath).reachable
    have hpartner := siteReturnPairing_eq_of_reachable
      hG sigma hSigma site start boundaryVertex hboundaryNe hreach
    refine Or.inr ?_
    change vertex = finish.1
    have hfinish := cycleVertexOrder_orderedSiteReturnPairing_partner
      hG sigma hSigma site position
    calc
      vertex = boundaryVertex.1 := rfl
      _ = ((siteReturnPairing hG sigma hSigma site).partner start).1 :=
        (congrArg Subtype.val hpartner).symm
      _ = finish.1 := congrArg Subtype.val hfinish.symm

/-- Canonical arcs for distinct return chords have disjoint vertex supports. -/
theorem orderedReturnPath_support_disjoint_of_chord_ne
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (firstPosition secondPosition : CyclePosition sigma site)
    (hchordNe :
      orderedReturnChord
          (orderedSiteReturnPairing hG sigma hSigma site) firstPosition ≠
        orderedReturnChord
          (orderedSiteReturnPairing hG sigma hSigma site) secondPosition) :
    (orderedReturnPath hG sigma hSigma site firstPosition).support.Disjoint
      (orderedReturnPath hG sigma hSigma site secondPosition).support :=
  orderedSiteReturnPairing_walk_support_disjoint_of_chord_ne
    hG sigma hSigma site firstPosition secondPosition
      (orderedReturnPath hG sigma hSigma site firstPosition)
      (orderedReturnPath hG sigma hSigma site secondPosition) hchordNe

end

end GoertzelV24ResidualReturnArc

end Mettapedia.GraphTheory.FourColor
