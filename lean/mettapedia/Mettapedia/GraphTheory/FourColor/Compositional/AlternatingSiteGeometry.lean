import Mettapedia.GraphTheory.FourColor.GoertzelV24AlternatingMatchingComponent
import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualOddness

/-!
# Residual-defect minimizers and proper alternating components

This module isolates the graph-theoretic content used when a supported perfect
matching is compared with a second supported matching through a prescribed
edge.  It is independent of meshes, deletion colourings, and embeddings.

An exchange-rigid residual-defect minimizer either already contains the
prescribed edge, or the alternating component through that edge is a proper
ambient cycle.  The theorem below constructs the latter witness from the exact
semantic hypotheses.  It does not assert that different prescribed edges have
compatible components.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.AlternatingSiteGeometry

open GoertzelV24AlternatingMatchingComponent
open GoertzelV24ResidualDefectDescent
open GoertzelV24ResidualOddness
open MatchingParity
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A graph-supported perfect matching with positive residual obstruction for
which no exchange with another graph-supported perfect matching lowers the
residual defect. -/
structure ResidualDefectMinimizer (G : SimpleGraph V)
    [DecidableRel G.Adj] where
  pairing : Pairing V
  supported : pairing.SupportedBy G
  two_le_defect : 2 ≤ residualDefect G pairing
  exchange_minimal :
    ∀ (other : Pairing V) (carrier : Finset V)
      (pairing_closed : ∀ vertex ∈ carrier,
        pairing.partner vertex ∈ carrier)
      (other_closed : ∀ vertex ∈ carrier,
        other.partner vertex ∈ carrier),
      other.SupportedBy G →
        residualDefect G pairing ≤
          residualDefect G
            (pairing.exchange other carrier pairing_closed other_closed)

/-- Every bridge-free cubic Tait counterexample has a residual-defect
minimizer. -/
theorem nonempty_residualDefectMinimizer
    (hCubic : G.IsRegularOfDegree 3)
    (hfree : ∀ edge : G.edgeSet, ¬ G.IsBridge edge.1)
    (hnot : ¬ TaitColorable G) :
    Nonempty (ResidualDefectMinimizer G) := by
  obtain ⟨pairing, supported, two_le, exchange_minimal⟩ :=
    exists_exchangeRigid_residualOddness_of_cubic_edgeBridgeFree
      hCubic hfree hnot
  exact ⟨{
    pairing := pairing
    supported := supported
    two_le_defect := two_le
    exchange_minimal := exchange_minimal }⟩

/-- A prescribed edge in the second matching lies on a proper alternating
component against a residual-defect minimizer. -/
structure ProperAlternatingComponentWitness
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (minimizer : Pairing V) (first second : V) where
  tau : Pairing V
  tau_supported : tau.SupportedBy G
  central : tau.partner first = second
  carrier : Finset V
  carrier_eq : carrier = alternatingComponent minimizer tau first
  first_mem : first ∈ carrier
  second_mem : second ∈ carrier
  cycle : G.Walk first first
  cycle_isCycle : cycle.IsCycle
  central_edge_mem_cycle : s(first, second) ∈ cycle.edges
  cycle_support_eq : cycle.support.toFinset = carrier
  cycle_edges_alternating :
    ∀ edge ∈ cycle.edges,
      edge ∈ (alternatingGraph minimizer tau).edgeSet
  sigma_closed :
    ∀ vertex ∈ carrier, minimizer.partner vertex ∈ carrier
  tau_closed : ∀ vertex ∈ carrier, tau.partner vertex ∈ carrier
  disagree_on_carrier :
    ∀ vertex ∈ carrier,
      minimizer.partner vertex ≠ tau.partner vertex
  four_le : 4 ≤ carrier.card
  shared_edge_outside :
    ∃ vertex : V,
      minimizer.partner vertex = tau.partner vertex ∧
      vertex ∉ carrier ∧ minimizer.partner vertex ∉ carrier
  exchange_rigid :
    residualDefect G minimizer ≤
      residualDefect G
        (minimizer.exchange tau carrier sigma_closed tau_closed)

/-- If the minimizer does not use the prescribed edge of a second supported
matching, that edge determines a proper alternating-component witness. -/
theorem properAlternatingComponentWitness_of_partner_ne
    (htriples : HasCubicIncidentEdgeTriples G)
    (hnot : ¬ TaitColorable G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    (other : Pairing V) (hOther : other.SupportedBy G)
    (hExchangeRigid :
      ∀ (carrier : Finset V)
        (hSigmaClosed : ∀ vertex ∈ carrier,
          sigma.partner vertex ∈ carrier)
        (hOtherClosed : ∀ vertex ∈ carrier,
          other.partner vertex ∈ carrier),
        residualDefect G sigma ≤
          residualDefect G
            (sigma.exchange other carrier hSigmaClosed hOtherClosed))
    (first second : V)
    (hprescribed : other.partner first = second)
    (hne : sigma.partner first ≠ second) :
    ∃ witness : ProperAlternatingComponentWitness G sigma first second,
      witness.tau = other := by
  have hroot :
      sigma.partner first ≠ other.partner first := by
    intro heq
    exact hne (heq.trans hprescribed)
  let carrier := alternatingComponent sigma other first
  have hfirst : first ∈ carrier :=
    root_mem_alternatingComponent sigma other first
  have hMinimizerClosed :
      ∀ vertex ∈ carrier, sigma.partner vertex ∈ carrier :=
    alternatingComponent_closed_first sigma other first
  have hOtherClosed :
      ∀ vertex ∈ carrier, other.partner vertex ∈ carrier :=
    alternatingComponent_closed_second sigma other first
  have hsecond : second ∈ carrier := by
    rw [← hprescribed]
    exact hOtherClosed first hfirst
  have hfour : 4 ≤ carrier.card :=
    four_le_card_alternatingComponent sigma other hroot
  obtain ⟨cycle, hcycle, hprescribedCycle, hcycleSupport,
      hcycleEdges⟩ :=
    exists_ambient_alternatingCycle sigma other hSigma hOther hroot
  have hprescribedCycle' : s(first, second) ∈ cycle.edges := by
    simpa only [hprescribed] using hprescribedCycle
  have houtside :
      ∃ vertex : V,
        sigma.partner vertex = other.partner vertex ∧
        vertex ∉ carrier ∧ sigma.partner vertex ∉ carrier :=
    exists_shared_edge_outside_alternatingComponent
      htriples hnot sigma other hSigma hOther hroot
  exact ⟨{
    tau := other
    tau_supported := hOther
    central := hprescribed
    carrier := carrier
    carrier_eq := rfl
    first_mem := hfirst
    second_mem := hsecond
    cycle := cycle
    cycle_isCycle := hcycle
    central_edge_mem_cycle := hprescribedCycle'
    cycle_support_eq := hcycleSupport
    cycle_edges_alternating := hcycleEdges
    sigma_closed := hMinimizerClosed
    tau_closed := hOtherClosed
    disagree_on_carrier := by
      intro vertex hvertex
      apply disagreement_of_mem_alternatingComponent
        sigma other hroot
      simpa only [carrier] using hvertex
    four_le := hfour
    shared_edge_outside := houtside
    exchange_rigid := hExchangeRigid carrier
      hMinimizerClosed hOtherClosed }, rfl⟩

/-- Specialization of the component constructor to a packaged residual-defect
minimizer. -/
theorem ResidualDefectMinimizer.properAlternatingComponentWitness
    (minimizer : ResidualDefectMinimizer G)
    (htriples : HasCubicIncidentEdgeTriples G)
    (hnot : ¬ TaitColorable G)
    (other : Pairing V) (hOther : other.SupportedBy G)
    (first second : V)
    (hprescribed : other.partner first = second)
    (hne : minimizer.pairing.partner first ≠ second) :
    Nonempty
      (ProperAlternatingComponentWitness G minimizer.pairing first second) := by
  obtain ⟨witness, _⟩ := properAlternatingComponentWitness_of_partner_ne
    htriples hnot minimizer.pairing minimizer.supported other hOther
      (fun carrier hMinimizerClosed hOtherClosed =>
        minimizer.exchange_minimal other carrier
          hMinimizerClosed hOtherClosed hOther)
      first second hprescribed hne
  exact ⟨witness⟩

end
end Mettapedia.GraphTheory.FourColor.Compositional.AlternatingSiteGeometry
