import Mettapedia.GraphTheory.FourColor.Compositional.AlternatingSiteGeometry
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedEdgeStructure

/-!
# Alternating carriers as unions of two matching roles

The source closed-web picture uses unions of two colour-class matchings,
whereas the residual route represents an alternating graph by symmetric
difference.  These representations agree precisely where the two matching
roles are edge-disjoint.

This file proves that agreement first for an arbitrary finite carrier and
then for every `ProperAlternatingComponentWitness`.  The latter already
contains the required pointwise disagreement theorem, so no new geometric or
colouring hypothesis is introduced.  This identifies the actual alternating
cycle with a two-matching union on its carrier; it does not identify the
ambient fixed-colour sweep graphs with the source's global closed web.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace AlternatingCarrierUnion

open AlternatingSiteGeometry
open GoertzelV24AlternatingMatchingComponent
open GoertzelV24ClosedWebSelectedEdgeStructure
open GoertzelV24ResidualExchange
open MatchingParity
open SimpleGraph
open scoped symmDiff

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The edges of one pairing whose two endpoints lie in a chosen carrier. -/
def pairingCarrierGraph (sigma : Pairing V) (carrier : Finset V) :
    SimpleGraph V where
  Adj left right :=
    left ∈ carrier ∧ right ∈ carrier ∧ sigma.partner left = right
  symm := ⟨by
    rintro left right ⟨hleft, hright, hadj⟩
    refine ⟨hright, hleft, ?_⟩
    rw [← hadj]
    exact sigma.partner_partner left⟩
  loopless := ⟨by
    rintro vertex ⟨_, _, hadj⟩
    exact sigma.partner_ne vertex hadj⟩

@[simp]
theorem pairingCarrierGraph_adj
    (sigma : Pairing V) (carrier : Finset V) {left right : V} :
    (pairingCarrierGraph sigma carrier).Adj left right ↔
      left ∈ carrier ∧ right ∈ carrier ∧ sigma.partner left = right :=
  Iff.rfl

/-- Pointwise disagreement makes the two restricted pairing graphs disjoint. -/
theorem pairingCarrierGraphs_disjoint_of_disagree
    (sigma tau : Pairing V) (carrier : Finset V)
    (hdisagree : ∀ vertex ∈ carrier,
      sigma.partner vertex ≠ tau.partner vertex) :
    Disjoint (pairingCarrierGraph sigma carrier)
      (pairingCarrierGraph tau carrier) := by
  rw [disjoint_iff_inf_le]
  intro left right hadj
  rw [SimpleGraph.bot_adj]
  rcases (SimpleGraph.inf_adj _ _ _ _).1 hadj with
    ⟨⟨hleft, _, hsigma⟩, ⟨_, _, htau⟩⟩
  exact hdisagree left hleft (hsigma.trans htau.symm)

/-- Restricting a symmetric difference to a carrier is the symmetric
difference of the two restricted graphs. -/
theorem exchangeCarrier_eq_symmDiff_pairingCarrierGraphs
    (sigma tau : Pairing V) (carrier : Finset V) :
    exchangeCarrier sigma tau carrier =
      pairingCarrierGraph sigma carrier ∆
        pairingCarrierGraph tau carrier := by
  ext left right
  simp only [exchangeCarrier_adj, pairingCarrierGraph_adj, symmDiff_def,
    SimpleGraph.sup_adj, SimpleGraph.sdiff_adj, pairingGraph_adj]
  tauto

/-- On a carrier where the pairings disagree, the alternating carrier is
literally their union. -/
theorem exchangeCarrier_eq_sup_pairingCarrierGraphs_of_disagree
    (sigma tau : Pairing V) (carrier : Finset V)
    (hdisagree : ∀ vertex ∈ carrier,
      sigma.partner vertex ≠ tau.partner vertex) :
    exchangeCarrier sigma tau carrier =
      pairingCarrierGraph sigma carrier ⊔
        pairingCarrierGraph tau carrier := by
  rw [exchangeCarrier_eq_symmDiff_pairingCarrierGraphs]
  exact (pairingCarrierGraphs_disjoint_of_disagree sigma tau carrier
    hdisagree).symmDiff_eq_sup

/-- Distinct colour classes of one edge colouring are edge-disjoint. -/
theorem colorClassGraphs_disjoint_of_ne
    (coloring : G.EdgeColoring Color) {first second : Color}
    (hne : first ≠ second) :
    Disjoint (colorClassGraph coloring first)
      (colorClassGraph coloring second) := by
  rw [disjoint_iff_inf_le]
  intro left right hadj
  rw [SimpleGraph.bot_adj]
  rcases (SimpleGraph.inf_adj _ _ _ _).1 hadj with
    ⟨hfirst, hsecond⟩
  rcases (colorClassGraph_adj_iff coloring first left right).1 hfirst with
    ⟨hambientFirst, hcolorFirst⟩
  rcases (colorClassGraph_adj_iff coloring second left right).1 hsecond with
    ⟨hambientSecond, hcolorSecond⟩
  let edge : G.edgeSet :=
    ⟨s(left, right), by simpa using hambientFirst⟩
  have hcolorFirst' : coloring edge = first := by
    simpa [edge] using hcolorFirst
  have hcolorSecond' : coloring edge = second := by
    simpa [edge] using hcolorSecond
  exact hne (hcolorFirst'.symm.trans hcolorSecond')

/-- Thus the source's two-colour union is also the symmetric difference of
its two selected colour classes. -/
theorem colorClassGraph_symmDiff_eq_colorPairGraph
    (coloring : G.EdgeColoring Color) {first second : Color}
    (hne : first ≠ second) :
    colorClassGraph coloring first ∆ colorClassGraph coloring second =
      colorPairGraph coloring first second := by
  unfold colorPairGraph
  exact (colorClassGraphs_disjoint_of_ne coloring hne).symmDiff_eq_sup

/-- Every proper alternating-component witness realizes the residual carrier
as the union of its two restricted matching roles. -/
theorem ProperAlternatingComponentWitness.exchangeCarrier_eq_pairingUnion
    {sigma : Pairing V} {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second) :
    exchangeCarrier sigma site.tau site.carrier =
      pairingCarrierGraph sigma site.carrier ⊔
        pairingCarrierGraph site.tau site.carrier :=
  exchangeCarrier_eq_sup_pairingCarrierGraphs_of_disagree
    sigma site.tau site.carrier site.disagree_on_carrier

/-- Every edge of the distinguished alternating cycle lies in that literal
two-matching union. -/
theorem ProperAlternatingComponentWitness.cycle_edges_pairingUnion
    {sigma : Pairing V} {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second) :
    ∀ edge ∈ site.cycle.edges,
      edge ∈ (pairingCarrierGraph sigma site.carrier ⊔
        pairingCarrierGraph site.tau site.carrier).edgeSet := by
  intro edge hedge
  induction edge using Sym2.inductionOn with
  | _ left right =>
      have hleftSupport : left ∈ site.cycle.support :=
        site.cycle.fst_mem_support_of_mem_edges hedge
      have hrightSupport : right ∈ site.cycle.support :=
        site.cycle.snd_mem_support_of_mem_edges hedge
      have hleft : left ∈ site.carrier := by
        rw [← site.cycle_support_eq]
        simpa using hleftSupport
      have hright : right ∈ site.carrier := by
        rw [← site.cycle_support_eq]
        simpa using hrightSupport
      have halternating := site.cycle_edges_alternating s(left, right) hedge
      rw [SimpleGraph.mem_edgeSet] at halternating ⊢
      rw [← exchangeCarrier_eq_sup_pairingCarrierGraphs_of_disagree
        sigma site.tau site.carrier site.disagree_on_carrier]
      exact ⟨hleft, hright, halternating⟩

end AlternatingCarrierUnion

end Mettapedia.GraphTheory.FourColor.Compositional
