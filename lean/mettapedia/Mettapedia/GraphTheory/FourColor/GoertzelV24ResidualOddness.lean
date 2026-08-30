import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualExchange
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Oddness of a residual two-factor

A graph-supported perfect matching in a cubic graph leaves a two-factor.  This
file identifies the residual defect with the classical oddness of that
two-factor: a connected residual component is non-bipartite exactly when its
cycle has odd length.  Consequently residual defect is even, so a positive
defect is at least two.

Contracting each residual cycle gives the correct wall-facing quotient
incidence: its vertices are residual connected components, its darts are the
original vertices, and the matching involution pairs the darts.  Loops and
parallel quotient edges are intentionally retained by this incidence view;
using a simple quotient graph would erase information.

The final theorem packages the exact obstruction that a high-width argument
must overcome: a bridge-free cubic Tait counterexample has a supported
matching with at least two odd residual components for which no supported
matching exchange lowers residual defect.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ResidualOddness

open SimpleGraph MatchingParity
open GoertzelV24ResidualTwoFactor
open GoertzelV24ResidualDefectDescent

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Consecutive entries in an even cyclic list have opposite index parity.
The exceptional wraparound pair is covered by evenness of the list length. -/
theorem even_idxOf_iff_not_even_idxOf_of_pair_infix_getLast_cons
    {alpha : Type*} [DecidableEq alpha] {l : List alpha} (hl : l ≠ [])
    (hnd : l.Nodup) (heven : Even l.length) {x y : alpha}
    (hxy : [x, y] <:+: l.getLast hl :: l) :
    Even (l.idxOf x) ↔ ¬ Even (l.idxOf y) := by
  rcases List.infix_iff_getElem?.1 hxy with ⟨k, hk, hget⟩
  have hx := hget 0 (by simp)
  have hy := hget 1 (by simp)
  simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hk
  cases k with
  | zero =>
      have hllen : 0 < l.length := List.length_pos_iff.mpr hl
      norm_num [List.getElem?_eq_getElem hllen] at hx hy
      have hx' : x = l.getLast hl := hx.symm
      have hy' : y = l[0]'hllen := hy.symm
      subst x
      subst y
      have hlast : l.getLast hl ∉ l.dropLast := by
        have hnd' : (l.dropLast ++ [l.getLast hl]).Nodup := by
          rw [List.dropLast_append_getLast hl]
          exact hnd
        rw [List.nodup_append] at hnd'
        intro hmem
        exact hnd'.2.2 _ hmem _ (by simp) rfl
      rw [hnd.idxOf_getElem, List.idxOf_getLast hl hlast]
      rcases heven with ⟨m, hm⟩
      constructor
      · rintro ⟨n, hn⟩
        exfalso
        rw [hm] at hllen hn
        omega
      · intro hnot
        exact (hnot Even.zero).elim
  | succ k =>
      have hk0 : k < l.length := by omega
      have hk1 : k + 1 < l.length := by omega
      norm_num [Nat.add_assoc, List.getElem?_eq_getElem hk0,
        List.getElem?_eq_getElem hk1] at hx hy
      have hx' : x = l[k]'hk0 := hx.symm
      have hy' : y = l[k + 1]'hk1 := by
        have hyraw : l[k + 1]? = some y := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hy
        rw [List.getElem?_eq_getElem hk1] at hyraw
        exact Option.some.inj hyraw.symm
      subst x
      subst y
      rw [hnd.idxOf_getElem, hnd.idxOf_getElem, Nat.even_add_one]
      tauto

variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-- A finite connected graph with exactly two neighbours at every vertex is
two-colourable when its number of vertices is even. -/
theorem colorable_two_of_connected_degree_two_of_even_card
    (hconn : H.Connected)
    (htwo : ∀ v, (H.neighborSet v).ncard = 2)
    (heven : Even (Fintype.card V)) :
    H.Colorable 2 := by
  have hcycles : H.IsCycles := fun _ _ => htwo _
  let root : V := hconn.nonempty.some
  let component : H.ConnectedComponent := H.connectedComponentMk root
  have hroot : root ∈ component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hcomponent : component.supp = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    apply SimpleGraph.ConnectedComponent.sound
    exact hconn.preconnected v root
  have hneighbor : (H.neighborSet root).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [htwo root]
    norm_num
  obtain ⟨p, hp, hpverts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := component) hroot hneighbor
  have hpverts' : p.toSubgraph.verts = Set.univ := hpverts.trans hcomponent
  let l : List V := p.support.tail
  have hl : l ≠ [] := by
    apply List.ne_nil_of_length_pos
    have hp3 := hp.three_le_length
    simp [l, List.length_tail, p.length_support]
    omega
  have hnd : l.Nodup := by
    change p.support.tail.Nodup
    rw [← p.support_tail_of_not_nil hp.not_nil]
    exact hp.isPath_tail.support_nodup
  have hlast : l.getLast hl = root := by
    simpa [l, ← p.support_tail_of_not_nil hp.not_nil] using
      p.tail.getLast_support
  have hsupport : p.support = l.getLast hl :: l := by
    calc
      p.support = root :: p.support.tail := by
        have h := List.cons_head_tail (show p.support ≠ [] by simp)
        simpa [p.head_support] using h.symm
      _ = l.getLast hl :: l := by simp [l, hlast]
  have hlen : l.length = Fintype.card V := by
    change p.support.tail.length = Fintype.card V
    rw [← p.support_tail_of_not_nil hp.not_nil]
    have hpath := hp.isPath_tail
    have hham : p.tail.IsHamiltonian := hpath.isHamiltonian_of_mem fun v => by
      rw [p.support_tail_of_not_nil hp.not_nil]
      change v ∈ l
      have hv : v ∈ p.toSubgraph.verts := by rw [hpverts']; trivial
      rw [p.mem_verts_toSubgraph] at hv
      by_cases hvr : v = root
      · subst v
        rw [← hlast]
        exact List.getLast_mem hl
      · rw [hsupport] at hv
        simp only [List.mem_cons] at hv
        exact hv.resolve_left (by simpa [hlast] using hvr)
    exact hham.length_support
  have hleven : Even l.length := hlen ▸ heven
  refine ⟨Coloring.mk
    (fun v => if Even (l.idxOf v) then (0 : Fin 2) else (1 : Fin 2)) ?_⟩
  intro v w hadj
  have hv : v ∈ p.toSubgraph.verts := by rw [hpverts']; trivial
  have hpAdj : p.toSubgraph.Adj v w :=
    (hp.adj_toSubgraph_iff_of_isCycles hcycles hv w).2 hadj
  have hedge : s(v, w) ∈ p.edges := p.adj_toSubgraph_iff_mem_edges.mp hpAdj
  have hinfix : [v, w] <:+: p.support ∨ [w, v] <:+: p.support :=
    p.infix_support_iff_mem_edges.mpr hedge
  rw [hsupport] at hinfix
  have hpar : Even (l.idxOf v) ↔ ¬ Even (l.idxOf w) := by
    rcases hinfix with hvw | hwv
    · exact even_idxOf_iff_not_even_idxOf_of_pair_infix_getLast_cons
        hl hnd hleven hvw
    · have h := even_idxOf_iff_not_even_idxOf_of_pair_infix_getLast_cons
        hl hnd hleven hwv
      tauto
  by_cases hev : Even (l.idxOf v)
  · have hnotw : ¬ Even (l.idxOf w) := hpar.mp hev
    simp [hev, hnotw]
  · have hew : Even (l.idxOf w) := by tauto
    simp [hev, hew]

/-- A finite connected graph with exactly two neighbours at every vertex is
two-colourable exactly when its order is even. -/
theorem colorable_two_iff_even_card_of_connected_degree_two
    (hconn : H.Connected)
    (htwo : ∀ v, (H.neighborSet v).ncard = 2) :
    H.Colorable 2 ↔ Even (Fintype.card V) := by
  have hdegree : ∀ v, H.degree v = 2 := by
    intro v
    calc
      H.degree v = Fintype.card (H.neighborSet v) :=
        (H.card_neighborSet_eq_degree v).symm
      _ = Nat.card (H.neighborSet v) := Nat.card_eq_fintype_card.symm
      _ = (H.neighborSet v).ncard := Nat.card_coe_set_eq (H.neighborSet v)
      _ = 2 := htwo v
  constructor
  · intro hbip
    obtain ⟨M, hM⟩ :=
      exists_isPerfectMatching_of_bipartite_degree_two hbip hdegree
    let sigma := Pairing.ofPerfectMatching hM
    simpa using even_card_of_closed sigma Finset.univ (by simp)
  · exact colorable_two_of_connected_degree_two_of_even_card hconn htwo

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The connected residual component is bipartite exactly when its support
has even cardinality. -/
theorem connectedComponent_colorable_two_iff_even_supp
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (htwo : ∀ v, (H.neighborSet v).ncard = 2)
    (c : H.ConnectedComponent) :
    c.toSimpleGraph.Colorable 2 ↔ Even c.supp.ncard := by
  classical
  letI : Fintype c.supp := Fintype.ofFinite c.supp
  letI : DecidableRel c.toSimpleGraph.Adj := Classical.decRel _
  have htwoC : ∀ v, (c.toSimpleGraph.neighborSet v).ncard = 2 := by
    intro v
    let neighborEquiv : c.toSimpleGraph.neighborSet v ≃ H.neighborSet v.val :=
      { toFun := fun w => ⟨w.val, w.prop⟩
        invFun := fun w =>
          ⟨⟨w.val, c.mem_supp_of_adj_mem_supp v.prop w.prop⟩, w.prop⟩
        left_inv := by intro w; rfl
        right_inv := by intro w; rfl }
    rw [Set.ncard_congr' neighborEquiv]
    exact htwo v.val
  have h := colorable_two_iff_even_card_of_connected_degree_two
    c.connected_toSimpleGraph htwoC
  have hcard : Nat.card c = c.supp.ncard := by
    change Nat.card c.supp = c.supp.ncard
    exact Nat.card_coe_set_eq c.supp
  simpa only [← Nat.card_eq_fintype_card, hcard] using h

/-- Vertices of the residual quotient are the residual cycles. -/
abbrev ResidualQuotientVertex (G : SimpleGraph V) (sigma : Pairing V) :=
  (residualGraph G sigma).ConnectedComponent

/-- An original vertex is a dart incident with its residual component in the
quotient incidence. -/
def residualQuotientVertOf (G : SimpleGraph V) (sigma : Pairing V) (v : V) :
    ResidualQuotientVertex G sigma :=
  (residualGraph G sigma).connectedComponentMk v

/-- Quotient degree counts incident matching darts with multiplicity.  This
is the residual cycle length, even when quotient loops or parallel edges are
present. -/
noncomputable def residualQuotientDegree {G : SimpleGraph V} {sigma : Pairing V}
    (c : ResidualQuotientVertex G sigma) : Nat :=
  c.supp.ncard

@[simp] theorem mem_residualQuotientVertOf_supp
    (G : SimpleGraph V) (sigma : Pairing V) (v : V) :
    v ∈ (residualQuotientVertOf G sigma v).supp :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- Residual defect is exactly the number of odd residual cycles. -/
theorem residualDefect_eq_oddComponents_ncard
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hsigma : sigma.SupportedBy G) :
    residualDefect G sigma = (residualGraph G sigma).oddComponents.ncard := by
  classical
  letI : DecidableRel (residualGraph G sigma).Adj := Classical.decRel _
  have htwo : ∀ v, ((residualGraph G sigma).neighborSet v).ncard = 2 := by
    intro v
    simpa only [Set.ncard_eq_toFinset_card', SimpleGraph.neighborFinset_def] using
      card_neighborFinset_residualGraph_eq_two hG sigma hsigma v
  unfold residualDefect
  congr 1
  ext c
  simp only [Set.mem_setOf_eq, SimpleGraph.oddComponents]
  rw [connectedComponent_colorable_two_iff_even_supp htwo]
  exact Nat.not_even_iff_odd

/-- Residual defect is the number of odd-degree vertices in the quotient
incidence obtained by contracting every residual cycle. -/
theorem residualDefect_eq_oddResidualQuotientVertices_ncard
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hsigma : sigma.SupportedBy G) :
    residualDefect G sigma =
      {c : ResidualQuotientVertex G sigma | Odd (residualQuotientDegree c)}.ncard := by
  simpa [SimpleGraph.oddComponents, residualQuotientDegree] using
    residualDefect_eq_oddComponents_ncard hG sigma hsigma

/-- The number of odd residual cycles is even.  Equivalently, the quotient
incidence obeys the handshaking parity law. -/
theorem residualDefect_even
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hsigma : sigma.SupportedBy G) :
    Even (residualDefect G sigma) := by
  rw [residualDefect_eq_oddComponents_ncard hG sigma hsigma,
    ← Nat.not_odd_iff_even, SimpleGraph.odd_ncard_oddComponents,
    Nat.not_odd_iff_even, Nat.card_eq_fintype_card]
  simpa using even_card_of_closed sigma Finset.univ (by simp)

/-- A positive residual defect contains at least two odd residual cycles. -/
theorem two_le_residualDefect_of_pos
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hsigma : sigma.SupportedBy G)
    (hpos : 0 < residualDefect G sigma) :
    2 ≤ residualDefect G sigma := by
  rcases residualDefect_even hG sigma hsigma with ⟨k, hk⟩
  omega

/-- A bridge-free cubic Tait counterexample contains an exchange-rigid
minimum-oddness matching.  Every exchange with another supported pairing has
residual defect at least that of the minimizer. -/
theorem exists_exchangeRigid_residualOddness_of_cubic_edgeBridgeFree
    (hCubic : G.IsRegularOfDegree 3)
    (hfree : ∀ edge : G.edgeSet, ¬ G.IsBridge edge.1)
    (hnot : ¬ TaitColorable G) :
    ∃ sigma : Pairing V,
      sigma.SupportedBy G ∧
      2 ≤ residualDefect G sigma ∧
      ∀ (tau : Pairing V) (s : Finset V)
        (hSigmaS : ∀ v ∈ s, sigma.partner v ∈ s)
        (hTauS : ∀ v ∈ s, tau.partner v ∈ s),
        tau.SupportedBy G →
          residualDefect G sigma ≤
            residualDefect G (sigma.exchange tau s hSigmaS hTauS) := by
  have htriples : HasCubicIncidentEdgeTriples G :=
    hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three fun vertex => by
      rw [incidentEdgeFinset_card_eq_degree, hCubic vertex]
  obtain ⟨sigma, hsigma, hpos, hminimal⟩ :=
    exists_positive_minimal_residualDefect_of_cubic_edgeBridgeFree
      hCubic hfree hnot
  refine ⟨sigma, hsigma,
    two_le_residualDefect_of_pos htriples sigma hsigma hpos, ?_⟩
  intro tau s hSigmaS hTauS htau
  apply hminimal
  exact Pairing.exchange_supportedBy sigma tau s hSigmaS hTauS hsigma htau

end GoertzelV24ResidualOddness

end Mettapedia.GraphTheory.FourColor
