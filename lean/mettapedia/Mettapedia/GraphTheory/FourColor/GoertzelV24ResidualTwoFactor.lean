import Mettapedia.GraphTheory.FourColor.GoertzelV24PetersenStartingMatching
import Mathlib.Combinatorics.SimpleGraph.Hall

/-!
# The residual two-factor obstruction

Delete a graph-supported perfect matching from a finite cubic graph. Exactly
two incident edges remain at every vertex, so the residual graph is a spanning
two-factor. A second matching disjoint from the first is precisely a perfect
matching of this residual graph.

Hall's theorem supplies the route-facing parity consequence uniformly: a
finite bipartite graph of degree two has a perfect matching. Therefore the
residual two-factor of every supported matching in a Tait counterexample is
non-bipartite and carries an odd closed walk. This replaces the vague global
"all matchings overlap" obstruction by an explicit parity carrier; it does not
assert the still-open high-width replacement theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ResidualTwoFactor

open SimpleGraph
open MatchingParity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Delete from `G` the perfect-matching edge selected by `sigma` at each vertex. -/
def residualGraph (G : SimpleGraph V) (sigma : Pairing V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ sigma.partner v ≠ w
  symm := ⟨by
    rintro v w ⟨hvw, hne⟩
    refine ⟨hvw.symm, ?_⟩
    intro h
    apply hne
    have hp := congrArg sigma.partner h
    rw [sigma.partner_partner] at hp
    exact hp.symm⟩
  loopless := ⟨by
    rintro v ⟨hvv, _⟩
    exact hvv.ne rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem residualGraph_adj {sigma : Pairing V} {v w : V} :
    (residualGraph G sigma).Adj v w ↔
      G.Adj v w ∧ sigma.partner v ≠ w := Iff.rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem residualGraph_le (sigma : Pairing V) : residualGraph G sigma ≤ G :=
  fun _ _ h => h.1

instance residualGraph_locallyFinite (sigma : Pairing V) :
    (residualGraph G sigma).LocallyFinite :=
  fun _ => Fintype.ofFinite _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A pairing is supported on the residual graph exactly when it is supported
on the ambient graph and is pointwise disjoint from the deleted pairing. -/
theorem supportedBy_residualGraph_iff (sigma tau : Pairing V) :
    tau.SupportedBy (residualGraph G sigma) ↔
      tau.SupportedBy G ∧ ∀ v, sigma.partner v ≠ tau.partner v := by
  constructor
  · intro htau
    exact ⟨fun v => (htau v).1, fun v => (htau v).2⟩
  · rintro ⟨htau, hne⟩ v
    exact ⟨htau v, hne v⟩

theorem neighborFinset_residualGraph
    (sigma : Pairing V) (v : V) :
    (residualGraph G sigma).neighborFinset v =
      (G.neighborFinset v).erase (sigma.partner v) := by
  ext w
  simp [residualGraph, and_comm, eq_comm]

theorem card_neighborFinset_residualGraph_eq_two
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hsigma : sigma.SupportedBy G) (v : V) :
    ((residualGraph G sigma).neighborFinset v).card = 2 := by
  have hcard : (G.neighborFinset v).card = 3 := by
    calc
      (G.neighborFinset v).card = G.degree v :=
        SimpleGraph.card_neighborFinset_eq_degree G v
      _ = (incidentEdgeFinset G v).card :=
        (incidentEdgeFinset_card_eq_degree v).symm
      _ = 3 :=
        incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples hG v
  have hmem : sigma.partner v ∈ G.neighborFinset v := by
    simpa using hsigma v
  rw [neighborFinset_residualGraph, Finset.card_erase_of_mem hmem]
  omega

theorem residualGraph_isCycles
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hsigma : sigma.SupportedBy G) :
    (residualGraph G sigma).IsCycles := by
  intro v _
  simpa only [Set.ncard_eq_toFinset_card', SimpleGraph.neighborFinset_def] using
    card_neighborFinset_residualGraph_eq_two hG sigma hsigma v

theorem taitColorable_iff_exists_residual_supportedPairing
    (hG : HasCubicIncidentEdgeTriples G) :
    TaitColorable G ↔
      ∃ sigma : Pairing V, sigma.SupportedBy G ∧
        ∃ tau : Pairing V, tau.SupportedBy (residualGraph G sigma) := by
  rw [GoertzelV24TaitMatchingPair.taitColorable_iff_hasTwoDisjointSupportedPairings hG]
  constructor
  · rintro ⟨sigma, tau, hsigma, htau, hne⟩
    exact ⟨sigma, hsigma, tau,
      (supportedBy_residualGraph_iff sigma tau).2 ⟨htau, hne⟩⟩
  · rintro ⟨sigma, hsigma, tau, htau⟩
    have hdata := (supportedBy_residualGraph_iff sigma tau).1 htau
    exact ⟨sigma, tau, hsigma, hdata.1, hdata.2⟩

/-- A finite bipartite graph of constant degree two satisfies Hall's
condition and therefore has a perfect matching. -/
theorem exists_isPerfectMatching_of_bipartite_degree_two
    {H : SimpleGraph V} [H.LocallyFinite]
    (hbip : H.IsBipartite) (hdegree : ∀ v, H.degree v = 2) :
    ∃ M : H.Subgraph, M.IsPerfectMatching := by
  classical
  rcases hbip.exists_isBipartiteWith with ⟨left, right, hparts⟩
  apply SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le hparts
  intro vertices
  let source : Finset V := vertices.toFinset
  let target : Finset V :=
    (⋃ vertex ∈ vertices, H.neighborSet vertex).toFinset
  have hsource (vertex : V) (hvertex : vertex ∈ source) :
      (target.bipartiteAbove H.Adj vertex).card = 2 := by
    have hvertex' : vertex ∈ vertices := by
      simpa [source] using hvertex
    calc
      (target.bipartiteAbove H.Adj vertex).card =
          (H.neighborFinset vertex).card := by
        congr 1
        ext neighbor
        simp only [Finset.mem_bipartiteAbove, SimpleGraph.mem_neighborFinset,
          target, Set.mem_toFinset, Set.mem_iUnion]
        constructor
        · rintro ⟨_, hadj⟩
          exact hadj
        · intro hadj
          exact ⟨⟨vertex, hvertex', hadj⟩, hadj⟩
      _ = H.degree vertex := SimpleGraph.card_neighborFinset_eq_degree H vertex
      _ = 2 := hdegree vertex
  have htarget (neighbor : V) (hneighbor : neighbor ∈ target) :
      (source.bipartiteBelow H.Adj neighbor).card ≤ 2 := by
    calc
      (source.bipartiteBelow H.Adj neighbor).card ≤
          (H.neighborFinset neighbor).card := by
        apply Finset.card_le_card
        intro vertex hvertex
        have hadj : H.Adj vertex neighbor :=
          ((Finset.mem_bipartiteBelow (r := H.Adj)).1 hvertex).2
        simpa using hadj.symm
      _ = H.degree neighbor := SimpleGraph.card_neighborFinset_eq_degree H neighbor
      _ = 2 := hdegree neighbor
  have hdouble : 2 * source.card ≤ 2 * target.card := by
    calc
      2 * source.card =
          ∑ vertex ∈ source, (target.bipartiteAbove H.Adj vertex).card := by
        calc
          2 * source.card = ∑ vertex ∈ source, 2 := by simp [Nat.mul_comm]
          _ = ∑ vertex ∈ source,
              (target.bipartiteAbove H.Adj vertex).card := by
            exact Finset.sum_congr rfl fun vertex hvertex =>
              (hsource vertex hvertex).symm
      _ = ∑ neighbor ∈ target,
          (source.bipartiteBelow H.Adj neighbor).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow H.Adj
      _ ≤ ∑ _neighbor ∈ target, 2 := by
        exact Finset.sum_le_sum fun neighbor hneighbor => htarget neighbor hneighbor
      _ = 2 * target.card := by simp [Nat.mul_comm]
  simpa only [source, target, Set.ncard_eq_toFinset_card'] using
    (Nat.le_of_mul_le_mul_left hdouble (by norm_num))

/-- Bipartiteness of the residual 2-factor supplies the disjoint second
matching and hence a Tait colouring. -/
theorem taitColorable_of_residualGraph_isBipartite
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hsigma : sigma.SupportedBy G)
    (hbip : (residualGraph G sigma).IsBipartite) :
    TaitColorable G := by
  have hdegree : ∀ v, (residualGraph G sigma).degree v = 2 := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact card_neighborFinset_residualGraph_eq_two hG sigma hsigma v
  rcases exists_isPerfectMatching_of_bipartite_degree_two hbip hdegree with
    ⟨M, hM⟩
  let tau := Pairing.ofPerfectMatching hM
  have htau : tau.SupportedBy (residualGraph G sigma) :=
    Pairing.ofPerfectMatching_supportedBy hM
  exact (taitColorable_iff_exists_residual_supportedPairing hG).2
    ⟨sigma, hsigma, tau, htau⟩

/-- In a cubic Tait counterexample, deleting any supported perfect matching
leaves a non-bipartite spanning 2-factor. -/
theorem residualGraph_not_isBipartite_of_not_taitColorable
    (hG : HasCubicIncidentEdgeTriples G) (hnot : ¬ TaitColorable G)
    (sigma : Pairing V) (hsigma : sigma.SupportedBy G) :
    ¬ (residualGraph G sigma).IsBipartite := by
  intro hbip
  exact hnot (taitColorable_of_residualGraph_isBipartite hG sigma hsigma hbip)

/-- The non-bipartite residual obstruction can be witnessed by an odd closed
walk. This is the formal parity form of the usual odd-cycle obstruction. -/
theorem exists_odd_closedWalk_residual_of_not_taitColorable
    (hG : HasCubicIncidentEdgeTriples G) (hnot : ¬ TaitColorable G)
    (sigma : Pairing V) (hsigma : sigma.SupportedBy G) :
    ∃ root : V, ∃ walk : (residualGraph G sigma).Walk root root,
      Odd walk.length := by
  have hnon :=
    residualGraph_not_isBipartite_of_not_taitColorable hG hnot sigma hsigma
  have hnon' : ¬ (residualGraph G sigma).Colorable 2 := hnon
  rw [SimpleGraph.two_colorable_iff_forall_loop_even] at hnon'
  push Not at hnon'
  rcases hnon' with ⟨root, walk, hwalk⟩
  exact ⟨root, walk, Nat.not_even_iff_odd.mp hwalk⟩

/-- Consumer-facing normal form: a bridge-free cubic Tait counterexample has
a starting supported matching, every supported matching overlaps it, and its
residual spanning 2-factor carries an odd closed walk. -/
theorem exists_startingPairing_overlap_and_odd_residual
    (hCubic : G.IsRegularOfDegree 3)
    (hfree : ∀ edge : G.edgeSet, ¬ G.IsBridge edge.1)
    (hnot : ¬ TaitColorable G) :
    ∃ starting : Pairing V,
      starting.SupportedBy G ∧
      (∀ other : Pairing V, other.SupportedBy G →
        ∃ vertex, starting.partner vertex = other.partner vertex) ∧
      ∃ root : V, ∃ walk : (residualGraph G starting).Walk root root,
        Odd walk.length := by
  obtain ⟨starting, hstarting, hoverlap⟩ :=
    GoertzelV24PetersenStartingMatching.exists_startingPairing_all_supportedPairings_overlap
      hCubic hfree hnot
  have htriples : HasCubicIncidentEdgeTriples G :=
    hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three fun vertex => by
      rw [incidentEdgeFinset_card_eq_degree, hCubic vertex]
  exact ⟨starting, hstarting, hoverlap,
    exists_odd_closedWalk_residual_of_not_taitColorable
      htriples hnot starting hstarting⟩

end

end GoertzelV24ResidualTwoFactor

end Mettapedia.GraphTheory.FourColor
