import MatchingParity
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Pairings and graph perfect matchings

`MatchingParity.Pairing` is a graph-free perfect matching: a fixed-point-free
involution on the vertices.  A perfect matching in a graph is the same data,
provided every paired edge belongs to the graph.  This file records that support
condition and supplies conversions in both directions.

Keeping support explicit matters for non-complete graphs.  It also lets the
graph-free exchange and parity results be used with Mathlib's matching API
without changing their general statements.
-/

namespace MatchingParity

open SimpleGraph

variable {V : Type*}

/-- Every edge selected by a pairing belongs to `G`. -/
def Pairing.SupportedBy (σ : Pairing V) (G : SimpleGraph V) : Prop :=
  ∀ v, G.Adj v (σ.partner v)

namespace Pairing

/-- A graph-supported pairing as a spanning subgraph. -/
def toSubgraph (σ : Pairing V) {G : SimpleGraph V} (hσ : σ.SupportedBy G) : G.Subgraph where
  verts := Set.univ
  Adj v w := σ.partner v = w
  adj_sub := by
    intro v w hvw
    rw [← hvw]
    exact hσ v
  edge_vert := by simp
  symm := by
    constructor
    intro v w hvw
    rw [← hvw]
    exact σ.partner_partner v

@[simp] theorem toSubgraph_verts (σ : Pairing V) {G : SimpleGraph V}
    (hσ : σ.SupportedBy G) : (σ.toSubgraph hσ).verts = Set.univ := rfl

@[simp] theorem toSubgraph_adj (σ : Pairing V) {G : SimpleGraph V}
    (hσ : σ.SupportedBy G) {v w : V} :
    (σ.toSubgraph hσ).Adj v w ↔ σ.partner v = w := Iff.rfl

/-- A supported pairing produces a Mathlib perfect matching. -/
theorem toSubgraph_isPerfectMatching (σ : Pairing V) {G : SimpleGraph V}
    (hσ : σ.SupportedBy G) : (σ.toSubgraph hσ).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  refine ⟨σ.partner v, rfl, ?_⟩
  intro w hw
  change σ.partner v = w at hw
  exact hw.symm

/-- The unique-neighbour involution carried by a Mathlib perfect matching. -/
noncomputable def ofPerfectMatching {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsPerfectMatching) : Pairing V where
  partner v := (hM.1 (hM.2 v)).choose
  partner_partner v := by
    have hv : M.Adj v (hM.1 (hM.2 v)).choose := (hM.1 (hM.2 v)).choose_spec.1
    exact ((hM.1 (hM.2 (hM.1 (hM.2 v)).choose)).choose_spec.2 v hv.symm).symm
  partner_ne v := by
    have hv : M.Adj v (hM.1 (hM.2 v)).choose := (hM.1 (hM.2 v)).choose_spec.1
    exact (M.adj_sub hv).ne.symm

@[simp] theorem ofPerfectMatching_partner {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsPerfectMatching) (v : V) :
    (ofPerfectMatching hM).partner v = (hM.1 (hM.2 v)).choose := rfl

/-- The recovered pairing uses edges of the original graph. -/
theorem ofPerfectMatching_supportedBy {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsPerfectMatching) : (ofPerfectMatching hM).SupportedBy G := by
  intro v
  exact M.adj_sub (hM.1 (hM.2 v)).choose_spec.1

/-- The recovered partner is exactly any neighbour in the perfect matching. -/
theorem ofPerfectMatching_partner_eq_of_adj {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsPerfectMatching) {v w : V} (hvw : M.Adj v w) :
    (ofPerfectMatching hM).partner v = w := by
  exact ((hM.1 (hM.2 v)).choose_spec.2 w hvw).symm

/-- Converting a perfect matching to a pairing and back preserves adjacency. -/
theorem toSubgraph_ofPerfectMatching_adj {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsPerfectMatching) {v w : V} :
    ((ofPerfectMatching hM).toSubgraph (ofPerfectMatching_supportedBy hM)).Adj v w ↔
      M.Adj v w := by
  constructor
  · intro hvw
    rw [toSubgraph_adj] at hvw
    have hchoice : M.Adj v ((ofPerfectMatching hM).partner v) :=
      (hM.1 (hM.2 v)).choose_spec.1
    rw [hvw] at hchoice
    exact hchoice
  · intro hvw
    rw [toSubgraph_adj]
    exact ofPerfectMatching_partner_eq_of_adj hM hvw

/-- Exchanging two graph-supported pairings along a set closed under both
pairings does not introduce an edge outside the graph. -/
theorem exchange_supportedBy [DecidableEq V]
    (σ τ : Pairing V) {G : SimpleGraph V} (s : Finset V)
    (hσs : ∀ v ∈ s, σ.partner v ∈ s) (hτs : ∀ v ∈ s, τ.partner v ∈ s)
    (hσG : σ.SupportedBy G) (hτG : τ.SupportedBy G) :
    (σ.exchange τ s hσs hτs).SupportedBy G := by
  intro v
  by_cases hv : v ∈ s
  · rw [exchange_of_mem σ τ s hσs hτs hv]
    exact hτG v
  · rw [exchange_of_notMem σ τ s hσs hτs hv]
    exact hσG v

/-- Exchange along a closed set, delivered as a Mathlib perfect matching. -/
theorem exchange_toSubgraph_isPerfectMatching [DecidableEq V]
    (σ τ : Pairing V) {G : SimpleGraph V}
    (s : Finset V) (hσs : ∀ v ∈ s, σ.partner v ∈ s)
    (hτs : ∀ v ∈ s, τ.partner v ∈ s)
    (hσG : σ.SupportedBy G) (hτG : τ.SupportedBy G) :
    ((σ.exchange τ s hσs hτs).toSubgraph
      (exchange_supportedBy σ τ s hσs hτs hσG hτG)).IsPerfectMatching :=
  toSubgraph_isPerfectMatching _ _

end Pairing

end MatchingParity
