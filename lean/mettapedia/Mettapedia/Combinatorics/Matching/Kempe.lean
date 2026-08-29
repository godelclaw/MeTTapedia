import Mettapedia.Combinatorics.Matching.GraphBridge

/-!
# Kempe exchange for two perfect matchings

Two graph-supported perfect matchings behave like two edge colours on their
symmetric difference. A vertex set closed under both partner maps is a union of
alternating components. Swapping the two matchings on such a set preserves both
perfect matchings, their graph support, and their uncoloured edge cover.

This is the matching-theoretic form of a Kempe exchange. It is stated for
fixed-point-free involutions, so it applies without choosing or enumerating cycle
traversals.
-/

namespace MatchingParity

open SimpleGraph

variable {V : Type*} [DecidableEq V]

namespace Pairing

/-- Swap two pairings on a set closed under both partner maps. -/
def kempeExchange (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ v ∈ s, σ.partner v ∈ s) (hτ : ∀ v ∈ s, τ.partner v ∈ s) :
    Pairing V × Pairing V :=
  (σ.exchange τ s hσ hτ, τ.exchange σ s hτ hσ)

@[simp] theorem kempeExchange_fst_partner_of_mem (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ v ∈ s, σ.partner v ∈ s) (hτ : ∀ v ∈ s, τ.partner v ∈ s)
    {v : V} (hv : v ∈ s) :
    (kempeExchange σ τ s hσ hτ).1.partner v = τ.partner v :=
  exchange_of_mem σ τ s hσ hτ hv

@[simp] theorem kempeExchange_snd_partner_of_mem (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ v ∈ s, σ.partner v ∈ s) (hτ : ∀ v ∈ s, τ.partner v ∈ s)
    {v : V} (hv : v ∈ s) :
    (kempeExchange σ τ s hσ hτ).2.partner v = σ.partner v :=
  exchange_of_mem τ σ s hτ hσ hv

@[simp] theorem kempeExchange_fst_partner_of_notMem (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ v ∈ s, σ.partner v ∈ s) (hτ : ∀ v ∈ s, τ.partner v ∈ s)
    {v : V} (hv : v ∉ s) :
    (kempeExchange σ τ s hσ hτ).1.partner v = σ.partner v :=
  exchange_of_notMem σ τ s hσ hτ hv

@[simp] theorem kempeExchange_snd_partner_of_notMem (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ v ∈ s, σ.partner v ∈ s) (hτ : ∀ v ∈ s, τ.partner v ∈ s)
    {v : V} (hv : v ∉ s) :
    (kempeExchange σ τ s hσ hτ).2.partner v = τ.partner v :=
  exchange_of_notMem τ σ s hτ hσ hv

/-- Kempe exchange preserves the two uncoloured matching edges incident to every
vertex. -/
theorem kempeExchange_partner_set (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ v ∈ s, σ.partner v ∈ s) (hτ : ∀ v ∈ s, τ.partner v ∈ s)
    (v : V) :
    ({(kempeExchange σ τ s hσ hτ).1.partner v,
        (kempeExchange σ τ s hσ hτ).2.partner v} : Set V) =
      {σ.partner v, τ.partner v} := by
  by_cases hv : v ∈ s
  · simp [kempeExchange_fst_partner_of_mem σ τ s hσ hτ hv,
      kempeExchange_snd_partner_of_mem σ τ s hσ hτ hv, Set.pair_comm]
  · simp [kempeExchange_fst_partner_of_notMem σ τ s hσ hτ hv,
      kempeExchange_snd_partner_of_notMem σ τ s hσ hτ hv]

/-- Kempe exchange preserves the support of the symmetric difference. -/
theorem kempeExchange_ne_iff (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ v ∈ s, σ.partner v ∈ s) (hτ : ∀ v ∈ s, τ.partner v ∈ s)
    (v : V) :
    (kempeExchange σ τ s hσ hτ).1.partner v ≠
        (kempeExchange σ τ s hσ hτ).2.partner v ↔
      σ.partner v ≠ τ.partner v := by
  by_cases hv : v ∈ s
  · simp [kempeExchange_fst_partner_of_mem σ τ s hσ hτ hv,
      kempeExchange_snd_partner_of_mem σ τ s hσ hτ hv, ne_comm]
  · simp [kempeExchange_fst_partner_of_notMem σ τ s hσ hτ hv,
      kempeExchange_snd_partner_of_notMem σ τ s hσ hτ hv]

/-- If both input matchings use edges of a graph, so do both matchings after a
Kempe exchange. -/
theorem kempeExchange_supportedBy (σ τ : Pairing V) {G : SimpleGraph V}
    (s : Finset V) (hσ : ∀ v ∈ s, σ.partner v ∈ s)
    (hτ : ∀ v ∈ s, τ.partner v ∈ s)
    (hσG : σ.SupportedBy G) (hτG : τ.SupportedBy G) :
    (kempeExchange σ τ s hσ hτ).1.SupportedBy G ∧
      (kempeExchange σ τ s hσ hτ).2.SupportedBy G :=
  ⟨exchange_supportedBy σ τ s hσ hτ hσG hτG,
    exchange_supportedBy τ σ s hτ hσ hτG hσG⟩

/-- A graph-supported Kempe exchange produces two Mathlib perfect matchings. -/
theorem kempeExchange_isPerfectMatching (σ τ : Pairing V) {G : SimpleGraph V}
    (s : Finset V) (hσ : ∀ v ∈ s, σ.partner v ∈ s)
    (hτ : ∀ v ∈ s, τ.partner v ∈ s)
    (hσG : σ.SupportedBy G) (hτG : τ.SupportedBy G) :
    let κ := kempeExchange σ τ s hσ hτ
    let hκ := kempeExchange_supportedBy σ τ s hσ hτ hσG hτG
    (κ.1.toSubgraph hκ.1).IsPerfectMatching ∧
      (κ.2.toSubgraph hκ.2).IsPerfectMatching := by
  dsimp
  exact ⟨toSubgraph_isPerfectMatching _ _, toSubgraph_isPerfectMatching _ _⟩

end Pairing

end MatchingParity
