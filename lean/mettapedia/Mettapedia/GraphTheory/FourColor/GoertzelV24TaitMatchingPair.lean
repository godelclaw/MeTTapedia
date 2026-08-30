import Mettapedia.Combinatorics.Matching.Kempe
import Mettapedia.GraphTheory.FourColor.GoertzelV24TaitMatchingDecomposition

/-!
# Two perfect matchings force a Tait colouring

On a cubic graph, two graph-supported perfect matchings with different
partners at every vertex force the third matching: it is the unique unused
incident edge. The unused-edge choice is consistent at both endpoints, so it
is itself a fixed-point-free involution.

Thus Tait colourability is equivalent to the existence of two edge-disjoint
supported perfect matchings. The contrapositive says that every two supported
perfect matchings in a cubic Tait counterexample share an edge.

The final wrapper records a limitation important to the wall-facing route:
Kempe exchange between a fixed pair preserves its pointwise overlap locus, so
such an exchange cannot create the disjoint pair required here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TaitMatchingPair

open SimpleGraph
open MatchingParity

variable {V : Type*} [DecidableEq V]
variable {G : SimpleGraph V} [Fintype G.edgeSet] [G.LocallyFinite]

/-- Neighbours of a vertex not selected by either of two pairings. -/
def residualNeighborFinset (σ τ : Pairing V) (G : SimpleGraph V)
    [G.LocallyFinite] (v : V) : Finset V :=
  ((G.neighborFinset v).erase (σ.partner v)).erase (τ.partner v)

/-- Cubicity and pointwise disjointness leave exactly one unused neighbour. -/
theorem card_residualNeighborFinset_eq_one
    (hG : HasCubicIncidentEdgeTriples G)
    (σ τ : Pairing V) (hσ : σ.SupportedBy G) (hτ : τ.SupportedBy G)
    (hne : ∀ v, σ.partner v ≠ τ.partner v) (v : V) :
    (residualNeighborFinset σ τ G v).card = 1 := by
  have hcard : (G.neighborFinset v).card = 3 := by
    calc
      (G.neighborFinset v).card = G.degree v :=
        SimpleGraph.card_neighborFinset_eq_degree G v
      _ = (incidentEdgeFinset G v).card :=
        (incidentEdgeFinset_card_eq_degree v).symm
      _ = 3 :=
        incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples hG v
  have hσmem : σ.partner v ∈ G.neighborFinset v := by
    simpa using hσ v
  have hτmem : τ.partner v ∈ G.neighborFinset v := by
    simpa using hτ v
  have hτerase :
      τ.partner v ∈ (G.neighborFinset v).erase (σ.partner v) := by
    exact Finset.mem_erase.mpr ⟨(hne v).symm, hτmem⟩
  have hcardσ := Finset.card_erase_of_mem hσmem
  have hcardτ := Finset.card_erase_of_mem hτerase
  unfold residualNeighborFinset
  omega

/-- The unused neighbour is characterized without a choice function. -/
theorem existsUnique_residualNeighbor
    (hG : HasCubicIncidentEdgeTriples G)
    (σ τ : Pairing V) (hσ : σ.SupportedBy G) (hτ : τ.SupportedBy G)
    (hne : ∀ v, σ.partner v ≠ τ.partner v) (v : V) :
    ∃! w, G.Adj v w ∧ w ≠ σ.partner v ∧ w ≠ τ.partner v := by
  have hcard :=
    card_residualNeighborFinset_eq_one hG σ τ hσ hτ hne v
  rcases Finset.card_eq_one.mp hcard with ⟨w, hw⟩
  refine ⟨w, ?_, ?_⟩
  · have hmem : w ∈ residualNeighborFinset σ τ G v := by
      rw [hw]
      simp
    have hdata :
        w ≠ τ.partner v ∧ w ≠ σ.partner v ∧ G.Adj v w := by
      simpa [residualNeighborFinset] using hmem
    exact ⟨hdata.2.2, hdata.2.1, hdata.1⟩
  · intro y hy
    have hmem : y ∈ residualNeighborFinset σ τ G v := by
      simp only [residualNeighborFinset, Finset.mem_erase,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hy.2.2, hy.2.1, hy.1⟩
    rw [hw] at hmem
    simpa using hmem

/-- The unique unused neighbour at a cubic vertex. -/
noncomputable def complementPartner
    (hG : HasCubicIncidentEdgeTriples G)
    (σ τ : Pairing V) (hσ : σ.SupportedBy G) (hτ : τ.SupportedBy G)
    (hne : ∀ v, σ.partner v ≠ τ.partner v) (v : V) : V :=
  Classical.choose (existsUnique_residualNeighbor hG σ τ hσ hτ hne v)

theorem complementPartner_spec
    (hG : HasCubicIncidentEdgeTriples G)
    (σ τ : Pairing V) (hσ : σ.SupportedBy G) (hτ : τ.SupportedBy G)
    (hne : ∀ v, σ.partner v ≠ τ.partner v) (v : V) :
    G.Adj v (complementPartner hG σ τ hσ hτ hne v) ∧
      complementPartner hG σ τ hσ hτ hne v ≠ σ.partner v ∧
      complementPartner hG σ τ hσ hτ hne v ≠ τ.partner v :=
  (Classical.choose_spec
    (existsUnique_residualNeighbor hG σ τ hσ hτ hne v)).1

/-- The unused edge at one endpoint is also unused at the other endpoint. -/
theorem complementPartner_partner
    (hG : HasCubicIncidentEdgeTriples G)
    (σ τ : Pairing V) (hσ : σ.SupportedBy G) (hτ : τ.SupportedBy G)
    (hne : ∀ v, σ.partner v ≠ τ.partner v) (v : V) :
    complementPartner hG σ τ hσ hτ hne
        (complementPartner hG σ τ hσ hτ hne v) = v := by
  let w := complementPartner hG σ τ hσ hτ hne v
  have hv := complementPartner_spec hG σ τ hσ hτ hne v
  have hvσ : v ≠ σ.partner w := by
    intro heq
    apply hv.2.1
    exact ((congrArg σ.partner heq).trans (σ.partner_partner w)).symm
  have hvτ : v ≠ τ.partner w := by
    intro heq
    apply hv.2.2
    exact ((congrArg τ.partner heq).trans (τ.partner_partner w)).symm
  have hvResidual :
      G.Adj w v ∧ v ≠ σ.partner w ∧ v ≠ τ.partner w :=
    ⟨hv.1.symm, hvσ, hvτ⟩
  exact
    (existsUnique_residualNeighbor hG σ τ hσ hτ hne w).unique
      (complementPartner_spec hG σ τ hσ hτ hne w) hvResidual

/-- The unique unused edge at each vertex forms the third perfect matching. -/
noncomputable def complementPairing
    (hG : HasCubicIncidentEdgeTriples G)
    (σ τ : Pairing V) (hσ : σ.SupportedBy G) (hτ : τ.SupportedBy G)
    (hne : ∀ v, σ.partner v ≠ τ.partner v) : Pairing V where
  partner := complementPartner hG σ τ hσ hτ hne
  partner_partner :=
    complementPartner_partner hG σ τ hσ hτ hne
  partner_ne := fun v =>
    (complementPartner_spec hG σ τ hσ hτ hne v).1.ne.symm

theorem complementPairing_supportedBy
    (hG : HasCubicIncidentEdgeTriples G)
    (σ τ : Pairing V) (hσ : σ.SupportedBy G) (hτ : τ.SupportedBy G)
    (hne : ∀ v, σ.partner v ≠ τ.partner v) :
    (complementPairing hG σ τ hσ hτ hne).SupportedBy G :=
  fun v => (complementPartner_spec hG σ τ hσ hτ hne v).1

/-- Package two disjoint supported pairings and their forced complement. -/
noncomputable def decompositionOfDisjointPairings
    (hG : HasCubicIncidentEdgeTriples G)
    (σ τ : Pairing V) (hσ : σ.SupportedBy G) (hτ : τ.SupportedBy G)
    (hne : ∀ v, σ.partner v ≠ τ.partner v) :
    GoertzelV24TaitMatchingDecomposition.ThreeMatchingDecomposition G where
  skeleton :=
    ⟨![σ, τ, complementPairing hG σ τ hσ hτ hne]⟩
  supported := by
    intro i
    fin_cases i
    · exact hσ
    · exact hτ
    · exact complementPairing_supportedBy hG σ τ hσ hτ hne
  partners_injective := by
    intro v i j hij
    have hρσ :=
      (complementPartner_spec hG σ τ hσ hτ hne v).2.1
    have hρτ :=
      (complementPartner_spec hG σ τ hσ hτ hne v).2.2
    fin_cases i <;> fin_cases j <;>
      simp_all [MatchingParity.Skeleton.partners, complementPairing]
    exact False.elim ((hne v) hij.symm)
  covers := by
    intro v w hvw
    by_cases hσw : w = σ.partner v
    · refine ⟨0, ?_⟩
      simpa [MatchingParity.Skeleton.partners] using hσw.symm
    by_cases hτw : w = τ.partner v
    · refine ⟨1, ?_⟩
      simpa [MatchingParity.Skeleton.partners] using hτw.symm
    · refine ⟨2, ?_⟩
      have hw :
          complementPartner hG σ τ hσ hτ hne v = w :=
        (existsUnique_residualNeighbor hG σ τ hσ hτ hne v).unique
          (complementPartner_spec hG σ τ hσ hτ hne v)
          ⟨hvw, hσw, hτw⟩
      simpa [MatchingParity.Skeleton.partners, complementPairing] using hw

/-- Two edge-disjoint supported perfect matchings force a Tait colouring. -/
theorem taitColorable_of_two_disjoint_supportedPairings
    (hG : HasCubicIncidentEdgeTriples G)
    (σ τ : Pairing V) (hσ : σ.SupportedBy G) (hτ : τ.SupportedBy G)
    (hne : ∀ v, σ.partner v ≠ τ.partner v) :
    TaitColorable G := by
  apply
    (GoertzelV24TaitMatchingDecomposition.taitColorable_iff_nonempty_threeMatchingDecomposition
      hG).2
  exact ⟨decompositionOfDisjointPairings hG σ τ hσ hτ hne⟩

/-- Existence of two graph-supported perfect matchings with no common edge. -/
def HasTwoDisjointSupportedPairings (G : SimpleGraph V) : Prop :=
  ∃ σ τ : Pairing V,
    σ.SupportedBy G ∧ τ.SupportedBy G ∧
      ∀ v, σ.partner v ≠ τ.partner v

/-- Two disjoint supported perfect matchings are exactly a Tait colouring. -/
theorem taitColorable_iff_hasTwoDisjointSupportedPairings
    (hG : HasCubicIncidentEdgeTriples G) :
    TaitColorable G ↔ HasTwoDisjointSupportedPairings G := by
  constructor
  · rintro ⟨C, hC⟩
    let D :=
      GoertzelV24TaitMatchingDecomposition.decompositionOfTaitColoring
        hG C hC
    refine
      ⟨D.skeleton.matching 0, D.skeleton.matching 1,
        D.supported 0, D.supported 1, ?_⟩
    intro v heq
    have hindex : (0 : Fin 3) = 1 := by
      apply D.partners_injective v
      simpa [MatchingParity.Skeleton.partners] using heq
    exact Fin.zero_ne_one hindex
  · rintro ⟨σ, τ, hσ, hτ, hne⟩
    exact
      taitColorable_of_two_disjoint_supportedPairings
        hG σ τ hσ hτ hne

/-- In a cubic Tait counterexample every two supported matchings share an edge. -/
theorem exists_shared_edge_of_not_taitColorable
    (hG : HasCubicIncidentEdgeTriples G) (hnot : ¬ TaitColorable G)
    (σ τ : Pairing V) (hσ : σ.SupportedBy G) (hτ : τ.SupportedBy G) :
    ∃ v, σ.partner v = τ.partner v := by
  by_contra hnone
  have hne : ∀ v, σ.partner v ≠ τ.partner v := by
    intro v heq
    exact hnone ⟨v, heq⟩
  exact hnot
    (taitColorable_of_two_disjoint_supportedPairings
      hG σ τ hσ hτ hne)

/-- Exchanging a fixed pair preserves its pointwise overlap locus. -/
theorem twoMatchingKempeExchange_ne_iff
    (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ v ∈ s, σ.partner v ∈ s)
    (hτ : ∀ v ∈ s, τ.partner v ∈ s) (v : V) :
    (Pairing.kempeExchange σ τ s hσ hτ).1.partner v ≠
        (Pairing.kempeExchange σ τ s hσ hτ).2.partner v ↔
      σ.partner v ≠ τ.partner v :=
  Pairing.kempeExchange_ne_iff σ τ s hσ hτ v

end GoertzelV24TaitMatchingPair

end Mettapedia.GraphTheory.FourColor
