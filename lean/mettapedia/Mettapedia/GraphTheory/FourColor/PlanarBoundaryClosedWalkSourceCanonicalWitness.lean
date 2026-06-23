import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusWitness

/-!
# Source-side criterion for canonical witness choice

This file keeps the canonical-witness question at the honest closed-walk source
layer.  The route file already constructs a canonical witness choice from the
source plus the facewise at-most-one interior-edge condition, while the positive
source obstruction file proves the reverse implication for any canonical
witness choice.  Combining the two gives the exact source-side obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- On an honest closed-walk annulus source, source-boundary canonical witness
choice is equivalent to the facewise at-most-one interior-edge condition. -/
theorem nonempty_planarBoundaryCanonicalWitnessChoice_iff_facewiseAtMostOneInteriorEdge_of_closedWalkAnnulusBoundarySource
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData) ↔
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1 := by
  constructor
  · intro hchoice f
    by_contra hle
    have hgt :
        1 <
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card :=
      Nat.lt_of_not_ge hle
    rw [Finset.one_lt_card] at hgt
    rcases hgt with ⟨e₁, he₁, e₂, he₂, hne⟩
    rcases Finset.mem_filter.1 he₁ with ⟨he₁Face, he₁Interior⟩
    rcases Finset.mem_filter.1 he₂ with ⟨he₂Face, he₂Interior⟩
    exact
      not_nonempty_planarBoundaryCanonicalWitnessChoice_of_exists_two_distinct_interior_edges_on_faceBoundary
        source.toPlanarBoundaryAnnulusBoundaryData
        ⟨f, e₁, he₁Face, e₂, he₂Face, hne, he₁Interior, he₂Interior⟩ hchoice
  · intro hAtMost
    classical
    have huniqueInterior :
        ∀ (f : AmbientFace emb.faces) {e₁ e₂ : G.edgeSet},
          e₁ ∈ emb.faceBoundary f.1 →
            e₂ ∈ emb.faceBoundary f.1 →
              e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e₁ = e₂ := by
      intro f e₁ e₂ he₁ he₂ hi₁ hi₂
      by_contra hne
      have he₁Filter :
          e₁ ∈ (emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :=
        Finset.mem_filter.2 ⟨he₁, hi₁⟩
      have he₂Filter :
          e₂ ∈ (emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :=
        Finset.mem_filter.2 ⟨he₂, hi₂⟩
      have hgt :
          1 <
            ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card :=
        Finset.one_lt_card.2 ⟨e₁, he₁Filter, e₂, he₂Filter, hne⟩
      exact Nat.not_lt_of_ge (hAtMost f) hgt
    exact
      ⟨PlanarBoundaryCanonicalWitnessChoice.of_atMostOneInteriorEdgePerFace
        (boundaryData := source.toPlanarBoundaryAnnulusBoundaryData)
        source.fallbackEdge source.fallbackEdge_mem_faceBoundary huniqueInterior
        (by
          intro f e heFace heNotInterior
          exact
            source.toPlanarBoundaryAnnulusBoundaryData
              |>.mem_outerAmbientBoundary_union_innerAmbientBoundary_of_mem_faceBoundary_of_not_mem_interiorEdgeSupport
                heFace heNotInterior)⟩

/-- Graph-level source criterion: exhibiting an honest closed-walk source with a
canonical witness choice is exactly exhibiting such a source with the facewise
at-most-one interior-edge condition. -/
theorem exists_closedWalkAnnulusBoundarySource_and_planarBoundaryCanonicalWitnessChoice_iff_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} :
    (∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData)) ↔
      (∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) := by
  constructor
  · rintro ⟨emb, source, hchoice⟩
    exact
      ⟨emb, source,
        (nonempty_planarBoundaryCanonicalWitnessChoice_iff_facewiseAtMostOneInteriorEdge_of_closedWalkAnnulusBoundarySource
          source).1 hchoice⟩
  · rintro ⟨emb, source, hAtMost⟩
    exact
      ⟨emb, source,
        (nonempty_planarBoundaryCanonicalWitnessChoice_iff_facewiseAtMostOneInteriorEdge_of_closedWalkAnnulusBoundarySource
          source).2 hAtMost⟩

end Mettapedia.GraphTheory.FourColor
