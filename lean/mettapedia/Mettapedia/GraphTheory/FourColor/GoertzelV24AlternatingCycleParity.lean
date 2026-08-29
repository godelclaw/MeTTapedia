import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Parity of finite alternating cycle systems

A finite graph in which every non-isolated vertex has degree two has as
many supported vertices as edges.  If its two incident edges alternate with
respect to a second graph, their intersection selects exactly one incident
edge at every supported vertex.  That intersection is a matching covering
the support, so the support -- and hence the edge set -- has even cardinality.

This is the abstract counting lemma used by the face-potential proof of the
Spencer--Brown--Kauffman parity invariant.  It contains no planarity or
colouring assumptions.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AlternatingCycleParity

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- The edges common to `cycles` and `selector`, regarded as a subgraph of
`cycles` whose vertex set is the full support of `cycles`. -/
def alternatingMatchingSubgraph
    (cycles selector : SimpleGraph V) : cycles.Subgraph where
  verts := cycles.support
  Adj left right := cycles.Adj left right ∧ selector.Adj left right
  adj_sub := fun hadj => hadj.1
  edge_vert := fun hadj => hadj.1.mem_support_left
  symm := {
    symm := fun left right hadj => ⟨hadj.1.symm, hadj.2.symm⟩
  }

/-- Alternation chooses exactly one of the two cycle edges incident with
each supported vertex. -/
theorem alternatingMatchingSubgraph_isMatching
    {cycles selector : SimpleGraph V}
    (hcycles : cycles.IsCycles)
    (halternating : cycles.IsAlternating selector) :
    (alternatingMatchingSubgraph cycles selector).IsMatching := by
  classical
  intro vertex hvertex
  rcases cycles.mem_support.mp hvertex with ⟨first, hfirst⟩
  rcases hcycles.other_adj_of_adj hfirst with
    ⟨second, hfirstSecond, hsecond⟩
  have halts := halternating hfirstSecond hfirst hsecond
  by_cases hselected : selector.Adj vertex first
  · refine ⟨first, ⟨hfirst, hselected⟩, ?_⟩
    intro other hother
    by_cases hotherFirst : other = first
    · exact hotherFirst
    · have hotherSecond : other = second :=
        (hcycles.existsUnique_ne_adj hfirst).unique
          ⟨Ne.symm hotherFirst, hother.1⟩ ⟨hfirstSecond, hsecond⟩
      exfalso
      apply halts.mp hselected
      simpa [hotherSecond] using hother.2
  · have hselectedSecond : selector.Adj vertex second := by
      by_contra hnot
      exact hselected (halts.mpr hnot)
    refine ⟨second, ⟨hsecond, hselectedSecond⟩, ?_⟩
    intro other hother
    by_cases hotherFirst : other = first
    · subst other
      exact False.elim (hselected hother.2)
    · exact (hcycles.existsUnique_ne_adj hfirst).unique
        ⟨Ne.symm hotherFirst, hother.1⟩ ⟨hfirstSecond, hsecond⟩

/-- A finite graph of cycles has one supported vertex per edge. -/
theorem ncard_support_eq_ncard_edgeSet_of_isCycles
    {cycles : SimpleGraph V} (hcycles : cycles.IsCycles) :
    cycles.support.ncard = cycles.edgeSet.ncard := by
  classical
  have hdegree : ∀ vertex ∈ cycles.support.toFinset,
      cycles.degree vertex = 2 := by
    intro vertex hvertex
    have hsupport : vertex ∈ cycles.support := by simpa using hvertex
    rcases cycles.mem_support.mp hsupport with ⟨neighbor, hneighbor⟩
    calc
      cycles.degree vertex = Fintype.card (cycles.neighborSet vertex) :=
        (cycles.card_neighborSet_eq_degree vertex).symm
      _ = (cycles.neighborSet vertex).ncard :=
        Set.fintypeCard_eq_ncard _
      _ = 2 := hcycles ⟨neighbor, hneighbor⟩
  have hhandshake := cycles.sum_degrees_support_eq_twice_card_edges
  have hsum :
      (∑ vertex ∈ cycles.support.toFinset, cycles.degree vertex) =
        2 * cycles.support.toFinset.card := by
    calc
      (∑ vertex ∈ cycles.support.toFinset, cycles.degree vertex) =
          ∑ _vertex ∈ cycles.support.toFinset, 2 := by
            exact Finset.sum_congr rfl hdegree
      _ = 2 * cycles.support.toFinset.card := by simp [Nat.mul_comm]
  have htwice :
      2 * cycles.support.toFinset.card = 2 * cycles.edgeFinset.card :=
    hsum.symm.trans hhandshake
  have hcards :
      cycles.support.toFinset.card = cycles.edgeFinset.card :=
    Nat.mul_left_cancel zero_lt_two htwice
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  exact hcards

/-- Every finite alternating cycle system has an even number of edges. -/
theorem even_ncard_edgeSet_of_isCycles_isAlternating
    {cycles selector : SimpleGraph V}
    (hcycles : cycles.IsCycles)
    (halternating : cycles.IsAlternating selector) :
    Even cycles.edgeSet.ncard := by
  classical
  have hmatching := alternatingMatchingSubgraph_isMatching
    hcycles halternating
  have hsupportEven : Even cycles.support.ncard := by
    have hmatchingEven := hmatching.even_card
    have hmatchingNcard :
        Even (alternatingMatchingSubgraph cycles selector).verts.ncard := by
      rw [Set.ncard_eq_toFinset_card']
      exact hmatchingEven
    simpa only [alternatingMatchingSubgraph] using hmatchingNcard
  rw [ncard_support_eq_ncard_edgeSet_of_isCycles hcycles] at hsupportEven
  exact hsupportEven

end

end GoertzelV24AlternatingCycleParity

end Mettapedia.GraphTheory.FourColor
