import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicSmallBoundaryCycle
import Mettapedia.GraphTheory.FourColor.ExactSizedCyclicEdgeCut

/-!
# Seam surgery: adjacent boundary darts of a nontrivial five-cut have
distinct retained endpoints

If two distinct outward boundary darts of an exact cyclic five-edge cut
shared their retained endpoint `v`, moving `v` across the cut would
trade the two crossing edges for the at most one remaining edge of the
cubic vertex `v`, producing a cyclic edge cut with at most four edges —
against cyclic five-edge-connectivity.  The deleted side keeps its
cycle; the retained side minus `v` keeps one because a cubic shore
behind at most four crossing edges contains a cycle as soon as one of
its vertices touches none of them: that vertex's component carries all
three of its neighbours, so the tree dart count cannot hold there.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace FiveCutSeamSurgery

open GoertzelV24CubicSmallBoundaryCycle
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- A nonempty connected side of a cubic graph with at most four outgoing
listed edges contains a cycle or has at most two vertices. -/
theorem hasCycleOnSide_or_card_le_two_of_crossing_le_four
    (hregular : G.IsRegularOfDegree 3) (side : V → Prop)
    (hsideNonempty : ∃ vertex, side vertex)
    (hsideConnected : (G.induce {vertex | side vertex}).Connected)
    (removed : Finset G.edgeSet) (hremovedCard : removed.card ≤ 4)
    (hcrossingRemoved : ∀ dart : CrossingSideDart G side,
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ removed) :
    HasCycleOnSide G side ∨
      Fintype.card {vertex : V // side vertex} ≤ 2 := by
  let sideFintype : Fintype {vertex : V // side vertex} :=
    Fintype.ofInjective (fun vertex => vertex.1) Subtype.val_injective
  letI sideSubtypeFintype : Fintype {vertex : V // side vertex} :=
    sideFintype
  letI sideSetFintype : Fintype ↑({vertex | side vertex} : Set V) :=
    sideFintype
  by_cases hcycle : HasCycleOnSide G side
  · exact Or.inl hcycle
  · right
    have hsideAcyclic : (G.induce {vertex | side vertex}).IsAcyclic := by
      intro vertex cycle hcycleWalk
      apply hcycle
      let inclusion :=
        (SimpleGraph.Embedding.induce (G := G) {vertex | side vertex}).toHom
      refine ⟨vertex.1, vertex.2, cycle.map inclusion, ?_, ?_⟩
      · exact hcycleWalk.map (fun _ _ heq => Subtype.ext heq)
      · intro other hother
        have hother' : other ∈ cycle.support.map inclusion := by
          exact Walk.support_map inclusion cycle ▸ hother
        rcases List.mem_map.mp hother' with ⟨source, _hsource, hsource⟩
        rw [← hsource]
        exact source.2
    have htree : (G.induce {vertex | side vertex}).IsTree :=
      ⟨hsideConnected, hsideAcyclic⟩
    have htreeCard := htree.card_edgeFinset
    have hpartition := Fintype.card_congr
      (sideDartEquivInternalSumCrossing G side)
    rw [Fintype.card_sum] at hpartition
    have hsideCard := card_sideDart_eq_three_mul hregular side
    have hinternalCard := card_internalSideDart_eq_twice_card_edges
      (G := G) side
    have hcrossingCard := card_crossingSideDart_le_card_removed
      side removed hcrossingRemoved
    have hsidePositive :
        0 < Fintype.card {vertex : V // side vertex} :=
      Fintype.card_pos_iff.mpr ⟨⟨hsideNonempty.choose,
        hsideNonempty.choose_spec⟩⟩
    have hsameSideCard :
        Fintype.card ↑({vertex | side vertex} : Set V) =
          Fintype.card {vertex : V // side vertex} := by
      rfl
    omega

/-- A cubic side behind at most four listed crossing edges contains a
cycle as soon as one side vertex touches none of the listed edges: that
vertex's component brings all three of its neighbours, so the tree dart
count cannot hold there.  No connectivity of the side is assumed. -/
theorem hasCycleOnSide_of_crossing_le_four_of_free_vertex
    (hregular : G.IsRegularOfDegree 3) (side : V → Prop)
    (removed : Finset G.edgeSet) (hremovedCard : removed.card ≤ 4)
    (hcrossingRemoved : ∀ dart : CrossingSideDart G side,
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ removed)
    (star : V) (hstarSide : side star)
    (hstarFree : ∀ edge ∈ removed, star ∉ (edge.1 : Sym2 V)) :
    HasCycleOnSide G side := by
  classical
  let comp : V → Prop := fun u => ∃ hu : side u,
    (G.induce {vertex | side vertex}).Reachable ⟨star, hstarSide⟩ ⟨u, hu⟩
  have hcompSide : ∀ u, comp u → side u := fun u hu => hu.1
  have hstarComp : comp star := ⟨hstarSide, Reachable.rfl⟩
  have hcompAdj : ∀ u w, comp u → side w → G.Adj u w → comp w := by
    rintro u w ⟨hu, hreach⟩ hw hadj
    exact ⟨hw, hreach.trans (SimpleGraph.Adj.reachable
      (by exact hadj :
        (G.induce {vertex | side vertex}).Adj ⟨u, hu⟩ ⟨w, hw⟩))⟩
  have hneighborComp : ∀ w, G.Adj star w → comp w := by
    intro w hadj
    have hwSide : side w := by
      by_contra hnot
      have hmem := hcrossingRemoved
        ⟨SimpleGraph.Dart.mk (star, w) hadj, hstarSide, hnot⟩
      apply hstarFree _ hmem
      exact Sym2.mem_mk_left star w
    exact hcompAdj star w hstarComp hwSide hadj
  have hcompCrossing : ∀ dart : CrossingSideDart G comp,
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ removed := by
    rintro ⟨dart, hfst, hsnd⟩
    by_cases hsndSide : side dart.snd
    · exact absurd (hcompAdj dart.fst dart.snd hfst hsndSide dart.adj) hsnd
    · exact hcrossingRemoved ⟨dart, hcompSide _ hfst, hsndSide⟩
  -- reachability inside the side pushes down to the component
  have hpush : ∀ (u a : {vertex : V // side vertex})
      (_ : (G.induce {vertex | side vertex}).Walk u a) (hu : comp u.1),
      ∃ ha : comp a.1,
        (G.induce {vertex | comp vertex}).Reachable
          ⟨u.1, hu⟩ ⟨a.1, ha⟩ := by
    intro u a walk
    induction walk with
    | nil =>
      intro hu
      exact ⟨hu, Reachable.rfl⟩
    | @cons b c d hadj tail ih =>
      intro hb
      have hcComp : comp c.1 := hcompAdj b.1 c.1 hb c.2 hadj
      obtain ⟨ha, hreach⟩ := ih hcComp
      refine ⟨ha, ?_⟩
      exact (SimpleGraph.Adj.reachable
        (by exact hadj :
          (G.induce {vertex | comp vertex}).Adj
            ⟨b.1, hb⟩ ⟨c.1, hcComp⟩)).trans hreach
  have hcompConnected : (G.induce {vertex | comp vertex}).Connected := by
    rw [SimpleGraph.connected_iff]
    refine ⟨?_, ⟨⟨star, hstarComp⟩⟩⟩
    have hfromStar : ∀ x : {vertex : V // comp vertex},
        (G.induce {vertex | comp vertex}).Reachable
          ⟨star, hstarComp⟩ x := by
      rintro ⟨x, hxComp⟩
      obtain ⟨walk⟩ := hxComp.2
      obtain ⟨ha, hreach⟩ := hpush _ _ walk hstarComp
      exact hreach
    rintro x y
    exact (hfromStar x).symm.trans (hfromStar y)
  -- the component has at least three vertices: star and two neighbours
  have hstarDegree : (G.neighborFinset star).card = 3 := hregular star
  obtain ⟨n₁, hn₁, n₂, hn₂, hn₁₂⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (G.neighborFinset star).card)
  have hadj₁ : G.Adj star n₁ := by
    rwa [SimpleGraph.mem_neighborFinset] at hn₁
  have hadj₂ : G.Adj star n₂ := by
    rwa [SimpleGraph.mem_neighborFinset] at hn₂
  have hcompCard : 3 ≤ Fintype.card {vertex : V // comp vertex} := by
    rw [Fintype.card_subtype]
    have hsubset : ({star, n₁, n₂} : Finset V) ⊆
        Finset.univ.filter comp := by
      intro u hu
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ u, ?_⟩
      rcases Finset.mem_insert.mp hu with h | h
      · exact h ▸ hstarComp
      · rcases Finset.mem_insert.mp h with h' | h'
        · exact h' ▸ hneighborComp n₁ hadj₁
        · rw [Finset.mem_singleton.mp h']
          exact hneighborComp n₂ hadj₂
    have hcard : ({star, n₁, n₂} : Finset V).card = 3 :=
      Finset.card_eq_three.mpr ⟨star, n₁, n₂,
        fun h => G.irrefl (h ▸ hadj₁),
        fun h => G.irrefl (h ▸ hadj₂), hn₁₂, rfl⟩
    calc 3 = ({star, n₁, n₂} : Finset V).card := hcard.symm
      _ ≤ (Finset.univ.filter comp).card := Finset.card_le_card hsubset
  rcases hasCycleOnSide_or_card_le_two_of_crossing_le_four hregular comp
      ⟨star, hstarComp⟩ hcompConnected removed hremovedCard
      hcompCrossing with hcycle | hsmall
  · exact hcycle.mono hcompSide
  · omega

end

end FiveCutSeamSurgery

end Mettapedia.GraphTheory.FourColor
