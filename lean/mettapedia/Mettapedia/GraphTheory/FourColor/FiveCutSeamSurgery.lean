import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicSmallBoundaryCycle
import Mettapedia.GraphTheory.FourColor.ExactSizedCyclicEdgeCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCutDartDecomposition

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
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RotationCutDartDecomposition
open SimpleGraph
open SimpleGraphDartRotation

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

/-- **Seam surgery.**  Two distinct outward boundary darts of a
nontrivial exact cyclic five-edge cut never share their retained
endpoint: sharing it would trade their two crossing edges for the at
most one remaining edge of the shared cubic vertex, a cyclic cut of at
most four edges. -/
theorem vertOf_ne_of_boundaryDart_ne
    (graphData : Data G)
    (hregular : G.IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5)
    (hretainedCard : 6 ≤ (exactCutVertexSide cut.compl).card)
    (d1 d2 : BoundaryDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut)))
    (hne : d1 ≠ d2) :
    graphData.toRotationSystem.vertOf d1.1.1 ≠
      graphData.toRotationSystem.vertOf d2.1.1 := by
  classical
  intro hveq
  -- underlying graph darts, shared retained vertex, deleted endpoints
  set g1 : G.Dart := d1.1.1 with hg1
  set g2 : G.Dart := d2.1.1 with hg2
  set v : V := g1.fst with hv
  have hfst2 : g2.fst = v := by
    have := hveq
    rw [graphData.toRotationSystem_vertOf, graphData.toRotationSystem_vertOf]
      at this
    exact this.symm
  have hvRetained : ¬ cut.side v := by
    have hkeep := d1.1.2
    rw [graphData.toRotationSystem_vertOf] at hkeep
    intro hside
    exact hkeep ((mem_exactCutVertexSide_iff cut v).mpr hside)
  set w1 : V := g1.snd with hw1def
  set w2 : V := g2.snd with hw2def
  have hw1 : cut.side w1 := by
    have hexposed := d1.2
    rw [graphData.toRotationSystem_alpha,
      graphData.toRotationSystem_vertOf] at hexposed
    have := not_not.mp hexposed
    exact (mem_exactCutVertexSide_iff cut _).mp this
  have hw2 : cut.side w2 := by
    have hexposed := d2.2
    rw [graphData.toRotationSystem_alpha,
      graphData.toRotationSystem_vertOf] at hexposed
    have := not_not.mp hexposed
    exact (mem_exactCutVertexSide_iff cut _).mp this
  have hadj1 : G.Adj v w1 := g1.adj
  have hadj2 : G.Adj v w2 := hfst2 ▸ g2.adj
  have hw12 : w1 ≠ w2 := by
    intro heq
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    show g1 = g2
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact hfst2.symm
    · exact heq
  -- the two crossing edges and the third edge at `v`
  set e1 : G.edgeSet := ⟨g1.edge, g1.edge_mem⟩ with he1def
  set e2 : G.edgeSet := ⟨g2.edge, g2.edge_mem⟩ with he2def
  have hv_mem_e1 : v ∈ e1.1 := Sym2.mem_mk_left g1.fst g1.snd
  have hw1_mem_e1 : w1 ∈ e1.1 := Sym2.mem_mk_right g1.fst g1.snd
  have hv_mem_e2 : v ∈ e2.1 := by
    show v ∈ g2.edge
    rw [← hfst2]
    exact Sym2.mem_mk_left g2.fst g2.snd
  have hw2_mem_e2 : w2 ∈ e2.1 := Sym2.mem_mk_right g2.fst g2.snd
  have he1_eq : e1.1 = s(v, w1) := rfl
  have he2_eq : e2.1 = s(v, w2) := by
    show g2.edge = s(v, w2)
    rw [← hfst2]
    rfl
  have he12 : e1 ≠ e2 := by
    intro heq
    apply hw12
    have hval : e1.1 = e2.1 := congrArg Subtype.val heq
    rw [he1_eq, he2_eq] at hval
    rcases Sym2.eq_iff.mp hval with ⟨-, h⟩ | ⟨hvw, -⟩
    · exact h
    · exact absurd (hvw ▸ hw2) hvRetained
  have hneighbors : ({w1, w2} : Finset V) ⊆ G.neighborFinset v := by
    intro u hu
    rcases Finset.mem_insert.mp hu with h | h
    · rw [h, SimpleGraph.mem_neighborFinset]; exact hadj1
    · rw [Finset.mem_singleton.mp h, SimpleGraph.mem_neighborFinset]
      exact hadj2
  have hthird : ((G.neighborFinset v) \ ({w1, w2} : Finset V)).card = 1 := by
    have hdeg : (G.neighborFinset v).card = 3 := hregular v
    rw [Finset.card_sdiff_of_subset hneighbors, hdeg]
    rw [Finset.card_insert_of_notMem (by
      intro h
      exact hw12 (Finset.mem_singleton.mp h)), Finset.card_singleton]
  obtain ⟨w3, hw3⟩ := Finset.card_eq_one.mp hthird
  have hw3mem : w3 ∈ (G.neighborFinset v) \ ({w1, w2} : Finset V) := by
    rw [hw3]; exact Finset.mem_singleton_self w3
  have hadj3 : G.Adj v w3 := by
    have := (Finset.mem_sdiff.mp hw3mem).1
    rwa [SimpleGraph.mem_neighborFinset] at this
  set e3 : G.edgeSet := ⟨s(v, w3), hadj3⟩
    with he3def
  -- the shifted side and its crossing edges
  set side' : V → Prop := fun u => cut.side u ∨ u = v with hside'
  letI : DecidablePred (EdgeCrossesVertexSide G side') :=
    fun e => Classical.propDecidable _
  set edgeCut' : Finset G.edgeSet :=
    Finset.univ.filter (fun e => EdgeCrossesVertexSide G side' e)
    with hedgeCut'
  have hmem_edgeCut' : ∀ e : G.edgeSet,
      e ∈ edgeCut' ↔ EdgeCrossesVertexSide G side' e := by
    intro e
    rw [hedgeCut', Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ e, h⟩⟩
  -- every new crossing edge is an old one away from the seam, or the
  -- third edge at `v`
  have hsubset : edgeCut' ⊆
      insert e3 ((cut.edgeCut \ ({e1, e2} : Finset G.edgeSet))) := by
    intro e he
    obtain ⟨x, y, hx, hy, hsx, hsy⟩ := (hmem_edgeCut' e).mp he
    have hxy : x ≠ y := by
      intro heq
      exact hsy (heq ▸ hsx)
    have hedge : e.1 = s(x, y) := ((Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩)
    by_cases hvmem : v ∈ e.1
    · -- an edge at `v` crossing the shifted side goes to `w3`
      have hxv : x = v := by
        rcases Sym2.mem_iff.mp (hedge ▸ hvmem) with h | h
        · exact h.symm
        · exfalso
          exact hsy (Or.inr h.symm)
      have hyAdj : G.Adj v y := by
        have hmem : e.1 ∈ G.edgeSet := e.2
        rw [hedge, hxv] at hmem
        exact hmem
      have hyRetained : ¬ cut.side y := fun h => hsy (Or.inl h)
      have hy3 : y = w3 := by
        have hymem : y ∈ (G.neighborFinset v) \ ({w1, w2} : Finset V) := by
          rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
          refine ⟨hyAdj, ?_⟩
          intro hmem
          rcases Finset.mem_insert.mp hmem with h | h
          · exact hyRetained (h ▸ hw1)
          · exact hyRetained ((Finset.mem_singleton.mp h) ▸ hw2)
        rw [hw3] at hymem
        exact Finset.mem_singleton.mp hymem
      have heq3 : e = e3 := by
        apply Subtype.ext
        rw [hedge, hxv, hy3]
      rw [heq3]
      exact Finset.mem_insert_self e3 _
    · -- an edge away from `v` crosses the original cut off the seam
      have hxside : cut.side x := by
        rcases hsx with h | h
        · exact h
        · exact absurd (h ▸ hx) hvmem
      have hyside : ¬ cut.side y := fun h => hsy (Or.inl h)
      have hcrossOld : EdgeCrossesVertexSide G cut.side e :=
        ⟨x, y, hx, hy, hxside, hyside⟩
      refine Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨?_, ?_⟩)
      · exact (cut.hcut_eq e).mpr hcrossOld
      · intro hmem
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hvmem (h ▸ hv_mem_e1)
        · exact hvmem ((Finset.mem_singleton.mp h) ▸ hv_mem_e2)
  -- both seam edges belong to the old cut
  have he1mem : e1 ∈ cut.edgeCut :=
    (cut.hcut_eq e1).mpr ⟨w1, v, hw1_mem_e1, hv_mem_e1, hw1, hvRetained⟩
  have he2mem : e2 ∈ cut.edgeCut :=
    (cut.hcut_eq e2).mpr ⟨w2, v, hw2_mem_e2, hv_mem_e2, hw2, hvRetained⟩
  have hpair : ({e1, e2} : Finset G.edgeSet) ⊆ cut.edgeCut := by
    intro e he
    rcases Finset.mem_insert.mp he with h | h
    · exact h ▸ he1mem
    · exact (Finset.mem_singleton.mp h) ▸ he2mem
  have hpairCard : ({e1, e2} : Finset G.edgeSet).card = 2 := by
    rw [Finset.card_insert_of_notMem (by
      intro h
      exact he12 (Finset.mem_singleton.mp h)), Finset.card_singleton]
  have hcard4 : edgeCut'.card ≤ 4 := by
    calc edgeCut'.card ≤
        (insert e3 (cut.edgeCut \ ({e1, e2} : Finset G.edgeSet))).card :=
          Finset.card_le_card hsubset
      _ ≤ (cut.edgeCut \ ({e1, e2} : Finset G.edgeSet)).card + 1 :=
          Finset.card_insert_le _ _
      _ = (5 - 2) + 1 := by
          rw [Finset.card_sdiff_of_subset hpair, cut.hcard_eq, hpairCard]
      _ ≤ 4 := by omega
  -- the retained shore minus `v` keeps a cycle
  have houtside : HasCycleOnSide G (fun u => ¬ side' u) := by
    have hcross : ∀ dart : CrossingSideDart G (fun u => ¬ side' u),
        (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ edgeCut' := by
      rintro ⟨dart, hfstd, hsndd⟩
      rw [hmem_edgeCut']
      exact ⟨dart.snd, dart.fst,
        Sym2.mem_mk_right dart.fst dart.snd,
        Sym2.mem_mk_left dart.fst dart.snd,
        not_not.mp hsndd, hfstd⟩
    set T : Finset V := (exactCutVertexSide cut.compl).erase v with hT
    have hvmemR : v ∈ exactCutVertexSide cut.compl :=
      (mem_exactCutVertexSide_iff cut.compl v).mpr hvRetained
    have hTcard : 5 ≤ T.card := by
      rw [hT, Finset.card_erase_of_mem hvmemR]
      omega
    have hTside : ∀ u ∈ T, ¬ side' u := by
      intro u hu
      rw [hT, Finset.mem_erase] at hu
      rcases hu with ⟨hune, humem⟩
      intro hside
      rcases hside with h | h
      · exact (mem_exactCutVertexSide_iff cut.compl u).mp humem h
      · exact hune h
    have hstar : ∃ star ∈ T, ∀ e ∈ edgeCut', star ∉ (e.1 : Sym2 V) := by
      by_contra hnot
      push_neg at hnot
      let f : V → G.edgeSet := fun u =>
        if h : ∃ e ∈ edgeCut', u ∈ (e.1 : Sym2 V) then h.choose else e3
      have hmaps : ∀ u ∈ T, f u ∈ edgeCut' := by
        intro u hu
        have h := hnot u hu
        simp only [f, dif_pos h]
        exact h.choose_spec.1
      have hin : ∀ u ∈ T, u ∈ ((f u).1 : Sym2 V) := by
        intro u hu
        have h := hnot u hu
        simp only [f, dif_pos h]
        exact h.choose_spec.2
      have hlt : edgeCut'.card < T.card := by omega
      obtain ⟨u1, hu1, u2, hu2, hne12, heqf⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
      obtain ⟨x, y, hx, hy, hsx, hsy⟩ :=
        (hmem_edgeCut' (f u1)).mp (hmaps u1 hu1)
      have hxy : x ≠ y := fun heq => hsy (heq ▸ hsx)
      have hedge : (f u1).1 = s(x, y) :=
        (Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩
      have honly : ∀ u ∈ T, u ∈ ((f u1).1 : Sym2 V) → u = y := by
        intro u hu humem
        rcases Sym2.mem_iff.mp (hedge ▸ humem) with h | h
        · exact absurd (h ▸ hsx) (hTside u hu)
        · exact h
      have h1 : u1 = y := honly u1 hu1 (hin u1 hu1)
      have hin2 : u2 ∈ ((f u1).1 : Sym2 V) := by
        rw [heqf]
        exact hin u2 hu2
      have h2 : u2 = y := honly u2 hu2 hin2
      exact hne12 (h1.trans h2.symm)
    obtain ⟨star, hstarT, hstarFree⟩ := hstar
    exact hasCycleOnSide_of_crossing_le_four_of_free_vertex hregular _
      edgeCut' hcard4 hcross star (hTside star hstarT) hstarFree
  -- the shifted cut is cyclic with at most four edges
  let smallCut : SmallCyclicEdgeCut G :=
    { edgeCut := edgeCut'
      side := side'
      hcut_eq := hmem_edgeCut'
      hcard_le_four := hcard4
      hinside_cycle := cut.hinside_cycle.mono (fun u hu => Or.inl hu)
      houtside_cycle := houtside }
  have hfive : 5 ≤ edgeCut'.card := hcyclic smallCut
  omega

end

end FiveCutSeamSurgery

end Mettapedia.GraphTheory.FourColor
