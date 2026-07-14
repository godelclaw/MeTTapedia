import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mettapedia.GraphTheory.EdgeColoring
import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24Necklace

open SimpleGraph

/-- In the canonical locked word, the blue/purple pair has exactly the two
singleton-color stubs `2` and `4` as its active support. -/
theorem cap5BadBoundaryWord2111_activeSupport_blue_purple :
    cap5ActiveSupport blue purple cap5BadBoundaryWord2111 =
      ({2, 4} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5ActiveSupport, cap5BadBoundaryWord2111, red, blue, purple]

/-- The five endpoint pairs in the locked-pentagon necklace. -/
def canonicalNecklaceSupports : Finset (Finset (Fin 5)) :=
  {{0, 3}, {1, 2}, {0, 4}, {1, 3}, {2, 4}}

/-- Number of necklace strands incident to a cap stub. -/
def necklaceIncidenceCount (i : Fin 5) : Nat :=
  (canonicalNecklaceSupports.filter fun support ↦ i ∈ support).card

/-- Endpoint graph of the five necklace strands. -/
def necklaceEndpointGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun i j ↦
    ({i, j} : Finset (Fin 5)) ∈ canonicalNecklaceSupports

theorem canonicalNecklaceSupports_card : canonicalNecklaceSupports.card = 5 := by
  decide

theorem canonicalNecklaceSupports_each_card_two :
    ∀ support ∈ canonicalNecklaceSupports, support.card = 2 := by
  decide

/-- Every cap spoke lies on exactly two of the five strands. -/
theorem necklaceIncidenceCount_eq_two (i : Fin 5) :
    necklaceIncidenceCount i = 2 := by
  fin_cases i <;> decide

/-- The endpoint graph spells the manuscript's closed necklace chain. -/
theorem necklaceEndpointGraph_closed_chain :
    necklaceEndpointGraph.Adj 0 4 ∧
    necklaceEndpointGraph.Adj 4 2 ∧
    necklaceEndpointGraph.Adj 2 1 ∧
    necklaceEndpointGraph.Adj 1 3 ∧
    necklaceEndpointGraph.Adj 3 0 := by
  unfold necklaceEndpointGraph canonicalNecklaceSupports
  decide

/-- The five strands form one connected endpoint union. -/
theorem necklaceEndpointGraph_connected : necklaceEndpointGraph.Connected := by
  unfold necklaceEndpointGraph canonicalNecklaceSupports
  decide

/-- Exceptional CAP5 component pairings, together with the forced
blue/purple singleton strand, are exactly the five necklace supports. The
component slots may occur in either order. -/
theorem necklaceSupports_eq_canonical_of_isExceptional
    (p : CAP5BadPairingSupports) (h : p.IsExceptional) :
    ({p.redBlue₁, p.redBlue₂, p.redPurple₁, p.redPurple₂,
        ({2, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5))) =
      canonicalNecklaceSupports := by
  rcases h with ⟨hredBlue, hredPurple⟩
  rcases hredBlue with hredBlue | hredBlue <;>
    rcases hredBlue with ⟨hredBlue₁, hredBlue₂⟩ <;>
    rcases hredPurple with hredPurple | hredPurple <;>
    rcases hredPurple with ⟨hredPurple₁, hredPurple₂⟩ <;>
    simp [hredBlue₁, hredBlue₂, hredPurple₁, hredPurple₂,
      canonicalNecklaceSupports] <;> decide

/-- Endpoint form of the Necklace Lemma from the component-cover interface:
if no immediate support switch repairs the locked word, the five recorded
component supports have the canonical necklace incidence. A graph-level
strand extraction must separately show that these supports come from the
corresponding connected Kempe strands. -/
theorem necklaceSupports_eq_canonical_of_componentCovers_of_not_hasRepair
    (p : CAP5BadPairingSupports) (hcovers : p.HasComponentCovers)
    (hlocked : ¬ p.HasRepair) :
    ({p.redBlue₁, p.redBlue₂, p.redPurple₁, p.redPurple₂,
        ({2, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5))) =
      canonicalNecklaceSupports := by
  apply necklaceSupports_eq_canonical_of_isExceptional p
  exact (CAP5BadPairingSupports.isExceptional_iff_not_hasRepair_of_componentCovers
    hcovers).2 hlocked

/-- In a finite graph with only two possible odd-degree vertices, the two are
reachable whenever the first is actually odd. Applied to a two-color line
subgraph, this is the handshaking step that forces the two strand endpoints
into one Kempe component. -/
theorem reachable_of_odd_degree_of_only_two_odd
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (u v : W)
    (hu : Odd (H.degree u))
    (honly : ∀ w : W, Odd (H.degree w) → w = u ∨ w = v) :
    H.Reachable u v := by
  classical
  let K : H.ConnectedComponent := H.connectedComponentMk u
  have huK : u ∈ K.supp := by
    exact ConnectedComponent.connectedComponentMk_mem
  let uK : K.supp := ⟨u, huK⟩
  have hclosed : H.neighborSet u ⊆ K.supp := by
    intro w huw
    exact K.mem_supp_of_adj_mem_supp huK huw
  have huDegree : (H.induce K.supp).degree uK = H.degree u := by
    exact H.degree_induce_of_neighborSet_subset (s := K.supp) (v := uK) hclosed
  have huOdd : Odd ((H.induce K.supp).degree uK) := by
    simpa [huDegree] using hu
  obtain ⟨wK, hne, hwOddK⟩ :=
    (H.induce K.supp).exists_ne_odd_degree_of_exists_odd_degree uK huOdd
  have hwClosed : H.neighborSet wK.val ⊆ K.supp := by
    intro z hwz
    exact K.mem_supp_of_adj_mem_supp wK.property hwz
  have hwDegree : (H.induce K.supp).degree wK = H.degree wK.val := by
    exact H.degree_induce_of_neighborSet_subset (s := K.supp) (v := wK) hwClosed
  have hwOdd : Odd (H.degree wK.val) := by
    simpa [hwDegree] using hwOddK
  rcases honly wK.val hwOdd with hwu | hwv
  · exact False.elim (hne (Subtype.ext hwu))
  · exact K.reachable_of_mem_supp huK (hwv ▸ wK.property)

/-- Stub `2` has the singleton color `blue` in the canonical locked CAP5 word. -/
theorem cap5BadBoundaryWord2111_edge_two_blue
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (boundaryEdge : Fin 5 → G.edgeSet)
    (C : G.EdgeColoring Color)
    (hword : cap5BoundaryWordOfEdges boundaryEdge C = cap5BadBoundaryWord2111) :
    C (boundaryEdge 2) = blue := by
  have h := congrFun hword 2
  simpa [cap5BoundaryWordOfEdges, cap5BadBoundaryWord2111, blue] using h

/-- Stub `4` has the singleton color `purple` in the canonical locked CAP5 word. -/
theorem cap5BadBoundaryWord2111_edge_four_purple
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (boundaryEdge : Fin 5 → G.edgeSet)
    (C : G.EdgeColoring Color)
    (hword : cap5BoundaryWordOfEdges boundaryEdge C = cap5BadBoundaryWord2111) :
    C (boundaryEdge 4) = purple := by
  have h := congrFun hword 4
  simpa [cap5BoundaryWordOfEdges, cap5BadBoundaryWord2111, purple] using h

/-- Graph-level forcing of the singleton necklace strand. If the actual
blue/purple line subgraph has stub `2` odd and has no odd vertices except the
two singleton-color stubs, the two stub edges lie in the same Kempe component.
The conclusion is reachability in the computed bicolored line graph, not an
assumed endpoint pairing. -/
theorem singletonBluePurpleStubs_reachable_of_odd_degree_classification
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (boundaryEdge : Fin 5 → G.edgeSet)
    (C : G.EdgeColoring Color)
    [Fintype (C.bicoloredSet blue purple)]
    (hword : cap5BoundaryWordOfEdges boundaryEdge C = cap5BadBoundaryWord2111)
    [DecidableRel (C.bicoloredSubgraph blue purple).Adj]
    (hoddTwo :
      Odd ((C.bicoloredSubgraph blue purple).degree
        ⟨boundaryEdge 2, by
          exact Or.inl (cap5BadBoundaryWord2111_edge_two_blue boundaryEdge C hword)⟩))
    (honly :
      ∀ e : C.bicoloredSet blue purple,
        Odd ((C.bicoloredSubgraph blue purple).degree e) →
          e.val = boundaryEdge 2 ∨ e.val = boundaryEdge 4) :
    (C.bicoloredSubgraph blue purple).Reachable
      ⟨boundaryEdge 2, by
        exact Or.inl (cap5BadBoundaryWord2111_edge_two_blue boundaryEdge C hword)⟩
      ⟨boundaryEdge 4, by
        exact Or.inr (cap5BadBoundaryWord2111_edge_four_purple boundaryEdge C hword)⟩ := by
  apply reachable_of_odd_degree_of_only_two_odd
    (C.bicoloredSubgraph blue purple)
  · exact hoddTwo
  · intro e he
    rcases honly e he with he2 | he4
    · exact Or.inl (Subtype.ext he2)
    · exact Or.inr (Subtype.ext he4)

/-- Exact endpoint predicate for a colored tangle: the odd vertices of the
selected bicolored line graph are precisely its selected-color boundary
edges. Both sides are computed from the coloring, graph, and boundary map. -/
def BicoloredOddVerticesAreExactlyBoundaryEdges
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (a b : Color) [Fintype (C.bicoloredSet a b)]
    [DecidableRel (C.bicoloredSubgraph a b).Adj] : Prop :=
  ∀ e : C.bicoloredSet a b,
    Odd ((C.bicoloredSubgraph a b).degree e) ↔
      ∃ i : Fin 5, e.val = boundaryEdge i

/-- The exact boundary-endpoint predicate and the locked CAP5 word force the
singleton blue/purple strand `R`: boundary edges `2` and `4` are reachable in
the actual bicolored line graph. -/
theorem singletonBluePurpleStubs_reachable_of_exact_boundary_odd_vertices
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (boundaryEdge : Fin 5 → G.edgeSet)
    (C : G.EdgeColoring Color)
    [Fintype (C.bicoloredSet blue purple)]
    (hword : cap5BoundaryWordOfEdges boundaryEdge C = cap5BadBoundaryWord2111)
    [DecidableRel (C.bicoloredSubgraph blue purple).Adj]
    (hendpoints :
      BicoloredOddVerticesAreExactlyBoundaryEdges
        boundaryEdge C blue purple) :
    (C.bicoloredSubgraph blue purple).Reachable
      ⟨boundaryEdge 2, by
        exact Or.inl (cap5BadBoundaryWord2111_edge_two_blue boundaryEdge C hword)⟩
      ⟨boundaryEdge 4, by
        exact Or.inr (cap5BadBoundaryWord2111_edge_four_purple boundaryEdge C hword)⟩ := by
  apply singletonBluePurpleStubs_reachable_of_odd_degree_classification
    boundaryEdge C hword
  · apply (hendpoints _).2
    exact ⟨2, rfl⟩
  · intro e he
    rcases (hendpoints e).1 he with ⟨i, hi⟩
    have hiColor : C (boundaryEdge i) = blue ∨ C (boundaryEdge i) = purple := by
      simpa [hi] using e.property
    have hiActive :
        i ∈ cap5ActiveSupport blue purple cap5BadBoundaryWord2111 := by
      rw [← hword]
      simpa [cap5ActiveSupport, cap5BoundaryWordOfEdges] using hiColor
    rw [cap5BadBoundaryWord2111_activeSupport_blue_purple] at hiActive
    simp only [Finset.mem_insert, Finset.mem_singleton] at hiActive
    rcases hiActive with hiTwo | hiFour
    · exact Or.inl (hi.trans (congrArg boundaryEdge hiTwo))
    · exact Or.inr (hi.trans (congrArg boundaryEdge hiFour))

end GoertzelV24Necklace

end Mettapedia.GraphTheory.FourColor
