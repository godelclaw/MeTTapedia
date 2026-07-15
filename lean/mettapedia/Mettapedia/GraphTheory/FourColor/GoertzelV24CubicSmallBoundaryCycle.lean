import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mettapedia.GraphTheory.FourColor.CyclicEdgeCut

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CubicSmallBoundaryCycle

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [LocallyFinite G]

noncomputable section

/-- Oriented graph edges whose initial vertex lies on a chosen side. -/
def SideDart (G : SimpleGraph V) (side : V → Prop) :=
  {dart : G.Dart // side dart.fst}

/-- Oriented graph edges whose two endpoints lie on a chosen side. -/
def InternalSideDart (G : SimpleGraph V) (side : V → Prop) :=
  {dart : G.Dart // side dart.fst ∧ side dart.snd}

/-- Oriented graph edges leaving a chosen side. -/
def CrossingSideDart (G : SimpleGraph V) (side : V → Prop) :=
  {dart : G.Dart // side dart.fst ∧ ¬ side dart.snd}

noncomputable instance sideDartFintype (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Prop) : Fintype (SideDart G side) := by
  letI : Fintype G.Dart := SimpleGraph.Dart.fintype
  exact Fintype.ofInjective (fun dart => dart.1) Subtype.val_injective

noncomputable instance internalSideDartFintype (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Prop) : Fintype (InternalSideDart G side) := by
  letI : Fintype G.Dart := SimpleGraph.Dart.fintype
  exact Fintype.ofInjective (fun dart => dart.1) Subtype.val_injective

noncomputable instance crossingSideDartFintype (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Prop) : Fintype (CrossingSideDart G side) := by
  letI : Fintype G.Dart := SimpleGraph.Dart.fintype
  exact Fintype.ofInjective (fun dart => dart.1) Subtype.val_injective

/-- Darts starting on a side are exactly its internal darts plus its outgoing
crossing darts. -/
noncomputable def sideDartEquivInternalSumCrossing
    (G : SimpleGraph V) (side : V → Prop) :
    SideDart G side ≃ InternalSideDart G side ⊕ CrossingSideDart G side := by
  classical
  refine
    { toFun := fun dart =>
        if hfinish : side dart.1.snd then
          Sum.inl ⟨dart.1, dart.2, hfinish⟩
        else
          Sum.inr ⟨dart.1, dart.2, hfinish⟩
      invFun := fun dart => dart.elim
        (fun internal => ⟨internal.1, internal.2.1⟩)
        (fun crossing => ⟨crossing.1, crossing.2.1⟩)
      left_inv := ?_
      right_inv := ?_ }
  · intro dart
    by_cases hfinish : side dart.1.snd
    · simp only [dif_pos hfinish, Sum.elim_inl]
      apply Subtype.ext
      rfl
    · simp only [dif_neg hfinish, Sum.elim_inr]
      apply Subtype.ext
      rfl
  · intro dart
    rcases dart with internal | crossing
    · simp only [dif_pos internal.2.2, Sum.elim_inl]
      rfl
    · simp only [dif_neg crossing.2.2, Sum.elim_inr]
      rfl

/-- A side dart is equivalently a side vertex together with one of its graph
neighbors. -/
def sideDartEquivSigmaNeighbor (G : SimpleGraph V) (side : V → Prop) :
    SideDart G side ≃ Σ vertex : {vertex : V // side vertex},
      G.neighborSet vertex.1 where
  toFun dart := ⟨⟨dart.1.fst, dart.2⟩, ⟨dart.1.snd, dart.1.adj⟩⟩
  invFun entry := ⟨⟨(entry.1.1, entry.2.1), entry.2.2⟩, entry.1.2⟩
  left_inv dart := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    rfl
  right_inv := by
    rintro ⟨vertex, neighbor⟩
    rfl

/-- Internal side darts are exactly the darts of the graph induced on that
side. -/
def internalSideDartEquivInduceDart (G : SimpleGraph V) (side : V → Prop) :
    InternalSideDart G side ≃ (G.induce {vertex | side vertex}).Dart where
  toFun dart :=
    ⟨(⟨dart.1.fst, dart.2.1⟩, ⟨dart.1.snd, dart.2.2⟩), dart.1.adj⟩
  invFun dart :=
    ⟨⟨(dart.fst.1, dart.snd.1), dart.adj⟩, dart.fst.2, dart.snd.2⟩
  left_inv dart := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    rfl
  right_inv dart := by
    apply SimpleGraph.Dart.ext
    rfl

/-- In a cubic graph, the number of darts starting on a side is three times
the number of vertices on that side. -/
theorem card_sideDart_eq_three_mul
    (hregular : G.IsRegularOfDegree 3) (side : V → Prop)
    [Fintype {vertex : V // side vertex}] :
    Fintype.card (SideDart G side) =
      3 * Fintype.card {vertex : V // side vertex} := by
  letI : (vertex : {vertex : V // side vertex}) →
      Fintype (G.neighborSet vertex.1) := fun vertex =>
    (inferInstance : LocallyFinite G) vertex.1
  rw [Fintype.card_congr (sideDartEquivSigmaNeighbor G side),
    Fintype.card_sigma]
  simp_rw [G.card_neighborSet_eq_degree, hregular.degree_eq]
  simp [mul_comm]

/-- The internal side-dart count is twice the number of induced side edges. -/
theorem card_internalSideDart_eq_twice_card_edges (side : V → Prop)
    [Fintype ↑({vertex | side vertex} : Set V)] :
    Fintype.card (InternalSideDart G side) =
      2 * (G.induce {vertex | side vertex}).edgeFinset.card := by
  rw [Fintype.card_congr (internalSideDartEquivInduceDart G side)]
  exact (G.induce {vertex | side vertex}).dart_card_eq_twice_card_edges

/-- Mapping an outgoing side dart to its underlying edge is injective: the
opposite orientation starts outside the side. -/
theorem crossingSideDart_edge_injective (side : V → Prop) :
    Function.Injective (fun dart : CrossingSideDart G side =>
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet)) := by
  intro left right hedge
  apply Subtype.ext
  have hedgeValue : left.1.edge = right.1.edge :=
    congrArg Subtype.val hedge
  rcases (SimpleGraph.dart_edge_eq_iff left.1 right.1).1 hedgeValue with
    heq | heq
  · exact heq
  · exfalso
    have hvertex : left.1.fst = right.1.snd := by
      rw [heq]
      rfl
    exact right.2.2 (hvertex ▸ left.2.1)

/-- At most `k` listed edges can support at most `k` outgoing side darts. -/
theorem card_crossingSideDart_le_card_removed
    (side : V → Prop) (removed : Finset G.edgeSet)
    (hremoved : ∀ dart : CrossingSideDart G side,
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ removed) :
    Fintype.card (CrossingSideDart G side) ≤ removed.card := by
  let toRemoved : CrossingSideDart G side → {edge // edge ∈ removed} :=
    fun dart => ⟨⟨dart.1.edge, dart.1.edge_mem⟩, hremoved dart⟩
  have hinjective : Function.Injective toRemoved := by
    intro left right heq
    apply crossingSideDart_edge_injective side
    exact congrArg (fun edge => edge.1) heq
  calc
    Fintype.card (CrossingSideDart G side) ≤
        Fintype.card {edge // edge ∈ removed} :=
      Fintype.card_le_of_injective toRemoved hinjective
    _ = removed.card := Fintype.card_coe removed

/-- A nonempty connected side of a cubic graph with at most two outgoing
listed edges contains a cycle. This is the finite dart-count obstruction to a
tree component behind a one- or two-edge separator. -/
theorem hasCycleOnSide_of_cubic_of_connected_induce_of_crossing_le_two
    (hregular : G.IsRegularOfDegree 3) (side : V → Prop)
    (hsideNonempty : ∃ vertex, side vertex)
    (hsideConnected : (G.induce {vertex | side vertex}).Connected)
    (removed : Finset G.edgeSet) (hremovedCard : removed.card ≤ 2)
    (hcrossingRemoved : ∀ dart : CrossingSideDart G side,
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ removed) :
    HasCycleOnSide G side := by
  let sideFintype : Fintype {vertex : V // side vertex} :=
    Fintype.ofInjective (fun vertex => vertex.1) Subtype.val_injective
  letI sideSubtypeFintype : Fintype {vertex : V // side vertex} :=
    sideFintype
  letI sideSetFintype : Fintype ↑({vertex | side vertex} : Set V) :=
    sideFintype
  by_contra hnoCycle
  have hsideAcyclic : (G.induce {vertex | side vertex}).IsAcyclic := by
    intro vertex cycle hcycle
    apply hnoCycle
    let inclusion :=
      (SimpleGraph.Embedding.induce (G := G) {vertex | side vertex}).toHom
    refine ⟨vertex.1, vertex.2, cycle.map inclusion, ?_, ?_⟩
    · exact hcycle.map (fun _ _ heq => Subtype.ext heq)
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

end

end GoertzelV24CubicSmallBoundaryCycle

end Mettapedia.GraphTheory.FourColor
