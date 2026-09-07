import Mettapedia.GraphTheory.FourColor.RankedForestParity
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedLocalDualCycleBond

/-!
# Deleting a ranked dual forest preserves primal connectedness

Full primal cuts have even incidence at every two-sided quotient face.
A cut supported in a ranked dual forest is therefore empty. It follows
that deleting the selected original edges preserves primal connectedness.
This supplies the connectivity part of the tree-cotree construction;
neither a spanning dual tree nor its metric bound is assumed to exist here.
-/

namespace Mettapedia.GraphTheory.FourColor.RankedDualForestComplement

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceTwoSided
open GoertzelV24FramedLocalDualCycleBond

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- An original-edge forest, oriented towards smaller quotient-face rank. -/
structure RankedDualForest (data : Data G) where
  edges : Finset G.edgeSet
  child : G.edgeSet → OrbitFace data.toRotationSystem
  parent : G.edgeSet → OrbitFace data.toRotationSystem
  rank : OrbitFace data.toRotationSystem → ℕ
  child_injective : Set.InjOn child edges
  descending : ∀ e ∈ edges, rank (parent e) < rank (child e)
  incidence : ∀ e ∈ edges, ∀ f,
    e ∈ orbitFaceBoundary data.toRotationSystem f ↔ child e = f ∨ parent e = f

namespace RankedDualForest

variable {data : Data G} (T : RankedDualForest data)

/-- A full cut contained in the forest is empty by literal face parity. -/
theorem crossing_eq_empty (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (side : V → Prop) (hsub : localCrossingEdgeFinset G side ⊆ T.edges) :
    localCrossingEdgeFinset G side = ∅ := by
  classical
  apply RankedForestParity.eq_empty_of_even_incidence _ T.child T.parent T.rank
    (T.child_injective.mono hsub) (fun e he => T.descending e (hsub he))
  intro f
  have heq : (localCrossingEdgeFinset G side).filter
      (fun e => T.child e = f ∨ T.parent e = f) =
      localCrossingEdgeFinset G side ∩ orbitFaceBoundary data.toRotationSystem f := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter]
    exact and_congr_right fun he => (T.incidence e (hsub he) f).symm
  rw [heq]
  exact even_card_crossingEdgeFinset_inter_orbitFaceBoundary_of_faceTwoSided
    data side f (fun d _ => htwo d)

/-- Delete selected original edges, retaining the full original vertex carrier. -/
def complementGraph : SimpleGraph V :=
  G.deleteEdges (Subtype.val '' (T.edges : Set G.edgeSet))

theorem complement_adj_iff {u v : V} (h : G.Adj u v) :
    T.complementGraph.Adj u v ↔ (⟨s(u, v), h⟩ : G.edgeSet) ∉ T.edges := by
  classical
  simp only [complementGraph, deleteEdges_adj, h, true_and, Set.mem_image, Finset.mem_coe]
  constructor
  · intro hn he
    exact hn ⟨⟨s(u, v), h⟩, he, rfl⟩
  · rintro hn ⟨e, he, heq⟩
    have heq' : e = (⟨s(u, v), h⟩ : G.edgeSet) := Subtype.ext heq
    exact hn (heq' ▸ he)

/-- A ranked dual forest cannot disconnect the connected original graph. -/
theorem complement_connected (hconn : G.Connected)
    (htwo : OrbitFacesTwoSided data.toRotationSystem) : T.complementGraph.Connected := by
  classical
  letI : Nonempty V := hconn.nonempty
  refine ⟨?_⟩
  intro u v
  let side : V → Prop := T.complementGraph.Reachable u
  have hsub : localCrossingEdgeFinset G side ⊆ T.edges := by
    intro e he
    have hcross := (mem_localCrossingEdgeFinset_iff side e).mp he
    obtain ⟨edge, hedge⟩ := e
    induction edge using Sym2.ind with
    | h a b =>
      by_contra hn
      have hadj : T.complementGraph.Adj a b := (T.complement_adj_iff hedge).mpr hn
      exact (not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq rfl hcross)
        ⟨fun ha => ha.trans hadj.reachable, fun hb => hb.trans hadj.symm.reachable⟩
  have hempty := T.crossing_eq_empty htwo side hsub
  have hstep : ∀ {a b}, G.Adj a b → side a → side b := by
    intro a b hab ha
    by_contra hb
    have he : (⟨s(a, b), hab⟩ : G.edgeSet) ∈ localCrossingEdgeFinset G side := by
      apply (mem_localCrossingEdgeFinset_iff side _).mpr
      exact ⟨a, b, by simp, by simp, ha, hb⟩
    simp [hempty] at he
  obtain ⟨p⟩ := hconn u v
  have hwalk : ∀ {a b} (q : G.Walk a b), side a → side b := by
    intro a b q
    induction q with
    | nil => exact id
    | cons h q ih => exact fun ha => ih (hstep h ha)
  exact hwalk p .rfl

/-- Euler supplies the complementary tree size when the forest spans all faces. -/
theorem complement_isTree (hconn : G.Connected)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (heuler : (Fintype.card V : ℤ) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (hsize : T.edges.card + 1 = Fintype.card (OrbitFace data.toRotationSystem)) :
    T.complementGraph.IsTree := by
  classical
  have hset : T.complementGraph.edgeFinset = G.edgeFinset \ T.edges.image Subtype.val := by
    ext e
    induction e using Sym2.ind with
    | h u v => simp [complementGraph, Finset.mem_sdiff, Finset.mem_image]
  have hsub : T.edges.image Subtype.val ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
    simpa only [SimpleGraph.mem_edgeFinset] using f.property
  have hc : T.complementGraph.edgeFinset.card + T.edges.card = G.edgeFinset.card := by
    rw [hset, ← Finset.card_image_of_injective T.edges Subtype.val_injective]
    exact Finset.card_sdiff_add_card_eq_card hsub
  have heuler' : (Fintype.card V : ℤ) - G.edgeFinset.card +
      Fintype.card (OrbitFace data.toRotationSystem) = 2 := by
    simpa only [SimpleGraph.edgeFinset_card] using heuler
  have hn : T.complementGraph.edgeFinset.card + 1 = Fintype.card V := by omega
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨T.complement_connected hconn htwo, ?_⟩
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using hn

end RankedDualForest
end
end Mettapedia.GraphTheory.FourColor.RankedDualForestComplement
