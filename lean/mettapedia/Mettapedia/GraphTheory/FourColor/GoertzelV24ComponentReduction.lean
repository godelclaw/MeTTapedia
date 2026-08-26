import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mettapedia.GraphTheory.PlanarEmbedding

/-!
# Reduction to the connected case

The reduction to connected graphs with at least three vertices has three
ingredients.  Two are available here; the third is named rather than assumed.

* A graph on at most two vertices — indeed on at most four — is four-colourable
  outright.
* If every connected component is four-colourable, so is the graph: colour each
  component independently with the same palette and take the union, which is
  proper because every edge has both endpoints in a single component.
* Planarity must pass to the components.  The source obtains this from
  planarity being inherited by subgraphs.  The plane-embedding layer here
  carries no such monotonicity, so the requirement is recorded as
  `InducedPlanarObligation` and used as an explicit hypothesis rather than
  quietly assumed.  It is the only missing piece of this lemma.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ComponentReduction

open Mettapedia.GraphTheory

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Small graphs are four-colourable outright. -/
theorem colorable_four_of_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ 4) : G.Colorable 4 :=
  (G.colorable_of_fintype).mono hcard

/-- The source's own case: at most two vertices. -/
theorem colorable_four_of_card_le_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ 2) : G.Colorable 4 :=
  colorable_four_of_card_le G (by omega)

/-- **Colouring componentwise.**  If every component of `G` is
four-colourable, so is `G`: every edge has both endpoints in one component, so
properness is inherited componentwise. -/
theorem colorable_four_of_components (G : SimpleGraph V)
    (hcomponents : ∀ c : G.ConnectedComponent,
      (G.induce (c.supp)).Colorable 4) :
    G.Colorable 4 := by
  classical
  let colouring : ∀ c : G.ConnectedComponent,
      (G.induce (c.supp)).Coloring (Fin 4) :=
    fun c => (hcomponents c).some
  let col : V → Fin 4 := fun v => colouring (G.connectedComponentMk v) ⟨v, rfl⟩
  have key : ∀ (c : G.ConnectedComponent) (x : V)
      (hx : G.connectedComponentMk x = c), col x = colouring c ⟨x, hx⟩ := by
    intro c x hx
    subst hx
    rfl
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  intro u v hadj
  have hc : G.connectedComponentMk v = G.connectedComponentMk u :=
    (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm
  have hu : G.connectedComponentMk u = G.connectedComponentMk u := rfl
  have hadj' : (G.induce ((G.connectedComponentMk u).supp)).Adj
      ⟨u, hu⟩ ⟨v, hc⟩ := hadj
  have hne := (colouring (G.connectedComponentMk u)).valid hadj'
  rw [key _ u hu, key _ v hc]
  exact hne

/-! ## The one missing ingredient -/

/-- Planarity must pass to the induced subgraph on a connected component.  The
source obtains this from planarity being inherited by subgraphs; the
plane-embedding layer here carries no monotonicity, so the requirement is
recorded rather than assumed.  Component *connectedness* is not part of this
obligation — it is already available. -/
def InducedPlanarObligation : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W),
    IsPlanar H → ∀ c : H.ConnectedComponent, IsPlanar (H.induce c.supp)

/-- **Reduction to the connected case.**  Granted that planarity passes to
components, it suffices to four-colour connected planar graphs on at least
three vertices: smaller components are four-colourable outright, and the
componentwise union is proper. -/
theorem colorable_four_of_connected_case
    (hinduced : InducedPlanarObligation.{u})
    (hconnected : ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      IsPlanar H → H.Connected → 3 ≤ Fintype.card W → H.Colorable 4)
    (G : SimpleGraph V) (hG : IsPlanar G) : G.Colorable 4 := by
  classical
  refine colorable_four_of_components G fun c => ?_
  haveI : Fintype (c.supp : Set V) := Fintype.ofFinite _
  haveI : DecidableRel (G.induce c.supp).Adj := Classical.decRel _
  by_cases hsmall : Fintype.card (c.supp : Set V) ≤ 2
  · exact colorable_four_of_card_le_two _ hsmall
  · exact hconnected _ (hinduced G hG c)
      ((SimpleGraph.ConnectedComponent.maximal_connected_induce_supp c).1)
      (by omega)

end GoertzelV24ComponentReduction

end Mettapedia.GraphTheory.FourColor
