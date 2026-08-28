import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mettapedia.GraphTheory.PlanarEmbedding

/-!
# Audit of the legacy face-incidence planarity predicate

`Mettapedia.GraphTheory.IsPlanar` currently means only that every edge occurs
in exactly two members of a finite family of edge sets.  It contains no cyclic
face order, Euler equation, or rotation-system realization.  Consequently it
is satisfied by every finite simple graph: take two formal faces, both having
the full edge set as boundary.

This is a machine-checked refutation of that predicate as a formalization of
graph planarity.  It does **not** refute the Four-Colour Theorem or Tait's
reduction.  The repaired Goertzel route must state its headline using a genuine
spherical rotation-system presentation instead of this legacy predicate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WeakPlanarityRefutation

open Mettapedia.GraphTheory

universe u

/-- Every finite simple graph admits the current weak `PlaneEmbedding`: use
two formal faces and put every edge on both formal boundaries. -/
theorem isPlanar_all_finite
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    IsPlanar G := by
  classical
  refine ⟨{
    Face := ULift.{u} Bool
    faceDecidableEq := inferInstance
    faces := Finset.univ
    faceBoundary := fun _ => Finset.univ
    edge_mem_faceSupport := ?_
    edge_two_faces := ?_
  }⟩
  · intro edge
    simp
  · intro edge hedge
    simp

/-- Five mutually adjacent vertices cannot be coloured with four colours. -/
theorem not_colorable_four_completeGraph_fin_five :
    ¬ (SimpleGraph.completeGraph (Fin 5)).Colorable 4 := by
  intro hcolorable
  obtain ⟨coloring⟩ := hcolorable
  have hinjective : Function.Injective coloring := by
    intro left right heq
    by_contra hne
    exact (coloring.valid hne) heq
  have hcard := Fintype.card_le_of_injective coloring hinjective
  simp at hcard

/-- The current weak planarity predicate does not imply four-colourability;
`K₅` is an explicit counterexample to that formal implication. -/
theorem current_planarity_does_not_imply_four_colorable :
    ∃ (G : SimpleGraph (Fin 5)), IsPlanar G ∧ ¬ G.Colorable 4 := by
  exact ⟨SimpleGraph.completeGraph (Fin 5),
    isPlanar_all_finite _, not_colorable_four_completeGraph_fin_five⟩

end GoertzelV24WeakPlanarityRefutation

end Mettapedia.GraphTheory.FourColor
