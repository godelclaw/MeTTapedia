import Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstruction
import Mettapedia.GraphTheory.Kempe.HomProjection
import Mettapedia.GraphTheory.Kempe.PaletteProjection

/-!
# A frozen finite observer obstructs repair in a larger graph

A homomorphism of the nine-vertex observer into an arbitrary surrounding graph
is enough: its leaves need not be ambient leaves, and the map need not be an
induced embedding or even injective. Proper colourings pull back, and actual
histories project to sequences of proper component switches. If the observer's
boundary images stay fixed, its frozen core cannot move.
-/

namespace Mettapedia.GraphTheory.FourColor.FrozenBoundaryObserver

open SimpleGraph Relation

variable {V : Type*} {G : SimpleGraph V}

/-- The complete observed colouring remains fixed through any physical history
that protects the images of the six observer leaves. -/
theorem fixed (f : AdjacentHiddenObstruction.graph →g G)
    (B : Set V) (keeps : AdjacentHiddenObstruction.boundary ⊆ f ⁻¹' B)
    (C D : G.Coloring (Fin 4))
    (initial : C.comp f = AdjacentHiddenObstruction.state 0)
    (path : ReflTransGen (G.KempeStepAvoiding B) C D) :
    D.comp f = AdjacentHiddenObstruction.state 0 := by
  have projected := kempe_path_comp f path
  have small := ReflTransGen.mono (fun _ _ h => h.mono keeps) _ _ projected
  rw [initial] at small
  exact AdjacentHiddenObstruction.frozen.eq_of_reflTransGen subset_rfl small

/-- The target may be a proper full colouring, but a changed third core colour
rules out every history with the specified context fixed. -/
theorem no_lift (f : AdjacentHiddenObstruction.graph →g G)
    (B : Set V) (keeps : AdjacentHiddenObstruction.boundary ⊆ f ⁻¹' B)
    (C D : G.Coloring (Fin 4))
    (initial : C.comp f = AdjacentHiddenObstruction.state 0)
    (moves : D (f 2) ≠ 1) :
    ¬ ReflTransGen (G.KempeStepAvoiding B) C D := by
  intro path
  exact moves (DFunLike.congr_fun (fixed f B keeps C D initial path) 2)

/-- The observer may use any permutation of the four colour labels.
This is the exact contract consumed by the spherical program witnesses. -/
theorem no_lift_renamed [Fintype V] (e : Equiv.Perm (Fin 4))
    (f : AdjacentHiddenObstruction.graph →g G)
    (B : Set V) (keeps : AdjacentHiddenObstruction.boundary ⊆ f ⁻¹' B)
    (C D : G.Coloring (Fin 4))
    (initial : ∀ v, C (f v) = e (AdjacentHiddenObstruction.state 0 v))
    (moves : D (f 2) ≠ e 1) :
    ¬ ReflTransGen (G.KempeStepAvoiding B) C D := by
  intro path
  apply no_lift f B keeps (G.recolorOfEmbedding e.symm.toEmbedding C)
    (G.recolorOfEmbedding e.symm.toEmbedding D) ?_ ?_ (kempe_path_recolor e.symm.toEmbedding path)
  · apply DFunLike.ext
    intro v
    change e.symm (C (f v)) = AdjacentHiddenObstruction.state 0 v
    rw [initial v, e.symm_apply_apply]
  · intro h
    apply moves
    exact (e.apply_symm_apply _).symm.trans (congrArg e h)

end Mettapedia.GraphTheory.FourColor.FrozenBoundaryObserver
