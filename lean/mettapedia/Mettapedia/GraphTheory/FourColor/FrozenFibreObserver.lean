import Mettapedia.GraphTheory.FourColor.FrozenBoundaryObserver

/-!
# Frozen observations obstruct exact state-forgetting

Two proper full colourings may have the same retained colouring while a
protected finite observer proves that their physical classes differ. No
choice of an abstract move relation on that retained state space alone can
give a fibration with connected fibres. The retained state must be refined,
the permitted context enlarged, or the requested lifting contract weakened.
-/

namespace Mettapedia.GraphTheory.FourColor.FrozenFibreObserver

open SimpleGraph Relation

variable {V : Type*} {G : SimpleGraph V} [Fintype V]

/-- A frozen observed core distinguishes two physical classes inside the
same retained-colouring fibre. -/
theorem not_fibres (e : Equiv.Perm (Fin 4))
    (f : AdjacentHiddenObstruction.graph →g G)
    (B : Set V) (keeps : AdjacentHiddenObstruction.boundary ⊆ f ⁻¹' B)
    (C D : G.Coloring (Fin 4))
    (initial : ∀ v, C (f v) = e (AdjacentHiddenObstruction.state 0 v))
    (moves : D (f 2) ≠ e 1) (same : ∀ x ∈ B, C x = D x) :
    ¬ G.FibreConnected (Fin 4) B := by
  intro connected
  exact FrozenBoundaryObserver.no_lift_renamed e f B keeps C D initial moves
    (connected C D (Coloring.boundaryWord_eq_iff.mpr same))

/-- The failure is in state identification, independently of how many step
guards are imposed on the retained colourings. -/
theorem not_fibration (e : Equiv.Perm (Fin 4))
    (f : AdjacentHiddenObstruction.graph →g G)
    (B : Set V) (keeps : AdjacentHiddenObstruction.boundary ⊆ f ⁻¹' B)
    (C D : G.Coloring (Fin 4))
    (initial : ∀ v, C (f v) = e (AdjacentHiddenObstruction.state 0 v))
    (moves : D (f 2) ≠ e 1) (same : ∀ x ∈ B, C x = D x)
    (step : (G.induce B).Coloring (Fin 4) → (G.induce B).Coloring (Fin 4) → Prop) :
    ¬ Mettapedia.Combinatorics.Reconfiguration.Fibration
      (G.KempeStepAvoiding B) step (fun E : G.Coloring (Fin 4) => E.restrictInduce B) := by
  intro lift
  exact FrozenBoundaryObserver.no_lift_renamed e f B keeps C D initial moves
    (lift.fibresConnected C D (DFunLike.ext _ _ (fun x : B => same x x.property)))

end Mettapedia.GraphTheory.FourColor.FrozenFibreObserver
