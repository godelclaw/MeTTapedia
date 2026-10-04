import MettapediaFourColor.CorePairChangeObstruction
import MettapediaFourColor.CoreProfilePreparedRepair
import Mettapedia.GraphTheory.Kempe.PairHistory

/-! # The source boundary requires a change of colour pair

The six source triangle arguments apply to every exterior and every
fixed-pair history, of arbitrary finite length. The earlier explicit
preparation gives a matching two-step upper bound on its actual sphere.
-/

namespace FourColor.CorePairHistoryObstruction

open SimpleGraph FiveTriangleCollapseObstruction CoreProfileSwitchObstruction
open CorePairChangeObstruction
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
open Mettapedia.GSLT.Ultrainfinite

/-- The exterior can have any size and topology. Even a whole phase of
switches in one colour pair cannot produce a source extension. -/
theorem no_fixed_pair_extension {W : Type*} {E : SimpleGraph W}
    (ports : Fin 11 → W) (C D : E.Coloring Palette)
    (start : ∀ j, C (ports j) = word true j) (a b : Palette)
    (history : Relation.ReflTransGen (KempePairHistory.Step a b) C D)
    (K : upper.graph.Coloring Palette)
    (boundary : ∀ j, K (j.castAdd 7) = D (ports j)) : False := by
  apply no_pair_change a b K
  intro j
  have h := KempePairHistory.pointwise history (ports j)
  rwa [start j, ← boundary j] at h

theorem no_single_step_extension {W : Type*} {E : SimpleGraph W}
    (ports : Fin 11 → W) (C D : E.Coloring Palette)
    (start : ∀ j, C (ports j) = word true j)
    (step : E.KempeStep C D) (K : upper.graph.Coloring Palette)
    (boundary : ∀ j, K (j.castAdd 7) = D (ports j)) : False := by
  obtain ⟨a, b, component, rfl⟩ := step
  exact no_fixed_pair_extension ports C _ start a b
    (.single ⟨component, rfl⟩) K boundary

/-- Any physical repair history leading to an extension has at least two
steps. The source argument rules out every choice of the first pair. -/
theorem history_needs_two {W : Type*} {E : SimpleGraph W}
    (ports : Fin 11 → W) (C D : E.Coloring Palette)
    (start : ∀ j, C (ports j) = word true j)
    (history : History C D) (K : upper.graph.Coloring Palette)
    (boundary : ∀ j, K (j.castAdd 7) = D (ports j)) : 2 ≤ history.length := by
  cases history with
  | refl =>
      exact False.elim (no_fixed_pair_extension ports C C start 0 1 .refl K boundary)
  | cons step rest =>
      cases rest with
      | refl =>
          exact False.elim (no_single_step_extension ports C _ start step.toKempeStep K boundary)
      | cons next tail =>
          simp only [Route.length]
          omega

/-- Pullback along a genuine source occurrence transports the bound to
colouring reconstruction in any ambient graph. -/
theorem ambient_history_needs_two {W V : Type*} {E : SimpleGraph W} {G : SimpleGraph V}
    (ports : Fin 11 → W) (embed : W → V) (source : upper.graph →g G)
    (aligned : ∀ j, source (j.castAdd 7) = embed (ports j))
    (C D : E.Coloring Palette) (start : ∀ j, C (ports j) = word true j)
    (history : History C D) (K : G.Coloring Palette)
    (fixed : ∀ w, K (embed w) = D w) : 2 ≤ history.length := by
  let L : upper.graph.Coloring Palette := .mk (fun v => K (source v))
    (fun edge => K.valid (source.map_rel edge))
  apply history_needs_two ports C D start history L
  intro j
  change K (source (j.castAdd 7)) = D (ports j)
  rw [aligned, fixed]

open CoreProfileSwitchGeometry

/-- The actual earlier sphere reaches this lower bound: two physical
component switches are necessary and sufficient for its second input. -/
theorem two_steps_optimal :
    (CoreProfilePreparedRepair.history true).length = 2 ∧
    ∀ (D : exterior.Coloring Palette) (history : History (initial true) D)
      (K : graph.Coloring Palette),
      (∀ j : Fin 11, K (j.castAdd 7) = D j) → 2 ≤ history.length := by
  refine ⟨rfl, ?_⟩
  intro D history K fixed
  exact ambient_history_needs_two id (Fin.castAdd 7) hom (fun _ => rfl)
    (initial true) D (fun _ => rfl) history K fixed

/-- Necessity and an explicit successful endpoint are stated together. -/
theorem optimal_reconstruction :
    (CoreProfilePreparedRepair.history true).length = 2 ∧
    (∃ K : graph.Coloring Palette, ∀ j : Fin 11,
      K (j.castAdd 7) = switched false j) ∧
    ∀ (D : exterior.Coloring Palette) (history : History (initial true) D)
      (K : graph.Coloring Palette),
      (∀ j : Fin 11, K (j.castAdd 7) = D j) → 2 ≤ history.length :=
  ⟨two_steps_optimal.1, (CoreProfilePreparedRepair.reconstruction true).2,
    two_steps_optimal.2⟩

end FourColor.CorePairHistoryObstruction
