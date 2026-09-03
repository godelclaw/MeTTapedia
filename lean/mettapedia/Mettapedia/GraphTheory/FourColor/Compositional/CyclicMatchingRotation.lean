import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

/-!
# Noncrossing matchings under rotation of the boundary circle

Cyclic boundary coordinates on a five-cut are pinned by the facial
successor only up to rotation.  This file shows the pin is enough: any two
coordinate systems with the same successor differ by a rotation, and
noncrossing of a matching is invariant under conjugating by a rotation.
Both facts are finite statements about `Fin 5` and are proved by `decide`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace Compositional

namespace CyclicMatchingRotation

open CyclicBoundaryMatching

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private instance (n : Nat) (first second third fourth : Fin n) :
    Decidable (ChordsCross first second third fourth) := by
  unfold ChordsCross
  infer_instance

private instance (n : Nat) (mate : Fin n → Fin n) :
    Decidable (IsNoncrossingMatching mate) := by
  unfold IsNoncrossingMatching
  infer_instance

/-- A self-map of the five-cycle commuting with the positive rotation is a
rotation. -/
theorem eq_add_of_commutes_with_rotation :
    ∀ r : Fin 5 → Fin 5, (∀ i, r (i + 1) = r i + 1) →
      ∀ i : Fin 5, r i = i + r 0 := by
  decide

/-- Noncrossing survives conjugation by a rotation of the boundary circle. -/
theorem isNoncrossingMatching_of_rotation_conj :
    ∀ (k : Fin 5) (mate : Fin 5 → Fin 5),
      IsNoncrossingMatching mate →
      IsNoncrossingMatching (fun i => mate (i - k) + k) := by
  decide

/-- Transfer noncrossing between two coordinate systems conjugate under an
equivalence commuting with the rotation. -/
theorem isNoncrossingMatching_conj_of_commutes
    (τ : Fin 5 ≃ Fin 5) (hτ : ∀ i, τ (i + 1) = τ i + 1)
    (mate : Fin 5 → Fin 5) (hmate : IsNoncrossingMatching mate) :
    IsNoncrossingMatching (fun i => τ (mate (τ.symm i))) := by
  have hadd : ∀ i : Fin 5, τ i = i + τ 0 :=
    eq_add_of_commutes_with_rotation τ hτ
  have hsymm : ∀ i : Fin 5, τ.symm i = i - τ 0 := by
    intro i
    apply τ.injective
    rw [Equiv.apply_symm_apply, hadd, sub_add_cancel]
  have heq : (fun i => τ (mate (τ.symm i))) =
      fun i => mate (i - τ 0) + τ 0 := by
    funext i
    rw [hsymm, hadd]
  rw [heq]
  exact isNoncrossingMatching_of_rotation_conj (τ 0) mate hmate

end CyclicMatchingRotation

end Compositional

end Mettapedia.GraphTheory.FourColor
