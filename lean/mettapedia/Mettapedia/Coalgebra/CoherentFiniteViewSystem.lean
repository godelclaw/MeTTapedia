import Mettapedia.Coalgebra.CoherentPrefixTower

/-!
# Streams as coherent finite observations

Streams instantiate the general finite-view interface. Their prefix towers
are already the canonical coherent towers, so the compatibility equivalence
is the identity. Each fixed Boolean prefix remains lossy.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.CoherentFiniteViewSystem

open Mettapedia.Coalgebra.StreamFinality
universe uLabel

/-- Finite prefixes form a coherent observation of stream behavior. -/
def streamObservation (Label : Type uLabel) :
    BehaviorObservation (streamPrefixSystem Label) (Stream Label) where
  observe := finiteView
  coherent := fun bounded stream => restrictPrefix_finiteView bounded stream

/-- Compatibility with the stream-specific tower name uses the same carrier. -/
def streamTowerEquiv (Label : Type uLabel) :
    (streamPrefixSystem Label).Tower ≃
      Mettapedia.Coalgebra.CoherentPrefixTower.Tower Label := Equiv.refl _

theorem streamTowerEquiv_toTower (Label : Type uLabel) (stream : Stream Label) :
    streamTowerEquiv Label ((streamObservation Label).toTower stream) =
      Mettapedia.Coalgebra.CoherentPrefixTower.Tower.ofStream stream := rfl

/-- The complete coherent prefix tower represents streams exactly. -/
theorem streamObservation_exact (Label : Type uLabel) :
    (streamObservation Label).Exact :=
  (Mettapedia.Coalgebra.CoherentPrefixTower.Tower.streamEquiv Label).bijective

/-- Loss at every fixed depth is compatible with an exact complete tower. -/
theorem fixed_view_lossy_complete_tower_exact (depth : Nat) :
    ¬ Function.Injective ((streamObservation Bool).observe depth) ∧
      (streamObservation Bool).Exact :=
  ⟨finiteView_not_injective depth Bool.false_ne_true, streamObservation_exact Bool⟩

/-- Commutation with every restriction does not itself preserve information. -/
theorem natural_map_can_erase_streams :
    ∃ mapping : FiniteViewSystem.Hom (streamPrefixSystem Bool) (streamPrefixSystem Bool),
      ¬ ((streamObservation Bool).map mapping).Faithful := by
  refine ⟨⟨fun _ _ _ => false, fun _ _ => rfl⟩, ?_⟩
  intro faithful
  exact Bool.false_ne_true
    (congrFun (faithful (a₁ := constant false) (a₂ := constant true) rfl) 0)

end Mettapedia.Coalgebra.CoherentFiniteViewSystem
