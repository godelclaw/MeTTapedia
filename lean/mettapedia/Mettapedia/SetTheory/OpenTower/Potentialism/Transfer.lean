import Mettapedia.SetTheory.OpenTower.Potentialism.BoundedMorphism
import Mettapedia.SetTheory.OpenTower.Potentialism.Modal

/-!
# Validity along a surjective bounded morphism

A map that sends accessible worlds to accessible worlds, and that can pull every
accessible world of the image back to an accessible world, preserves forcing.
When the map is surjective, validity on the source frame passes to the target.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Potentialism

open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Mettapedia.SetTheory.OpenTower.Strength.StageFamilies

universe u

/-- Forcing is unchanged when a world is replaced by its image under a bounded morphism. -/
theorem forces_along_bounded {W W' : Type*} {R : W → W → Prop} {R' : W' → W' → Prop}
    (f : W → W') (hforth : ∀ a b, R a b → R' (f a) (f b))
    (hback : ∀ a w', R' (f a) w' → ∃ b, R a b ∧ f b = w') (V' : ℕ → W' → Prop) (a : W) (φ : Formula) :
    Forces R (fun n x => V' n (f x)) a φ ↔ Forces R' V' (f a) φ := by
  induction φ generalizing a with
  | atom _ =>
    rfl
  | neg φ ih =>
    rw [forces_neg, forces_neg]
    exact not_congr (ih a)
  | conj φ ψ ihφ ihψ =>
    rw [forces_conj, forces_conj]
    exact and_congr (ihφ a) (ihψ a)
  | box φ ih =>
    rw [forces_box, forces_box]
    constructor
    · intro h w' hw'
      obtain ⟨b, hb, hb'⟩ := hback a w' hw'
      have hφ : Forces R' V' (f b) φ := (ih b).mp (h b hb)
      rw [hb'] at hφ
      exact hφ
    · intro h b hb
      exact (ih b).mpr (h (f b) (hforth a b hb))

/-- Validity passes from the source of a surjective bounded morphism to its target. -/
theorem valid_of_surjective_bounded {W W' : Type*} {R : W → W → Prop} {R' : W' → W' → Prop}
    (f : W → W') (hsurj : ∀ w', ∃ a, f a = w') (hforth : ∀ a b, R a b → R' (f a) (f b))
    (hback : ∀ a w', R' (f a) w' → ∃ b, R a b ∧ f b = w') {φ : Formula} (hvalid : Valid R φ) :
    Valid R' φ := by
  intro V' w'
  obtain ⟨a, ha⟩ := hsurj w'
  have hsrc := hvalid (fun n x => V' n (f x)) a
  have himage := (forces_along_bounded f hforth hback V' a φ).mp hsrc
  rw [ha] at himage
  exact himage

/-- A formula valid on the closed sets is valid on every nonempty finite total preorder. -/
theorem valid_finite_total_of_valid_closed (h : CofinalInaccessibles.{u}) {φ : Formula}
    (hvalid : Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1) φ) {W : Type}
    (R : W → W → Prop) (finite : Finite W) (inhab : Nonempty W) (refl : ∀ w, R w w)
    (trans : ∀ a b c, R a b → R b c → R a c) (total : ∀ a b, R a b ∨ R b a) : Valid R φ := by
  obtain ⟨f, hsurj, hforth, hback⟩ :=
    closed_bounded_onto_finite_total h R finite inhab refl trans total
  exact valid_of_surjective_bounded f hsurj hforth hback hvalid

end Mettapedia.SetTheory.OpenTower.Potentialism
