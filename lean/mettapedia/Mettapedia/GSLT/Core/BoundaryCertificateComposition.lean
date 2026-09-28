import Mettapedia.GSLT.Core.RelationalRouteSemantics

/-!
# Composing local boundary certificates along routes

A local replacement retains the two boundary states and transports actual
witnesses in both directions. The replacement extends to every finite route
and every surrounding route. No uniqueness, totality, or equality of witness
counts is required. This is the relational form of exact interior elimination.
-/

namespace Mettapedia.GSLT.RelationalRouteSemantics

open Mettapedia.GSLT.Ultrainfinite Mettapedia.GSLT.LooseRelationEquipment

universe uObj uStep u

namespace Semantics

variable {Object : Type uObj} {Step : Object → Object → Type uStep}
variable (semantics : Semantics.{uObj, uStep, u} Step)

/-- Local certificates include reconstruction, so elimination does not
silently strengthen an existence claim. -/
structure BoundaryReduction where
  normalize : {a b : Object} → Step a b → Step a b
  forward : ∀ {a b} (event : Step a b),
    Cell id id (semantics.step event) (semantics.step (normalize event))
  backward : ∀ {a b} (event : Step a b),
    Cell id id (semantics.step (normalize event)) (semantics.step event)

namespace BoundaryReduction

variable {semantics} (reduction : semantics.BoundaryReduction)

def route (reduction : semantics.BoundaryReduction) :
    {a b : Object} → Route Step a b → Route Step a b
  | _, _, .refl a => .refl a
  | _, _, .cons event rest => .cons (reduction.normalize event) (reduction.route rest)

/-- Local witness transports compose without discarding seam choices. -/
def forwardRoute (reduction : semantics.BoundaryReduction) :
    {a b : Object} → (path : Route Step a b) →
    semantics.Replacement path (reduction.route path)
  | _, _, .refl _ => Cell.id _
  | _, _, .cons event rest =>
      Cell.hcomp (reduction.forward event) (reduction.forwardRoute rest)

def backwardRoute (reduction : semantics.BoundaryReduction) :
    {a b : Object} → (path : Route Step a b) →
    semantics.Replacement (reduction.route path) path
  | _, _, .refl _ => Cell.id _
  | _, _, .cons event rest =>
      Cell.hcomp (reduction.backward event) (reduction.backwardRoute rest)

theorem supports_iff {a b : Object} (path : Route Step a b)
    (x : semantics.State a) (y : semantics.State b) :
    semantics.Supports path x y ↔ semantics.Supports (reduction.route path) x y :=
  ⟨semantics.supports_of_replacement (reduction.forwardRoute path),
    semantics.supports_of_replacement (reduction.backwardRoute path)⟩

/-- An arbitrary test of the two outer states is preserved. -/
theorem boundary_predicate_iff {a b : Object} (path : Route Step a b)
    (outside : semantics.State a → semantics.State b → Prop) :
    (∃ x y, semantics.Supports path x y ∧ outside x y) ↔
      (∃ x y, semantics.Supports (reduction.route path) x y ∧ outside x y) := by
  simp only [reduction.supports_iff path]

/-- The same local certificates work in every initial and final route. -/
theorem in_context_iff {a b c d : Object} (initial : Route Step a b)
    (middle : Route Step b c) (final : Route Step c d)
    (x : semantics.State a) (z : semantics.State d) :
    semantics.Supports ((initial.append middle).append final) x z ↔
      semantics.Supports ((initial.append (reduction.route middle)).append final) x z :=
  ⟨semantics.supports_of_replacement
      (semantics.replaceInContext initial (reduction.forwardRoute middle) final),
    semantics.supports_of_replacement
      (semantics.replaceInContext initial (reduction.backwardRoute middle) final)⟩

end BoundaryReduction
end Semantics
end Mettapedia.GSLT.RelationalRouteSemantics
