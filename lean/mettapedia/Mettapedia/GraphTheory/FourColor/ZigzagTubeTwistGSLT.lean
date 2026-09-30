import Mettapedia.GraphTheory.FourColor.ZigzagTubeTwistReduction
import Mettapedia.GraphTheory.FourColor.ZigzagTubeBoundaryGSLT

/-!
# Directed tube reconstruction inside GSLT routes

The cyclically reattached shorter tube supplies actual colouring witnesses
for the longer tube. The existing operational semantics composes this cell
with arbitrary prefix and suffix routes, retaining both seam choices.
This is directed reconstruction, not a two-way boundary normalization or
an equality of witness counts.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagTubeTwistGSLT

open Mettapedia.GSLT.Ultrainfinite Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.RelationalRouteSemantics
open ZigzagRing OpenTangleWitnessComposition ZigzagTubeBoundaryGSLT

noncomputable section
variable (k : ℕ) [NeZero k]

def reconstruction (n : ℕ) :
    Cell id id (colourRelation (twistedTube k n)) (colourRelation (tube k (n + 2)).data) where
  map := fun {x y} witness => Classical.choice <|
    (nonempty_colourRelation_iff _ x y).mpr <|
      twistedTube_reconstruct k n x y ⟨witness.val, witness.property⟩

def shortEvent (n : ℕ) : Event ⟨k⟩ ⟨k⟩ :=
  .piece ⟨(tube k n).V, (tube k n).I, twistedTube k n⟩

def longEvent (n : ℕ) : Event ⟨k⟩ ⟨k⟩ := .piece (tube k (n + 2))

def shortRoute (n : ℕ) : Route Event ⟨k⟩ ⟨k⟩ := .cons (shortEvent k n) (.refl _)

def longRoute (n : ℕ) : Route Event ⟨k⟩ ⟨k⟩ := .cons (longEvent k n) (.refl _)

def localReplacement (n : ℕ) : colouring.Replacement (shortRoute k n) (longRoute k n) :=
  Cell.hcomp (reconstruction k n) (Cell.id _)

/-- One shared interface assignment is kept at each end of the replacement. -/
def inContext {a b : Interface} (initial : Route Event a ⟨k⟩)
    (n : ℕ) (final : Route Event ⟨k⟩ b) :
    colouring.Replacement ((initial.append (shortRoute k n)).append final)
      ((initial.append (longRoute k n)).append final) :=
  colouring.replaceInContext initial (localReplacement k n) final

theorem supports_in_context {a b : Interface} (initial : Route Event a ⟨k⟩)
    (n : ℕ) (final : Route Event ⟨k⟩ b) (x : colouring.State a) (y : colouring.State b) :
    colouring.Supports ((initial.append (shortRoute k n)).append final) x y →
      colouring.Supports ((initial.append (longRoute k n)).append final) x y :=
  colouring.supports_of_replacement (inContext k initial n final)

theorem boundary_predicate {a b : Interface} (initial : Route Event a ⟨k⟩)
    (n : ℕ) (final : Route Event ⟨k⟩ b)
    (outside : colouring.State a → colouring.State b → Prop) :
    (∃ x y, colouring.Supports ((initial.append (shortRoute k n)).append final) x y ∧ outside x y) →
      ∃ x y, colouring.Supports ((initial.append (longRoute k n)).append final) x y ∧ outside x y := by
  rintro ⟨x, y, h, hx⟩
  exact ⟨x, y, supports_in_context k initial n final x y h, hx⟩

end
end Mettapedia.GraphTheory.FourColor.ZigzagTubeTwistGSLT
