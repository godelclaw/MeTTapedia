import Mathlib.Data.Finset.Card

/-!
# Compact observations for recolouring the end of a short boundary arc

For a proper three-vertex arc, the forbidden-colour set has size two
exactly when its endpoints have the same colour. Thus the set, its arc
length, and the old endpoint colour determine the forbidden colours after
changing that endpoint. A two-vertex arc has no repeated endpoint colour.
The palette and the replacement colour are unrestricted.
-/

namespace SimpleGraph.BoundaryEndpointTransport

variable {A : Type*} [DecidableEq A]

/-- The geometry determines whether removing the old endpoint leaves
another occurrence of its colour in the same arc. -/
def change (three : Bool) (old new : A) (forbidden : Finset A) : Finset A :=
  insert new (if three = true ∧ forbidden.card = 2 then forbidden else forbidden.erase old)

theorem two (x old new : A) (hne : x ≠ old) :
    change false old new {x,old} = {x,new} := by
  ext z
  simp [change]
  aesop

theorem three (x y old new : A) (hxy : x ≠ y) (hyo : y ≠ old) :
    change true old new {x,y,old} = {x,y,new} := by
  by_cases hxo : x = old
  · subst x
    ext z
    simp [change]
    aesop
  · have hc : ({x,y,old} : Finset A).card = 3 := by
      simp [hxo, hxy, hyo]
    ext z
    simp [change, hc]
    aesop

end SimpleGraph.BoundaryEndpointTransport
