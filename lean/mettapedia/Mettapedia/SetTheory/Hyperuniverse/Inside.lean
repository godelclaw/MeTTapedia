import Mettapedia.SetTheory.AntiFoundation.Core
import Mettapedia.SetTheory.Hyperuniverse.Membership
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Hyperset

/-!
# The closed-set limit as a graph of hypersets

Pointing the membership graph of the limit at a point and keeping the nodes
reachable from it determines a hyperset. A hyperset belongs to that picture
exactly when it is the picture of a member.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Hyperuniverse

open Mettapedia.SetTheory.AntiFoundation
open Mettapedia.TypeTheory.MaterialSets.Hypersets

/-- The hyperset pictured by the membership graph at `y`. Its nodes are the
points reachable from `y`, and its edge is membership. -/
def decorateN (y : N) : HSet.{0} :=
  HSet.decorate (memChild member) y

/-- The members of the picture of `y` are the pictures of the members of `y`. -/
theorem decorateN_mem {y : N} {z : HSet.{0}} :
    z ∈ decorateN y ↔ ∃ x, member x y ∧ z = decorateN x := by
  constructor
  · intro hz
    rcases HSet.mem_decorate.mp hz with ⟨x, hx, he⟩
    exact ⟨x, hx, he.symm⟩
  · intro ⟨x, hx, he⟩
    exact he ▸ HSet.decorate_mem_decorate hx

example : decorateN emptySet ∈ decorateN univSet :=
  HSet.decorate_mem_decorate (member_univ emptySet)

example : ¬ decorateN univSet ∈ decorateN emptySet := by
  intro h
  rcases decorateN_mem.mp h with ⟨x, hx, _⟩
  exact member_empty x hx

example : decorateN emptySet ≠ decorateN univSet := by
  intro h
  have hmem : decorateN emptySet ∈ decorateN univSet :=
    HSet.decorate_mem_decorate (member_univ emptySet)
  rw [← h] at hmem
  rcases decorateN_mem.mp hmem with ⟨x, hx, _⟩
  exact member_empty x hx

end Mettapedia.SetTheory.Hyperuniverse
