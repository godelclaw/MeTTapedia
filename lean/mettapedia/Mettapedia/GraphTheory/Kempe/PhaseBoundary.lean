import Mettapedia.GraphTheory.Kempe.RouteProjection

/-!
# Boundary normal form from retained bichromatic routes

Routes from indexed roots to the active boundary vertices suffice to
describe every endpoint of a fixed-pair phase. Each root contributes one
Boolean choice, shared by every port reached from it. The routes need not
describe whole components, and the graph and phase lengths are unrestricted.
-/

namespace SimpleGraph.KempePhaseBoundary

variable {V P I α : Type*} {G : SimpleGraph V} [DecidableEq α]

/-- Proper partial transpositions agree on whether either endpoint of an
initially bichromatic route changes. -/
theorem endpoint (C D : G.Coloring α) (a b : α)
    (pair : ∀ v, D v = C v ∨ D v = Equiv.swap a b (C v))
    (ports : P → V) (roots : I → V) (label : P → I)
    (routes : ∀ i, (C (ports i) = a ∨ C (ports i) = b) →
      ∃ p : G.Walk (roots (label i)) (ports i),
        ∀ x ∈ p.support, C x = a ∨ C x = b) :
    ∃ bits : I → Bool, ∀ i, D (ports i) =
      if bits (label i) then Equiv.swap a b (C (ports i)) else C (ports i) := by
  classical
  refine ⟨fun k => decide (D (roots k) ≠ C (roots k)), ?_⟩
  intro i
  by_cases active : C (ports i) = a ∨ C (ports i) = b
  · obtain ⟨p, hp⟩ := routes i active
    have same : D (roots (label i)) ≠ C (roots (label i)) ↔
        D (ports i) ≠ C (ports i) :=
      ⟨KempeRouteProjection.changed_along_walk C D a b pair p hp,
       KempeRouteProjection.changed_along_walk C D a b pair p.reverse
         (fun x hx => hp x (by simpa using hx))⟩
    by_cases changed : D (roots (label i)) ≠ C (roots (label i))
    · simpa [changed] using
        (pair (ports i)).resolve_left (same.mp changed)
    · have fixed : D (ports i) = C (ports i) := by
        by_contra h
        exact changed (same.mpr h)
      simpa [changed] using fixed
  · have ha : C (ports i) ≠ a := fun h => active (Or.inl h)
    have hb : C (ports i) ≠ b := fun h => active (Or.inr h)
    have fixed := pair (ports i)
    simp only [Equiv.swap_apply_of_ne_of_ne ha hb, or_self] at fixed
    simp only [Equiv.swap_apply_of_ne_of_ne ha hb, ite_self]
    exact fixed

/-- Any number of switches of the selected pair has the same finite
boundary normal form. This does not apply after a change of colour pair. -/
theorem phase (C D : G.Coloring α) (a b : α)
    (ports : P → V) (roots : I → V) (label : P → I)
    (routes : ∀ i, (C (ports i) = a ∨ C (ports i) = b) →
      ∃ p : G.Walk (roots (label i)) (ports i),
        ∀ x ∈ p.support, C x = a ∨ C x = b)
    (history : Relation.ReflTransGen (KempePairHistory.Step a b) C D) :
    ∃ bits : I → Bool, ∀ i, D (ports i) =
      if bits (label i) then Equiv.swap a b (C (ports i)) else C (ports i) :=
  endpoint C D a b (KempePairHistory.pointwise history) ports roots label routes

end SimpleGraph.KempePhaseBoundary
