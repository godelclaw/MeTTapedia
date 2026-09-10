import Mettapedia.GraphTheory.FourColor.DisagreementComponentExchange

/-!
# Negative controls for unrestricted component copying and port potentials

Injectivity is proper edge colouring on a star. Copying the donor's whole
two-edge disagreement component onto the three-edge star fails at its
retained third edge. The second control records the nonzero Klein flux
at a proper degree-two port. Neither example is a least counterexample.
-/

namespace Mettapedia.GraphTheory.FourColor.ComponentExchangeControls

def recipient : Fin 3 → Color := ![(1, 0), (0, 1), (1, 1)]
def donor : Fin 2 → Color := ![(0, 1), (1, 1)]
def copied : Fin 3 → Color := ![(0, 1), (1, 1), (1, 1)]

/-- Both source colourings are proper and nonzero. The common two-edge
star is a single disagreement component. Copying it creates a collision
with the edge outside the common star. -/
theorem unchecked_copy_fails :
    Function.Injective recipient ∧ Function.Injective donor ∧
    (∀ i, recipient i ≠ 0) ∧ (∀ i, donor i ≠ 0) ∧
    (∀ i : Fin 2, recipient i.castSucc ≠ donor i) ∧
    (∀ i : Fin 2, copied i.castSucc = donor i) ∧
    copied 2 = recipient 2 ∧ ¬ Function.Injective copied := by decide

/-- Distinct incident colours at a degree-two port are not a conserved
Klein flow. A closed-map face-potential theorem needs a boundary repair
before it applies to a deletion colouring. -/
theorem degree_two_flux_ne_zero : ∀ a b : Color, a ≠ b → a + b ≠ 0 := by decide

/-- At a cubic vertex, normalize one proper nonzero colouring to the
identity permutation of the three colours. An edgewise choice between
that colouring and another proper colouring cannot give a third one.
This includes the three-cycle (branching disagreement) case. -/
theorem cubic_binary_mixing_rigid : ∀ p q : Equiv.Perm (Fin 3),
    (∀ i, q i = i ∨ q i = p i) → q = Equiv.refl _ ∨ q = p := by decide

end Mettapedia.GraphTheory.FourColor.ComponentExchangeControls
