import Mettapedia.GraphTheory.FourColor.PermutationFirstReturnRestriction

/-!
# Equal cyclic order on wires does not fix their full-boundary positions

The width-five geometric diagnostic has two surviving wires. Relative to
the first wire, the second is at position three on the inner boundary and
position two on the outer boundary. A matching of complete cyclic boundaries
cannot fix both. This module certifies that normalized matching obstruction;
the accompanying prism geometry is checked separately by the diagnostic.
-/

namespace Mettapedia.GraphTheory.FourColor.PersistentWireMatchingObstruction

def step : Equiv.Perm (Fin 5) := Equiv.addRight 1

/-- Commuting with successor and fixing one port fixes every cyclic position. -/
theorem no_full_matching :
    ¬ ∃ e : Fin 5 ≃ Fin 5, e 0 = 0 ∧ e 3 = 2 ∧
      ∀ i, e (step i) = step (e i) := by
  rintro ⟨e, h0, h3, hc⟩
  have h1 : e 1 = 1 := by simpa [step, h0] using hc 0
  have h2 : e 2 = 2 := by simpa [step, h1] using hc 1
  have h3' : e 3 = 3 := by simpa [step, h2] using hc 2
  have hfalse : (2 : Fin 5) = 3 := h3.symm.trans h3'
  exact (by decide : (2 : Fin 5) ≠ 3) hfalse

end Mettapedia.GraphTheory.FourColor.PersistentWireMatchingObstruction
