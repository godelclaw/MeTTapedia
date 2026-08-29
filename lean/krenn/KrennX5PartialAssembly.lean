import KrennX5ResidualDispatch
import KrennX5LegacyDispatch

/-!
Assembly of the X5 physical-support connector with the currently typed finite
refutation tables.

The only hypothesis of the final theorem is explicit finite coverage of the
336 representative ordinals.  As migrations are added to the generated
historical table, this interface does not change.
-/

namespace Krenn.X5PartialAssembly

open MonochromaticQuantumGraph
open Krenn.X5SupportConnector

/-- A representative is covered when it occurs in either the strict residual
registry or the currently migrated historical registry. -/
def Covered (representative : Fin 336) : Prop :=
  (∃ index, representative =
      (Krenn.X5ResidualDispatch.residualRepresentatives index).ordinal) ∨
  (∃ index, representative =
      (Krenn.X5LegacyDispatch.migratedRepresentatives index).ordinal)

theorem refutes_of_covered (representative : Fin 336)
    (W : WeightsN 6 3 ℂ) (hEq : EqSystemN 6 3 W)
    (hNormalized : NormalizedRepresentative representative W)
    (covered : Covered representative) : False := by
  rcases covered with ⟨index, rfl⟩ | ⟨index, rfl⟩
  · exact (Krenn.X5ResidualDispatch.residualRepresentatives index).impossible
      W hEq hNormalized
  · exact (Krenn.X5LegacyDispatch.migratedRepresentatives index).impossible
      W hEq hNormalized

/-- Once all 336 finite representatives occur in one of the typed registries,
no official witness can have physical support exactly
`{01,02,03,04,15}`. -/
theorem noPhysicalX5Support_of_coverage
    (coverage : ∀ representative : Fin 336, Covered representative) :
    ¬ ∃ W : WeightsN 6 3 ℂ,
      EqSystemN 6 3 W ∧ PhysicalX5Support W := by
  rintro ⟨W, hEq, support⟩
  obtain ⟨representative, _leaf, _colour, normalized, _action,
      normalizedSystem, normalizedCase⟩ :=
    support.exists_normalized_representative W hEq
  exact refutes_of_covered representative normalized normalizedSystem
    normalizedCase (coverage representative)

#print axioms Krenn.X5PartialAssembly.refutes_of_covered
#print axioms Krenn.X5PartialAssembly.noPhysicalX5Support_of_coverage

end Krenn.X5PartialAssembly
