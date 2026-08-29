import KrennCollapseComponentContainmentDataDefs

/-!
Indexing gate for the bridge from the externally numbered C6 minimal-prime
components to the zero-based Lean connector table.

The audited external component numbered 46 is row 45 of the `Fin 67` table.
Its normalized generators are recorded here as a finite kernel-checked
equality, so a future full-system bridge cannot silently use row 46 instead.
The source minimal-prime transcript has SHA-256
`f6228b8a39db80d8450b47586ab1599b1f4c429f56279ab430d4c4509db1de7f`.
-/

namespace Krenn.CollapseComponent46IndexGate

open Krenn.CollapseComponentContainmentData

/-- Normalized generator vocabulary of external (one-based) component 46. -/
def external46Generators : List (Fin 78) :=
  [24, 18, 73, 53, 47, 48, 25, 26, 20, 0, 1, 4, 5, 7, 77, 8, 28, 9, 10]

/-- The external component-46 generator list is Lean row 45, not row 46. -/
theorem external46_is_zero_based_45 :
    componentGenerators (45 : Fin 67) = external46Generators := by
  decide

/-- A direct guard against the one-based/zero-based off-by-one error. -/
theorem external46_is_not_zero_based_46 :
    componentGenerators (46 : Fin 67) ≠ external46Generators := by
  decide

end Krenn.CollapseComponent46IndexGate

#print axioms Krenn.CollapseComponent46IndexGate.external46_is_zero_based_45
#print axioms Krenn.CollapseComponent46IndexGate.external46_is_not_zero_based_46
