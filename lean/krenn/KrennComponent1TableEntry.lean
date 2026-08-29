import KrennAllCollapseAssembly
import KrennComponent1RootCommonZero

/-!
The concrete all-collapse table entry for external component 1.

This small module is deliberately separate from the growing aggregate table:
the component root connector is serially kernel-audited first, then this
wrapper attaches exactly that checked contradiction to index `0 : Fin 67`.
-/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 1 is zero-based component index 0 in the 67-entry
all-collapse table. -/
theorem component1_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (0 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component1RootCommonZero.no_base_common_zero_on_component1
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component1_refutes_selected
