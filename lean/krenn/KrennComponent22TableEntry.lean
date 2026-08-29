import KrennAllCollapseAssembly
import KrennComponent22RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 22 occupies zero-based table slot 21. -/
theorem component22_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (21 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component22RootCommonZero.no_base_common_zero_on_component22
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component22_refutes_selected
