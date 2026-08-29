import KrennAllCollapseAssembly
import KrennComponent55RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 55 occupies zero-based table slot 54. -/
theorem component55_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (54 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component55RootCommonZero.no_base_common_zero_on_component55
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component55_refutes_selected
