import KrennAllCollapseAssembly
import KrennComponent11RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 11 occupies zero-based table slot 10. -/
theorem component11_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (10 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component11RootCommonZero.no_base_common_zero_on_component11
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component11_refutes_selected
