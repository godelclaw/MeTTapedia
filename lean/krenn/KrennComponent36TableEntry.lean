import KrennAllCollapseAssembly
import KrennComponent36RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 36 occupies zero-based table slot 35. -/
theorem component36_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (35 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component36RootCommonZero.no_base_common_zero_on_component36
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component36_refutes_selected
