import KrennAllCollapseAssembly
import KrennComponent54RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 54 occupies zero-based table slot 53. -/
theorem component54_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (53 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component54RootCommonZero.no_base_common_zero_on_component54
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component54_refutes_selected
