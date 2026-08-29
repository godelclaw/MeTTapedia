import KrennAllCollapseAssembly
import KrennComponent45RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 45 occupies zero-based table slot 44. -/
theorem component45_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (44 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component45RootCommonZero.no_base_common_zero_on_component45
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component45_refutes_selected
