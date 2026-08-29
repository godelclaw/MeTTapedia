import KrennAllCollapseAssembly
import KrennComponent12RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 12 occupies zero-based table slot 11. -/
theorem component12_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (11 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component12RootCommonZero.no_base_common_zero_on_component12
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component12_refutes_selected
