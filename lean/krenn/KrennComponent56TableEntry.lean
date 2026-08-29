import KrennAllCollapseAssembly
import KrennComponent56RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 56 occupies zero-based table slot 55. -/
theorem component56_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (55 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component56RootCommonZero.no_base_common_zero_on_component56
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component56_refutes_selected
