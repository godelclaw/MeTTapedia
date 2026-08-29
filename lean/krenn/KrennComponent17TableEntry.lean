import KrennAllCollapseAssembly
import KrennComponent17RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 17 occupies zero-based table slot 16. -/
theorem component17_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (16 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component17RootCommonZero.no_base_common_zero_on_component17
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component17_refutes_selected
