import KrennAllCollapseAssembly
import KrennComponent48RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 48 occupies zero-based table slot 47. -/
theorem component48_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (47 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component48RootCommonZero.no_base_common_zero_on_component48
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component48_refutes_selected
