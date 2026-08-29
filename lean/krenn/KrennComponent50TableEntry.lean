import KrennAllCollapseAssembly
import KrennComponent50RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 50 occupies zero-based table slot 49. -/
theorem component50_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (49 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component50RootCommonZero.no_base_common_zero_on_component50
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component50_refutes_selected
