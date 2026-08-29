import KrennAllCollapseAssembly
import KrennComponent62RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 62 occupies zero-based table slot 61. -/
theorem component62_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (61 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component62RootCommonZero.no_base_common_zero_on_component62
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component62_refutes_selected
