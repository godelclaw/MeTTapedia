import KrennAllCollapseAssembly
import KrennComponent64RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 64 occupies zero-based table slot 63. -/
theorem component64_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (63 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component64RootCommonZero.no_base_common_zero_on_component64
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component64_refutes_selected
