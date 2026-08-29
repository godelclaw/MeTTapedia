import KrennAllCollapseAssembly
import KrennComponent6RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 6 occupies zero-based table slot 5. -/
theorem component6_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (5 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component6RootCommonZero.no_base_common_zero_on_component6
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component6_refutes_selected
