import KrennAllCollapseAssembly
import KrennComponent13RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 13 occupies zero-based table slot 12. -/
theorem component13_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (12 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component13RootCommonZero.no_base_common_zero_on_component13
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component13_refutes_selected
