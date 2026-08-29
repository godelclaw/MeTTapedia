import KrennAllCollapseAssembly
import KrennComponent14RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 14 occupies zero-based table slot 13. -/
theorem component14_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (13 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component14RootCommonZero.no_base_common_zero_on_component14
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component14_refutes_selected
