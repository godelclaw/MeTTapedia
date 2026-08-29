import KrennAllCollapseAssembly
import KrennComponent10RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 10 occupies zero-based table slot 9. -/
theorem component10_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (9 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component10RootCommonZero.no_base_common_zero_on_component10
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component10_refutes_selected
