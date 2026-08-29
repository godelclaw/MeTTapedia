import KrennAllCollapseAssembly
import KrennComponent51RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 51 occupies zero-based table slot 50. -/
theorem component51_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (50 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component51RootCommonZero.no_base_common_zero_on_component51
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component51_refutes_selected
