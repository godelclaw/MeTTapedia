import KrennAllCollapseAssembly
import KrennComponent15RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 15 occupies zero-based table slot 14. -/
theorem component15_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (14 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component15RootCommonZero.no_base_common_zero_on_component15
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component15_refutes_selected
