import KrennAllCollapseAssembly
import KrennComponent47RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 47 occupies zero-based table slot 46. -/
theorem component47_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (46 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component47RootCommonZero.no_base_common_zero_on_component47
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component47_refutes_selected
