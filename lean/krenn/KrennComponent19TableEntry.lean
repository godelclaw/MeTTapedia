import KrennAllCollapseAssembly
import KrennComponent19RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 19 occupies zero-based table slot 18. -/
theorem component19_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (18 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component19RootCommonZero.no_base_common_zero_on_component19
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component19_refutes_selected
