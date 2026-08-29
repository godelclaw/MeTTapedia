import KrennAllCollapseAssembly
import KrennComponent53RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 53 occupies zero-based table slot 52. -/
theorem component53_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (52 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component53RootCommonZero.no_base_common_zero_on_component53
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component53_refutes_selected
