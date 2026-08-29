import KrennAllCollapseAssembly
import KrennComponent25RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 25 occupies zero-based table slot 24. -/
theorem component25_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (24 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component25RootCommonZero.no_base_common_zero_on_component25
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component25_refutes_selected
