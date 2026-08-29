import KrennAllCollapseAssembly
import KrennComponent39RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 39 occupies zero-based table slot 38. -/
theorem component39_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (38 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component39RootCommonZero.no_base_common_zero_on_component39
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component39_refutes_selected
