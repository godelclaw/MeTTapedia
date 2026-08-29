import KrennAllCollapseAssembly
import KrennComponent44RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 44 occupies zero-based table slot 43. -/
theorem component44_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (43 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component44RootCommonZero.no_base_common_zero_on_component44
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component44_refutes_selected
