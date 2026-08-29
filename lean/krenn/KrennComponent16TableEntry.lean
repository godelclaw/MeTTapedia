import KrennAllCollapseAssembly
import KrennComponent16RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 16 occupies zero-based table slot 15. -/
theorem component16_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (15 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component16RootCommonZero.no_base_common_zero_on_component16
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component16_refutes_selected
