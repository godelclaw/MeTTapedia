import KrennAllCollapseAssembly
import KrennComponent24RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 24 occupies zero-based table slot 23. -/
theorem component24_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (23 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component24RootCommonZero.no_base_common_zero_on_component24
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component24_refutes_selected
