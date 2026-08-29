import KrennAllCollapseAssembly
import KrennComponent59RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 59 occupies zero-based table slot 58. -/
theorem component59_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (58 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component59RootCommonZero.no_base_common_zero_on_component59
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component59_refutes_selected
