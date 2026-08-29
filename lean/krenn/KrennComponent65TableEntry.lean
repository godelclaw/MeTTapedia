import KrennAllCollapseAssembly
import KrennComponent65RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 65 occupies zero-based table slot 64. -/
theorem component65_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (64 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component65RootCommonZero.no_base_common_zero_on_component65
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component65_refutes_selected
