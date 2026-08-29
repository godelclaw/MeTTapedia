import KrennAllCollapseAssembly
import KrennComponent58RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 58 occupies zero-based table slot 57. -/
theorem component58_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (57 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component58RootCommonZero.no_base_common_zero_on_component58
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component58_refutes_selected
