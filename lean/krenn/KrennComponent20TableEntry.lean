import KrennAllCollapseAssembly
import KrennComponent20RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 20 occupies zero-based table slot 19. -/
theorem component20_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (19 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component20RootCommonZero.no_base_common_zero_on_component20
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component20_refutes_selected
