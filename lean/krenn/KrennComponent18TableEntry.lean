import KrennAllCollapseAssembly
import KrennComponent18RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 18 occupies zero-based table slot 17. -/
theorem component18_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (17 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component18RootCommonZero.no_base_common_zero_on_component18
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component18_refutes_selected
