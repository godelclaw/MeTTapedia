import KrennAllCollapseAssembly
import KrennComponent37RootCommonZero

/-! A provenance-bound concrete entry in the all-collapse table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- External component 37 occupies zero-based table slot 36. -/
theorem component37_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (36 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component37RootCommonZero.no_base_common_zero_on_component37
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component37_refutes_selected
