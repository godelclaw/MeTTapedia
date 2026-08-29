import KrennAllCollapseAssembly
import KrennComponent1TableEntry
import KrennComponent6TableEntry
import KrennComponent10TableEntry
import KrennComponent11TableEntry
import KrennComponent12TableEntry
import KrennComponent13TableEntry
import KrennComponent14TableEntry
import KrennComponent15TableEntry
import KrennComponent16TableEntry
import KrennComponent17TableEntry
import KrennComponent18TableEntry
import KrennComponent19TableEntry
import KrennComponent20TableEntry
import KrennComponent22TableEntry
import KrennComponent24TableEntry
import KrennComponent25TableEntry
import KrennComponent36TableEntry
import KrennComponent37TableEntry
import KrennComponent39TableEntry
import KrennComponent44TableEntry
import KrennComponent45TableEntry
import KrennComponent46RootCommonZero
import KrennComponent47TableEntry
import KrennComponent48TableEntry
import KrennComponent50TableEntry
import KrennComponent51TableEntry
import KrennComponent52TableEntry
import KrennComponent53TableEntry
import KrennComponent54TableEntry
import KrennComponent55TableEntry
import KrennComponent56TableEntry
import KrennComponent57RootCommonZero
import KrennComponent58TableEntry
import KrennComponent59TableEntry
import KrennComponent60RootCommonZero
import KrennComponent62TableEntry
import KrennComponent64TableEntry
import KrennComponent65TableEntry

/-! Concrete entries already available for the all-collapse assembly table. -/

namespace Krenn.FrozenCase0AllCollapseAssembly

open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- Component 46 supplies one checked entry of the finite all-collapse table. -/
theorem component46_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (45 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component46RootCommonZero.no_base_common_zero_on_component46
    full base selectedVanish

/-- Component 57 supplies a second checked entry of the finite all-collapse table. -/
theorem component57_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (56 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component57RootCommonZero.no_base_common_zero_on_component57
    full base selectedVanish

/-- Component 60 supplies a third checked entry of the finite all-collapse table. -/
theorem component60_refutes_selected
    {R : Type*} [Field R] [CharZero R] :
    RefutesSelectedComponent (R := R) (59 : Fin 67) := by
  intro full base selectedVanish
  exact Krenn.Component60RootCommonZero.no_base_common_zero_on_component60
    full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms Krenn.FrozenCase0AllCollapseAssembly.component1_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component6_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component10_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component11_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component12_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component13_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component14_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component15_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component16_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component17_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component18_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component19_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component20_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component22_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component24_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component25_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component36_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component37_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component39_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component44_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component45_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component46_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component47_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component48_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component50_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component51_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component52_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component53_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component54_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component55_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component56_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component57_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component58_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component59_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component60_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component62_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component64_refutes_selected
#print axioms Krenn.FrozenCase0AllCollapseAssembly.component65_refutes_selected
