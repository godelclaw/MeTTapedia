import Mettapedia.OSLF.NativeTypes.Instances.Local.Driver
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver
import Mettapedia.OSLF.NativeTypes.Instances.Local.CursorBackend
import Mettapedia.OSLF.NativeTypes.Decision.Profiles
import Mettapedia.OSLF.NativeTypes.Runtime.Interface

open Mettapedia.OSLF.Framework

/-!
# Installed authored local and original machine execution

The generated driver retains its actual authored presentation. The attached
runtime consumes local occurrence cursors and finite constructor tests with
one total work account. Its native predicates agree with the generated
structural readouts for all sources and all admitted configurations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime.Local

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.Runtime

def localRuntime (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr)
    (foundation : generated.plan.complete = true) (equationFree : generated.plan.equations = [])
    (generic : GeneralExecutionTotalAdmission.checkGeneric generated.plan = true)
    (mask : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool) :
    Engine (Mettapedia.OSLF.NativeTypes.Instances.Local.Driver.driver generated bound expected foundation equationFree generic mask) where
  cursor := Mettapedia.OSLF.NativeTypes.Instances.Local.CursorBackend.cursorBackend generated.plan bound expected
    rfl foundation equationFree generic
  leaves leaf := Mettapedia.OSLF.NativeTypes.Decision.Profiles.fixedTest
    (Mettapedia.OSLF.NativeTypes.Instances.Local.Driver.tests generated bound expected equationFree mask leaf) 0
    (fun _ => Nat.le_refl _)
  leaf_meaning _ := rfl

def installedLocal (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr)
    (foundation : generated.plan.complete = true) (equationFree : generated.plan.equations = [])
    (generic : GeneralExecutionTotalAdmission.checkGeneric generated.plan = true)
    (mask : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool) : Installed :=
  ⟨Mettapedia.OSLF.NativeTypes.Instances.Local.Driver.driver generated bound expected foundation equationFree generic mask,
    localRuntime generated bound expected foundation equationFree generic mask⟩

def partrecRuntime (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr) :
    Engine (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.driver configuration bound) where
  cursor := Mettapedia.OSLF.NativeTypes.Instances.Local.CursorBackend.cursorBackend Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan bound
    (.base "Cfg") rfl Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_foundation
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_equations Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_generic
  leaves leaf := Mettapedia.OSLF.NativeTypes.Decision.Profiles.fixedTest
    (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.tests configuration bound leaf) 0 (fun _ => Nat.le_refl _)
  leaf_meaning _ := rfl

def partrec (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr) : Installed :=
  ⟨Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.driver configuration bound, partrecRuntime configuration bound⟩

theorem local_leaf_meaning (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr)
    (foundation : generated.plan.complete = true) (equationFree : generated.plan.equations = [])
    (generic : GeneralExecutionTotalAdmission.checkGeneric generated.plan = true)
    (mask : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool)
    (leaf : Mettapedia.OSLF.NativeTypes.Instances.Local.Driver.Leaf generated expected) (source : Pattern) :
    ((localRuntime generated bound expected foundation equationFree generic mask).leaves leaf).predicate source ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode
        (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanModel generated mask bound)
        leaf.index (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanInputs
          generated bound leaf.index leaf.accepts)).meaning source :=
  Mettapedia.OSLF.NativeTypes.Instances.Local.Driver.native_structural_meaning generated bound expected equationFree mask leaf source

theorem partrec_leaf_meaning (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    (leaf : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Leaf) (source : Pattern) :
    ((partrecRuntime configuration bound).leaves leaf).predicate source ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode
        (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanModel
          (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.generated configuration) Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.syntaxMask bound)
        leaf.val (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanInputs
          (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.generated configuration) bound leaf.val (fun _ _ => true))).meaning source :=
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.native_structural_meaning configuration bound leaf source

end Mettapedia.OSLF.NativeTypes.Runtime.Local
