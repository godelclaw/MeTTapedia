import Mettapedia.TypeTheory.CwfYonedaComparisonControls
import Mettapedia.TypeTheory.CwfYonedaProductSectionComparison

/-!
# Empty present arguments and complete future functions

A varying argument family has no present argument at zero, but admits an
argument at one. The native present function values therefore agree at
zero, while their complete future sections remain different. A separate
everywhere-empty family has one complete function section, including all
future contexts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfYonedaEmptyProductControls

open CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open CwfYonedaComparisonControls (represented products context)

abbrev domain : represented.Ty context := ⟨fun n : Nat => Fin n⟩
abbrev codomain : represented.Ty (represented.ext context domain) :=
  ⟨fun point : Σ n : Nat, Fin n => Fin (point.1 + point.2.val + 1)⟩

def zeroFunction : represented.Tm context (products.operations.pi domain codomain) :=
  ⟨fun _ _ => ⟨0, Nat.zero_lt_succ _⟩⟩

def varyingFunction : represented.Tm context (products.operations.pi domain codomain) :=
  ⟨fun n argument => ⟨n, Nat.lt_succ_of_le (Nat.le_add_right n argument.val)⟩⟩

abbrev unitContext : represented.Ctx := ⟨PUnit⟩
def zeroEnvironment : represented.Sub unitContext context := ⟨fun _ => 0⟩
abbrev zeroPoint : (CwfYoneda.contextFace represented context).Elements :=
  ⟨op (CwfYoneda.context represented unitContext), zeroEnvironment⟩

noncomputable def zeroNative := CwfYoneda.interpretFunction represented products zeroFunction
noncomputable def varyingNative := CwfYoneda.interpretFunction represented products varyingFunction

theorem native_present_values_agree : zeroNative.val zeroPoint = varyingNative.val zeroPoint := by
  have zeroRead := Functor.sections_ext_iff.mp
    (CwfYoneda.productFamilyForward_section represented products domain codomain zeroFunction) zeroPoint
  have varyingRead := Functor.sections_ext_iff.mp
    (CwfYoneda.productFamilyForward_section represented products domain codomain varyingFunction) zeroPoint
  have originalEqual : (CwfYoneda.interpretTerm represented zeroFunction).val zeroPoint =
      (CwfYoneda.interpretTerm represented varyingFunction).val zeroPoint := by
    apply Subtype.ext
    apply congrArg ULift.up
    funext point
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext argument
      exact Fin.elim0 argument
  exact zeroRead.symm.trans ((congrArg
    ((CwfYoneda.productFamilyForward represented products domain codomain).app zeroPoint)
    originalEqual).trans varyingRead)

theorem complete_native_sections_differ : zeroNative ≠ varyingNative := by
  intro equal
  have originalEqual := (CwfYoneda.productTermSectionEquiv represented products domain codomain).injective equal
  have values := congrArg (fun function : represented.Tm context
    (products.operations.pi domain codomain) => (function.down 1 ⟨0, by decide⟩).val) originalEqual
  exact (by decide : (0 : Nat) ≠ 1) values

theorem an_actual_future_argument : Nonempty (domain.down 1) := ⟨⟨0, by decide⟩⟩
theorem no_present_argument : IsEmpty (domain.down 0) := inferInstance

abbrev everywhereEmpty : represented.Ty unitContext := ⟨fun _ : PUnit => PEmpty⟩
abbrev emptyCodomain : represented.Ty (represented.ext unitContext everywhereEmpty) :=
  ⟨fun _ => PEmpty⟩

theorem complete_empty_native_functions_unique
    (first second : (CwfYoneda.representedProductFamily represented everywhereEmpty emptyCodomain).sections) :
    first = second := by
  apply (CwfYoneda.productTermSectionEquiv represented products everywhereEmpty emptyCodomain).symm.injective
  apply ULift.ext
  funext point argument
  exact PEmpty.elim argument

end Mettapedia.TypeTheory.CwfYonedaEmptyProductControls
