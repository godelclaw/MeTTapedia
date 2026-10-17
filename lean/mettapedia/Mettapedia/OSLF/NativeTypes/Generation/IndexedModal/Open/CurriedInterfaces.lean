import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Joined
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeAdequacy

/-!
# Local focus classifiers and ambient curried classifiers

A focus beneath local binders is a raw term in the extended context.
As a value in the ambient native model it is a function over that prefix.
The two interfaces retain the same indices, relies, target and provenance;
only their classifier carrier changes. Empty-prefix interfaces coincide.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.CurriedInterfaces

open Mettapedia.OSLF.NativeTypes.Modal
open Mettapedia.OSLF.Binding IntrinsicScopedConditionalPresheaf
open CurriedBindingLanguage

variable (installed : Pipeline.Installed)

abbrev header (index : Fin installed.headers.length) :=
  installed.operational.modal[installed.headers[index].origin]

def interface (index : Fin installed.headers.length) :
    Interface (NativeSignature.Carrier (NativeCubeProfile.language installed.operational)) :=
  { installed.interfaces index with focus := (header installed index).focusArgument }

@[simp] theorem indices (index : Fin installed.headers.length) :
    (interface installed index).indices = (installed.interfaces index).indices := rfl

@[simp] theorem relies (index : Fin installed.headers.length) :
    (interface installed index).relies = (installed.interfaces index).relies := rfl

@[simp] theorem target (index : Fin installed.headers.length) :
    (interface installed index).target = (installed.interfaces index).target := rfl

@[simp] theorem sort (index : Fin installed.headers.length) :
    (interface installed index).resultSort = (installed.interfaces index).resultSort := rfl

@[simp] theorem parameter_context (index : Fin installed.headers.length) :
    parameters (D := Pipeline.classifierSignature installed.operational) (interface installed index) =
      parameters (D := Pipeline.classifierSignature installed.operational) (installed.interfaces index) := rfl

@[simp] theorem parameter_arity (index : Fin installed.headers.length) :
    arity (D := Pipeline.classifierSignature installed.operational) (interface installed index) =
      arity (D := Pipeline.classifierSignature installed.operational) (installed.interfaces index) := rfl

/-- No global change is made to the existing raw/local interface. -/
theorem empty_prefix (index : Fin installed.headers.length)
    (empty : (header installed index).focusBinders = []) :
    interface installed index = installed.interfaces index := by
  have raw : (installed.interfaces index).focus = (header installed index).focus := by
    rw [installed.interfaces_source]
    rfl
  unfold interface NativeModalHeaders.Header.focusArgument
  rw [empty]
  simp only [List.reverse_nil, List.foldr_nil]
  cases original : installed.interfaces index
  simp only [original] at raw ⊢
  rw [raw]

/-- The ambient classifier's focus carrier is the existing, earned function
object for the generated local binder prefix. -/
theorem focus_meaning (index : Fin installed.headers.length) :
    meaning (interface installed index).focus =
      meaning ((header installed index).focusBinders.reverse.foldr
        NativeSignature.Carrier.function (header installed index).focus) := rfl

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.CurriedInterfaces
