import Mettapedia.OSLF.NativeTypes.Modal.NativeScopedParameterTypes
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission

/-!
# Mixed-sort local binders distinguish dependency and function order

Scoped assignment bodies use innermost-first dependency contexts. Native
function parameters use outermost-first domains. Two unequal sorts expose
the distinction: the generated function header types the actual nested
binder body, while the unreversed header is rejected by independent typing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeScopedParameterOrderControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Generation.NativeSignature NativeScopedParameterTypes

def language : LanguageDef where
  name := "MixedScopedParameters"
  types := [{ name := "Outer" }, { name := "Inner" }, { name := "Result" }]
  terms :=
    [{ label := "Join", category := "Result",
       params := [.simple "outer" (.base "Outer"), .simple "inner" (.base "Inner")],
       syntaxPattern := [] },
     { label := "Bind", category := "Result",
       params := [.abstractionNamed (some "outer") "body"
         (.arrow (.base "Outer") (.arrow (.base "Inner") (.base "Result")))],
       syntaxPattern := [] }]
  equations := []
  rewrites := []

def outer : Carrier language := .sort ⟨0, by decide⟩
def inner : Carrier language := .sort ⟨1, by decide⟩
def result : Carrier language := .sort ⟨2, by decide⟩

def body : Pattern := .apply "Join" [.bvar 1, .bvar 0]
def function : Pattern := .lambda none (.lambda none body)
def generated : Carrier language := functionCarrier [inner, outer] result
def wrong : TypeExpr := .arrow (.base "Inner") (.arrow (.base "Outer") (.base "Result"))

theorem original_parameter_context :
    Generation.BindingSemanticAdmission.parameterMeaning? language.terms[1].params[0] =
      some (["Inner", "Outer"], "Result") := by decide

theorem generated_header : generated.source =
    .arrow (.base "Outer") (.arrow (.base "Inner") (.base "Result")) := rfl

theorem body_typed : HasType language FreeTypeContext.empty [.base "Inner", .base "Outer"]
    body (.base "Result") := checkHasType_sound (by decide +kernel)

theorem generated_function_typed : HasType language FreeTypeContext.empty [] function generated.source :=
  checkHasType_sound (by decide +kernel)

theorem unreversed_header_refuted : ¬ HasType language FreeTypeContext.empty [] function wrong := by
  intro typed
  have checked := (checkHasType_eq_true_iff (by rfl : isObjectPattern function = true)).mpr typed
  have refused : checkHasType language FreeTypeContext.empty [] function wrong = false := by decide +kernel
  rw [refused] at checked
  cases checked

#guard generated.source == .arrow (.base "Outer") (.arrow (.base "Inner") (.base "Result"))
#guard checkHasType language FreeTypeContext.empty [] function generated.source
#guard !(checkHasType language FreeTypeContext.empty [] function wrong)

end Mettapedia.OSLF.NativeTypes.Modal.NativeScopedParameterOrderControls
