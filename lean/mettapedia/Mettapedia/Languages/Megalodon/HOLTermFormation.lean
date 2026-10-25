import Mettapedia.Languages.Megalodon.HOLTermEncoding
import Mettapedia.Languages.Megalodon.HenkinTermSubstitution

/-!
# Structural native readings of typed HOL constructors

Application, implication and binders retain their literal native shape after
the full equality/connective encoding. These equations expose the actual
annotation and support checks used by proof compilation. Renaming preserves
the corresponding native variable shift.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLTermFormation

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation HOLTermEncoding

variable {environment : Environment} {gamma : Ctx Base} {type domain result : Ty Base}

theorem native_eq_of_erase (source : Term (Constant environment) gamma type) {output : Tm}
    (erased : erase (encode source) = some output) : native source = output :=
  Option.some.inj ((native_erased source).symm.trans erased)

@[simp] theorem native_supported (source : Term (Constant environment) gamma type) :
    supported (native source) = true :=
  supported_of_erase (encode source) (native_erased source)

@[simp] theorem native_app (function : Term (Constant environment) gamma (domain ⇒ result))
    (argument : Term (Constant environment) gamma domain) :
    native (.app function argument) = .app (native function) (native argument) := by
  apply native_eq_of_erase
  change erase (.app (encode function) (encode argument)) = _
  simp [erase, native_erased]

@[simp] theorem native_imp (left right : Formula (Constant environment) gamma) :
    native (.imp left right) = .imp (native left) (native right) := by
  apply native_eq_of_erase
  change erase (.imp (encode left) (encode right)) = _
  simp [erase, native_erased]

@[simp] theorem native_lam (body : Term (Constant environment) (domain :: gamma) result) :
    native (.lam body) = .lam (reifyType domain) (native body) := by
  apply native_eq_of_erase
  change erase (.lam (encode body)) = _
  simp [erase, native_erased]

@[simp] theorem native_all (body : Formula (Constant environment) (domain :: gamma)) :
    native (.all body) = .all (reifyType domain) (native body) := by
  apply native_eq_of_erase
  change erase (.all (encode body)) = _
  simp [erase, native_erased]

@[simp] theorem native_weaken (source : Term (Constant environment) gamma type) :
    native (weaken (σ := domain) source) = Tm.shift 0 1 (native source) := by
  apply native_eq_of_erase
  rw [weaken, encode_rename]
  change erase (weaken (encode source)) = _
  rw [erase_weaken, native_erased]
  rfl

#print axioms native_app
#print axioms native_imp
#print axioms native_lam
#print axioms native_all
#print axioms native_weaken

end Mettapedia.Languages.Megalodon.HOLTermFormation
