import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls

/-!
# Controls: the generated formulas as higher-order logic

- **What a translation looks like.** "Some step leads to a term" is `λx. ∃y. step_any x y ∧ (λz. ⊤) y`
  (`possibly_top_shape`).
- **Truth carries over.** Under full β, safety holds at `(λx. (λy. y) x) ok` and reaching `Err` fails
  there; their translations hold and fail in the standard model alike (`safety_holds`,
  `reaching_err_fails`). At `(λx. Err) ok` reaching `Err` holds, and so does its translation
  (`reaching_err_holds`).
- **The basis.** Translations use only variables, constants, application, abstraction and equality
  (`safety_basis`); a primitive conjunction is outside the basis (`primitive_and_outside`).
- **The signature.** A constructor former the language provides translates into its signature
  (`par_in_signature`); a step label naming a rule the language lacks does not (`missing_rule_outside`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrderControls

open Mettapedia.Logic.HOL (Term)
open Mettapedia.Logic.HOL.HOLLightBooleanDefinitions (truth)
open Mettapedia.OSLF.Framework.NativeBasis (BasisOnly nowhere)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls
  (FullLambda safety reachesErr full_beta_safe full_beta_never_errs err_reachable)
open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls (underBinder app lam ok err)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls (tiny generated_par)

/-- **"Some step leads to a term"**, as a predicate of higher-order logic. -/
theorem possibly_top_shape :
    translate (.possibly .any .top : Formula 0) = someWith (related (.step .any)) (.lam (Mettapedia.Logic.HOL.weakenCtx _ truth)) :=
  rfl

/-- **Safety's translation holds** where safety does. -/
theorem safety_holds :
    ((standardModel FullLambda).denote (translate safety) (nowhere (presentation FullLambda))
      (ULift.up (app underBinder ok))).down :=
  (denote_translate_closed safety _).mpr full_beta_safe

/-- **Reaching `Err`'s translation fails** where reaching `Err` does. -/
theorem reaching_err_fails :
    ¬ ((standardModel FullLambda).denote (translate reachesErr) (nowhere (presentation FullLambda))
      (ULift.up (app underBinder ok))).down :=
  fun holds => full_beta_never_errs ((denote_translate_closed reachesErr _).mp holds)

/-- **Reaching `Err`'s translation holds** at `(λx. Err) ok`. -/
theorem reaching_err_holds :
    ((standardModel FullLambda).denote (translate reachesErr) (nowhere (presentation FullLambda))
      (ULift.up (app (lam err) ok))).down :=
  (denote_translate_closed reachesErr _).mpr err_reachable

/-- Safety's translation is built from the basis. -/
theorem safety_basis : BasisOnly (translate safety) = true :=
  basisOnly_translate safety

/-- A primitive conjunction is not. -/
theorem primitive_and_outside : BasisOnly (Term.and .top .top : Term Constant [] .prop) = false :=
  rfl

/-- **`Par` with two arguments translates into the tiny language's signature.** -/
theorem par_in_signature :
    UsesOnly (Provides tiny) (translate (.built "Par" (.cons .top (.cons .top .nil)) : Formula 0)) :=
  usesOnly_translate tiny _ generated_par

/-- **A step label for a third rule does not**: the tiny language has two rules. -/
theorem missing_rule_outside : ¬ UsesOnly (Provides tiny) (translate (.possibly (.rule 2) .top : Formula 0)) := by
  simp [translate, someWith, related, atNewest, UsesOnly, Provides, LabelOf, tiny]

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrderControls
