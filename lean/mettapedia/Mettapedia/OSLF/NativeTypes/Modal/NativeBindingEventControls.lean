import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingEventPresheaf
import Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalTransportControls
import Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmissionControls

/-!
# Original binder receipts through the common native program carrier

The original authored lambda language uses the same generated signature,
constructor printer, intrinsic substitution and operational event action.
The controls execute an open beta step and a recursive step under a binder,
then inspect the transported complete receipts through the certified checker.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingEventControls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission
open NativeBindingEventAction

abbrev environment := StructuralDescent.Controls.lambdaEnvironment
abbrev language := environment.language

theorem admitted : Admitted language :=
  (BindingSemanticAdmission.check_exact _).mp
    BindingSemanticAdmission.Controls.original_lambda_admitted

theorem free_empty : environment.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty := rfl

def app {context : List String} (function argument : Term (signature language) context "Term") :
    Term (signature language) context "Term" :=
  .op (originalOperator admitted ⟨0, by decide⟩) (.cons function (.cons argument .nil))

def lam {context : List String} (body : Term (signature language) ("Term" :: context) "Term") :
    Term (signature language) context "Term" :=
  .op (originalOperator admitted ⟨1, by decide⟩) (.cons body .nil)

def identity {context : List String} : Term (signature language) context "Term" := lam (.var .zero)

def beta : Term (signature language) ["Term"] "Term" := app identity (.var .zero)

def binder : Term (signature language) ["Term"] "Term" :=
  lam (app identity (.var (.succ .zero)))

def close : Sub (signature language) ["Term"] [] := fun _ position =>
  match position with
  | .zero => identity
  | .succ impossible => nomatch impossible

def betaEvents : List (Point environment ["Term"] "Term") :=
  (Execution.roots environment 3 (bound ["Term"]) (.base "Term") (toPattern beta)).map
    fun receipt => ⟨beta, receipt⟩

def binderEvents : List (Point environment ["Term"] "Term") :=
  (Execution.roots environment 4 (bound ["Term"]) (.base "Term") (toPattern binder)).map
    fun receipt => ⟨binder, receipt⟩

def closedBetaEvents := betaEvents.map
  (action free_empty NativeOperationalTransportControls.lambda_profile close)

def closedBinderEvents := binderEvents.map
  (action free_empty NativeOperationalTransportControls.lambda_profile close)

#guard toPattern beta == NativeOperationalTransportControls.openBeta
#guard toPattern binder == NativeOperationalTransportControls.openBinderSource
#guard betaEvents.length == 1
#guard binderEvents.length == 1
#guard closedBetaEvents.map (fun point => toPattern point.source) ==
  [.apply "App" [toPattern (identity (context := [])), toPattern (identity (context := []))]]
#guard closedBetaEvents.map (fun point => point.receipt.target) == [toPattern (identity (context := []))]
#guard closedBinderEvents.map (fun point => point.receipt.target) ==
  [.apply "Lam" [.lambda none (toPattern (identity (context := [])))]]
#guard closedBinderEvents.map (fun point => point.receipt.history.flatMap StructuralDescent.Controls.childIndices) == [[0]]
#guard closedBinderEvents.map (fun point => point.receipt.index) == binderEvents.map (fun point => point.receipt.index)
#guard closedBetaEvents.all fun point =>
  (NativeReceiptRechecking.recheck environment [] (.base "Term") (toPattern point.source)
    (NativeReceiptRechecking.read point.receipt)).isSome
#guard closedBinderEvents.all fun point =>
  (NativeReceiptRechecking.recheck environment [] (.base "Term") (toPattern point.source)
    (NativeReceiptRechecking.read point.receipt)).isSome

theorem all_original_lambda_events {source target : List String} {sort : String}
    (substitution : Sub (signature language) source target) (point : Point environment source sort) :
    ∃ receipt, NativeReceiptRechecking.recheck environment (bound target) (.base sort)
        (toPattern (Binding.bind substitution point.source))
        (NativeReceiptRechecking.read (action free_empty
          NativeOperationalTransportControls.lambda_profile substitution point).receipt) = some receipt ∧
      NativeReceiptRechecking.read receipt =
        NativeReceiptRechecking.read (action free_empty
          NativeOperationalTransportControls.lambda_profile substitution point).receipt :=
  action_rechecked free_empty NativeOperationalTransportControls.lambda_profile substitution point

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingEventControls
