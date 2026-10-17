import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalCompletion

/-!
# Local coverage controls with binders and ordered conditional origins

The authored rules require a finite input query. Two identical declarations
and two identical provider rows remain four distinct firing origins. The
same query executes at a typed site beneath an object-language binder.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.LocalEquationFree.Controls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted

def term : TypeExpr := .base "Term"
def zero : Pattern := .apply "Zero" []
def successor (body : Pattern) : Pattern := .apply "Successor" [body]
def accept (body : Pattern) : Pattern := .apply "Accept" [body]
def binder (body : Pattern) : Pattern := .apply "Lam" [.lambda none body]

def rule : RewriteRule where
  name := "conditionally-accept"
  typeContext := [("X", term)]
  premises := [.relationQuery "allowed" [.fvar "X"]]
  left := successor (.fvar "X")
  right := accept (.fvar "X")

def language : LanguageDef where
  name := "ConditionalLocalBinder"
  types := ["Term"]
  terms := [
    {label := "Zero", category := "Term", params := [], syntaxPattern := []},
    {label := "Successor", category := "Term", params := [.simple "body" term], syntaxPattern := []},
    {label := "Accept", category := "Term", params := [.simple "body" term], syntaxPattern := []},
    {label := "Lam", category := "Term", params := [.abstraction "body" (.arrow term term)], syntaxPattern := []}]
  rewrites := [rule, {rule with name := "conditionally-accept-again"}]
  equations := []

def provider : GeneralPremise.ProviderSnapshot :=
  {signatures := [⟨"allowed", [term], [.input]⟩],
   rows := [⟨"allowed", [zero]⟩, ⟨"allowed", [zero]⟩], dynamicRelations := []}

def snapshot : Snapshot := ⟨language, [], provider⟩
def permissions : Permissions := {sites := .all}
def plan : Plan := GeneralExecutionAdmission.compile snapshot permissions

theorem whole_profile_foundation : plan.complete = true := by cbv
theorem whole_profile_generic : GeneralExecutionTotalAdmission.checkGeneric plan = true := by cbv
theorem whole_profile_equation_free : plan.equations = [] := rfl

def request (source : Pattern) : Request := ⟨plan, [], term, source⟩
def finished (source : Pattern) : State (request source) :=
  run (request source) (workBound (request source))

theorem whole_source_completion (source : Pattern)
    (typed : OpenPatternWellSorted language FreeTypeContext.empty [] term source) :
    complete (request source) (finished source) = true ∧
      checkCertificate (request source) (finished source) = true := by
  have canonical := Pattern.eraseBinderMetadata_eq_self_of_canonical typed.2.1
  have admitted : Admitted (request source) := by
    refine ⟨rfl, whole_profile_foundation, ?_⟩
    change OpenPatternWellSorted language FreeTypeContext.empty [] term source.eraseBinderMetadata
    rw [canonical]
    exact typed
  exact ⟨complete_at_workBound admitted whole_profile_equation_free whole_profile_generic,
    certificate_at_workBound admitted whole_profile_equation_free whole_profile_generic⟩

def queryRows (history : List GeneralPremise.Event) : List Nat :=
  history.filterMap fun event => match event with | .query _ _ row _ => some row | _ => none

def receiptOrigin (receipt : GeneralRuleJobs.Receipt) :
    Nat × List Nat × List TypeExpr × List Nat × Pattern :=
  (receipt.job.declaration.declarationIndex, receipt.job.site.address,
    receipt.job.site.focusBound, queryRows receipt.premiseHistory, receipt.target)

def origins (source : Pattern) : List (Nat × List Nat × List TypeExpr × List Nat × Pattern) :=
  (finished source).answers.map fun receipt => receiptOrigin receipt.val.firing

def completedOrigins (source : Pattern) : List (Nat × List Nat × List TypeExpr × List Nat × Pattern) :=
  (GeneralRuleJobExecution.completedReceipts plan [] term source).map receiptOrigin

#guard origins (successor zero) ==
  [(0, [], [], [0], accept zero), (0, [], [], [1], accept zero),
   (1, [], [], [0], accept zero), (1, [], [], [1], accept zero)]

#guard origins (binder (successor zero)) ==
  [(0, [0, 0], [term], [0], binder (accept zero)),
   (0, [0, 0], [term], [1], binder (accept zero)),
   (1, [0, 0], [term], [0], binder (accept zero)),
   (1, [0, 0], [term], [1], binder (accept zero))]

#guard origins (binder (successor (.bvar 0))) == []
#guard completedOrigins (successor zero) == origins (successor zero)
#guard completedOrigins (binder (successor zero)) == origins (binder (successor zero))
#guard completedOrigins (binder (successor (.bvar 0))) == []
#guard completedOrigins (successor (.bvar 0)) == []
#guard checkCertificate (request (binder (successor (.bvar 0))))
  (finished (binder (successor (.bvar 0))))

#guard (run (request (successor zero)) 1).answers.isEmpty
#guard !complete (request (successor zero)) (run (request (successor zero)) 1)

#guard (GeneralOccurrenceFrontier.run (request (successor zero))
  (workBound (request (successor zero))) (run (request (successor zero)) 1)).answers.length == 4

theorem resumed_execution_exact (first second : Nat) :
    run (request (successor zero)) (first + second) =
      GeneralOccurrenceFrontier.run (request (successor zero)) second
        (run (request (successor zero)) first) := run_resume _ first second

#guard ((finished (successor zero)).answers.map fun receipt =>
  (GeneralOccurrenceNativeReceipts.history plan [] term receipt).length) == [1, 1, 1, 1]

#guard ((finished (successor zero)).answers.map fun receipt => receipt.val.conversions.length) == [0, 0, 0, 0]

#guard !checkCertificate (request (successor zero))
  {finished (successor zero) with answers := (finished (successor zero)).answers.drop 1}

#guard !checkCertificate (request (successor zero)) {finished (successor zero) with answers := []}

#guard (finished (successor (.bvar 0))).unresolved == [.sourceRejected]
#guard !complete (request (successor (.bvar 0))) (finished (successor (.bvar 0)))

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.LocalEquationFree.Controls
