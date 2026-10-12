import Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalReceiptTransport
import Mettapedia.OSLF.NativeTypes.Modal.NativeSubstitutionBoundary
import Mettapedia.OSLF.NativeTypes.Modal.NativeQuerySubstitutionBoundary
import Mettapedia.OSLF.MeTTaIL.StructuralDescentControls
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSharedOutputControls

/-!
# Contextual receipt transport on original binding and quantified consumers

The original four-rule lambda language supplies recursive and binder-local
firings. The existing compiled shared-output consumer supplies positive
queries, duplicate provider origins and lexical quantification. Both execute
through the same independent scoped semantics and certified receipt checker.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalTransportControls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching StructuralDescent
open Mettapedia.GSLT.LanguageDef.WellSorted
open NativeOperationalReceiptTransport NativeReceiptRechecking

abbrev term : TypeExpr := .base "Term"
abbrev lambdaEnvironment := StructuralDescent.Controls.lambdaEnvironment

theorem lambda_profile : NativeOperationalProfile.Admitted lambdaEnvironment := by
  apply (NativeOperationalProfile.check_exact lambdaEnvironment).mp
  have prerequisites : NativeOperationalAdmission.checkPrerequisites lambdaEnvironment = true := by
    unfold NativeOperationalAdmission.checkPrerequisites
    rw [StructuralDescent.Controls.lambda_structural_admission]
    decide +kernel
  simp only [NativeOperationalProfile.check, prerequisites, Bool.true_and]
  decide +kernel

def identity : Pattern := .apply "Lam" [.lambda none (.bvar 0)]

def close : TypedBoundAssignment lambdaEnvironment.language lambdaEnvironment.free [term] [] where
  assignment := fun _ => identity
  typed := by
    intro index type selected
    have same : type = term := by
      cases index with
      | zero => exact (Option.some.inj selected).symm
      | succ index => simp at selected
    rw [same]
    exact (checkOpenPatternWellSorted_sound (by decide +kernel)).1

theorem close_canonical : ∀ index, (close.assignment index).hasCanonicalBinderMetadata = true := by intro index; rfl

theorem close_objects : ∀ index, isObjectPattern (close.assignment index) = true := by intro index; rfl

def openBeta : Pattern := .apply "App" [identity, .bvar 0]
def betaAnswers := Execution.roots lambdaEnvironment 3 [term] term openBeta

def closedBetaAnswers := betaAnswers.map (transport lambda_profile close close_canonical close_objects)

#guard betaAnswers.map (·.target) == [.bvar 0]
#guard closedBetaAnswers.map (·.target) == [identity]
#guard closedBetaAnswers.map (·.index) == betaAnswers.map (·.index)
#guard closedBetaAnswers.all fun answer => answer.captured.all fun entry => entry.2.ambient == 0
#guard closedBetaAnswers.all fun answer =>
  (recheck lambdaEnvironment [] term (ContextSubstitution.substitute close.assignment openBeta) (read answer)).isSome

def openBinderSource : Pattern := .apply "Lam" [.lambda none (.apply "App" [identity, .bvar 1])]
def openBinderTarget : Pattern := .apply "Lam" [.lambda none (.bvar 1)]
def binderAnswers := Execution.roots lambdaEnvironment 4 [term] term openBinderSource

def closedBinderAnswers := binderAnswers.map (transport lambda_profile close close_canonical close_objects)

#guard binderAnswers.map (·.target) == [openBinderTarget]
#guard closedBinderAnswers.map (·.target) == [.apply "Lam" [.lambda none identity]]
#guard binderAnswers.map (fun answer => answer.history.flatMap StructuralDescent.Controls.childIndices) == [[0]]
#guard closedBinderAnswers.map (fun answer => answer.history.flatMap StructuralDescent.Controls.childIndices) == [[0]]
#guard closedBinderAnswers.all fun answer =>
  (recheck lambdaEnvironment [] term (ContextSubstitution.substitute close.assignment openBinderSource) (read answer)).isSome

theorem lambda_every_actual_receipt {bound target : List TypeExpr} {source : Pattern}
    (substitution : TypedBoundAssignment lambdaEnvironment.language lambdaEnvironment.free bound target)
    (canonical : ∀ index, (substitution.assignment index).hasCanonicalBinderMetadata = true)
    (objects : ∀ index, isObjectPattern (substitution.assignment index) = true)
    (answer : Execution.RootAnswer lambdaEnvironment bound term source) :
    ∃ recovered, recheck lambdaEnvironment target term (ContextSubstitution.substitute substitution.assignment source)
        (payload bound target substitution.assignment (read answer)) = some recovered ∧
      read recovered = payload bound target substitution.assignment (read answer) :=
  transported_rechecked lambda_profile substitution canonical objects answer

abbrev queryEnvironment := GeneralPremise.SharedOutputControls.environment

theorem query_profile : NativeOperationalProfile.Admitted queryEnvironment := by
  apply (NativeOperationalProfile.check_exact queryEnvironment).mp
  decide +kernel

def extend : TypedBoundAssignment queryEnvironment.language queryEnvironment.free [] [term] where
  assignment := Pattern.bvar
  typed := by intro index type selected; simp at selected

theorem extend_canonical : ∀ index, (extend.assignment index).hasCanonicalBinderMetadata = true := by intro index; rfl

theorem extend_objects : ∀ index, isObjectPattern (extend.assignment index) = true := by intro index; rfl

def querySource := GeneralPremise.SharedOutputControls.source
  [GeneralPremise.SharedOutputControls.zero, GeneralPremise.SharedOutputControls.zero]

def queryAnswers := Execution.roots queryEnvironment 1 [] term querySource

def extendedQueryAnswers := queryAnswers.map (transport query_profile extend extend_canonical extend_objects)

#guard queryAnswers.length == 2
#guard queryAnswers.map (fun answer => answer.history.flatMap GeneralPremise.SharedOutputControls.queryRows) ==
  [[0, 2, 2, 5], [1, 2, 2, 5]]
#guard extendedQueryAnswers.map (fun answer => answer.history.flatMap GeneralPremise.SharedOutputControls.queryRows) ==
  [[0, 2, 2, 5], [1, 2, 2, 5]]
#guard extendedQueryAnswers.map (·.target) == queryAnswers.map (·.target)
#guard extendedQueryAnswers.all fun answer => answer.completed.all fun entry => entry.2.ambient == 1
#guard extendedQueryAnswers.all fun answer =>
  (recheck queryEnvironment [term] term querySource (read answer)).isSome

#guard !(NativeOperationalProfile.check NativeSubstitutionBoundary.environment)
#guard NativeOperationalProfile.check NativeQuerySubstitutionBoundary.environment

theorem freshness_rejected : NativeOperationalProfile.check NativeSubstitutionBoundary.environment = false := by
  decide +kernel

theorem positive_query_has_no_reflection {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List Event} {target : Pattern} :
    ¬ RootFiring NativeQuerySubstitutionBoundary.environment [term] term (.bvar 0) index trace captured completed history target :=
  NativeQuerySubstitutionBoundary.no_original_firing

end Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalTransportControls
