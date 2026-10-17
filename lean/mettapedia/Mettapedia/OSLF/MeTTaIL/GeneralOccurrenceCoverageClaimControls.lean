import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceCoverageClaims
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalControls
import Mettapedia.OSLF.NativeTypes.Modal.Counterexamples

/-!
# Rejection controls for external coverage claims

An accepted manifest is obtained from actual completed execution. The
controls omit an enabled origin, fabricate an unlicensed site, change the
source or snapshot, change the finite provider, and remove required equation
archives. Endpoint agreement alone cannot certify occurrence coverage.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.CoverageClaims.Controls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralOccurrenceKeys GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.Framework

def localRequest : Request := LocalEquationFree.Controls.request (LocalEquationFree.Controls.successor LocalEquationFree.Controls.zero)
def localState : State localRequest := LocalEquationFree.Controls.finished (LocalEquationFree.Controls.successor LocalEquationFree.Controls.zero)
def localManifest : Manifest := read localRequest localState

#guard check localRequest localState localManifest

def omittedOrigin : Manifest := {localManifest with occurrences := localManifest.occurrences.drop 1}

#guard (omittedOrigin.occurrences.map (fun occurrence => occurrence.2.target)).eraseDups ==
  (localManifest.occurrences.map (fun occurrence => occurrence.2.target)).eraseDups
#guard !check localRequest localState omittedOrigin
#guard !check localRequest {localState with answers := localState.answers.drop 1}
  (read localRequest {localState with answers := localState.answers.drop 1})

def unlicensedContext : DerivedContexts.OneHoleContext := .substBody .hole LocalEquationFree.Controls.zero

#guard !LocalEquationFree.Controls.permissions.sites.permitsContext unlicensedContext

def illicitSite (key : Pattern × RuleReplayRecord) : Pattern × RuleReplayRecord :=
  (key.1, {key.2 with job := (key.2.job.1,
    {key.2.job.2 with address := [0], context := unlicensedContext})})

def illicitManifest : Manifest :=
  {localManifest with occurrences := localManifest.occurrences.map illicitSite}

#guard !check localRequest localState illicitManifest

def otherSource : Manifest :=
  {localManifest with request := {localManifest.request with source := LocalEquationFree.Controls.zero}}

#guard !check localRequest localState otherSource

def otherLanguage : Manifest :=
  {localManifest with request := {localManifest.request with plan :=
    {localManifest.request.plan with snapshot := {localManifest.request.plan.snapshot with
      language := {localManifest.request.plan.snapshot.language with name := "different-snapshot"}}}}}

#guard !check localRequest localState otherLanguage

def otherProvider : Manifest :=
  {localManifest with request := {localManifest.request with plan :=
    {localManifest.request.plan with snapshot := {localManifest.request.plan.snapshot with
      provider := {localManifest.request.plan.snapshot.provider with
        rows := (localManifest.request.plan.snapshot.provider.rows.drop 1)}}}}}

#guard !check localRequest localState otherProvider

def otherPermissions : Manifest :=
  {localManifest with request := {localManifest.request with plan :=
    {localManifest.request.plan with permissions :=
      {localManifest.request.plan.permissions with ruleIndices := some [0]}}}}

#guard !check localRequest localState otherPermissions

def equationRequest : Request := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.request Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha

theorem equationAdmitted : Admitted equationRequest := by
  refine ⟨Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.actual_plan.symm, by cbv, ?_⟩
  apply checkOpenPatternWellSorted_sound
  cbv

def equationState : State equationRequest := finish equationRequest equationAdmitted
def equationManifest : Manifest := read equationRequest equationState

#guard !equationRequest.plan.equations.isEmpty
#guard !equationState.checkedEquations.isEmpty
#guard check equationRequest equationState equationManifest

def noEquationArchives : State equationRequest := {equationState with checkedEquations := []}

#guard complete equationRequest noEquationArchives
#guard !check equationRequest noEquationArchives (read equationRequest noEquationArchives)
#guard !check equationRequest equationState {equationManifest with equationArchives := []}

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.CoverageClaims.Controls
