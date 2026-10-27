import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EngineAgreement
import Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy

/-!
# MeTTa Zero at the front door

MeTTa Zero's authored language answers queries and one-step evaluations against a space through relation premises,
which a model of the space supplies (`semanticRelationEnv`). The language is aligned and equation-free (`profile`,
`equationFree`), so its native types are read through the engine's steps (`EngineAgreement`):

- **a query's answers** are the terms at which the native type "some step to the answer" holds at the query request
  (`sat_query_iff`): exactly the space's query results;
- **an evaluation's results** likewise (`sat_evaluation_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.MeTTaZero

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (ReferenceProfile)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy (totalTheory_query_step_iff totalTheory_evaluation_step_iff)

/-- **The language is aligned**: its reference steps are its engine steps. -/
theorem profile : ReferenceProfile language := by
  have checked : language.rewrites.all Mettapedia.OSLF.MeTTaIL.ReferenceStep.ruleAligned = true := by decide +kernel
  exact fun rule member => List.all_eq_true.mp checked rule member

theorem equationFree : language.isEquationFree = true := by decide +kernel

/-- The front door's reading of MeTTa Zero over a space. -/
noncomputable abbrev Zero (model : Model) (space : model.Space) (spaceTerm : Pattern) : NativeStructure Pattern :=
  referenceStructure (semanticRelationEnv model space spaceTerm) language

theorem langReduces_iff_totalTheory (model : Model) (space : model.Space) (spaceTerm source target : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing (semanticRelationEnv model space spaceTerm) language source
      target ↔ (totalTheory model space spaceTerm).Step source target :=
  (Mettapedia.GSLT.LanguageDef.TotalGSLT.languageGSLTUsing_step _ _ _ _ _).symm

/-- **A query's answers are its native type**: some step from the request reaches the answer exactly when the answer
is among the space's query results. -/
theorem sat_query_iff (model : Model) (space : model.Space) {spaceTerm pattern template answer : Pattern}
    (requestState : IsState (queryRequestPattern spaceTerm pattern template))
    (answerState : IsState (queryAnswerPattern answer)) :
    (Zero model space spaceTerm).sat Env.closed (.possibly .any (.is (queryAnswerPattern answer)))
        (queryRequestPattern spaceTerm pattern template) ↔
      answer ∈ query model space pattern template := by
  rw [sat_possibly_is_iff profile equationFree requestState answerState, langReduces_iff_totalTheory,
    totalTheory_query_step_iff]

/-- **An evaluation's results are its native type.** -/
theorem sat_evaluation_iff (model : Model) (space : model.Space) {spaceTerm subject answer : Pattern}
    (requestState : IsState (evaluationRequestPattern spaceTerm subject))
    (answerState : IsState (evaluationAnswerPattern answer)) :
    (Zero model space spaceTerm).sat Env.closed (.possibly .any (.is (evaluationAnswerPattern answer)))
        (evaluationRequestPattern spaceTerm subject) ↔
      answer ∈ evaluateOne model space subject := by
  rw [sat_possibly_is_iff profile equationFree requestState answerState, langReduces_iff_totalTheory,
    totalTheory_evaluation_step_iff]

end Mettapedia.OSLF.NativeTypes.Instances.MeTTaZero
