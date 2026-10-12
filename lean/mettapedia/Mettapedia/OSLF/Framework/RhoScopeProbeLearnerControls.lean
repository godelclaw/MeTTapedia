import Mettapedia.OSLF.Framework.RhoScopeProbeControls
import Mettapedia.OSLF.Framework.RhoScopeProbeIdentification

/-!
# Actual scope response revision and silent-round controls

The paid output-pair question refutes the offered quoted null and removes
the distinct output-bearing candidate from a two-name prior. The surviving
candidate is the actual supplied name. At insufficient funding the same
round leaves the whole prior unchanged, even though delivery occurred.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeProbeLearnerControls

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoIntrinsicReadback RhoEquationGeneratedScope
open RhoScopeDecisionControls RhoScopeProbeControls
open FiniteAssayLearner
open Mettapedia.GSLT.Causality ProbeCampaign

local instance : DecidableEq (Name []) := equationClassDecision [] Srt.nm
local instance : ∀ question, DecidablePred (left question) := leftDecision
local instance : ∀ question, DecidablePred (right question) := rightDecision

def prior : Finset (Name []) := {nullName, futureName}

theorem actual_and_alternative_distinct : nullName ≠ futureName := by
  intro same
  have rejected := output_question_rejects_null
  rw [same, output_question_accepts_actual_outputs] at rejected
  cases rejected

theorem refutation_removes_actual_output_alternative :
    futureName ∉ revise (RhoScopeProbeLearner.prediction left right) prior .outputPair
      (run .outputPair (some nullName) 5).responses := by
  apply RhoScopeProbeLearner.refuted_response_removes_admitted_candidate left right
    .outputPair prior futureName _ (0, .refute, 22, nullName)
  · rw [affordable_null_refutation]
    exact Multiset.mem_singleton_self _
  · rfl
  · exact certificate_sound futureCertificate

theorem actual_paid_response_identifies_this_prior :
    revise (RhoScopeProbeLearner.prediction left right) prior .outputPair
      (run .outputPair (some nullName) 5).responses = {nullName} := by
  have actualCompatible : Compatible (RhoScopeProbeLearner.prediction left right) nullName .outputPair
      (run .outputPair (some nullName) 5).responses := by
    intro response present
    rw [affordable_null_refutation] at present
    have same := Multiset.mem_singleton.mp present
    subst response
    exact output_question_rejects_null
  have held : nullName ∈ prior := Finset.mem_insert_self _ _
  have actualRetained := (revise_mem (RhoScopeProbeLearner.prediction left right)
    prior Question.outputPair _ nullName).mpr ⟨held, actualCompatible⟩
  apply Finset.ext
  intro candidate
  constructor
  · intro retained
    have original : candidate ∈ prior :=
      revise_subset (RhoScopeProbeLearner.prediction left right) prior Question.outputPair
        (run .outputPair (some nullName) 5).responses retained
    unfold prior at original
    rcases Finset.mem_insert.mp original with same | alternative
    · exact Finset.mem_singleton.mpr same
    · have same := Finset.mem_singleton.mp alternative
      subst candidate
      exact (refutation_removes_actual_output_alternative retained).elim
  · intro member
    have same := Finset.mem_singleton.mp member
    subst candidate
    exact actualRetained

theorem underfunded_round_preserves_this_whole_prior :
    revise (RhoScopeProbeLearner.prediction left right) prior .nullPair
      (run .nullPair (some nullName) 4).responses = prior := by
  rw [underfunded_admitted_name_has_no_verdict.2]
  exact silence_preserves _ _ _

end Mettapedia.OSLF.Framework.RhoScopeProbeLearnerControls
