import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWhereQueryExecution

/-!
# Complementary receiver executions with a genuinely bound continuation

Both receivers listen on the same channel. Their continuations send the
dereferenced received name on distinct answer channels. The tested payloads
are a parallel pair of actual outputs and the null process. Matching,
continuation substitution, query-row histories and the complete retained
capture are checked against the executable scoped interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWhereExecutionControls

open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding ScopedRuleMatching FocusedRelationQueryExecution
open ScopedPremiseExecution (RuleFiring RuleHistory PremiseEvent StepOracle)
open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding RhoIntrinsicReadback RhoGuardRelationQueries
open Mettapedia.GSLT.Causality.ComplementaryAssay (Verdict)
open ScopeWherePresentation ScopeWhereQueryExecution

def opposite : Verdict → Verdict
  | .confirm => .refute
  | .refute => .confirm

def rawPayload : Verdict → Term sig [] Srt.pr
  | .confirm => parallel RhoSourceOutputPredicate.output RhoSourceOutputPredicate.output
  | .refute => null

def payload (sample : Verdict) : Pattern := encodeTerm (rawPayload sample)

def channel : Pattern := .apply "NQuote" [.apply "PZero" []]

def answerChannel : Verdict → Pattern
  | .confirm => .apply "NQuote" [.apply "POutput" [channel, .apply "PZero" []]]
  | .refute => .apply "NQuote" [.apply "PInput" [channel, .lambda none (.apply "PDrop" [.bvar 0])]]

def continuation (branch : Verdict) : Pattern :=
  .apply "POutput" [answerChannel branch, .apply "PDrop" [.bvar 0]]

def probe (branch : Verdict) : Pattern := receiver branch channel (continuation branch)

def source (sample : Verdict) : Pattern :=
  .collection .hashBag [probe .confirm, probe .refute, .apply "POutput" [channel, payload sample]] none

def capture (sample branch : Verdict) : Assignment :=
  [("rest", ⟨[], 0, .collection .hashBag [probe (opposite branch)] none⟩),
   ("q", ⟨[], 0, payload sample⟩),
   ("p", ⟨[TypeExpr.name], 0, continuation branch⟩),
   ("n", ⟨[], 0, channel⟩)]

def target (sample branch : Verdict) : Pattern :=
  .collection .hashBag
    [.apply "POutput" [answerChannel branch, .apply "PDrop" [.apply "NQuote" [payload sample]]],
     probe (opposite branch)] none

def firing (sample branch : Verdict) : RuleFiring RuleHistory where
  captured := capture sample branch
  completed := capture sample branch
  history := [.root 0 0]
  target := target sample branch

theorem matching (sample branch : Verdict) :
    matchRuleAt (guardedComm branch) bindingSpec 0 (source sample) = [capture sample branch] := by
  cases sample <;> cases branch <;> decide +kernel

theorem captured_payload (sample branch : Verdict) :
    lookup (capture sample branch) "q" = some ⟨[], 0, payload sample⟩ := by
  cases sample <;> cases branch <;> decide +kernel

theorem projected_payload (sample : Verdict) :
    instantiateValue? ⟨[], 0, payload sample⟩ 0 0 [] = some (payload sample) := by
  cases sample <;> decide +kernel

theorem captured_continuation (sample branch : Verdict) :
    lookup (capture sample branch) "p" = some ⟨[TypeExpr.name], 0, continuation branch⟩ := by
  cases sample <;> cases branch <;> decide +kernel

theorem continuation_needs_its_binder (branch : Verdict) :
    instantiateValue? ⟨[TypeExpr.name], 0, continuation branch⟩ 0 0 [] = none := by
  cases branch <;> decide +kernel

theorem whole_root_projection_declines (sample branch : Verdict) :
    projectRoot? 0 (capture sample branch) = none := by
  cases sample <;> cases branch <;> decide +kernel

theorem focused_payload_projection (sample branch : Verdict) :
    projectNames? 0 (capture sample branch) ["q"] = some [("q", payload sample)] :=
  projectNames?_one_bound 0 _ "q" _ _ (captured_payload sample branch) (projected_payload sample)

theorem actual_continuation_substitution (sample branch : Verdict) :
    reduct? (guardedComm branch) bindingSpec 0 (capture sample branch) = some (target sample branch) := by
  cases sample <;> cases branch <;> decide +kernel

theorem source_scoped (sample : Verdict) : (source sample).isWellScoped = true := by
  cases sample <;> decide +kernel

theorem target_scoped (sample branch : Verdict) : (target sample branch).isWellScoped = true := by
  cases sample <;> cases branch <;> decide +kernel

theorem guarded_receivers_are_not_ordinary_COMM (sample : Verdict) :
    matchRuleAt Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommRewrite
      Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec 0 (source sample) = [] := by
  cases sample <;> decide +kernel

noncomputable section

theorem query_run {Evidence : Type} (guard : Name [] → Bool) (sample branch : Verdict) :
    queryResults (Evidence := Evidence) (environment guard) language bindingSpec
      0 0 (relationName branch) [.fvar "q"] (capture sample branch) =
        if enabled guard branch (payload sample) then
          [(.root 0 0, capture sample branch)] else [] := by
  have noOccurrence : ScopedPremiseExecution.hasOccurrenceAt bindingSpec 0 = false := by decide +kernel
  have argumentNames :
      (List.flatMap Pattern.freeFvarNames [Pattern.fvar "q"]).eraseDups = ["q"] := by cbv
  unfold queryResults
  rw [noOccurrence, argumentNames]
  simp only [Bool.false_eq_true, if_false, focused_payload_projection]
  rw [bound_query_exact guard branch language (bindings := [("q", payload sample)])
    (slotName := "q") (payload := payload sample) (by rfl)]
  by_cases admitted : enabled guard branch (payload sample) = true
  · simp only [admitted, if_true, List.zipIdx_cons, List.zipIdx_nil,
      List.filterMap_cons, List.filterMap_nil]
    rw [echo_retains_capture _ _ _ (captured_payload sample branch) (projected_payload sample)]
    rfl
  · have declined : enabled guard branch (payload sample) = false := Bool.eq_false_iff.mpr admitted
    simp [declined]

theorem ordered_guard_run (guard : Name [] → Bool) (oracle : StepOracle RuleHistory)
    (sample branch : Verdict) :
    runPremises oracle (environment guard) language (guardedComm branch) bindingSpec 0 0
      (guardedComm branch).premises (capture sample branch) =
        if enabled guard branch (payload sample) then
          [(capture sample branch, [PremiseEvent.root 0 0])] else [] := by
  change (queryResults (environment guard) language bindingSpec 0 0 (relationName branch)
    [.fvar "q"] (capture sample branch)).flatMap _ = _
  rw [query_run]
  by_cases admitted : enabled guard branch (payload sample) = true
  · simp only [admitted, if_true, List.flatMap_cons, List.flatMap_nil, runPremises,
      List.map_cons, List.map_nil, List.append_nil]
  · have declined : enabled guard branch (payload sample) = false := Bool.eq_false_iff.mpr admitted
    simp [declined]

theorem finished_firing (sample branch : Verdict) :
    ScopedPremiseExecution.finish? (guardedComm branch) bindingSpec 0
      (capture sample branch) (capture sample branch) [.root 0 0] = some (firing sample branch) := by
  unfold ScopedPremiseExecution.finish?
  rw [actual_continuation_substitution]
  have wellScoped : (target sample branch).isWellScopedAt 0 = true := target_scoped sample branch
  change (if (target sample branch).isWellScopedAt 0 then
    some (firing sample branch) else none) = _
  rw [wellScoped]
  rfl

theorem guarded_firings_exact (guard : Name [] → Bool) (oracle : StepOracle RuleHistory)
    (sample branch : Verdict) :
    applyRuleWithOracle oracle (environment guard) language 0 (guardedComm branch) (source sample) =
      if enabled guard branch (payload sample) then [firing sample branch] else [] := by
  have admitted : admittedFor (guardedComm branch) bindingSpec = true := by
    cases branch <;> decide +kernel
  unfold applyRuleWithOracle
  change (if admittedFor (guardedComm branch) bindingSpec then _ else []) = _
  rw [admitted]
  simp only [if_true, matching, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [ordered_guard_run]
  by_cases permitted : enabled guard branch (payload sample) = true
  · simp only [permitted, if_true, List.filterMap_cons, List.filterMap_nil, finished_firing]
  · have declined : enabled guard branch (payload sample) = false := Bool.eq_false_iff.mpr permitted
    simp [declined]

theorem ordinary_COMM_has_no_firing (guard : Name [] → Bool) (oracle : StepOracle RuleHistory)
    (sample : Verdict) :
    applyRuleWithOracle oracle (environment guard) language 0
      Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommRewrite (source sample) = [] := by
  unfold applyRuleWithOracle
  change (if admittedFor _ _ then (matchRuleAt _ _ 0 (source sample)).flatMap _ else []) = []
  rw [guarded_receivers_are_not_ordinary_COMM]
  simp

theorem depth_zero_parallel_has_no_firing (guard : Name [] → Bool) (sample : Verdict) :
    applyRuleWithOracle (rewriteAt (environment guard) language 0) (environment guard) language 0
      Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedParCongRewrite (source sample) = [] := by
  cases sample <;> cbv

def chosenBranch (guard : Name [] → Bool) (sample : Verdict) : Verdict :=
  Mettapedia.GSLT.Causality.ComplementaryAssay.verdictOf
    (guard (quote (project (rawPayload sample))))

theorem rewrite_one_exact (guard : Name [] → Bool) (sample : Verdict) :
    rewriteAt (environment guard) language 1 0 (source sample) =
      [(.fire (match chosenBranch guard sample with | .confirm => 2 | .refute => 3) [.root 0 0],
        target sample (chosenBranch guard sample))] := by
  have rules : language.rewrites =
      [Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommRewrite,
       Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedParCongRewrite,
       guardedComm .confirm, guardedComm .refute] := rfl
  unfold rewriteAt
  rw [rules]
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rw [ordinary_COMM_has_no_firing, depth_zero_parallel_has_no_firing,
    guarded_firings_exact, guarded_firings_exact]
  cases answer : guard (quote (project (rawPayload sample))) <;>
    simp [enabled, payload, payloadGuard_encoded, answer, chosenBranch,
      Mettapedia.GSLT.Causality.ComplementaryAssay.Verdict.bit,
      Mettapedia.GSLT.Causality.ComplementaryAssay.verdictOf, firing]

end

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWhereExecutionControls
