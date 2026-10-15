import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWherePresentation
import Mettapedia.OSLF.MeTTaIL.FocusedRelationQueryExecution

/-!
# Readouts of actual scoped where-query firings

A successful guarded communication consults the received payload, retains
the original contextual capture, and records its unique echo-row position.
The root projection condition describes the actual captured output value;
it does not supply a guard result. That result is recovered from the
successful interpreter run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWhereQueryExecution

open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding ScopedRuleMatching FocusedRelationQueryExecution
open ScopedPremiseExecution (StepOracle RuleFiring PremiseEvent)
open Mettapedia.OSLF.Binding.RhoGuardRelationQueries
open Mettapedia.OSLF.Binding.RhoQuotationClassFibres (Name)
open Mettapedia.GSLT.Causality.ComplementaryAssay (Verdict)
open ScopeWherePresentation

noncomputable section

theorem echo_retains_capture (assignment : Assignment) (value : ContextualValue)
    (payload : Pattern) (found : lookup assignment "q" = some value)
    (reading : instantiateValue? value 0 0 [] = some payload) :
    extendRoot? bindingSpec 0 assignment [("q", payload)] = some assignment := by
  simp only [extendRoot?, List.foldlM_cons, List.foldlM_nil,
    reconcileRootResult?, found, reading]
  change (if payload == payload then some assignment else none).bind
    (fun actual => some actual) = some assignment
  simp

theorem firing_query_readout {Evidence : Type} (guard : Name [] → Bool)
    (oracle : StepOracle Evidence) (branch : Verdict) (source : Pattern)
    (firing : RuleFiring Evidence) (value : ContextualValue) (payload : Pattern)
    (present : firing ∈ applyRuleWithOracle oracle (environment guard) language 0
      (guardedComm branch) source)
    (found : lookup firing.captured "q" = some value)
    (reading : instantiateValue? value 0 0 [] = some payload) :
    enabled guard branch payload = true ∧ firing.completed = firing.captured ∧
      firing.history = [.root 0 0] := by
  obtain ⟨spec, captured, completed, history, declared, _, _, ran, finished⟩ :=
    (mem_applyRuleWithOracle_iff oracle (environment guard) language 0
      (guardedComm branch) source firing).mp present
  change some bindingSpec = some spec at declared
  cases Option.some.inj declared
  obtain ⟨captureReadout, completionReadout, historyReadout, _⟩ :=
    finish_readout (guardedComm branch) bindingSpec 0 captured completed history firing finished
  rw [captureReadout] at found
  change (completed, history) ∈ runPremises oracle (environment guard) language
    (guardedComm branch) bindingSpec 0 0 [.relationQuery (relationName branch) [.fvar "q"]] captured at ran
  obtain ⟨event, queried, historyEvent⟩ :=
    (runPremises_singleton_iff oracle (environment guard) language (guardedComm branch)
      bindingSpec 0 0 _ captured completed history).mp ran
  change (event, completed) ∈ queryResults (environment guard) language bindingSpec
    0 0 (relationName branch) [.fvar "q"] captured at queried
  obtain ⟨root, result, ordinal, projected, row, reconciled, eventReadout⟩ :=
    queryResults_readout (environment guard) language bindingSpec 0 0
      (relationName branch) [.fvar "q"] captured completed event queried
  have argumentNames :
      (List.flatMap Pattern.freeFvarNames [Pattern.fvar "q"]).eraseDups = ["q"] := by cbv
  rw [argumentNames] at projected
  have rootReadout := projectNames?_one_bound 0 captured "q" value payload found reading
  have rootEqual : root = [("q", payload)] :=
    (Option.some.inj (projected.symm.trans rootReadout))
  subst root
  have queryReadout := bound_query_exact guard branch language
    (bindings := [("q", payload)]) (slotName := "q") (payload := payload) (by rfl)
  rw [queryReadout] at row
  by_cases admitted : enabled guard branch payload = true
  · rw [admitted] at row
    simp only [if_true, List.zipIdx_cons, List.zipIdx_nil, List.mem_singleton,
      Prod.mk.injEq] at row
    obtain ⟨resultReadout, ordinalReadout⟩ := row
    subst result
    subst ordinal
    have captureRetained := echo_retains_capture captured value payload found reading
    have completionEqual : completed = captured := Option.some.inj
      (reconciled.symm.trans captureRetained)
    refine ⟨admitted, ?_, ?_⟩
    · exact completionReadout.trans (completionEqual.trans captureReadout.symm)
    · exact historyReadout.trans (historyEvent.trans (congrArg (fun selected => [selected]) eventReadout))
  · have rejected : enabled guard branch payload = false := Bool.eq_false_iff.mpr admitted
    simp [rejected] at row

theorem firings_do_not_race {Evidence : Type} (guard : Name [] → Bool)
    (oracle : StepOracle Evidence) (source : Pattern)
    (first last : RuleFiring Evidence) (firstValue lastValue : ContextualValue) (payload : Pattern)
    (firstPresent : first ∈ applyRuleWithOracle oracle (environment guard) language 0
      (guardedComm .confirm) source)
    (lastPresent : last ∈ applyRuleWithOracle oracle (environment guard) language 0
      (guardedComm .refute) source)
    (firstFound : lookup first.captured "q" = some firstValue)
    (lastFound : lookup last.captured "q" = some lastValue)
    (firstReadout : instantiateValue? firstValue 0 0 [] = some payload)
    (lastReadout : instantiateValue? lastValue 0 0 [] = some payload) : False := by
  have firstEnabled := (firing_query_readout guard oracle .confirm source first
    firstValue payload firstPresent firstFound firstReadout).1
  have lastEnabled := (firing_query_readout guard oracle .refute source last
    lastValue payload lastPresent lastFound lastReadout).1
  have impossible : Verdict.confirm = Verdict.refute :=
    enabled_unique guard payload firstEnabled lastEnabled
  cases impossible

end

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWhereQueryExecution
