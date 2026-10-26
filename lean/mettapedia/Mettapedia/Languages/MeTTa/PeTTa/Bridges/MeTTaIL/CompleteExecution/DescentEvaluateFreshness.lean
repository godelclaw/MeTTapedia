import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentEvaluate

/-!
# Evaluating freshness tests

A freshness test reads its name from the assignment (the name itself when unbound, the atom its
value instantiates to otherwise), instantiates its subject, and delivers when the name does not
occur free in the subject.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted (checkOpenPatternWellSorted FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching RuleBinding
open StructuralDescent.Scheduled (Goal Result Task Obligation Continuation)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec
open PremiseSchedulerExecution (schedulerStateTerm schedulerExpansionTerm)

open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)

namespace Interpreted

namespace FreshnessSelection

private theorem constructor_head_mismatch (caller : Subst) (left right : String) (patterns values : List Atom)
    (ordinary : left ≠ "cons") (different : left ≠ right) :
    SpaceSemantics.matchValue caller (apply left patterns) (apply right values) = none := by
  rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by
    intro first rest equal
    exact ordinary (Atom.symbol.inj (List.cons.inj equal).1))]
  rw [SpaceSemantics.matchValue.matchValues]
  simp only [SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    beq_iff_eq, if_neg different, Option.bind_eq_bind]
  rfl

private theorem some_constructor_mismatch (caller : Subst) (left right : String) (patterns values : List Atom)
    (ordinary : left ≠ "cons") (different : left ≠ right) :
    SpaceSemantics.matchValue caller (apply "Some" [apply left patterns]) (apply "Some" [apply right values]) = none := by
  rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by
    intro first rest equal
    exact (by decide : ("Some" : String) ≠ "cons") (Atom.symbol.inj (List.cons.inj equal).1))]
  rw [SpaceSemantics.matchValue.matchValues]
  have head : SpaceSemantics.matchValue caller (.symbol "Some") (.symbol "Some") = some caller := by
    simp [SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]
  rw [head]
  change SpaceSemantics.matchValue.matchValues caller [apply left patterns] [apply right values] = none
  rw [SpaceSemantics.matchValue.matchValues]
  rw [constructor_head_mismatch caller left right
    patterns values ordinary different]
  rfl

private theorem some_fvar_non_atom (caller : Subst) (name : String) (value : Pattern)
    (nonAtom : ∀ atom, value ≠ .fvar atom) :
    SpaceSemantics.matchValue caller (apply "Some" [apply "FVar" [.var name]])
      (encoded (encodeOption InferenceCettaWire.encodePattern (some value))) = none := by
  cases value with
  | fvar atom => exact False.elim (nonAtom atom rfl)
  | bvar index =>
    simpa only [encodeOption, InferenceCettaWire.encodePattern, encoded, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, WireKit.apply] using
      some_constructor_mismatch caller "FVar" "Var" [.var name] [encoded (.natural index)] (by decide) (by decide)
  | apply label arguments =>
    simpa only [encodeOption, InferenceCettaWire.encodePattern, encoded, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, WireKit.apply] using
      some_constructor_mismatch caller "FVar" "PApp" [.var name] [encoded (.string label), encoded (InferenceCettaWire.encodePatterns arguments)] (by decide) (by decide)
  | lambda binder body =>
    simpa only [encodeOption, InferenceCettaWire.encodePattern, encoded, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, WireKit.apply] using
      some_constructor_mismatch caller "FVar" "PLam" [.var name] [encoded (InferenceCettaWire.encodeBinder binder), encoded (InferenceCettaWire.encodePattern body)] (by decide) (by decide)
  | multiLambda arity binders body =>
    simpa only [encodeOption, InferenceCettaWire.encodePattern, encoded, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, WireKit.apply] using
      some_constructor_mismatch caller "FVar" "PMultiLam" [.var name] [encoded (.natural arity), encoded (InferenceCettaWire.encodeList Term.string binders), encoded (InferenceCettaWire.encodePattern body)] (by decide) (by decide)
  | subst body replacement =>
    simpa only [encodeOption, InferenceCettaWire.encodePattern, encoded, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, WireKit.apply] using
      some_constructor_mismatch caller "FVar" "PSubst" [.var name] [encoded (InferenceCettaWire.encodePattern body), encoded (InferenceCettaWire.encodePattern replacement)] (by decide) (by decide)
  | collection kind elements rest =>
    simpa only [encodeOption, InferenceCettaWire.encodePattern, encoded, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, WireKit.apply] using
      some_constructor_mismatch caller "FVar" "PCollection" [.var name] [encoded (InferenceCettaWire.encodeCollectionType kind), encoded (InferenceCettaWire.encodePatterns elements), encoded (InferenceCettaWire.encodeRest rest)] (by decide) (by decide)

example : SpaceSemantics.matchValue [] (apply "Some" [apply "FVar" [.var "name"]])
    (encoded (encodeOption InferenceCettaWire.encodePattern (some (.fvar "a")))) =
      some [("name", encoded (.string "a"))] := by decide +kernel

example : SpaceSemantics.matchValue [] (apply "Some" [apply "FVar" [.var "name"]])
    (encoded (encodeOption InferenceCettaWire.encodePattern (some (.bvar 0)))) = none := by decide +kernel


private theorem non_atom_case_selection (caller : Subst) (value : Pattern)
    (nonAtom : ∀ atom, value ≠ .fvar atom) (yes no : Atom) (rest : SpaceSemantics.Cases) :
    SpaceSemantics.selectCase caller (encoded (encodeOption InferenceCettaWire.encodePattern (some value)))
      ((apply "Some" [apply "FVar" [.var "atom"]], yes) :: (.var "nonName", no) :: rest) =
    SpaceSemantics.selectCase caller (encoded (encodeOption InferenceCettaWire.encodePattern (some value)))
      ((.var "nonName", no) :: rest) := by
  rw [SpaceSemantics.selectCase, some_fvar_non_atom caller "atom" value nonAtom]


private theorem non_atom_name_case_returns
    (program : SpaceSemantics.Program) (caller : Subst)
    (host : Effects.State) (expression : Atom) (value : Pattern)
    (nonAtom : ∀ atom, value ≠ .fvar atom)
    (fresh : Subst.lookup caller "nonName" = none)
    (computed : Eval.PureReturns program caller host expression host
      (encoded (encodeOption InferenceCettaWire.encodePattern (some value)))) :
    Eval.PureReturns program caller host
      (apply "case" [expression, .expression [
        .expression [apply "Some" [apply "FVar" [.var "atom"]], apply "Some" [.var "atom"]],
        .expression [.var "nonName", .symbol "None"]]]) host (.symbol "None") := by
  refine BridgeKit.rows_case_returns program caller
    (("nonName", encoded (encodeOption InferenceCettaWire.encodePattern (some value))) :: caller)
    host host host expression (encoded (encodeOption InferenceCettaWire.encodePattern (some value)))
    (.symbol "None") (.symbol "None")
    [.expression [apply "Some" [apply "FVar" [.var "atom"]], apply "Some" [.var "atom"]],
      .expression [.var "nonName", .symbol "None"]]
    [(apply "Some" [apply "FVar" [.var "atom"]], apply "Some" [.var "atom"]),
      (.var "nonName", .symbol "None")] rfl computed ?_ ?_
  · rw [non_atom_case_selection caller value nonAtom]
    simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, fresh]
  · exact Eval.symbol_returns _ _ _ _

end FreshnessSelection

theorem freshness_non_atom_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (context : Context) (name : String) (term : Pattern) (initial : Assignment)
    (stored : ContextualValue) (value : Pattern)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment
      (.premise depth context (.freshness ⟨name, term⟩) initial) outer)
    (looked : ScopedRuleMatching.lookup initial name = some stored)
    (valued : instantiateValue? stored context.bound.length 0 [] = some value)
    (nonAtom : ∀ atom, value ≠ .fvar atom)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)))
    (rewrites : PureReturns descentLibrary.runtime [] host (apply "gslt:automata:length"
      [encoded (encodeList InferenceCettaWire.AuthoredRule.rewriteTerm environment.language.rewrites)]) host
      (number environment.language.rewrites.length))
    (bound : PureReturns descentLibrary.runtime [] host (apply "gslt:automata:length"
      [encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm context.bound)]) host (number context.bound.length))
    (binding : PureReturns descentLibrary.runtime [] host (apply "gslt:automata:binding" [encoded (.string name),
      encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm initial)]) host
      (encoded (RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm (ScopedRuleMatching.lookup initial name))))
    (valuedFact : PureReturns descentLibrary.runtime [] host (apply "gslt:rule:scope-instantiate-value"
      [encoded (InferenceCettaWire.AuthoredRule.contextualValueTerm stored), number context.bound.length,
        number 0, encoded (InferenceCettaWire.encodePatterns [])]) host
      (encoded (MatchAutomataBindingExecution.patternOptionTerm (instantiateValue? stored context.bound.length 0 [])))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.premise depth context (.freshness ⟨name, term⟩) initial)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer
          (.premise depth context (.freshness ⟨name, term⟩) initial) tail)))) := by
  have noName : freshnessName? context.bound.length initial name = none := by
    cases value with
    | fvar atom => exact False.elim (nonAtom atom rfl)
    | _ => simp [freshnessName?, looked, valued]
  have projected : PureReturns descentLibrary.runtime [] host (apply "gslt:rule:scope-instantiate-value"
      [encoded (InferenceCettaWire.AuthoredRule.contextualValueTerm stored), number context.bound.length,
        number 0, encoded (InferenceCettaWire.encodePatterns [])]) host
      (encoded (encodeOption InferenceCettaWire.encodePattern (some value))) := by
    simpa only [valued, MatchAutomataBindingExecution.patternOptionTerm,
      MatchAutomataBindingExecution.payloadOptionTerm, Option.map, encodeOption] using valuedFact
  rw [StructuralDescent.Scheduled.evaluate_freshness_none _ tail (by unfold freshnessSubject?; rw [noName]; rfl)]
  descent_interpreted_eval [view, rewrites, bound, binding]
    unfolding [looked, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
      MatchAutomataBindingExecution.payloadOptionTerm, Option.map]
  · refine FreshnessSelection.non_atom_name_case_returns descentLibrary.runtime _ host _ value nonAtom ?_ ?_
    · simp [Subst.lookup, List.find?]
    · metta_capture_any projected unfolding [valued,
           MatchAutomataBindingExecution.patternOptionTerm,
           MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
           InferenceCettaWire.encodePatterns]
  all_goals metta_eval with descentProof_checked in descentProof_agreement unfolding [
    PremiseOperationsExecution.GeneralExecution.environmentTerm, PremiseOperationsExecution.GeneralExecution.providerTerm,
    RetainedMatchingWire.Scheduled.continuationTerm, RetainedMatchingWire.Scheduled.resultTerm,
    RetainedMatchingWire.Scheduled.answerTerm, RetainedMatchingWire.Scheduled.expansionTerm,
    CompleteExecution.DescentCodec.goalTerm, CompleteExecution.DescentCodec.obligationTerm,
    RetainedMatchingWire.Scheduled.taskTerm, RetainedMatchingWire.stepCallTerm,
    PremiseOperationsExecution.GeneralExecution.contextTerm, schedulerExpansionTerm,
    Library.bind, encodeList, encodeOption, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList, Subst.lookup, List.find?,
    InferenceCettaWire.AuthoredRule.premiseTerm, InferenceCettaWire.encodeList]



private theorem evaluate_freshness_unbound_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (context : Context) (condition : FreshnessCondition) (initial : Assignment)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment
      (.premise depth context (.freshness condition) initial) outer)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)))
    (looked : ScopedRuleMatching.lookup initial condition.varName = none) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.premise depth context (.freshness condition) initial)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer
          (.premise depth context (.freshness condition) initial) tail)))) := by
  obtain ⟨name, term⟩ := condition
  change ScopedRuleMatching.lookup initial name = none at looked
  have rewrites := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm host environment.language.rewrites
  have bound := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host context.bound
  have binding := descent_binding_returns host name initial
  have subject := descent_instantiate_returns host context.rule context.spec context.bound.length
    (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial term
  cases interpreted : instantiateAt? context.rule context.spec context.bound.length
      (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial term with
  | none =>
    rw [StructuralDescent.Scheduled.evaluate_freshness_none _ tail
      (by simp [freshnessSubject?, freshnessName?, looked, interpreted])]
    descent_interpreted_eval [view, rewrites, bound, binding, subject]
      unfolding [looked, interpreted, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
        MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
        MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.AuthoredRule.siteTerm]
  | some actual =>
    rw [StructuralDescent.Scheduled.evaluate_freshness_some _ name actual tail
      (by simp [freshnessSubject?, freshnessName?, looked, interpreted])]
    have tested := descent_fresh_returns host name actual
    by_cases fresh : Substitution.isFresh name actual = true
    · rw [dif_pos fresh]
      descent_interpreted_eval [view, rewrites, bound, binding, subject, tested]
        unfolding [looked, interpreted, fresh, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
        MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
          MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.AuthoredRule.siteTerm,
          RetainedMatchingWire.eventTerm]
    · rw [dif_neg fresh]
      have stale : Substitution.isFresh name actual = false := by simpa using fresh
      descent_interpreted_eval [view, rewrites, bound, binding, subject, tested]
        unfolding [looked, interpreted, stale, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
        MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
          MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.AuthoredRule.siteTerm,
          RetainedMatchingWire.eventTerm]

private theorem evaluate_freshness_bound_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (context : Context) (condition : FreshnessCondition) (initial : Assignment)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment
      (.premise depth context (.freshness condition) initial) outer)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free))) (stored : ContextualValue)
    (looked : ScopedRuleMatching.lookup initial condition.varName = some stored) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.premise depth context (.freshness condition) initial)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer
          (.premise depth context (.freshness condition) initial) tail)))) := by
  obtain ⟨name, term⟩ := condition
  change ScopedRuleMatching.lookup initial name = some stored at looked
  have rewrites := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm host environment.language.rewrites
  have bound := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host context.bound
  have binding := descent_binding_returns host name initial
  have subject := descent_instantiate_returns host context.rule context.spec context.bound.length
    (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial term
  have valuedFact := descent_instantiate_value_returns host stored context.bound.length 0 []
  cases valued : instantiateValue? stored context.bound.length 0 [] with
  | none =>
    rw [StructuralDescent.Scheduled.evaluate_freshness_none _ tail
      (by simp [freshnessSubject?, freshnessName?, looked, valued])]
    descent_interpreted_eval [view, rewrites, bound, binding, valuedFact]
      unfolding [looked, valued, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
        MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
        MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.encodePatterns]
  | some value =>
    classical
    by_cases atomValue : ∃ atom, value = .fvar atom
    · obtain ⟨atom, rfl⟩ := atomValue
      have tested := fun actual => descent_fresh_returns host atom actual
      cases interpreted : instantiateAt? context.rule context.spec context.bound.length
          (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial term with
      | none =>
        rw [StructuralDescent.Scheduled.evaluate_freshness_none _ tail
          (by simp [freshnessSubject?, freshnessName?, looked, valued, interpreted])]
        descent_interpreted_eval [view, rewrites, bound, binding, valuedFact, subject]
          unfolding [looked, valued, interpreted, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
        MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
            MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.encodePatterns,
            InferenceCettaWire.encodePattern, InferenceCettaWire.AuthoredRule.siteTerm]
      | some actual =>
        rw [StructuralDescent.Scheduled.evaluate_freshness_some _ atom actual tail
          (by simp [freshnessSubject?, freshnessName?, looked, valued, interpreted])]
        have tested := descent_fresh_returns host atom actual
        by_cases fresh : Substitution.isFresh atom actual = true
        · rw [dif_pos fresh]
          descent_interpreted_eval [view, rewrites, bound, binding, valuedFact, subject, tested]
            unfolding [looked, valued, interpreted, fresh,
              RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
        MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
              MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.encodePatterns,
              InferenceCettaWire.encodePattern, InferenceCettaWire.AuthoredRule.siteTerm,
              RetainedMatchingWire.eventTerm]
        · rw [dif_neg fresh]
          have stale : Substitution.isFresh atom actual = false := by simpa using fresh
          descent_interpreted_eval [view, rewrites, bound, binding, valuedFact, subject, tested]
            unfolding [looked, valued, interpreted, stale,
              RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
        MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
              MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.encodePatterns,
              InferenceCettaWire.encodePattern, InferenceCettaWire.AuthoredRule.siteTerm,
              RetainedMatchingWire.eventTerm]
    · apply freshness_non_atom_returns host environment matcher codec free profile depth context name term initial stored value
        tail looked valued _ view rewrites bound binding valuedFact
      intro atom equal
      exact atomValue ⟨atom, equal⟩

theorem evaluate_freshness_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (context : Context) (condition : FreshnessCondition) (initial : Assignment)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment
      (.premise depth context (.freshness condition) initial) outer)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.premise depth context (.freshness condition) initial)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer
          (.premise depth context (.freshness condition) initial) tail)))) := by
  cases looked : ScopedRuleMatching.lookup initial condition.varName with
  | none =>
    exact evaluate_freshness_unbound_returns host environment matcher codec free profile depth context
      condition initial tail view looked
  | some stored =>
    exact evaluate_freshness_bound_returns host environment matcher codec free profile depth context
      condition initial tail view stored looked



end Interpreted

theorem descent_evaluate_freshness_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (condition : FreshnessCondition) (initial : Assignment)
    (tail : Continuation environment (.premise depth context (.freshness condition) initial) outer) :
    Evaluates state environment footprint (.premise depth context (.freshness condition) initial) tail := by
  unfold Evaluates
  simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_continuation,
    Interpreted.ordinary_expansion_terms] using
    Interpreted.evaluate_freshness_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec (environment.free.entriesOn footprint)
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
        (environment.free.entriesOn footprint)) depth context condition initial tail
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint))

#print axioms Interpreted.freshness_non_atom_returns
#print axioms Interpreted.evaluate_freshness_returns
#print axioms descent_evaluate_freshness_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
