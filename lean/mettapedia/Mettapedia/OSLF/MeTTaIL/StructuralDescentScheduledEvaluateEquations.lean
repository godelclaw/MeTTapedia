import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledExecution

/-!
# Equations of the scheduled descent machine's evaluation and matching

`evaluate`, `expandQuery`, `expandRootMatch` and `expandTargetMatch` decide by dependent matches
that keep the decided fact; `simp` does not reduce them. These equations state each case directly,
from the decided fact.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {environment : Environment} {outer : Goal}

section Premise

variable {depth : Nat} {context : Context} {initial : Assignment}

theorem evaluate_relationQuery (relation : String) (arguments : List Pattern)
    (tail : Continuation environment (.premise depth context (.relationQuery relation arguments) initial) outer) :
    evaluate environment outer (.premise depth context (.relationQuery relation arguments) initial) tail =
      { tasks := [.query depth ⟨context, relation, arguments, initial⟩
          (Query.start environment ⟨context, relation, arguments, initial⟩) 0 tail] } := rfl

theorem evaluate_freshness_none (condition : FreshnessCondition)
    (tail : Continuation environment (.premise depth context (.freshness condition) initial) outer)
    (read : freshnessSubject? context.rule context.spec context.bound context.premiseIndex
      context.quantifierDepth initial condition = none) :
    evaluate environment outer (.premise depth context (.freshness condition) initial) tail =
      { unresolved := [.freshnessProjection context.premiseIndex context.quantifierDepth] } := by
  change evaluatePremise environment outer depth context (.freshness condition) initial tail = _
  rw [evaluatePremise.eq_2]
  split
  · rfl
  · rename_i atom subject found
    simp [read] at found

theorem evaluate_freshness_some (condition : FreshnessCondition) (atom : String) (subject : Pattern)
    (tail : Continuation environment (.premise depth context (.freshness condition) initial) outer)
    (read : freshnessSubject? context.rule context.spec context.bound context.premiseIndex
      context.quantifierDepth initial condition = some (atom, subject)) :
    evaluate environment outer (.premise depth context (.freshness condition) initial) tail =
      if checked : Substitution.isFresh atom subject then
        { tasks := [.deliver (.premise initial (.freshness context.premiseIndex context.quantifierDepth atom subject)
            (.freshness read ((syntactic_freshness_iff atom subject).mp checked))) tail] }
      else {} := by
  change evaluatePremise environment outer depth context (.freshness condition) initial tail = _
  rw [evaluatePremise.eq_2]
  split
  · rename_i unavailable
    simp [read] at unavailable
  · rename_i actualAtom actualSubject found
    have same := Option.some.inj (found.symm.trans read)
    have one := congrArg Prod.fst same
    have two := congrArg Prod.snd same
    dsimp only at one two
    subst actualAtom actualSubject
    rfl

theorem evaluate_forAll_none (collection parameter : String) (body : Premise)
    (tail : Continuation environment (.premise depth context (.forAll collection parameter body) initial) outer)
    (read : finiteCollection? context.bound.length initial collection = none) :
    evaluate environment outer (.premise depth context (.forAll collection parameter body) initial) tail =
      { unresolved := [.collectionProjection context.premiseIndex context.quantifierDepth collection] } := by
  change evaluatePremise environment outer depth context (.forAll collection parameter body) initial tail = _
  rw [evaluatePremise.eq_3]
  split
  · rfl
  · rename_i kind elements found
    simp [read] at found

theorem evaluate_forAll_some (collection parameter : String) (body : Premise) (kind : CollType)
    (elements : List Pattern)
    (tail : Continuation environment (.premise depth context (.forAll collection parameter body) initial) outer)
    (read : finiteCollection? context.bound.length initial collection = some (kind, elements)) :
    evaluate environment outer (.premise depth context (.forAll collection parameter body) initial) tail =
      { tasks := [.evaluate (.quantified depth context parameter body 0 elements initial)
          (.quantifier depth context collection parameter body initial kind elements read tail)] } := by
  change evaluatePremise environment outer depth context (.forAll collection parameter body) initial tail = _
  rw [evaluatePremise.eq_3]
  split
  · rename_i unavailable
    simp [read] at unavailable
  · rename_i actualKind actualElements found
    have same := Option.some.inj (found.symm.trans read)
    have one := congrArg Prod.fst same
    have two := congrArg Prod.snd same
    dsimp only at one two
    subst actualKind actualElements
    rfl

theorem evaluate_congruence_sort_none (source target : Pattern)
    (tail : Continuation environment (.premise depth context (.congruence source target) initial) outer)
    (typed : sourceType? environment.language context.rule source = none) :
    evaluate environment outer (.premise depth context (.congruence source target) initial) tail =
      { unresolved := [.stepSort context.premiseIndex context.quantifierDepth] } := by
  change evaluatePremise environment outer depth context (.congruence source target) initial tail = _
  rw [evaluatePremise.eq_4]
  split
  · rfl
  · rename_i type found
    simp [typed] at found

theorem evaluate_congruence_projection_none (source target : Pattern) (type : TypeExpr)
    (tail : Continuation environment (.premise depth context (.congruence source target) initial) outer)
    (typed : sourceType? environment.language context.rule source = some type)
    (interpreted : instantiateAt? context.rule context.spec context.bound.length (context.site 0) [] 0 initial
      source = none) :
    evaluate environment outer (.premise depth context (.congruence source target) initial) tail =
      { unresolved := [.stepProjection context.premiseIndex context.quantifierDepth] } := by
  change evaluatePremise environment outer depth context (.congruence source target) initial tail = _
  rw [evaluatePremise.eq_4]
  split
  · rename_i unavailable
    simp [typed] at unavailable
  · rename_i actualType found
    have same := Option.some.inj (found.symm.trans typed)
    subst actualType
    split
    · rfl
    · rename_i actualSource found
      simp [interpreted] at found

theorem evaluate_congruence_some (source target actualSource : Pattern) (type : TypeExpr)
    (tail : Continuation environment (.premise depth context (.congruence source target) initial) outer)
    (typed : sourceType? environment.language context.rule source = some type)
    (interpreted : instantiateAt? context.rule context.spec context.bound.length (context.site 0) [] 0 initial
      source = some actualSource) :
    evaluate environment outer (.premise depth context (.congruence source target) initial) tail =
      { tasks := [.evaluate (.steps depth context.bound type actualSource environment.language.rewrites.length)
          (.stepped depth {
            context := context, premise := .congruence source target, initial := initial, binders := [],
            type := type, source := actualSource, targetSchema := target,
            conclude := fun _ _ _ _ _ _ _ _ child matching finalTyped =>
              .step typed interpreted child matching finalTyped } tail)] } := by
  change evaluatePremise environment outer depth context (.congruence source target) initial tail = _
  rw [evaluatePremise.eq_4]
  split
  · rename_i unavailable
    simp [typed] at unavailable
  · rename_i actualType found
    have same := Option.some.inj (found.symm.trans typed)
    subst actualType
    split
    · rename_i unavailable
      simp [interpreted] at unavailable
    · rename_i actual found
      have same := Option.some.inj (found.symm.trans interpreted)
      subst actual
      rfl

theorem evaluate_scopedStep_none (step : ScopedStepPremise)
    (tail : Continuation environment (.premise depth context (.scopedStep step) initial) outer)
    (interpreted : instantiateAt? context.rule context.spec context.bound.length (context.site 0) []
      step.binders.length initial step.source = none) :
    evaluate environment outer (.premise depth context (.scopedStep step) initial) tail =
      { unresolved := [.stepProjection context.premiseIndex context.quantifierDepth] } := by
  change evaluatePremise environment outer depth context (.scopedStep step) initial tail = _
  rw [evaluatePremise.eq_5]
  split
  · rfl
  · rename_i actualSource found
    simp [interpreted] at found

theorem evaluate_scopedStep_some (step : ScopedStepPremise) (actualSource : Pattern)
    (tail : Continuation environment (.premise depth context (.scopedStep step) initial) outer)
    (interpreted : instantiateAt? context.rule context.spec context.bound.length (context.site 0) []
      step.binders.length initial step.source = some actualSource) :
    evaluate environment outer (.premise depth context (.scopedStep step) initial) tail =
      { tasks := [.evaluate
          (.steps depth (step.binders ++ context.bound) step.resultType actualSource environment.language.rewrites.length)
          (.stepped depth {
            context := context, premise := .scopedStep step, initial := initial, binders := step.binders,
            type := step.resultType, source := actualSource, targetSchema := step.target,
            conclude := fun _ _ _ _ _ _ _ _ child matching finalTyped =>
              .scopedStep interpreted child matching finalTyped } tail)] } := by
  change evaluatePremise environment outer depth context (.scopedStep step) initial tail = _
  rw [evaluatePremise.eq_5]
  split
  · rename_i unavailable
    simp [interpreted] at unavailable
  · rename_i actual found
    have same := Option.some.inj (found.symm.trans interpreted)
    subst actual
    rfl

end Premise

section Quantified

variable {depth : Nat} {context : Context} {parameter : String} {body : Premise} {index : Nat}
  {element : Pattern} {elements : List Pattern} {initial : Assignment}

theorem evaluate_quantified_checked
    (tail : Continuation environment (.quantified depth context parameter body index (element :: elements) initial) outer)
    (checked : checkTypedAssignment environment context.quantified
      (bindParameter parameter (localValue context.bound element) initial) = true) :
    evaluate environment outer (.quantified depth context parameter body index (element :: elements) initial) tail =
      { tasks := [.evaluate (.premise depth context.quantified body
            (bindParameter parameter (localValue context.bound element) initial))
          (.element depth context parameter body index element elements initial
            (checkTypedAssignment_sound checked) tail)] } := by
  simp only [evaluate, checked, ↓reduceDIte]

theorem evaluate_quantified_unchecked
    (tail : Continuation environment (.quantified depth context parameter body index (element :: elements) initial) outer)
    (unchecked : checkTypedAssignment environment context.quantified
      (bindParameter parameter (localValue context.bound element) initial) = false) :
    evaluate environment outer (.quantified depth context parameter body index (element :: elements) initial) tail =
      { unresolved := [.quantifiedAssignment context.premiseIndex context.quantifierDepth index] } := by
  simp only [evaluate, unchecked, Bool.false_eq_true, ↓reduceDIte]

end Quantified

section Root

variable {depth : Nat} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {index : Nat}

theorem evaluate_root_zero (tail : Continuation environment (.root 0 bound type source index) outer) :
    evaluate environment outer (.root 0 bound type source index) tail =
      { unresolved := [.depthExhausted index] } := rfl

theorem evaluate_root_unavailable
    (tail : Continuation environment (.root (depth + 1) bound type source index) outer)
    (missing : environment.language.rewrites[index]? = none) :
    evaluate environment outer (.root (depth + 1) bound type source index) tail =
      { unresolved := [.ruleUnavailable index] } := by
  change evaluateRoot environment outer (depth + 1) bound type source index tail = _
  rw [evaluateRoot.eq_2]
  split
  · rfl
  · rename_i rule found
    simp [missing] at found

theorem evaluate_root_unspecified {rule : RewriteRule}
    (tail : Continuation environment (.root (depth + 1) bound type source index) outer)
    (declared : environment.language.rewrites[index]? = some rule)
    (missing : specification? environment index = none) :
    evaluate environment outer (.root (depth + 1) bound type source index) tail =
      { unresolved := [.bindingUnavailable index] } := by
  change evaluateRoot environment outer (depth + 1) bound type source index tail = _
  rw [evaluateRoot.eq_2]
  split
  · rename_i unavailable
    simp [declared] at unavailable
  · split
    · rfl
    · rename_i spec found
      simp [missing] at found

theorem evaluate_root_specified {rule : RewriteRule} {spec : RuleBindingSpec}
    (tail : Continuation environment (.root (depth + 1) bound type source index) outer)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec) :
    evaluate environment outer (.root (depth + 1) bound type source index) tail =
      if admitted : admittedFor rule spec then
        if checked : checkOpenPatternWellSorted environment.language environment.free bound type source then
          { tasks := [.rootMatch {
              depth := depth
              bound := bound
              type := type
              source := source
              index := index
              rule := rule
              spec := spec
              declared := declared
              specified := specified
              admitted := admitted
              sorted := checkOpenPatternWellSorted_sound checked
              state := GeneralScopedMatchMachine.start ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
              reachable := .start
              cursor := 0
              tail := tail }] }
        else { unresolved := [.sourceRejected index] }
      else { unresolved := [.bindingRejected index] } := by
  change evaluateRoot environment outer (depth + 1) bound type source index tail = _
  rw [evaluateRoot.eq_2]
  split
  · rename_i unavailable
    simp [declared] at unavailable
  · rename_i actualRule found
    have same := Option.some.inj (found.symm.trans declared)
    subst actualRule
    split
    · rename_i unavailable
      simp [specified] at unavailable
    · rename_i actualSpec found
      have same := Option.some.inj (found.symm.trans specified)
      subst actualSpec
      rfl

end Root

section Matching

theorem expandQuery_found {depth : Nat} {request : Query.Request} {state : Query.State environment request}
    {cursor : Nat} {answer : Query.Answer environment request}
    (tail : Continuation environment
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (found : state.answers[cursor]? = some answer) :
    expandQuery environment outer depth request state cursor tail =
      { tasks := [
          .deliver (.premise answer.assignment
            (.query request.context.premiseIndex request.context.quantifierDepth answer.rowIndex answer.origins)
            (.query answer.valid)) tail,
          .query depth request state (cursor + 1) tail] } := by
  unfold expandQuery
  split
  · rename_i other present
    rw [found] at present
    cases present
    rfl
  · rename_i absent
    rw [found] at absent
    cases absent

theorem expandQuery_missing {depth : Nat} {request : Query.Request} {state : Query.State environment request}
    {cursor : Nat}
    (tail : Continuation environment
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (missing : state.answers[cursor]? = none) :
    expandQuery environment outer depth request state cursor tail =
      if state.agenda.isEmpty then { unresolved := state.unresolved.map Obligation.query }
      else { tasks := [.query depth request (Query.tick environment request state) cursor tail] } := by
  unfold expandQuery
  split
  · rename_i other present
    rw [missing] at present
    cases present
  · rfl

theorem expandRootMatch_found (frame : RootMatchFrame environment outer)
    {answer : GeneralScopedMatchMachine.Answer} (found : frame.state.answers[frame.cursor]? = some answer) :
    expandRootMatch environment outer frame =
      if checked : checkTypedAssignment environment ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩
          answer.assignment then
        { tasks := [
            .evaluate (.premises frame.depth ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩
                frame.rule.premises answer.assignment)
              (.rootBody frame.depth frame.bound frame.type frame.source frame.index frame.rule frame.spec
                frame.declared frame.specified frame.admitted frame.sorted answer.trace answer.assignment
                (GeneralScopedMatchMachine.answers_sound frame.reachable (List.mem_of_getElem? found))
                (checkTypedAssignment_sound checked) frame.tail),
            .rootMatch { frame with cursor := frame.cursor + 1 }] }
      else { tasks := [.rootMatch { frame with cursor := frame.cursor + 1 }] } := by
  unfold expandRootMatch
  split
  · rename_i other present
    have same := Option.some.inj (present.symm.trans found)
    subst same
    rfl
  · rename_i absent
    rw [found] at absent
    cases absent

theorem expandRootMatch_missing (frame : RootMatchFrame environment outer)
    (missing : frame.state.answers[frame.cursor]? = none) :
    expandRootMatch environment outer frame =
      if GeneralScopedMatchMachine.complete frame.state then {}
      else
        { tasks := [.rootMatch { frame with
            state := GeneralScopedMatchMachine.tick
              ⟨frame.rule, frame.spec, frame.bound.length, .left, [], 0, [], frame.rule.left, frame.source⟩ frame.state
            reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable }] } := by
  unfold expandRootMatch
  split
  · rename_i other present
    rw [missing] at present
    cases present
  · rfl

theorem expandTargetMatch_found (frame : TargetMatchFrame environment outer)
    {answer : GeneralScopedMatchMachine.Answer} (found : frame.state.answers[frame.cursor]? = some answer) :
    expandTargetMatch environment outer frame =
      if checked : checkTypedAssignment environment frame.call.context answer.assignment then
        { tasks := [
            .deliver (.premise answer.assignment
              (.child frame.call.context.premiseIndex frame.call.context.quantifierDepth frame.index
                (frame.call.binders ++ frame.call.context.bound) frame.call.source frame.target
                frame.trace answer.trace frame.captured frame.completed frame.history)
              (frame.call.conclude _ _ _ _ _ _ _ _ frame.valid
                (GeneralScopedMatchMachine.answers_sound frame.reachable (List.mem_of_getElem? found))
                (checkTypedAssignment_sound checked))) frame.tail,
            .targetMatch { frame with cursor := frame.cursor + 1 }] }
      else { tasks := [.targetMatch { frame with cursor := frame.cursor + 1 }] } := by
  unfold expandTargetMatch
  split
  · rename_i other present
    have same := Option.some.inj (present.symm.trans found)
    subst same
    rfl
  · rename_i absent
    rw [found] at absent
    cases absent

theorem expandTargetMatch_missing (frame : TargetMatchFrame environment outer)
    (missing : frame.state.answers[frame.cursor]? = none) :
    expandTargetMatch environment outer frame =
      if GeneralScopedMatchMachine.complete frame.state then {}
      else
        { tasks := [.targetMatch { frame with
            state := GeneralScopedMatchMachine.tick
              ⟨frame.call.context.rule, frame.call.context.spec, frame.call.context.bound.length,
                frame.call.context.site 1, [], frame.call.binders.length, frame.call.initial,
                frame.call.targetSchema, frame.target⟩ frame.state
            reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable }] } := by
  unfold expandTargetMatch
  split
  · rename_i other present
    rw [missing] at present
    cases present
  · rfl

end Matching

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
