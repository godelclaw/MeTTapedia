import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryCorrectness
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCertified
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseEventEquality
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs

/-!
# Enumerating replay as a search-cost comparison

This comparison retains the earlier enumerate-then-filter algorithm and its
soundness and finite-completeness proofs. Source proof services use guided
recipe replay instead. The enumerating procedure consumes original events
and assignments. Directed
child firings are validated recursively without a declaration-order bound.
Matching and relation queries use their existing source-valid machines.
Fuel bounds the attempted replay, not the source relation: failure at one
budget is refusal of that attempted candidate, never semantic falsity.

No new source syntax or premise semantics is introduced. Quoted syntax,
scoped child contexts, query/bag origins, duplicate quantified occurrences
and lexical parameter restoration retain their original owners.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.EnumeratingReplay

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Filter actual matcher answers by the receipt's literal bag-choice trace. -/
def matchAnswers (fuel : Nat) (request : GeneralScopedMatchMachine.Request)
    (trace : List GeneralScopedMatchMachine.BagChoice) : List Assignment :=
  ((GeneralScopedMatchMachine.run request fuel
    (GeneralScopedMatchMachine.start request)).answers.filter
      (fun answer => answer.trace == trace)).map (fun answer => answer.assignment)

theorem mem_matchAnswers (fuel : Nat) (request : GeneralScopedMatchMachine.Request)
    (trace : List GeneralScopedMatchMachine.BagChoice) (final : Assignment) :
    final ∈ matchAnswers fuel request trace ↔
      ∃ answer ∈ (GeneralScopedMatchMachine.run request fuel
        (GeneralScopedMatchMachine.start request)).answers,
        answer.trace = trace ∧ answer.assignment = final := by
  simp only [matchAnswers, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨answer, ⟨present, traced⟩, value⟩
    exact ⟨answer, present, traced, value⟩
  · rintro ⟨answer, present, traced, value⟩
    exact ⟨answer, ⟨present, traced⟩, value⟩

theorem matchAnswers_sound {fuel : Nat} {request : GeneralScopedMatchMachine.Request}
    {trace : List GeneralScopedMatchMachine.BagChoice} {final : Assignment}
    (present : final ∈ matchAnswers fuel request trace) :
    GeneralScopedMatchMachine.TracedMatches request.rule request.spec request.ambient request.site
      request.path request.depth request.initial request.schema request.target trace final := by
  obtain ⟨answer, member, traced, value⟩ := (mem_matchAnswers fuel request trace final).mp present
  have valid := GeneralScopedMatchMachine.answers_sound
    (GeneralScopedMatchMachine.reachable_run fuel .start) member
  simpa only [GeneralScopedMatchMachine.Answer.Valid, traced, value] using valid

theorem matchAnswers_mono {first last : Nat} (increase : first ≤ last)
    (request : GeneralScopedMatchMachine.Request) (trace : List GeneralScopedMatchMachine.BagChoice)
    {final : Assignment} (present : final ∈ matchAnswers first request trace) :
    final ∈ matchAnswers last request trace := by
  obtain ⟨answer, member, traced, value⟩ := (mem_matchAnswers first request trace final).mp present
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le increase
  apply (mem_matchAnswers _ request trace final).mpr
  refine ⟨answer, ?_, traced, value⟩
  rw [GeneralScopedMatchMachine.run_add]
  exact GeneralScopedMatchMachine.answers_persist_run request _ extra member

theorem matchAnswers_complete {request : GeneralScopedMatchMachine.Request}
    {trace : List GeneralScopedMatchMachine.BagChoice} {final : Assignment}
    (held : GeneralScopedMatchMachine.TracedMatches request.rule request.spec request.ambient request.site
      request.path request.depth request.initial request.schema request.target trace final) :
    ∃ fuel, final ∈ matchAnswers fuel request trace := by
  obtain ⟨fuel, _, exhaustive⟩ := GeneralScopedMatchMachine.completedEventually request
  exact ⟨fuel, (mem_matchAnswers fuel request trace final).mpr
    ⟨⟨final, trace⟩, (exhaustive ⟨final, trace⟩).mpr held, rfl, rfl⟩⟩

/-- Provider occurrence and each argument's matching origins must agree with
those retained by the original query machine. -/
def queryAnswers (fuel : Nat) (environment : Environment) (request : Query.Request)
    (rowIndex : Nat) (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) :
    List Assignment :=
  ((Query.run environment request fuel (Query.start environment request)).answers.filter
    (fun answer => answer.rowIndex == rowIndex && answer.origins == origins)).map
      (fun answer => answer.assignment)

theorem mem_queryAnswers (fuel : Nat) (environment : Environment) (request : Query.Request)
    (rowIndex : Nat) (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) (final : Assignment) :
    final ∈ queryAnswers fuel environment request rowIndex origins ↔
      ∃ answer ∈ (Query.run environment request fuel (Query.start environment request)).answers,
        answer.rowIndex = rowIndex ∧ answer.origins = origins ∧ answer.assignment = final := by
  simp only [queryAnswers, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨answer, ⟨present, row, traced⟩, value⟩
    exact ⟨answer, present, row, traced, value⟩
  · rintro ⟨answer, present, row, traced, value⟩
    exact ⟨answer, ⟨present, row, traced⟩, value⟩

theorem queryAnswers_sound {fuel : Nat} {environment : Environment} {request : Query.Request}
    {rowIndex : Nat} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)} {final : Assignment}
    (present : final ∈ queryAnswers fuel environment request rowIndex origins) :
    TracedQuery environment request.context request.relation request.arguments request.initial
      rowIndex final origins := by
  obtain ⟨answer, _, row, traced, value⟩ :=
    (mem_queryAnswers fuel environment request rowIndex origins final).mp present
  simpa only [row, traced, value] using answer.valid

theorem queryAnswers_mono {first last : Nat} (increase : first ≤ last)
    (environment : Environment) (request : Query.Request)
    (rowIndex : Nat) (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice))
    {final : Assignment} (present : final ∈ queryAnswers first environment request rowIndex origins) :
    final ∈ queryAnswers last environment request rowIndex origins := by
  obtain ⟨answer, member, row, traced, value⟩ :=
    (mem_queryAnswers first environment request rowIndex origins final).mp present
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le increase
  apply (mem_queryAnswers _ environment request rowIndex origins final).mpr
  refine ⟨answer, ?_, row, traced, value⟩
  rw [Query.run_add]
  obtain ⟨later, appended⟩ := Query.receipts_prefix environment request extra
    (Query.run environment request first (Query.start environment request))
  rw [appended]
  exact List.mem_append_left _ member

theorem queryAnswers_complete {environment : Environment} {request : Query.Request}
    {rowIndex : Nat} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)} {final : Assignment}
    (held : TracedQuery environment request.context request.relation request.arguments request.initial
      rowIndex final origins) :
    ∃ fuel, final ∈ queryAnswers fuel environment request rowIndex origins := by
  obtain ⟨fuel, _, answer, present, row, value, traced⟩ :=
    Query.traced_query_eventually MatchingExecution.ordinaryCursorLaws
      MatchingExecution.ordinaryCursorCost MatchingExecution.ordinary_answer_representation environment request held
  exact ⟨fuel, (mem_queryAnswers fuel environment request rowIndex origins final).mpr
    ⟨answer, present, row, traced, value⟩⟩


private theorem traced_match_eventually {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial : Assignment} {schema target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {final : Assignment}
    (held : GeneralScopedMatchMachine.TracedMatches rule spec ambient site path depth initial
      schema target trace final) :
    ∃ fuel, final ∈ matchAnswers fuel
      ⟨rule, spec, ambient, site, path, depth, initial, schema, target⟩ trace :=
  matchAnswers_complete (request := ⟨rule, spec, ambient, site, path, depth, initial, schema, target⟩) held

private theorem traced_query_eventually {environment : Environment} {context : Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : TracedQuery environment context relation arguments initial rowIndex final origins) :
    ∃ fuel, final ∈ queryAnswers fuel environment ⟨context, relation, arguments, initial⟩ rowIndex origins :=
  queryAnswers_complete (request := ⟨context, relation, arguments, initial⟩) held


mutual
/-- Check a recorded finite directed firing. Recursive child declaration
indices are unrestricted; every recursive attempt consumes replay fuel. -/
def root : Nat → (environment : Environment) → (bound : List TypeExpr) → TypeExpr → Pattern → Nat →
    List GeneralScopedMatchMachine.BagChoice → Assignment → Assignment → List Event → Pattern → Bool
  | 0, _, _, _, _, _, _, _, _, _, _ => false
  | fuel + 1, environment, bound, type, source, index, trace, captured, completed, history, target =>
      match environment.language.rewrites[index]?, specification? environment index with
      | some rule, some spec =>
          admittedFor rule spec &&
          checkOpenPatternWellSorted environment.language environment.free bound type source &&
          decide (captured ∈ matchAnswers fuel
            ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩ trace) &&
          checkTypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured &&
          decide (completed ∈ premises fuel environment ⟨index, rule, spec, bound, 0, 0⟩
            rule.premises captured history) &&
          decide (reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
            rule spec bound.length completed = some target) &&
          checkOpenPatternWellSorted environment.language environment.free bound type target
      | _, _ => false

/-- Replay one original event and compute all compatible intermediate
assignments. Provider and matcher alternatives retain their literal origins. -/
def premise : Nat → Environment → Context → Premise → Assignment → Event → List Assignment
  | 0, _, _, _, _, _ => []
  | fuel + 1, environment, context, .relationQuery relation arguments, initial,
      .query p q row origins =>
      if p = context.premiseIndex ∧ q = context.quantifierDepth then
        queryAnswers fuel environment ⟨context, relation, arguments, initial⟩ row origins
      else []
  | _fuel + 1, _environment, context, .freshness condition, initial,
      .freshness p q atom subject =>
      if p = context.premiseIndex ∧ q = context.quantifierDepth ∧
          freshnessSubject? context.rule context.spec context.bound context.premiseIndex
            context.quantifierDepth initial condition = some (atom, subject) ∧
          Substitution.isFresh atom subject = true then [initial]
      else []
  | fuel + 1, environment, context, .congruence source target, initial,
      .child p q childIndex bound actualSource actualTarget trace targetTrace captured completed history =>
      match sourceType? environment.language context.rule source with
      | none => []
      | some type =>
          if p = context.premiseIndex ∧ q = context.quantifierDepth ∧ bound = context.bound ∧
              instantiateAt? context.rule context.spec context.bound.length (context.site 0) [] 0
                initial source = some actualSource ∧
              root fuel environment context.bound type actualSource childIndex trace captured completed
                history actualTarget = true then
            (matchAnswers fuel ⟨context.rule, context.spec, context.bound.length, context.site 1,
              [], 0, initial, target, actualTarget⟩ targetTrace).filter
                (checkTypedAssignment environment context)
          else []
  | fuel + 1, environment, context, .scopedStep step, initial,
      .child p q childIndex bound actualSource actualTarget trace targetTrace captured completed history =>
      if p = context.premiseIndex ∧ q = context.quantifierDepth ∧
          bound = step.binders ++ context.bound ∧
          instantiateAt? context.rule context.spec context.bound.length (context.site 0) []
            step.binders.length initial step.source = some actualSource ∧
          root fuel environment (step.binders ++ context.bound) step.resultType actualSource childIndex
            trace captured completed history actualTarget = true then
        (matchAnswers fuel ⟨context.rule, context.spec, context.bound.length, context.site 1,
          [], step.binders.length, initial, step.target, actualTarget⟩ targetTrace).filter
            (checkTypedAssignment environment context)
      else []
  | fuel + 1, environment, context, .forAll collection parameter body, initial,
      .quantified p q kind history =>
      match finiteCollection? context.bound.length initial collection with
      | none => []
      | some (actualKind, elements) =>
          if p = context.premiseIndex ∧ q = context.quantifierDepth ∧ actualKind = kind then
            quantified fuel environment context parameter body 0 elements initial history
          else []
  | _ + 1, _, _, _, _, _ => []

/-- The receipt stores an event at every authored premise position. Missing
or extra history never supplies an implicit premise. -/
def premises : Nat → Environment → Context → List Premise → Assignment → List Event → List Assignment
  | 0, _, _, _, _, _ => []
  | _ + 1, _, _, [], initial, [] => [initial]
  | fuel + 1, environment, context, first :: later, initial, event :: events =>
      (premise fuel environment context first initial event).flatMap
        (fun middle => premises fuel environment context.next later middle events)
  | _ + 1, _, _, _, _, _ => []

/-- Quantifier occurrences retain exact indices, exact elements and one
actual child event. The lexical parameter is restored after each body. -/
def quantified : Nat → Environment → Context → String → Premise → Nat → List Pattern →
    Assignment → List (Nat × Pattern × List Event) → List Assignment
  | 0, _, _, _, _, _, _, _, _ => []
  | _ + 1, _, _, _, _, _, [], initial, [] => [initial]
  | fuel + 1, environment, context, parameter, body, index, element :: elements, initial,
      (recordedIndex, recordedElement, [event]) :: events =>
      if recordedIndex = index ∧ recordedElement = element ∧
          checkTypedAssignment environment context.quantified
            (bindParameter parameter (localValue context.bound element) initial) = true then
        (premise fuel environment context.quantified body
          (bindParameter parameter (localValue context.bound element) initial) event).flatMap
          (fun _middle => quantified fuel environment context parameter body (index + 1) elements
            initial events)
      else []
  | _ + 1, _, _, _, _, _, _, _, _ => []
end


mutual
 theorem root_sound {fuel : Nat} {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (checked : root fuel environment bound type source index trace captured completed history target = true) :
    RootFiring environment bound type source index trace captured completed history target := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases declared : environment.language.rewrites[index]? with
      | none => simp only [root, declared] at checked; cases checked
      | some rule =>
          cases specified : specification? environment index with
          | none => simp only [root, declared, specified] at checked; cases checked
          | some spec =>
              simp only [root, declared, specified, Bool.and_eq_true, decide_eq_true_eq] at checked
              rcases checked with ⟨⟨⟨⟨⟨⟨admitted, sorted⟩, matched⟩, capturedTyped⟩, body⟩, targetRead⟩, targetTyped⟩
              exact .fire declared specified admitted (checkOpenPatternWellSorted_sound sorted)
                (matchAnswers_sound matched) (checkTypedAssignment_sound capturedTyped)
                (premises_sound body) targetRead (checkOpenPatternWellSorted_sound targetTyped)
 termination_by fuel

 theorem premise_sound {fuel : Nat} {environment : Environment} {context : Context}
    {body : Premise} {initial final : Assignment} {event : Event}
    (present : final ∈ premise fuel environment context body initial event) :
    PremiseHolds environment context body initial final event := by
  cases fuel with
  | zero => simp only [premise, List.not_mem_nil] at present
  | succ fuel =>
      cases body with
      | relationQuery relation arguments =>
          cases event <;> simp only [premise, List.not_mem_nil] at present
          split at present
          · rename_i metadata
            rcases metadata with ⟨rfl, rfl⟩
            exact .query (queryAnswers_sound present)
          · simp only [List.not_mem_nil] at present
      | freshness condition =>
          cases event <;> simp only [premise, List.not_mem_nil] at present
          split at present
          · rename_i metadata
            rcases metadata with ⟨rfl, rfl, interpreted, fresh⟩
            simp only [List.mem_singleton] at present
            subst final
            exact .freshness interpreted ((syntactic_freshness_iff _ _).mp fresh)
          · simp only [List.not_mem_nil] at present
      | congruence source target =>
          cases event <;> simp only [premise, List.not_mem_nil] at present
          split at present
          · simp only [List.not_mem_nil] at present
          · rename_i type typed
            split at present
            · rename_i metadata
              rcases metadata with ⟨rfl, rfl, rfl, interpreted, child⟩
              rcases List.mem_filter.mp present with ⟨matched, finalTyped⟩
              exact .step typed interpreted (root_sound child) (matchAnswers_sound matched)
                (checkTypedAssignment_sound finalTyped)
            · simp only [List.not_mem_nil] at present
      | scopedStep step =>
          cases event <;> simp only [premise, List.not_mem_nil] at present
          split at present
          · rename_i metadata
            rcases metadata with ⟨rfl, rfl, rfl, interpreted, child⟩
            rcases List.mem_filter.mp present with ⟨matched, finalTyped⟩
            exact .scopedStep interpreted (root_sound child) (matchAnswers_sound matched)
              (checkTypedAssignment_sound finalTyped)
          · simp only [List.not_mem_nil] at present
      | forAll collection parameter body =>
          cases event <;> simp only [premise, List.not_mem_nil] at present
          split at present
          · simp only [List.not_mem_nil] at present
          · rename_i actualKind elements interpreted
            split at present
            · rename_i metadata
              rcases metadata with ⟨rfl, rfl, rfl⟩
              exact .quantified interpreted (quantified_sound present)
            · simp only [List.not_mem_nil] at present
 termination_by fuel

 theorem premises_sound {fuel : Nat} {environment : Environment} {context : Context}
    {bodies : List Premise} {initial final : Assignment} {events : List Event}
    (present : final ∈ premises fuel environment context bodies initial events) :
    PremisesHold environment context bodies initial final events := by
  cases fuel with
  | zero => simp only [premises, List.not_mem_nil] at present
  | succ fuel =>
      cases bodies with
      | nil =>
          cases events with
          | nil =>
              simp only [premises, List.mem_singleton] at present
              subst final
              exact .nil
          | cons event events => simp only [premises, List.not_mem_nil] at present
      | cons body bodies =>
          cases events with
          | nil => simp only [premises, List.not_mem_nil] at present
          | cons event events =>
              obtain ⟨middle, head, tail⟩ := List.mem_flatMap.mp present
              exact .cons (premise_sound head) (premises_sound tail)
 termination_by fuel

 theorem quantified_sound {fuel : Nat} {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List Event)}
    (present : final ∈ quantified fuel environment context parameter body index elements initial events) :
    QuantifiedElements environment context parameter body index elements initial final events := by
  cases fuel with
  | zero => simp only [quantified, List.not_mem_nil] at present
  | succ fuel =>
      cases elements with
      | nil =>
          cases events with
          | nil =>
              simp only [quantified, List.mem_singleton] at present
              subst final
              exact .nil
          | cons entry events => simp only [quantified, List.not_mem_nil] at present
      | cons element elements =>
          cases events with
          | nil => simp only [quantified, List.not_mem_nil] at present
          | cons entry events =>
              rcases entry with ⟨recordedIndex, recordedElement, childEvents⟩
              cases childEvents with
              | nil => simp only [quantified, List.not_mem_nil] at present
              | cons event childEvents =>
                  cases childEvents with
                  | cons _ _ => simp only [quantified, List.not_mem_nil] at present
                  | nil =>
                      simp only [quantified] at present
                      split at present
                      · rename_i metadata
                        rcases metadata with ⟨rfl, rfl, localTyped⟩
                        obtain ⟨middle, head, tail⟩ := List.mem_flatMap.mp present
                        exact .cons (checkTypedAssignment_sound localTyped)
                          (premise_sound head) (quantified_sound tail)
                      · simp only [List.not_mem_nil] at present
 termination_by fuel
end


mutual
 theorem root_mono_one {fuel : Nat} {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (checked : root fuel environment bound type source index trace captured completed history target = true) :
    root (fuel + 1) environment bound type source index trace captured completed history target = true := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases declared : environment.language.rewrites[index]? with
      | none => simp only [root, declared] at checked; cases checked
      | some rule =>
          cases specified : specification? environment index with
          | none => simp only [root, declared, specified] at checked; cases checked
          | some spec =>
              simp only [root, declared, specified, Bool.and_eq_true, decide_eq_true_eq] at checked ⊢
              rcases checked with ⟨⟨⟨⟨⟨⟨admitted, sorted⟩, matched⟩, capturedTyped⟩, body⟩, targetRead⟩, targetTyped⟩
              exact ⟨⟨⟨⟨⟨⟨admitted, sorted⟩,
                matchAnswers_mono (Nat.le_succ fuel) _ _ matched⟩, capturedTyped⟩,
                premises_mono_one body⟩, targetRead⟩, targetTyped⟩
 termination_by fuel

 theorem premise_mono_one {fuel : Nat} {environment : Environment} {context : Context}
    {body : Premise} {initial final : Assignment} {event : Event}
    (present : final ∈ premise fuel environment context body initial event) :
    final ∈ premise (fuel + 1) environment context body initial event := by
  cases fuel with
  | zero => simp only [premise, List.not_mem_nil] at present
  | succ fuel =>
      cases body with
      | relationQuery relation arguments =>
          cases event <;> simp only [premise, List.not_mem_nil] at present
          split at present
          · rename_i metadata
            simp only [premise, if_pos metadata]
            exact queryAnswers_mono (Nat.le_succ fuel) _ _ _ _ present
          · simp only [List.not_mem_nil] at present
      | freshness condition =>
          cases event <;> simp only [premise, List.not_mem_nil] at present
          simpa only [premise] using present
      | congruence source target =>
          cases event <;> simp only [premise, List.not_mem_nil] at present
          split at present
          · simp only [List.not_mem_nil] at present
          · rename_i type typed
            split at present
            · rename_i metadata
              have child := root_mono_one metadata.2.2.2.2
              rcases List.mem_filter.mp present with ⟨matched, finalTyped⟩
              have larger := And.intro metadata.1 (And.intro metadata.2.1
                (And.intro metadata.2.2.1 (And.intro metadata.2.2.2.1 child)))
              simp only [premise, typed, if_pos larger]
              exact List.mem_filter.mpr ⟨matchAnswers_mono (Nat.le_succ fuel) _ _ matched, finalTyped⟩
            · simp only [List.not_mem_nil] at present
      | scopedStep step =>
          cases event <;> simp only [premise, List.not_mem_nil] at present
          split at present
          · rename_i metadata
            have child := root_mono_one metadata.2.2.2.2
            rcases List.mem_filter.mp present with ⟨matched, finalTyped⟩
            have larger := And.intro metadata.1 (And.intro metadata.2.1
              (And.intro metadata.2.2.1 (And.intro metadata.2.2.2.1 child)))
            simp only [premise, if_pos larger]
            exact List.mem_filter.mpr ⟨matchAnswers_mono (Nat.le_succ fuel) _ _ matched, finalTyped⟩
          · simp only [List.not_mem_nil] at present
      | forAll collection parameter body =>
          cases event <;> simp only [premise, List.not_mem_nil] at present
          split at present
          · simp only [List.not_mem_nil] at present
          · rename_i actualKind elements interpreted
            split at present
            · rename_i metadata
              simp only [premise, interpreted, if_pos metadata]
              exact quantified_mono_one present
            · simp only [List.not_mem_nil] at present
 termination_by fuel

 theorem premises_mono_one {fuel : Nat} {environment : Environment} {context : Context}
    {bodies : List Premise} {initial final : Assignment} {events : List Event}
    (present : final ∈ premises fuel environment context bodies initial events) :
    final ∈ premises (fuel + 1) environment context bodies initial events := by
  cases fuel with
  | zero => simp only [premises, List.not_mem_nil] at present
  | succ fuel =>
      cases bodies with
      | nil =>
          cases events with
          | nil => simpa only [premises] using present
          | cons event events => simp only [premises, List.not_mem_nil] at present
      | cons body bodies =>
          cases events with
          | nil => simp only [premises, List.not_mem_nil] at present
          | cons event events =>
              obtain ⟨middle, head, tail⟩ := List.mem_flatMap.mp present
              exact List.mem_flatMap.mpr ⟨middle, premise_mono_one head, premises_mono_one tail⟩
 termination_by fuel

 theorem quantified_mono_one {fuel : Nat} {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List Event)}
    (present : final ∈ quantified fuel environment context parameter body index elements initial events) :
    final ∈ quantified (fuel + 1) environment context parameter body index elements initial events := by
  cases fuel with
  | zero => simp only [quantified, List.not_mem_nil] at present
  | succ fuel =>
      cases elements with
      | nil =>
          cases events with
          | nil => simpa only [quantified] using present
          | cons entry events => simp only [quantified, List.not_mem_nil] at present
      | cons element elements =>
          cases events with
          | nil => simp only [quantified, List.not_mem_nil] at present
          | cons entry events =>
              rcases entry with ⟨recordedIndex, recordedElement, childEvents⟩
              cases childEvents with
              | nil => simp only [quantified, List.not_mem_nil] at present
              | cons event childEvents =>
                  cases childEvents with
                  | cons _ _ => simp only [quantified, List.not_mem_nil] at present
                  | nil =>
                      simp only [quantified] at present
                      split at present
                      · rename_i metadata
                        obtain ⟨middle, head, tail⟩ := List.mem_flatMap.mp present
                        simp only [quantified, if_pos metadata]
                        exact List.mem_flatMap.mpr
                          ⟨middle, premise_mono_one head, quantified_mono_one tail⟩
                      · simp only [List.not_mem_nil] at present
 termination_by fuel
end

 theorem root_mono {first last : Nat} (increase : first ≤ last)
    {environment : Environment} {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
    {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event}
    (checked : root first environment bound type source index trace captured completed history target = true) :
    root last environment bound type source index trace captured completed history target = true := by
  induction last, increase using Nat.le_induction with
  | base => exact checked
  | succ _ _ ih => exact root_mono_one ih

 theorem premise_mono {first last : Nat} (increase : first ≤ last)
    {environment : Environment} {context : Context} {body : Premise}
    {initial final : Assignment} {event : Event}
    (present : final ∈ premise first environment context body initial event) :
    final ∈ premise last environment context body initial event := by
  induction last, increase using Nat.le_induction with
  | base => exact present
  | succ _ _ ih => exact premise_mono_one ih

 theorem premises_mono {first last : Nat} (increase : first ≤ last)
    {environment : Environment} {context : Context} {bodies : List Premise}
    {initial final : Assignment} {events : List Event}
    (present : final ∈ premises first environment context bodies initial events) :
    final ∈ premises last environment context bodies initial events := by
  induction last, increase using Nat.le_induction with
  | base => exact present
  | succ _ _ ih => exact premises_mono_one ih

 theorem quantified_mono {first last : Nat} (increase : first ≤ last)
    {environment : Environment} {context : Context} {parameter : String} {body : Premise}
    {index : Nat} {elements : List Pattern} {initial final : Assignment}
    {events : List (Nat × Pattern × List Event)}
    (present : final ∈ quantified first environment context parameter body index elements initial events) :
    final ∈ quantified last environment context parameter body index elements initial events := by
  induction last, increase using Nat.le_induction with
  | base => exact present
  | succ _ _ ih => exact quantified_mono_one ih


mutual
/-- Completeness ranges over every independently derived finite firing;
there is no declaration stratification or bound on the selected child index. -/
 theorem root_complete {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (held : RootFiring environment bound type source index trace captured completed history target) :
    ∃ fuel, root fuel environment bound type source index trace captured completed history target = true :=
  match held with
  | .fire declared specified admitted sorted matched capturedTyped body targetRead targetTyped => by
      obtain ⟨matcherFuel, matching⟩ := traced_match_eventually matched
      obtain ⟨bodyFuel, bodyPresent⟩ := premises_complete body
      refine ⟨max matcherFuel bodyFuel + 1, ?_⟩
      simp only [root, declared, specified, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨⟨admitted, checkOpenPatternWellSorted_complete sorted⟩,
        matchAnswers_mono (Nat.le_max_left _ _) _ _ matching⟩,
        checkTypedAssignment_complete capturedTyped⟩,
        premises_mono (Nat.le_max_right _ _) bodyPresent⟩, targetRead⟩,
        checkOpenPatternWellSorted_complete targetTyped⟩

 termination_by structural held

 theorem premise_complete {environment : Environment} {context : Context}
    {body : Premise} {initial final : Assignment} {event : Event}
    (held : PremiseHolds environment context body initial final event) :
    ∃ fuel, final ∈ premise fuel environment context body initial event :=
  match held with
  | .query query => by
      obtain ⟨fuel, present⟩ := traced_query_eventually query
      refine ⟨fuel + 1, ?_⟩
      simpa [premise] using present
  | .freshness interpreted fresh => by
      refine ⟨1, ?_⟩
      simp [premise, interpreted, (syntactic_freshness_iff _ _).mpr fresh]
  | .step typed interpreted child matched finalTyped => by
      obtain ⟨childFuel, childAccepted⟩ := root_complete child
      obtain ⟨matcherFuel, matching⟩ := traced_match_eventually matched
      refine ⟨max childFuel matcherFuel + 1, ?_⟩
      have childLater := root_mono (Nat.le_max_left childFuel matcherFuel) childAccepted
      simp only [premise, typed]
      split
      · exact List.mem_filter.mpr ⟨matchAnswers_mono (Nat.le_max_right childFuel matcherFuel) _ _ matching,
          checkTypedAssignment_complete finalTyped⟩
      · rename_i denied
        exact (denied ⟨trivial, trivial, trivial, interpreted, childLater⟩).elim
  | .scopedStep interpreted child matched finalTyped => by
      obtain ⟨childFuel, childAccepted⟩ := root_complete child
      obtain ⟨matcherFuel, matching⟩ := traced_match_eventually matched
      refine ⟨max childFuel matcherFuel + 1, ?_⟩
      have childLater := root_mono (Nat.le_max_left childFuel matcherFuel) childAccepted
      simp only [premise]
      split
      · exact List.mem_filter.mpr ⟨matchAnswers_mono (Nat.le_max_right childFuel matcherFuel) _ _ matching,
          checkTypedAssignment_complete finalTyped⟩
      · rename_i denied
        exact (denied ⟨trivial, trivial, trivial, interpreted, childLater⟩).elim
  | .quantified interpreted elements => by
      obtain ⟨fuel, present⟩ := quantified_complete elements
      refine ⟨fuel + 1, ?_⟩
      simpa [premise, interpreted] using present

 termination_by structural held

 theorem premises_complete {environment : Environment} {context : Context}
    {bodies : List Premise} {initial final : Assignment} {events : List Event}
    (held : PremisesHold environment context bodies initial final events) :
    ∃ fuel, final ∈ premises fuel environment context bodies initial events :=
  match held with
  | .nil => by exact ⟨1, List.mem_singleton_self _⟩
  | .cons head tail => by
      obtain ⟨headFuel, before⟩ := premise_complete head
      obtain ⟨tailFuel, after⟩ := premises_complete tail
      refine ⟨max headFuel tailFuel + 1, List.mem_flatMap.mpr ?_⟩
      exact ⟨_, premise_mono (Nat.le_max_left _ _) before,
        premises_mono (Nat.le_max_right _ _) after⟩

 termination_by structural held

 theorem quantified_complete {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List Event)}
    (held : QuantifiedElements environment context parameter body index elements initial final events) :
    ∃ fuel, final ∈ quantified fuel environment context parameter body index elements initial events :=
  match held with
  | .nil => by exact ⟨1, List.mem_singleton_self _⟩
  | .cons localTyped head tail => by
      obtain ⟨headFuel, before⟩ := premise_complete head
      obtain ⟨tailFuel, after⟩ := quantified_complete tail
      refine ⟨max headFuel tailFuel + 1, ?_⟩
      simp only [quantified]
      split
      · exact List.mem_flatMap.mpr ⟨_, premise_mono (Nat.le_max_left headFuel tailFuel) before,
          quantified_mono (Nat.le_max_right headFuel tailFuel) after⟩
      · rename_i denied
        exact (denied ⟨trivial, trivial, checkTypedAssignment_complete localTyped⟩).elim
 termination_by structural held
end

/-- The original semantic firing relation is exactly the union of all finite
replay budgets. An individual false result is not a refutation. -/
theorem root_exact {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event} :
    RootFiring environment bound type source index trace captured completed history target ↔
      ∃ fuel, root fuel environment bound type source index trace captured completed history target = true :=
  ⟨root_complete, fun ⟨_, checked⟩ => root_sound checked⟩

theorem premise_exact {environment : Environment} {context : Context}
    {body : Premise} {initial final : Assignment} {event : Event} :
    PremiseHolds environment context body initial final event ↔
      ∃ fuel, final ∈ premise fuel environment context body initial event :=
  ⟨premise_complete, fun ⟨_, present⟩ => premise_sound present⟩

theorem premises_exact {environment : Environment} {context : Context}
    {bodies : List Premise} {initial final : Assignment} {events : List Event} :
    PremisesHold environment context bodies initial final events ↔
      ∃ fuel, final ∈ premises fuel environment context bodies initial events :=
  ⟨premises_complete, fun ⟨_, present⟩ => premises_sound present⟩

theorem quantified_exact {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List Event)} :
    QuantifiedElements environment context parameter body index elements initial final events ↔
      ∃ fuel, final ∈ quantified fuel environment context parameter body index elements initial events :=
  ⟨quantified_complete, fun ⟨_, present⟩ => quantified_sound present⟩


/-! ## Original typed occurrence receipts -/

open GeneralExecutionAdmission GeneralTypedSites

private def ruleFields (rule : RewriteRule) :=
  (rule.name, rule.typeContext, rule.premises, rule.left, rule.right, rule.bindings)

private theorem ruleFields_injective : Function.Injective ruleFields := by
  intro first second same
  cases first
  cases second
  simp only [ruleFields, Prod.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

/-- Compare every original declaration field, including origin index,
binding plan and the complete authored rule rather than its elaborated RHS. -/
private def samePlan (first second : RulePlan) : Bool :=
  decide (first.declarationIndex = second.declarationIndex ∧
    first.authored.name = second.authored.name ∧
    first.authored.typeContext = second.authored.typeContext ∧
    first.authored.premises = second.authored.premises ∧
    first.authored.left = second.authored.left ∧
    first.authored.right = second.authored.right ∧
    first.authored.bindings = second.authored.bindings ∧ first.binding = second.binding)

private theorem samePlan_exact (first second : RulePlan) : samePlan first second = true ↔ first = second := by
  simp only [samePlan, decide_eq_true_eq]
  constructor
  · rintro ⟨index, name, types, premises, left, right, bindings, binding⟩
    have rules : first.authored = second.authored := ruleFields_injective (by
      simp only [ruleFields, Prod.mk.injEq]
      exact ⟨name, types, premises, left, right, bindings⟩)
    cases first
    cases second
    dsimp only at index binding rules
    subst_vars
    rfl
  · intro same
    subst second
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def sameJob (first second : GeneralRuleJobs.Job) : Bool :=
  decide (first.ordinal = second.ordinal) && samePlan first.declaration second.declaration &&
    decide (first.site = second.site)

private theorem sameJob_exact (first second : GeneralRuleJobs.Job) :
    sameJob first second = true ↔ first = second := by
  simp only [sameJob, Bool.and_eq_true, decide_eq_true_eq, samePlan_exact]
  constructor
  · rintro ⟨⟨ordinal, declaration⟩, site⟩
    cases first
    cases second
    dsimp only at ordinal declaration site
    subst_vars
    rfl
  · intro same
    subst second
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- Validate actual selected declaration membership and every original typed
occurrence field against the existing job generator. -/
def checkJob (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (job : GeneralRuleJobs.Job) : Bool :=
  (GeneralRuleJobs.jobs plan bound type source).any (fun selected => sameJob selected job)

theorem checkJob_exact (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (job : GeneralRuleJobs.Job) :
    checkJob plan bound type source job = true ↔ job.Valid plan bound type source := by
  simp only [checkJob, List.any_eq_true, sameJob_exact]
  constructor
  · rintro ⟨selected, present, rfl⟩
    exact (GeneralRuleJobs.jobs_spec plan bound type source selected).mp present
  · intro valid
    exact ⟨job, (GeneralRuleJobs.jobs_spec plan bound type source job).mpr valid, rfl⟩

/-- Check the original receipt directly. This does not require the separate
runner's global child-stratification/readiness condition. The selected rule,
site, source/target typing and complete local history are all checked. -/
def receipt (fuel : Nat) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (value : GeneralRuleJobs.Receipt) : Bool :=
  let environment := GeneralPlanEnvironment.environmentWith plan dynamic
  checkJob plan bound type source value.job &&
    root fuel environment value.job.site.focusBound value.job.site.focusType value.job.site.focus
      value.job.ordinal value.matcherTrace value.captured value.completed value.premiseHistory value.localTarget &&
    value.job.site.acceptsReplacementRepresentation environment.language value.localTarget &&
    decide (value.target = value.job.site.context.fill value.localTarget) &&
    checkOpenPatternWellSorted environment.language plan.snapshot.free bound type value.target

theorem receipt_sound {fuel : Nat} {dynamic : DynamicProvider} {plan : Plan}
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {value : GeneralRuleJobs.Receipt}
    (checked : receipt fuel dynamic plan bound type source value = true) :
    value.ValidWith dynamic plan bound type source := by
  simp only [receipt, Bool.and_eq_true, decide_eq_true_eq] at checked
  rcases checked with ⟨⟨⟨⟨job, firing⟩, represented⟩, target⟩, typed⟩
  exact ⟨(checkJob_exact plan bound type source value.job).mp job, root_sound firing,
    represented, target, checkOpenPatternWellSorted_sound typed⟩

theorem receipt_complete {dynamic : DynamicProvider} {plan : Plan}
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {value : GeneralRuleJobs.Receipt}
    (valid : value.ValidWith dynamic plan bound type source) :
    ∃ fuel, receipt fuel dynamic plan bound type source value = true := by
  obtain ⟨fuel, firing⟩ := root_complete valid.2.1
  refine ⟨fuel, ?_⟩
  simp only [receipt, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨(checkJob_exact plan bound type source value.job).mpr valid.1, firing⟩,
    valid.2.2.1⟩, valid.2.2.2.1⟩, checkOpenPatternWellSorted_complete valid.2.2.2.2⟩

theorem receipt_exact (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (value : GeneralRuleJobs.Receipt) :
    value.ValidWith dynamic plan bound type source ↔
      ∃ fuel, receipt fuel dynamic plan bound type source value = true :=
  ⟨receipt_complete, fun ⟨_, checked⟩ => receipt_sound checked⟩

theorem receipt_mono {first last : Nat} (increase : first ≤ last)
    {dynamic : DynamicProvider} {plan : Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {value : GeneralRuleJobs.Receipt}
    (checked : receipt first dynamic plan bound type source value = true) :
    receipt last dynamic plan bound type source value = true := by
  simp only [receipt, Bool.and_eq_true, decide_eq_true_eq] at checked ⊢
  rcases checked with ⟨⟨⟨⟨job, firing⟩, represented⟩, target⟩, typed⟩
  exact ⟨⟨⟨⟨job, root_mono increase firing⟩, represented⟩, target⟩, typed⟩


/-! ## Total validation of each fixed finite receipt -/

/-- The existing matcher is drained at its actual finite agenda measure.
This is a computable scheduling bound, not a physical execution clock. -/
def matchFuel (request : GeneralScopedMatchMachine.Request) : Nat :=
  GeneralScopedMatchMachine.agendaCost request (GeneralScopedMatchMachine.start request).agenda

private theorem match_drains (request : GeneralScopedMatchMachine.Request)
    (fuel : Nat) (state : GeneralScopedMatchMachine.State)
    (enough : GeneralScopedMatchMachine.agendaCost request state.agenda ≤ fuel) :
    GeneralScopedMatchMachine.complete (GeneralScopedMatchMachine.run request fuel state) = true := by
  induction fuel generalizing state with
  | zero =>
      by_cases ready : GeneralScopedMatchMachine.complete state = true
      · exact ready
      · have decreased := GeneralScopedMatchMachine.tick_cost (request := request)
          (state := state) (Bool.eq_false_iff.mpr ready)
        omega
  | succ fuel ih =>
      by_cases ready : GeneralScopedMatchMachine.complete state = true
      · have idle := (GeneralScopedMatchMachine.complete_eq_true_iff state).mp ready
        have same : GeneralScopedMatchMachine.tick request state = state := by
          simp only [GeneralScopedMatchMachine.tick, idle]
        simpa only [GeneralScopedMatchMachine.run, same] using ih state (by simp only [idle, GeneralScopedMatchMachine.agendaCost_nil]; omega)
      · have decreased := GeneralScopedMatchMachine.tick_cost (request := request)
          (state := state) (Bool.eq_false_iff.mpr ready)
        exact ih _ (by omega)

theorem matchFuel_complete {request : GeneralScopedMatchMachine.Request}
    {trace : List GeneralScopedMatchMachine.BagChoice} {final : Assignment}
    (held : GeneralScopedMatchMachine.TracedMatches request.rule request.spec request.ambient request.site
      request.path request.depth request.initial request.schema request.target trace final) :
    final ∈ matchAnswers (matchFuel request) request trace := by
  apply (mem_matchAnswers _ request trace final).mpr
  refine ⟨⟨final, trace⟩, ?_, rfl, rfl⟩
  exact GeneralScopedMatchMachine.answers_complete
    (GeneralScopedMatchMachine.reachable_run _ .start)
    (match_drains request _ _ (Nat.le_refl _)) held

/-- The original finite provider/query agenda includes matching and dynamic
provider rows. Its measure supplies termination of a fixed query replay. -/
def queryFuel (environment : Environment) (request : Query.Request) : Nat :=
  Query.agendaCost MatchingExecution.ordinaryCursorCost environment request (Query.start environment request).agenda

private theorem query_drains (environment : Environment) (request : Query.Request)
    (fuel : Nat) (state : Query.State environment request)
    (enough : Query.agendaCost MatchingExecution.ordinaryCursorCost environment request state.agenda ≤ fuel) :
    (Query.run environment request fuel state).agenda = [] := by
  induction fuel generalizing state with
  | zero =>
      by_cases ready : state.agenda = []
      · exact ready
      · have decreased := Query.tick_cost MatchingExecution.ordinaryCursorCost environment request state ready
        omega
  | succ fuel ih =>
      by_cases ready : state.agenda = []
      · have same : Query.tick environment request state = state := by
          simp only [Query.tick, Scheduler.tick, ready]
        change (Query.run environment request fuel (Query.tick environment request state)).agenda = []
        rw [same]
        exact ih state (by simp only [ready, Query.agendaCost_nil]; omega)
      · have decreased := Query.tick_cost MatchingExecution.ordinaryCursorCost environment request state ready
        exact ih _ (by
          change Query.agendaCost MatchingExecution.ordinaryCursorCost environment request (Query.tick environment request state).agenda ≤ fuel
          omega)

theorem queryFuel_complete {environment : Environment} {request : Query.Request}
    {rowIndex : Nat} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)} {final : Assignment}
    (held : TracedQuery environment request.context request.relation request.arguments request.initial
      rowIndex final origins) :
    final ∈ queryAnswers (queryFuel environment request) environment request rowIndex origins := by
  apply (mem_queryAnswers _ environment request rowIndex origins final).mpr
  refine ⟨⟨rowIndex, final, origins, held⟩, ?_, rfl, rfl, rfl⟩
  exact Query.answers_complete MatchingExecution.ordinaryCursorLaws MatchingExecution.ordinary_answer_representation environment request _ _
    (query_drains environment request _ _ (Nat.le_refl _))


private def greatest : List Nat → Nat
  | [] => 0
  | first :: rest => max first (greatest rest)

private theorem le_greatest {values : List Nat} {value : Nat} (present : value ∈ values) :
    value ≤ greatest values := by
  induction values with
  | nil => cases present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

mutual
/-- Compute sufficient replay fuel from the actual finite child histories.
Intermediate assignments are generated by the existing checker; no unknown
assignment or semantic oracle is inserted. -/
def rootFuel (environment : Environment) (bound : List TypeExpr) (_type : TypeExpr)
    (source : Pattern) (index : Nat) (_trace : List GeneralScopedMatchMachine.BagChoice)
    (captured _completed : Assignment) (history : List Event) (_target : Pattern) : Nat :=
  match environment.language.rewrites[index]?, specification? environment index with
  | some rule, some spec =>
      max (matchFuel ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩)
        (premisesFuel environment ⟨index, rule, spec, bound, 0, 0⟩ rule.premises captured history) + 1
  | _, _ => 1
termination_by 4 * sizeOf history + 3

/-- Every primitive matcher/query is fully drained. A child firing consumes
its literal finite subhistory, regardless of its declaration index. -/
def premiseFuel (environment : Environment) (context : Context) (body : Premise)
    (initial : Assignment) (event : Event) : Nat :=
  match body, event with
  | .relationQuery relation arguments, .query _ _ _ _ =>
      queryFuel environment ⟨context, relation, arguments, initial⟩ + 1
  | .congruence source target,
      .child _ _ childIndex _ actualSource actualTarget trace _targetTrace captured completed history =>
      match sourceType? environment.language context.rule source with
      | none => 1
      | some type =>
          max (rootFuel environment context.bound type actualSource childIndex trace captured completed history actualTarget)
            (matchFuel ⟨context.rule, context.spec, context.bound.length, context.site 1,
              [], 0, initial, target, actualTarget⟩) + 1
  | .scopedStep step,
      .child _ _ childIndex _ actualSource actualTarget trace _targetTrace captured completed history =>
      max (rootFuel environment (step.binders ++ context.bound) step.resultType actualSource childIndex
          trace captured completed history actualTarget)
        (matchFuel ⟨context.rule, context.spec, context.bound.length, context.site 1,
          [], step.binders.length, initial, step.target, actualTarget⟩) + 1
  | .forAll collection parameter inner, .quantified _ _ _ history =>
      match finiteCollection? context.bound.length initial collection with
      | none => 1
      | some (_, elements) => quantifiedFuel environment context parameter inner 0 elements initial history + 1
  | _, _ => 1
termination_by 4 * sizeOf event + 1

/-- Tail bounds range over every actually produced head assignment. This
preserves implicit intermediate assignments and duplicate finite answers. -/
def premisesFuel (environment : Environment) (context : Context) (bodies : List Premise)
    (initial : Assignment) (events : List Event) : Nat :=
  match bodies, events with
  | first :: later, event :: events =>
      let before := premiseFuel environment context first initial event
      max before (greatest ((premise before environment context first initial event).map
        (fun middle => premisesFuel environment context.next later middle events))) + 1
  | _, _ => 1
termination_by 4 * sizeOf events + 2

def quantifiedFuel (environment : Environment) (context : Context) (parameter : String)
    (body : Premise) (index : Nat) (elements : List Pattern) (initial : Assignment)
    (events : List (Nat × Pattern × List Event)) : Nat :=
  match elements, events with
  | element :: elements, (_, _, [event]) :: events =>
      let localAssignment := bindParameter parameter (localValue context.bound element) initial
      let before := premiseFuel environment context.quantified body localAssignment event
      max before (greatest ((premise before environment context.quantified body localAssignment event).map
        (fun middle => quantifiedFuel environment context parameter body (index + 1) elements
          initial events))) + 1
  | _, _ => 1
termination_by 4 * sizeOf events
end


private theorem traced_match_bounded {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial : Assignment} {schema target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {final : Assignment}
    (held : GeneralScopedMatchMachine.TracedMatches rule spec ambient site path depth initial
      schema target trace final) :
    final ∈ matchAnswers (matchFuel ⟨rule, spec, ambient, site, path, depth, initial, schema, target⟩)
      ⟨rule, spec, ambient, site, path, depth, initial, schema, target⟩ trace :=
  matchFuel_complete (request := ⟨rule, spec, ambient, site, path, depth, initial, schema, target⟩) held

private theorem traced_query_bounded {environment : Environment} {context : Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : TracedQuery environment context relation arguments initial rowIndex final origins) :
    final ∈ queryAnswers (queryFuel environment ⟨context, relation, arguments, initial⟩) environment
      ⟨context, relation, arguments, initial⟩ rowIndex origins :=
  queryFuel_complete (request := ⟨context, relation, arguments, initial⟩) held

mutual
/-- A valid original finite firing succeeds at the computed budget. -/
theorem rootFuel_complete {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (held : RootFiring environment bound type source index trace captured completed history target) :
    root (rootFuel environment bound type source index trace captured completed history target)
      environment bound type source index trace captured completed history target = true :=
  match held with
  | .fire declared specified admitted sorted matched capturedTyped body targetRead targetTyped => by
      have matching := traced_match_bounded matched
      have bodyPresent := premisesFuel_complete body
      simp only [rootFuel, declared, specified, root, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨⟨admitted, checkOpenPatternWellSorted_complete sorted⟩,
        matchAnswers_mono (Nat.le_max_left _ _) _ _ matching⟩,
        checkTypedAssignment_complete capturedTyped⟩,
        premises_mono (Nat.le_max_right _ _) bodyPresent⟩, targetRead⟩,
        checkOpenPatternWellSorted_complete targetTyped⟩
termination_by structural held

theorem premiseFuel_complete {environment : Environment} {context : Context}
    {body : Premise} {initial final : Assignment} {event : Event}
    (held : PremiseHolds environment context body initial final event) :
    final ∈ premise (premiseFuel environment context body initial event)
      environment context body initial event :=
  match held with
  | .query query => by
      simpa [premiseFuel, premise] using traced_query_bounded query
  | .freshness interpreted fresh => by
      simp [premiseFuel, premise, interpreted, (syntactic_freshness_iff _ _).mpr fresh]
  | .step typed interpreted child matched finalTyped => by
      have matching := traced_match_bounded matched
      have childAccepted := rootFuel_complete child
      simp only [premiseFuel, typed, premise]
      split
      · exact List.mem_filter.mpr ⟨matchAnswers_mono (Nat.le_max_right _ _) _ _ matching,
          checkTypedAssignment_complete finalTyped⟩
      · rename_i denied
        exact (denied ⟨trivial, trivial, trivial, interpreted,
          root_mono (Nat.le_max_left _ _) childAccepted⟩).elim
  | .scopedStep interpreted child matched finalTyped => by
      have matching := traced_match_bounded matched
      have childAccepted := rootFuel_complete child
      simp only [premiseFuel, premise]
      split
      · exact List.mem_filter.mpr ⟨matchAnswers_mono (Nat.le_max_right _ _) _ _ matching,
          checkTypedAssignment_complete finalTyped⟩
      · rename_i denied
        exact (denied ⟨trivial, trivial, trivial, interpreted,
          root_mono (Nat.le_max_left _ _) childAccepted⟩).elim
  | .quantified interpreted elements => by
      simpa [premiseFuel, premise, interpreted] using quantifiedFuel_complete elements
termination_by structural held

theorem premisesFuel_complete {environment : Environment} {context : Context}
    {bodies : List Premise} {initial final : Assignment} {events : List Event}
    (held : PremisesHold environment context bodies initial final events) :
    final ∈ premises (premisesFuel environment context bodies initial events)
      environment context bodies initial events :=
  match held with
  | .nil => by simpa only [premisesFuel, premises] using List.mem_singleton_self initial
  | .cons (premise := first) (premises := rest) (middle := middle)
      (event := event) (events := events) head tail => by
      have before := premiseFuel_complete head
      have after := premisesFuel_complete tail
      have later : premisesFuel environment context.next rest middle events ≤
          greatest ((premise (premiseFuel environment context first initial event)
            environment context first initial event).map
              (fun next => premisesFuel environment context.next rest next events)) :=
        le_greatest (List.mem_map.mpr ⟨middle, before, rfl⟩)
      simp only [premisesFuel, premises]
      refine List.mem_flatMap.mpr ⟨_, premise_mono (Nat.le_max_left _ _) before, ?_⟩
      exact premises_mono (Nat.le_trans later (Nat.le_max_right _ _)) after
termination_by structural held

theorem quantifiedFuel_complete {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List Event)}
    (held : QuantifiedElements environment context parameter body index elements initial final events) :
    final ∈ quantified (quantifiedFuel environment context parameter body index elements initial events)
      environment context parameter body index elements initial events :=
  match held with
  | .nil => by simpa only [quantifiedFuel, quantified] using List.mem_singleton_self initial
  | .cons (element := element) (elements := rest) (middle := middle)
      (event := event) (events := events) localTyped head tail => by
      have before := premiseFuel_complete head
      have after := quantifiedFuel_complete tail
      have later : quantifiedFuel environment context parameter body (index + 1) rest
          initial events ≤
          greatest ((premise (premiseFuel environment context.quantified body
            (bindParameter parameter (localValue context.bound element) initial) event)
            environment context.quantified body
              (bindParameter parameter (localValue context.bound element) initial) event).map
                (fun next => quantifiedFuel environment context parameter body (index + 1) rest
                  initial events)) :=
        le_greatest (List.mem_map.mpr ⟨middle, before, rfl⟩)
      simp only [quantifiedFuel, quantified]
      split
      · refine List.mem_flatMap.mpr ⟨_, premise_mono (Nat.le_max_left _ _) before, ?_⟩
        exact quantified_mono (Nat.le_trans later (Nat.le_max_right _ _)) after
      · rename_i denied
        exact (denied ⟨trivial, trivial, checkTypedAssignment_complete localTyped⟩).elim
termination_by structural held
end


/-- Total validation of a fixed finite firing certificate. This does not
search an unbounded source proof space. -/
def checkRoot (environment : Environment) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (index : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List Event) (target : Pattern) : Bool :=
  root (rootFuel environment bound type source index trace captured completed history target)
    environment bound type source index trace captured completed history target

theorem checkRoot_exact (environment : Environment) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (index : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List Event) (target : Pattern) :
    checkRoot environment bound type source index trace captured completed history target = true ↔
      RootFiring environment bound type source index trace captured completed history target :=
  ⟨root_sound, rootFuel_complete⟩

def checkPremise (environment : Environment) (context : Context) (body : Premise)
    (initial final : Assignment) (event : Event) : Bool :=
  decide (final ∈ premise (premiseFuel environment context body initial event)
    environment context body initial event)

theorem checkPremise_exact (environment : Environment) (context : Context) (body : Premise)
    (initial final : Assignment) (event : Event) :
    checkPremise environment context body initial final event = true ↔
      PremiseHolds environment context body initial final event := by
  simp only [checkPremise, decide_eq_true_eq]
  exact ⟨premise_sound, premiseFuel_complete⟩

def checkPremises (environment : Environment) (context : Context) (bodies : List Premise)
    (initial final : Assignment) (events : List Event) : Bool :=
  decide (final ∈ premises (premisesFuel environment context bodies initial events)
    environment context bodies initial events)

theorem checkPremises_exact (environment : Environment) (context : Context) (bodies : List Premise)
    (initial final : Assignment) (events : List Event) :
    checkPremises environment context bodies initial final events = true ↔
      PremisesHold environment context bodies initial final events := by
  simp only [checkPremises, decide_eq_true_eq]
  exact ⟨premises_sound, premisesFuel_complete⟩

def checkQuantified (environment : Environment) (context : Context) (parameter : String)
    (body : Premise) (index : Nat) (elements : List Pattern) (initial final : Assignment)
    (events : List (Nat × Pattern × List Event)) : Bool :=
  decide (final ∈ quantified (quantifiedFuel environment context parameter body index elements initial events)
    environment context parameter body index elements initial events)

theorem checkQuantified_exact (environment : Environment) (context : Context) (parameter : String)
    (body : Premise) (index : Nat) (elements : List Pattern) (initial final : Assignment)
    (events : List (Nat × Pattern × List Event)) :
    checkQuantified environment context parameter body index elements initial final events = true ↔
      QuantifiedElements environment context parameter body index elements initial final events := by
  simp only [checkQuantified, decide_eq_true_eq]
  exact ⟨quantified_sound, quantifiedFuel_complete⟩

/-- The total receipt validator retains the original job, representation,
source/result typing, replacement context and complete firing evidence. -/
def checkReceipt (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (value : GeneralRuleJobs.Receipt) : Bool :=
  let environment := GeneralPlanEnvironment.environmentWith plan dynamic
  receipt (rootFuel environment value.job.site.focusBound value.job.site.focusType value.job.site.focus
    value.job.ordinal value.matcherTrace value.captured value.completed value.premiseHistory value.localTarget)
      dynamic plan bound type source value

theorem checkReceipt_exact (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (value : GeneralRuleJobs.Receipt) :
    checkReceipt dynamic plan bound type source value = true ↔
      value.ValidWith dynamic plan bound type source := by
  constructor
  · exact receipt_sound
  · intro valid
    simp only [checkReceipt, receipt, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨(checkJob_exact plan bound type source value.job).mpr valid.1,
      rootFuel_complete valid.2.1⟩, valid.2.2.1⟩, valid.2.2.2.1⟩,
      checkOpenPatternWellSorted_complete valid.2.2.2.2⟩

/-- Any successful budgeted replay is accepted by total validation; budget
refusal never supplies the converse implication. -/
theorem budgeted_receipt_accepted {fuel : Nat} {dynamic : DynamicProvider} {plan : Plan}
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {value : GeneralRuleJobs.Receipt}
    (accepted : receipt fuel dynamic plan bound type source value = true) :
    checkReceipt dynamic plan bound type source value = true :=
  (checkReceipt_exact dynamic plan bound type source value).mpr (receipt_sound accepted)


/-- No amount of history can authorize an undeclared root rule. -/
theorem checkRoot_missing_rule {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event}
    (missing : environment.language.rewrites[index]? = none) :
    checkRoot environment bound type source index trace captured completed history target = false := by
  apply Bool.eq_false_iff.mpr
  intro checked
  have valid := (checkRoot_exact environment bound type source index trace captured completed history target).mp checked
  cases valid with
  | fire declared => rw [missing] at declared; cases declared

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.EnumeratingReplay
