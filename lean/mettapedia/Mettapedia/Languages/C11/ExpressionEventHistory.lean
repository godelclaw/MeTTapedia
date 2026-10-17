import Mettapedia.Languages.C11.ExpressionEventExecution
import Mettapedia.Languages.C11.ExpressionPlanConstruction

/-!
# Connected expression histories and exact residual execution

Every admitted finite history of the independent occurrence rules is realized
by the executable scheduler, with the same occurrence observations and exact
semantic memory/cache endpoint. Every executable prefix constructs a connected
history. Pending occurrence count and receipt count are conserved, and an
occurrence cannot execute twice. Prefix resumption retains the original source
plan and complete memory, cache and pending state.

These are histories of constructed finite integer-expression evaluations.
Calls, loops and data-dependent branch construction require source rules that
construct their next evaluation. Finite occurrence progress does not imply
termination of arbitrary C programs.

The store-result extension retains every operand occurrence, then permits
both relative orders of the separate write and value occurrences. A proved
root-dominance condition orders all pure operand reads before the write. The
store account ties the pending store to unchanged memory and the consumed
store to the independent owned-write judgment, so arbitrary completed legal
schedules cannot invent a value or bypass the write.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ExpressionEventHistory

section Histories

open ExpressionEvents ExpressionEventExecution IntegerMemoryModel
open Mettapedia.GSLT.Distinction.ProductiveBlocks (Machine)

variable {Index : Type} {model : Model}

structure Occurrence (Index : Type) (model : Model) where
  index : Index
  outcome : Outcome model
  deriving DecidableEq, Repr

def observation (receipt : Receipt Index model) : Occurrence Index model := ⟨receipt.index, receipt.outcome⟩

inductive SemanticHistory [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model) :
    SemanticState Index model → List (Occurrence Index model) → SemanticState Index model → Prop where
  | nil (state : SemanticState Index model) : SemanticHistory policy plan state [] state
  | cons (before middle after : SemanticState Index model) (event : Occurrence Index model)
      (events : List (Occurrence Index model))
      (step : Reduction policy plan before event.index event.outcome middle)
      (following : SemanticHistory policy plan middle events after) :
      SemanticHistory policy plan before (event :: events) after

inductive History [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model) :
    State Index model → List (Receipt Index model) → State Index model → Prop where
  | nil (state : State Index model) : History policy plan state [] state
  | cons (receipt : Receipt Index model) (events : List (Receipt Index model)) (final : State Index model)
      (justified : ValidReceipt policy plan receipt)
      (following : History policy plan receipt.after events final) :
      History policy plan receipt.before (receipt :: events) final

theorem History.semantic [DecidableEq Index] {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before after : State Index model} {events : List (Receipt Index model)}
    (history : History policy plan before events after) :
    SemanticHistory policy plan (represent before) (events.map observation) (represent after) := by
  induction history with
  | nil state => exact .nil _
  | cons receipt events final justified following ih => exact .cons _ _ _ _ _ justified ih

theorem history_realization [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (before after : SemanticState Index model) (events : List (Occurrence Index model))
    (history : SemanticHistory policy plan before events after)
    (actual : State Index model) (represented : represent actual = before) (rest : List Index) :
    ∃ receipts saved,
      represent saved = after ∧ receipts.map observation = events ∧ History policy plan actual receipts saved ∧
      (machine model policy).run events.length
          ⟨plan, actual, events.map Occurrence.index ++ rest⟩ =
        (receipts, .exhausted ⟨plan, saved, rest⟩) := by
  induction history generalizing actual with
  | nil state => exact ⟨[], actual, represented, rfl, .nil _, rfl⟩
  | cons before middle after event events step following ih =>
      rw [← represented] at step
      obtain ⟨saved, computed, savedRepresentation⟩ := execute_complete policy plan actual middle event.index event.outcome step
      obtain ⟨receipts, final, finalRepresentation, observations, connected, ran⟩ := ih saved savedRepresentation
      let receipt : Receipt Index model := ⟨event.index, event.outcome, actual, saved⟩
      refine ⟨receipt :: receipts, final, finalRepresentation, ?_, ?_, ?_⟩
      · simp only [List.map_cons, observation, receipt, observations]
      · exact .cons receipt receipts final (execute_sound _ _ _ _ _ _ computed) connected
      · have stepped := step_of_execute policy plan actual saved event.index
          (events.map Occurrence.index ++ rest) event.outcome computed
        simp only [List.length_cons, List.map_cons, List.cons_append]
        rw [(machine model policy).run_succ_publish stepped, ran]
        rfl

theorem History.origins [DecidableEq Index] {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before after : State Index model} {events : List (Receipt Index model)}
    (history : History policy plan before events after) : ∀ receipt ∈ events, receipt.index ∈ before.pending := by
  induction history with
  | nil state => simp
  | cons receipt events final justified following ih =>
      cases justified with
      | execute _ _ _ partition continuing clean scheduled operation cached halted =>
          cases scheduled with
          | consume _ _ ready removed =>
              intro emitted present
              rcases List.mem_cons.mp present with rfl | present
              · exact ready.1
              · exact removed.sublist.subset (ih emitted present)

theorem History.account [DecidableEq Index] {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before after : State Index model} {events : List (Receipt Index model)}
    (history : History policy plan before events after) :
    after.pending.length + events.length = before.pending.length := by
  induction history with
  | nil state => simp
  | cons receipt events final justified following ih =>
      cases justified with
      | execute _ _ _ partition continuing clean scheduled operation cached halted =>
          cases scheduled with
          | consume _ _ ready removed =>
              have consumed := removed.length
              change receipt.after.pending.length + 1 = receipt.before.pending.length at consumed
              simp only [List.length_cons]
              omega

theorem History.unique [DecidableEq Index] {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before after : State Index model} {events : List (Receipt Index model)}
    (history : History policy plan before events after) (unique : before.pending.Nodup) :
    (events.map Receipt.index).Nodup ∧ after.pending.Nodup := by
  induction history with
  | nil state => exact ⟨by simp, unique⟩
  | cons receipt events final justified following ih =>
      cases justified with
      | execute _ _ _ partition continuing clean scheduled operation cached halted =>
          cases scheduled with
          | consume _ _ ready removed =>
              obtain ⟨laterUnique, residualUnique⟩ := ih (removed.unique unique)
              refine ⟨?_, residualUnique⟩
              simp only [List.map_cons, List.nodup_cons]
              refine ⟨?_, laterUnique⟩
              intro repeated
              obtain ⟨later, present, same⟩ := List.mem_map.mp repeated
              have pending := following.origins later present
              rw [same] at pending
              exact removed.absent unique pending

def verdictConfiguration : Verdict Index model → Configuration Index model
  | .returned _ saved | .terminal _ _ saved | .unsequenced _ _ saved | .refused saved => saved

def endpoint : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
    (Configuration Index model) (Verdict Index model) (SelectionRequest Index) → Option (Configuration Index model)
  | .exhausted saved | .stuck saved | .suspended _ saved => some saved
  | .finished verdict => some (verdictConfiguration verdict)
  | .faulted => none

inductive StepShape [DecidableEq Index] (policy : SignedConversionPolicy)
    (configuration : Configuration Index model) :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition
      (Configuration Index model) (Receipt Index model) (Verdict Index model) (SelectionRequest Index) → Prop where
  | finished (verdict : Verdict Index model) (saved : verdictConfiguration verdict = configuration) :
      StepShape policy configuration (.finish verdict)
  | suspended (request : SelectionRequest Index) : StepShape policy configuration (.call request configuration)
  | published (index : Index) (outcome : Outcome model) (after : State Index model) (rest : List Index)
      (selected : configuration.selections = index :: rest)
      (computed : execute policy configuration.plan configuration.state index = some (outcome, after)) :
      StepShape policy configuration (.publish [⟨index, outcome, configuration.state, after⟩]
        ⟨configuration.plan, after, rest⟩)

theorem machine_shape [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (configuration : Configuration Index model) :
    ∃ transition, (machine model policy).step configuration = some transition ∧ StepShape policy configuration transition := by
  cases conflict : configuration.plan.component.evaluation.findConflict configuration.plan.component.enumeration with
  | some pair =>
      rcases pair with ⟨first, second⟩
      exact ⟨.finish (.unsequenced first second configuration), by simp only [machine, conflict], .finished _ rfl⟩
  | none =>
      by_cases checked : partitionCheck configuration.plan configuration.state.pending configuration.state.cache = true
      · have base : (machine model policy).step configuration = some
          (match configuration.state.halted with
          | some (index, outcome) =>
              if outcome.terminal then .finish (.terminal index outcome configuration)
              else .finish (.refused configuration)
          | none =>
              match configuration.state.pending with
              | [] =>
                  match lookupScalar configuration.state.cache configuration.plan.component.result with
                  | some scalar => .finish (.returned scalar configuration)
                  | none => .finish (.refused configuration)
              | _ :: _ =>
                  match configuration.selections with
                  | [] => .call ⟨SequencingSchedule.choices configuration.plan.component.evaluation.order
                      configuration.state.pending⟩ configuration
                  | index :: rest =>
                      match execute policy configuration.plan configuration.state index with
                      | none => .finish (.refused configuration)
                      | some (outcome, after) => .publish [⟨index, outcome, configuration.state, after⟩]
                          ⟨configuration.plan, after, rest⟩) := by
          simp only [machine, conflict, checked, ↓reduceIte]
          rfl
        cases halted : configuration.state.halted with
        | some stopped =>
            rcases stopped with ⟨index, outcome⟩
            by_cases terminal : outcome.terminal = true
            · exact ⟨_, by simpa [halted, terminal] using base, .finished _ rfl⟩
            · exact ⟨_, by simpa [halted, terminal] using base, .finished _ rfl⟩
        | none =>
            cases pending : configuration.state.pending with
            | nil =>
                cases result : lookupScalar configuration.state.cache configuration.plan.component.result with
                | none => exact ⟨_, by simpa only [halted, pending, result] using base, .finished _ rfl⟩
                | some scalar => exact ⟨_, by simpa only [halted, pending, result] using base, .finished _ rfl⟩
            | cons head tail =>
                cases selected : configuration.selections with
                | nil => exact ⟨_, by simpa only [halted, pending, selected] using base, .suspended _⟩
                | cons index rest =>
                    cases computed : execute policy configuration.plan configuration.state index with
                    | none => exact ⟨_, by simpa only [halted, pending, selected, computed] using base, .finished _ rfl⟩
                    | some result =>
                        rcases result with ⟨outcome, after⟩
                        exact ⟨_, by simpa only [halted, pending, selected, computed] using base,
                          .published _ _ _ _ selected computed⟩
      · exact ⟨.finish (.refused configuration), by simp [machine, conflict, checked], .finished _ rfl⟩

theorem run_history [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (initial : Configuration Index model) :
    ∃ final, endpoint ((machine model policy).run fuel initial).2 = some final ∧ final.plan = initial.plan ∧
      History policy initial.plan initial.state ((machine model policy).run fuel initial).1 final.state := by
  induction fuel generalizing initial with
  | zero => exact ⟨initial, rfl, rfl, .nil _⟩
  | succ fuel ih =>
      obtain ⟨transition, stepped, shape⟩ := machine_shape model policy initial
      cases shape with
      | finished verdict saved =>
          rw [(machine model policy).run_succ_finish stepped]
          exact ⟨initial, by simp only [endpoint, saved], rfl, .nil _⟩
      | suspended request =>
          rw [(machine model policy).run_succ_call stepped]
          exact ⟨initial, rfl, rfl, .nil _⟩
      | published index outcome after rest selected computed =>
          rw [(machine model policy).run_succ_publish stepped]
          obtain ⟨final, endState, planRetained, following⟩ := ih ⟨initial.plan, after, rest⟩
          exact ⟨final, endState, planRetained,
            .cons ⟨index, outcome, initial.state, after⟩ _ final.state
              (execute_sound _ _ _ _ _ _ computed) following⟩

theorem run_conserves_occurrences [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (initial : Configuration Index model) :
    ∃ final, endpoint ((machine model policy).run fuel initial).2 = some final ∧ final.plan = initial.plan ∧
      final.state.pending.length + ((machine model policy).run fuel initial).1.length = initial.state.pending.length := by
  obtain ⟨final, endState, samePlan, history⟩ := run_history model policy fuel initial
  exact ⟨final, endState, samePlan, history.account⟩

theorem run_unique_occurrences [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (initial : Configuration Index model) (unique : initial.state.pending.Nodup) :
    (((machine model policy).run fuel initial).1.map Receipt.index).Nodup := by
  obtain ⟨final, endState, samePlan, history⟩ := run_history model policy fuel initial
  exact (history.unique unique).1

theorem resume_retains_plan [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (initial saved : Configuration Index model) (events : List (Receipt Index model))
    (paused : (machine model policy).run fuel initial = (events, .exhausted saved)) : saved.plan = initial.plan := by
  obtain ⟨final, endState, samePlan, history⟩ := run_history model policy fuel initial
  rw [paused] at endState
  have same : saved = final := Option.some.inj endState
  exact (congrArg Configuration.plan same).trans samePlan

theorem resume_no_repeat [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (first second : Nat) (initial saved : Configuration Index model) (events : List (Receipt Index model))
    (unique : initial.state.pending.Nodup)
    (paused : (machine model policy).run first initial = (events, .exhausted saved)) :
    ((events ++ ((machine model policy).run second saved).1).map Receipt.index).Nodup := by
  have once := run_unique_occurrences model policy (first + second) initial unique
  rw [resume_after_prefix model policy first second initial saved events paused] at once
  exact once

/-- The scalar observation of an operation with its inputs already named.
Stores are excluded; an absent result includes a memory refusal or a terminal
arithmetic/conversion/representation observation. -/
def operationValue (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters)
    (values : Index → Option (IntegerScalar.Value model.parameters)) :
    Operation Index model → Option (IntegerScalar.Value model.parameters)
  | .constant scalar => some scalar
  | .copy source => values source
  | .load location => (load model memory location).bind (fun loaded => (loadedOutcome model loaded).scalar)
  | .binary operator first second => do
      let left ← values first
      let right ← values second
      (arithmeticOutcome model (IntegerScalar.binary model.parameters operator left right)).scalar
  | .cast type source => do
      let input ← values source
      (castOutcome model (IntegerScalar.cast model.parameters policy type input)).scalar
  | .store _ _ => none

def ReadOnly (plan : Plan Index model) : Prop :=
  ∀ index location source, plan.operation index ≠ .store location source

/-- Each equation checks one actual primitive operation, not a complete run. -/
def ValueEquations (policy : SignedConversionPolicy) (plan : Plan Index model)
    (memory : ObjectAccessMemory.State model.characters)
    (values : Index → Option (IntegerScalar.Value model.parameters)) : Prop :=
  ∀ index, values index = operationValue policy memory values (plan.operation index)

def CacheAgrees [DecidableEq Index]
    (values : Index → Option (IntegerScalar.Value model.parameters)) (cache : Cache Index model) : Prop :=
  ∀ index outcome, cache.lookup index = some outcome → outcome.scalar = values index

theorem CacheAgrees.lookup [DecidableEq Index]
    {values : Index → Option (IntegerScalar.Value model.parameters)} {cache : Cache Index model}
    (agrees : CacheAgrees values cache) {index : Index} {scalar : IntegerScalar.Value model.parameters}
    (found : lookupScalar cache index = some scalar) : values index = some scalar := by
  obtain ⟨outcome, present, extracted⟩ := Option.bind_eq_some_iff.mp found
  exact (agrees index outcome present).symm.trans extracted

theorem CacheAgrees.cons [DecidableEq Index]
    {values : Index → Option (IntegerScalar.Value model.parameters)} {cache : Cache Index model}
    (agrees : CacheAgrees values cache) (index : Index) (outcome : Outcome model)
    (same : outcome.scalar = values index) : CacheAgrees values ((index, outcome) :: cache) := by
  intro selected actual found
  by_cases equal : selected = index
  · subst selected
    have actualEq : actual = outcome := by simpa using found.symm
    subst actual
    exact same
  · have previous : cache.lookup selected = some actual := by
      simpa only [List.lookup_cons, show (selected == index) = false from beq_eq_false_iff_ne.mpr equal] using found
    exact agrees selected actual previous

theorem operationValue_map {First Second : Type} (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters)
    (assigned : Second → Option (IntegerScalar.Value model.parameters))
    (rename : First → Second) (operation : Operation First model) :
    operationValue policy memory assigned (operation.map rename) =
      operationValue policy memory (assigned ∘ rename) operation := by
  cases operation <;> rfl

theorem operation_map_ne_store {First Second : Type} (rename : First → Second)
    (operation : Operation First model)
    (readOnly : ∀ location source, operation ≠ .store location source) :
    ∀ location source, operation.map rename ≠ .store location source := by
  cases operation <;> intros <;> simp only [Operation.map, ne_eq, reduceCtorEq, not_false_eq_true]
  exact False.elim (readOnly _ _ rfl)

theorem operation_evaluation_agrees [DecidableEq Index]
    (policy : SignedConversionPolicy) (memory : ObjectAccessMemory.State model.characters)
    (values : Index → Option (IntegerScalar.Value model.parameters)) (cache : Cache Index model)
    (operation : Operation Index model) (outcome : Outcome model)
    (after : ObjectAccessMemory.SemanticState model.characters)
    (readOnly : ∀ location source, operation ≠ .store location source)
    (agrees : CacheAgrees values cache)
    (evaluated : OperationEvaluation model policy cache (ObjectAccessMemory.represent memory)
      operation outcome after) :
    after = ObjectAccessMemory.represent memory ∧ outcome.scalar = operationValue policy memory values operation := by
  cases evaluated with
  | constant scalar => exact ⟨rfl, rfl⟩
  | copy source scalar available =>
      exact ⟨rfl, (agrees.lookup ((lookupScalar_iff _ _ _).mpr available)).symm⟩
  | load location loaded reading =>
      exact ⟨rfl, by simp [operationValue, load_complete _ _ _ _ reading]⟩
  | binary operator first second left right result leftAvailable rightAvailable arithmetic =>
      refine ⟨rfl, ?_⟩
      simp only [operationValue, agrees.lookup ((lookupScalar_iff _ _ _).mpr leftAvailable),
        agrees.lookup ((lookupScalar_iff _ _ _).mpr rightAvailable), bind, Option.bind_some,
        (IntegerScalar.binary_iff _ _ _ _ _ _).mpr arithmetic]
  | cast type source input result available conversion =>
      refine ⟨rfl, ?_⟩
      simp only [operationValue, agrees.lookup ((lookupScalar_iff _ _ _).mpr available),
        bind, Option.bind_some, IntegerScalar.cast_complete _ _ _ _ _ conversion]
  | store after location source scalar available writing => exact False.elim (readOnly location source rfl)

theorem reduction_readOnly_values [DecidableEq Index]
    {policy : SignedConversionPolicy} {plan : Plan Index model}
    {memory : ObjectAccessMemory.State model.characters}
    {values : Index → Option (IntegerScalar.Value model.parameters)}
    {before after : SemanticState Index model} {index : Index} {outcome : Outcome model}
    (readOnly : ReadOnly plan) (equations : ValueEquations policy plan memory values)
    (sameMemory : before.memory = ObjectAccessMemory.represent memory)
    (agrees : CacheAgrees values before.cache)
    (step : Reduction policy plan before index outcome after) :
    after.memory = ObjectAccessMemory.represent memory ∧ CacheAgrees values after.cache ∧
      outcome.scalar = values index := by
  cases step with
  | execute _ _ _ partition continuing clean scheduled operation cached halted =>
      rw [sameMemory] at operation
      obtain ⟨memoryEqual, observed⟩ :=
        operation_evaluation_agrees policy memory values before.cache _ outcome after.memory
          (readOnly index) agrees operation
      have valueEqual := observed.trans (equations index).symm
      refine ⟨memoryEqual, ?_, valueEqual⟩
      rw [cached]
      exact agrees.cons index outcome valueEqual

theorem SemanticHistory.readOnly_values [DecidableEq Index]
    {policy : SignedConversionPolicy} {plan : Plan Index model}
    {memory : ObjectAccessMemory.State model.characters}
    {values : Index → Option (IntegerScalar.Value model.parameters)}
    {before after : SemanticState Index model} {events : List (Occurrence Index model)}
    (readOnly : ReadOnly plan) (equations : ValueEquations policy plan memory values)
    (sameMemory : before.memory = ObjectAccessMemory.represent memory)
    (agrees : CacheAgrees values before.cache)
    (history : SemanticHistory policy plan before events after) :
    after.memory = ObjectAccessMemory.represent memory ∧ CacheAgrees values after.cache := by
  induction history with
  | nil _ => exact ⟨sameMemory, agrees⟩
  | cons before middle after event events step following ih =>
      obtain ⟨memoryEqual, cacheEqual, _⟩ :=
        reduction_readOnly_values readOnly equations sameMemory agrees step
      exact ih memoryEqual cacheEqual

theorem SemanticHistory.readOnly_result [DecidableEq Index]
    {policy : SignedConversionPolicy} {plan : Plan Index model}
    {memory : ObjectAccessMemory.State model.characters}
    {values : Index → Option (IntegerScalar.Value model.parameters)}
    {after : SemanticState Index model} {events : List (Occurrence Index model)}
    (readOnly : ReadOnly plan) (equations : ValueEquations policy plan memory values)
    (history : SemanticHistory policy plan (represent (initialState plan memory)) events after)
    {scalar : IntegerScalar.Value model.parameters}
    (result : lookupScalar after.cache plan.component.result = some scalar) :
    values plan.component.result = some scalar ∧ after.memory = ObjectAccessMemory.represent memory := by
  obtain ⟨unchanged, agrees⟩ := history.readOnly_values readOnly equations rfl
    (by intro index outcome found; simp [represent, initialState] at found)
  exact ⟨agrees.lookup result, unchanged⟩

theorem lookup_exists_of_key [DecidableEq Index] (cache : Cache Index model) (index : Index)
    (present : index ∈ cache.map Prod.fst) : ∃ outcome, cache.lookup index = some outcome := by
  induction cache with
  | nil => cases present
  | cons head tail ih =>
      rcases head with ⟨key, value⟩
      by_cases same : index = key
      · exact ⟨value, by simp [same]⟩
      · have member : index ∈ tail.map Prod.fst := by simpa [same] using present
        obtain ⟨outcome, found⟩ := ih member
        exact ⟨outcome, by simpa only [List.lookup_cons,
          show (index == key) = false from beq_eq_false_iff_ne.mpr same] using found⟩

theorem CacheAgrees.cached [DecidableEq Index]
    {values : Index → Option (IntegerScalar.Value model.parameters)} {cache : Cache Index model}
    (agrees : CacheAgrees values cache) {index : Index} (present : index ∈ cache.map Prod.fst) :
    lookupScalar cache index = values index := by
  obtain ⟨outcome, found⟩ := lookup_exists_of_key cache index present
  simp only [lookupScalar, found, Option.bind_some, agrees index outcome found]

theorem readOnly_clean (plan : Plan Index model) (readOnly : ReadOnly plan) :
    ¬ plan.component.evaluation.Undefined := by
  have noModify : ∀ index object, plan.component.evaluation.access index ≠ .modify object := by
    intro index object
    rw [plan.access index]
    cases operation : plan.operation index <;>
      simp only [Operation.access, ObjectAccessMemory.Lvalue.readEvent, ne_eq, reduceCtorEq, not_false_eq_true]
    exact False.elim (readOnly index _ _ operation)
  rintro ⟨first, second, _, conflict⟩
  have hasModification {first second : Sequencing.Access ObjectAccessMemory.Identity}
      (conflict : Sequencing.Conflict first second) :
      (∃ object, first = .modify object) ∨ (∃ object, second = .modify object) := by
    cases conflict with
    | modifyModify object => exact Or.inl ⟨object, rfl⟩
    | modifyRead object => exact Or.inl ⟨object, rfl⟩
    | readModify object => exact Or.inr ⟨object, rfl⟩
  have someModify := hasModification conflict
  rcases someModify with ⟨object, same⟩ | ⟨object, same⟩
  · exact noModify first object same
  · exact noModify second object same

theorem operationValue_realized [DecidableEq Index]
    (policy : SignedConversionPolicy) (memory : ObjectAccessMemory.State model.characters)
    (values : Index → Option (IntegerScalar.Value model.parameters)) (cache : Cache Index model)
    (operation : Operation Index model) (scalar : IntegerScalar.Value model.parameters)
    (available : ∀ source ∈ operation.inputs, lookupScalar cache source = values source)
    (value : operationValue policy memory values operation = some scalar) :
    ∃ outcome, executeOperation model policy memory cache operation = some (outcome, memory) ∧
      outcome.scalar = some scalar := by
  cases operation with
  | constant input => exact ⟨.value input, rfl, value⟩
  | copy source =>
      have found := (available source (by simp [Operation.inputs])).trans value
      exact ⟨.value scalar, by simp [executeOperation, found], rfl⟩
  | load location =>
      obtain ⟨loaded, found, scalarValue⟩ := Option.bind_eq_some_iff.mp value
      exact ⟨loadedOutcome model loaded, by simp [executeOperation, found], scalarValue⟩
  | binary operator first second =>
      obtain ⟨left, leftValue, following⟩ := Option.bind_eq_some_iff.mp value
      obtain ⟨right, rightValue, result⟩ := Option.bind_eq_some_iff.mp following
      have firstCached := (available first (by simp [Operation.inputs])).trans leftValue
      have secondCached := (available second (by simp [Operation.inputs])).trans rightValue
      exact ⟨_, by simp only [executeOperation, firstCached, secondCached, bind, Option.bind_some], result⟩
  | cast type source =>
      obtain ⟨input, inputValue, result⟩ := Option.bind_eq_some_iff.mp value
      have found := (available source (by simp [Operation.inputs])).trans inputValue
      exact ⟨_, by simp only [executeOperation, found, bind, Option.bind_some], result⟩
  | store location source => cases value

theorem readOnly_progress [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (memory : ObjectAccessMemory.State model.characters)
    (values : Index → Option (IntegerScalar.Value model.parameters))
    (readOnly : ReadOnly plan) (equations : ValueEquations policy plan memory values)
    (ordered : plan.InputsOrdered) (total : ∀ index, ∃ scalar, values index = some scalar)
    (before : SemanticState Index model) (partition : Partition plan before.pending before.cache)
    (sameMemory : before.memory = ObjectAccessMemory.represent memory)
    (agrees : CacheAgrees values before.cache) (continuing : before.halted = none)
    (index : Index) (ready : SequencingSchedule.Ready plan.component.evaluation.order before.pending index) :
    ∃ outcome after, Reduction policy plan before index outcome after ∧
      after.pending.length + 1 = before.pending.length ∧ after.halted = none ∧
      after.memory = ObjectAccessMemory.represent memory ∧ CacheAgrees values after.cache := by
  obtain ⟨scalar, observed⟩ := total index
  obtain ⟨outcome, computed, scalarValue⟩ := operationValue_realized policy memory values before.cache
    (plan.operation index) scalar
    (fun source present => agrees.cached (ready_inputs_cached plan _ _ index partition ordered ready source present))
    ((equations index).symm.trans observed)
  have terminal : haltAfter index outcome = none := by simp [haltAfter, Outcome.terminal, scalarValue]
  let after : SemanticState Index model :=
    ⟨before.pending.erase index, ObjectAccessMemory.represent memory, (index, outcome) :: before.cache, none⟩
  have removed := SequencingSchedule.removal_erase index before.pending ready.1
  have operation : OperationEvaluation model policy before.cache before.memory
      (plan.operation index) outcome (ObjectAccessMemory.represent memory) := by
    rw [sameMemory]
    exact executeOperation_sound model policy memory memory before.cache _ outcome computed
  have stepped : Reduction policy plan before index outcome after :=
    .execute before after index outcome partition continuing (readOnly_clean plan readOnly)
      (.consume _ _ index ready removed) operation rfl terminal.symm
  exact ⟨outcome, after, stepped, removed.length, rfl, rfl,
    agrees.cons index outcome (scalarValue.trans observed.symm)⟩

theorem readOnly_complete_history [DecidableEq Index]
    (policy : SignedConversionPolicy) (plan : Plan Index model)
    (memory : ObjectAccessMemory.State model.characters)
    (values : Index → Option (IntegerScalar.Value model.parameters))
    (readOnly : ReadOnly plan) (equations : ValueEquations policy plan memory values)
    (ordered : plan.InputsOrdered) (total : ∀ index, ∃ scalar, values index = some scalar)
    (fuel : Nat) (before : SemanticState Index model)
    (bounded : before.pending.length ≤ fuel) (partition : Partition plan before.pending before.cache)
    (sameMemory : before.memory = ObjectAccessMemory.represent memory)
    (agrees : CacheAgrees values before.cache) (continuing : before.halted = none) :
    ∃ events after, SemanticHistory policy plan before events after ∧ after.pending = [] ∧
      after.halted = none ∧ after.memory = ObjectAccessMemory.represent memory ∧
      CacheAgrees values after.cache ∧ Partition plan after.pending after.cache := by
  induction fuel generalizing before with
  | zero =>
      have empty : before.pending = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero bounded)
      exact ⟨[], before, .nil _, empty, continuing, sameMemory, agrees, partition⟩
  | succ fuel ih =>
      by_cases empty : before.pending = []
      · exact ⟨[], before, .nil _, empty, continuing, sameMemory, agrees, partition⟩
      · obtain ⟨index, ready⟩ := SequencingSchedule.ready_exists plan.component.enumeration
          plan.component.evaluation.order plan.component.valid before.pending empty
        obtain ⟨outcome, middle, step, length, active, unchanged, cache⟩ :=
          readOnly_progress policy plan memory values readOnly equations ordered total before
            partition sameMemory agrees continuing index ready
        obtain ⟨events, after, history, drained, unhalted, finalMemory, finalCache, finalPartition⟩ :=
          ih middle (by omega) step.partition unchanged cache active
        exact ⟨⟨index, outcome⟩ :: events, after, .cons _ _ _ _ _ step history,
          drained, unhalted, finalMemory, finalCache, finalPartition⟩

section Failures
variable [DecidableEq Index]

/-- A faulting primitive is either a recorded terminal occurrence or a
licensed ready operation whose memory access is refused. Invalid scheduler
choices and an empty choice suffix are not expression faults. -/
inductive Failure (policy : SignedConversionPolicy) (plan : Plan Index model)
    (state : SemanticState Index model) : Prop where
  | terminal (index : Index) (outcome : Outcome model)
      (halted : state.halted = some (index, outcome))
      (recorded : state.cache.lookup index = some outcome)
      (terminal : outcome.terminal = true)
  | refused (index : Index) (continuing : state.halted = none)
      (ready : SequencingSchedule.Ready plan.component.evaluation.order state.pending index)
      (refused : ∀ outcome after, ¬ OperationEvaluation model policy state.cache state.memory
        (plan.operation index) outcome after)

private def ScalarCache (cache : Cache Index model) : Prop :=
  ∀ index outcome, cache.lookup index = some outcome → ∃ scalar, outcome.scalar = some scalar

private theorem scalarCache_cons {cache : Cache Index model} (valid : ScalarCache cache)
    (index : Index) (outcome : Outcome model) (value : ∃ scalar, outcome.scalar = some scalar) :
    ScalarCache ((index, outcome) :: cache) := by
  intro selected actual found
  by_cases same : selected = index
  · subst selected
    have equal : actual = outcome := by simpa using found.symm
    subst actual
    exact value
  · apply valid selected actual
    simpa only [List.lookup_cons, show (selected == index) = false from beq_eq_false_iff_ne.mpr same] using found

/-- Every finite conflict-free plan can be drained or can reach a genuine
primitive failure. The argument selects only a currently ready occurrence;
it places no additional order on independent operands. -/
private theorem plan_complete_or_failure (policy : SignedConversionPolicy) (plan : Plan Index model)
    (clean : ¬ plan.component.evaluation.Undefined)
    (fuel : Nat) (before : State Index model)
    (bounded : before.pending.length ≤ fuel) (partition : Partition plan before.pending before.cache)
    (continuing : before.halted = none) (cache : ScalarCache before.cache) :
    ∃ events after, SemanticHistory policy plan (represent before) events (represent after) ∧
      Partition plan after.pending after.cache ∧
      ((∃ scalar, after.pending = [] ∧ after.halted = none ∧
          lookupScalar after.cache plan.component.result = some scalar) ∨ Failure policy plan (represent after)) := by
  induction fuel generalizing before with
  | zero =>
      have empty : before.pending = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero bounded)
      have present := partition.2 plan.component.result (plan.component.enumeration.complete _)
      rw [empty] at present
      obtain ⟨outcome, found⟩ := lookup_exists_of_key before.cache _ (present.resolve_left (by simp))
      obtain ⟨scalar, value⟩ := cache _ _ found
      exact ⟨[], before, .nil _, partition, Or.inl ⟨scalar, empty, continuing,
        by simp only [lookupScalar, found, Option.bind_some, value]⟩⟩
  | succ fuel ih =>
      by_cases empty : before.pending = []
      · have present := partition.2 plan.component.result (plan.component.enumeration.complete _)
        rw [empty] at present
        obtain ⟨outcome, found⟩ := lookup_exists_of_key before.cache _ (present.resolve_left (by simp))
        obtain ⟨scalar, value⟩ := cache _ _ found
        exact ⟨[], before, .nil _, partition, Or.inl ⟨scalar, empty, continuing,
          by simp only [lookupScalar, found, Option.bind_some, value]⟩⟩
      · obtain ⟨index, ready⟩ := SequencingSchedule.ready_exists plan.component.enumeration
          plan.component.evaluation.order plan.component.valid before.pending empty
        cases computed : executeOperation model policy before.memory before.cache (plan.operation index) with
        | none =>
            refine ⟨[], before, .nil _, partition, Or.inr (.refused index continuing ready ?_)⟩
            intro outcome after operation
            obtain ⟨saved, executed, _⟩ := executeOperation_complete model policy before.memory after
              before.cache (plan.operation index) outcome operation
            rw [computed] at executed
            cases executed
        | some pair =>
            obtain ⟨outcome, memory⟩ := pair
            let after : State Index model := ⟨before.pending.erase index, memory,
              (index, outcome) :: before.cache, haltAfter index outcome⟩
            have removed := SequencingSchedule.removal_erase index before.pending ready.1
            have step : Reduction policy plan (represent before) index outcome (represent after) :=
              .execute _ _ _ _ partition continuing clean
                (.consume _ _ index ready removed) (executeOperation_sound _ _ _ _ _ _ _ computed) rfl rfl
            by_cases terminal : outcome.terminal = true
            · refine ⟨[⟨index, outcome⟩], after, .cons _ _ _ _ _ step (.nil _), step.partition,
                Or.inr (.terminal index outcome ?_ ?_ terminal)⟩
              · simp only [represent, after, haltAfter, terminal, ↓reduceIte]
              · simp only [represent, after, List.lookup_cons, beq_self_eq_true]
            · have value : ∃ scalar, outcome.scalar = some scalar := by
                cases actual : outcome.scalar with
                | none => exact False.elim (terminal (by simp [Outcome.terminal, actual]))
                | some scalar => exact ⟨scalar, rfl⟩
              obtain ⟨events, final, history, finalPartition, stopped⟩ := ih after
                (by have decreased := removed.length; dsimp [after]; omega) step.partition
                (by simp [after, haltAfter, terminal]) (scalarCache_cons cache index outcome value)
              exact ⟨⟨index, outcome⟩ :: events, final, .cons _ _ _ _ _ step history,
                finalPartition, stopped⟩

/-- Every conflict-free finite expression plan has a complete history or a
history ending in a genuine primitive failure. Only ready occurrences are
selected; independent operands retain their permitted scheduling freedom. -/
theorem complete_or_failure (policy : SignedConversionPolicy) (plan : Plan Index model)
    (memory : ObjectAccessMemory.State model.characters)
    (clean : ¬ plan.component.evaluation.Undefined) :
    ∃ events after, SemanticHistory policy plan (represent (initialState plan memory)) events (represent after) ∧
      Partition plan after.pending after.cache ∧
      ((∃ scalar, after.pending = [] ∧ after.halted = none ∧
          lookupScalar after.cache plan.component.result = some scalar) ∨ Failure policy plan (represent after)) :=
  plan_complete_or_failure policy plan clean (initialState plan memory).pending.length
    (initialState plan memory) le_rfl (initial_partition _ _) rfl
    (by intro index outcome found; cases found)

private def EarnedStatus (state : SemanticState Index model) : Prop :=
  (∀ index outcome, state.halted = some (index, outcome) →
    state.cache.lookup index = some outcome ∧ outcome.terminal = true) ∧
  (state.halted = none → ScalarCache state.cache)

private theorem reduction_status {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before after : SemanticState Index model} {index : Index} {outcome : Outcome model}
    (status : EarnedStatus before) (step : Reduction policy plan before index outcome after) : EarnedStatus after := by
  cases step with
  | execute _ _ _ partition continuing clean scheduled operation cached halted =>
      constructor
      · intro actual terminal found
        rw [halted, haltAfter] at found
        split at found
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
          exact ⟨by simp [cached], by assumption⟩
        · cases found
      · intro active
        have value : ∃ scalar, outcome.scalar = some scalar := by
          cases observed : outcome.scalar with
          | none => simp [halted, haltAfter, Outcome.terminal, observed] at active
          | some scalar => exact ⟨scalar, rfl⟩
        rw [cached]
        exact scalarCache_cons (status.2 continuing) index outcome value

private theorem history_status {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before after : SemanticState Index model} {events : List (Occurrence Index model)}
    (history : SemanticHistory policy plan before events after) (status : EarnedStatus before) : EarnedStatus after := by
  induction history with
  | nil => exact status
  | cons before middle after event events step following ih => exact ih (reduction_status status step)

theorem SemanticHistory.partition {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before after : SemanticState Index model} {events : List (Occurrence Index model)}
    (history : SemanticHistory policy plan before events after) (partition : Partition plan before.pending before.cache) :
    Partition plan after.pending after.cache := by
  induction history with
  | nil => exact partition
  | cons before middle after event events step following ih => exact ih step.partition

/-- A reached terminal flag names the exact terminal occurrence retained in
the cache. Arbitrary fabricated cache/flag pairs do not satisfy this invariant. -/
theorem SemanticHistory.halted_recorded {policy : SignedConversionPolicy} {plan : Plan Index model}
    {memory : ObjectAccessMemory.State model.characters} {after : SemanticState Index model}
    {events : List (Occurrence Index model)}
    (history : SemanticHistory policy plan (represent (initialState plan memory)) events after)
    (index : Index) (outcome : Outcome model) (halted : after.halted = some (index, outcome)) :
    after.cache.lookup index = some outcome ∧ outcome.terminal = true := by
  have initialStatus : EarnedStatus (represent (initialState plan memory)) :=
    ⟨(by intro selected actual stopped; cases stopped), (by intro _ selected actual found; cases found)⟩
  exact (history_status history initialStatus).1 index outcome halted

/-- Every cached occurrence of a continuing reached state has a scalar value.
This is earned by the history, not assumed from the representation. -/
theorem SemanticHistory.unhalted_scalar_cache {policy : SignedConversionPolicy} {plan : Plan Index model}
    {memory : ObjectAccessMemory.State model.characters} {after : SemanticState Index model}
    {events : List (Occurrence Index model)}
    (history : SemanticHistory policy plan (represent (initialState plan memory)) events after)
    (halted : after.halted = none) (index : Index) (outcome : Outcome model)
    (found : after.cache.lookup index = some outcome) : ∃ scalar, outcome.scalar = some scalar := by
  have initialStatus : EarnedStatus (represent (initialState plan memory)) :=
    ⟨(by intro selected actual stopped; cases stopped), (by intro _ selected actual present; cases present)⟩
  exact (history_status history initialStatus).2 halted index outcome found

end Failures

end Histories

section StoreEmbedding
open ExpressionEvents ExpressionEventExecution IntegerMemoryModel ExpressionPlanConstruction
open Sequencing ValueSequencing
variable {Index : Type} {model : Model}
local instance [DecidableEq Index] : BEq (Index ⊕ Fin 2) := instBEqOfDecidableEq

def mapCache (cache : Cache Index model) : Cache (Index ⊕ Fin 2) model :=
  cache.map (fun entry => (Sum.inl entry.1, entry.2))

@[simp] theorem mapCache_lookup [DecidableEq Index] (cache : Cache Index model) (index : Index) :
    (mapCache cache).lookup (.inl index) = cache.lookup index := by
  induction cache with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨key, outcome⟩
    by_cases same : key = index
    · subst key; simp only [mapCache, List.map_cons, List.lookup_cons, beq_self_eq_true]
    · simpa only [mapCache, List.map_cons, List.lookup_cons,
        show (index == key) = false from beq_eq_false_iff_ne.mpr (Ne.symm same),
        show ((Sum.inl index : Index ⊕ Fin 2) == Sum.inl key) = false from
          beq_eq_false_iff_ne.mpr (fun equal => same (Sum.inl.inj equal).symm)] using ih

@[simp] theorem mapCache_lookup_new [DecidableEq Index] (cache : Cache Index model) (index : Fin 2) :
    (mapCache cache).lookup (.inr index) = none := by
  induction cache with
  | nil => rfl
  | cons head tail ih =>
    simpa only [mapCache, List.map_cons, List.lookup_cons,
      show ((Sum.inr index : Index ⊕ Fin 2) == Sum.inl head.1) = false from rfl] using ih

@[simp] theorem mapCache_keys (cache : Cache Index model) :
    (mapCache cache).map Prod.fst = (cache.map Prod.fst).map Sum.inl := by
  simp [mapCache, List.map_map]

theorem mapCache_available [DecidableEq Index] (cache : Cache Index model) (index : Index)
    (scalar : IntegerScalar.Value model.parameters) (available : Available cache index scalar) :
    Available (mapCache cache) (.inl index) scalar := by
  rcases available with ⟨outcome, found, value⟩
  exact ⟨outcome, (mapCache_lookup cache index).trans found, value⟩

theorem operation_mapCache [DecidableEq Index] (policy : SignedConversionPolicy)
    (cache : Cache Index model) (before after : ObjectAccessMemory.SemanticState model.characters)
    (operation : Operation Index model) (outcome : Outcome model)
    (evaluated : OperationEvaluation model policy cache before operation outcome after) :
    OperationEvaluation model policy (mapCache cache) before (operation.map Sum.inl) outcome after := by
  cases evaluated with
  | constant scalar => exact .constant _ _
  | copy source scalar available => exact .copy _ _ _ (mapCache_available _ _ _ available)
  | load location loaded reading => exact .load _ _ _ reading
  | binary operator first second left right result firstAvailable secondAvailable arithmetic =>
    exact .binary _ _ _ _ _ _ _ (mapCache_available _ _ _ firstAvailable)
      (mapCache_available _ _ _ secondAvailable) arithmetic
  | cast type source input result available conversion =>
    exact .cast _ _ _ _ _ (mapCache_available _ _ _ available) conversion
  | store after location source scalar available writing =>
    exact .store _ _ _ _ _ (mapCache_available _ _ _ available) writing

def storePending (pending : List Index) : List (Index ⊕ Fin 2) := pending.map Sum.inl ++ [.inr 0, .inr 1]

def storeState (state : SemanticState Index model) : SemanticState (Index ⊕ Fin 2) model :=
  ⟨storePending state.pending, state.memory, mapCache state.cache,
    state.halted.map (fun entry => (.inl entry.1, entry.2))⟩

theorem storePending_partition [DecidableEq Index] (plan : Plan Index model)
    (location : ObjectAccessMemory.Lvalue) (pending : List Index) (cache : Cache Index model)
    (partition : Partition plan pending cache) :
    Partition (storeResult plan location) (storePending pending) (mapCache cache) := by
  constructor
  · have unique := partition.1.map (@Sum.inl_injective Index (Fin 2))
    rw [List.map_append] at unique
    have rearrange : (storePending pending ++ (mapCache cache).map Prod.fst).Perm
        ((pending ++ cache.map Prod.fst).map Sum.inl ++ [.inr 0, .inr 1]) := by
      simp only [storePending, mapCache_keys, List.map_append]
      rw [List.append_assoc]
      exact (List.Perm.append_left _ (List.perm_append_comm)).trans (by rw [List.append_assoc])
    apply rearrange.nodup_iff.mpr
    apply List.nodup_append.mpr
    refine ⟨by simpa [List.map_append] using unique, by simp, ?_⟩
    intro left leftPresent right rightPresent same
    obtain ⟨old, _, rfl⟩ := List.mem_map.mp leftPresent
    simp only [List.mem_cons, List.not_mem_nil, or_false] at rightPresent
    rcases rightPresent with rfl | rfl <;> cases same
  · intro index _
    cases index with
    | inl index =>
      rcases partition.2 index (plan.component.enumeration.complete index) with pending | cached
      · exact Or.inl (by simp [storePending, pending])
      · exact Or.inr (by rw [mapCache_keys]; exact List.mem_map.mpr ⟨index, cached, rfl⟩)
    | inr index =>
      have casesIndex : index = 0 ∨ index = 1 := by omega
      rcases casesIndex with rfl | rfl <;> exact Or.inl (by simp [storePending])

theorem storePending_removal [DecidableEq Index] {index : Index} {before after : List Index}
    (removed : SequencingSchedule.Removal index before after) :
    SequencingSchedule.Removal (.inl index) (storePending before) (storePending after) := by
  induction removed with
  | here tail => exact .here _
  | there head before after different following ih =>
    exact .there _ _ _ (fun same => different (Sum.inl.inj same)) ih

theorem storePending_ready [DecidableEq Index] (plan : Plan Index model)
    (location : ObjectAccessMemory.Lvalue) (pending : List Index) (index : Index)
    (ready : SequencingSchedule.Ready plan.component.evaluation.order pending index) :
    SequencingSchedule.Ready (storeResult plan location).component.evaluation.order
      (storePending pending) (.inl index) := by
  constructor
  · simp [storePending, ready.1]
  · intro predecessor present before
    cases predecessor with
    | inl predecessor =>
      exact ready.2 predecessor (by simpa [storePending] using present) before
    | inr predecessor => cases before

theorem storeState_reduction [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (location : ObjectAccessMemory.Lvalue) (clean : ¬ (storeResult plan location).component.evaluation.Undefined)
    (before after : SemanticState Index model) (index : Index) (outcome : Outcome model)
    (step : Reduction policy plan before index outcome after) :
    Reduction policy (storeResult plan location) (storeState before) (.inl index) outcome (storeState after) := by
  cases step with
  | execute _ _ _ partition continuing _ scheduled operation cached halted =>
    refine .execute _ _ _ _ (storePending_partition plan location _ _ partition)
      (by simp [storeState, continuing]) clean ?_ (operation_mapCache _ _ _ _ _ _ operation) ?_ ?_
    · cases scheduled with
      | consume _ _ ready removed =>
        exact .consume _ _ _ (storePending_ready _ _ _ _ ready) (storePending_removal removed)
    · simp [storeState, cached, mapCache]
    · simp only [storeState, halted, haltAfter]
      split <;> rfl

theorem SemanticHistory.storeState [DecidableEq Index] {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before after : SemanticState Index model} {events : List (Occurrence Index model)}
    (history : SemanticHistory policy plan before events after) (location : ObjectAccessMemory.Lvalue)
    (clean : ¬ (storeResult plan location).component.evaluation.Undefined) :
    SemanticHistory policy (storeResult plan location) (storeState before)
      (events.map (fun event => ⟨.inl event.index, event.outcome⟩)) (storeState after) := by
  induction history with
  | nil state => exact .nil _
  | cons before middle after event events step following ih =>
    exact .cons _ _ _ _ _ (storeState_reduction policy plan location clean before middle event.index event.outcome step) ih

end StoreEmbedding

section StoreCompletion
open ExpressionEvents ExpressionEventExecution IntegerMemoryModel ExpressionPlanConstruction
open Sequencing ValueSequencing
variable {Index : Type} {model : Model}
local instance [DecidableEq Index] : BEq (Index ⊕ Fin 2) := instBEqOfDecidableEq

theorem storeResult_clean [DecidableEq Index] (plan : Plan Index model)
    (location : ObjectAccessMemory.Lvalue) (readOnly : ReadOnly plan)
    (dominates : ∀ index, index = plan.component.result ∨ plan.component.evaluation.order.Precedes index plan.component.result) :
    ¬ (storeResult plan location).component.evaluation.Undefined := by
  have beforeNew (old : Index) (fresh : Fin 2) :
      (storeResult plan location).component.evaluation.order.Precedes (.inl old) (.inr fresh) := by
    exact (afterRoots_follows _ _ _ _ _).mpr ⟨_, by simp, dominates old⟩
  rintro ⟨first, second, unordered, conflict⟩
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      apply readOnly_clean plan readOnly
      exact ⟨first, second, ⟨(fun same => unordered.1 (congrArg Sum.inl same)), unordered.2⟩, conflict⟩
    | inr second => exact unordered.2.1 (beforeNew first second)
  | inr first =>
    cases second with
    | inl second => exact unordered.2.2 (beforeNew second first)
    | inr second =>
      have firstCases : first = 0 ∨ first = 1 := by omega
      have secondCases : second = 0 ∨ second = 1 := by omega
      rcases firstCases with rfl | rfl <;> rcases secondCases with rfl | rfl
      · exact unordered.1 rfl
      · cases conflict
      · cases conflict
      · exact unordered.1 rfl

theorem storeState_initial [DecidableEq Index] (plan : Plan Index model)
    (location : ObjectAccessMemory.Lvalue) (memory : ObjectAccessMemory.State model.characters)
    (unique : plan.component.enumeration.items.Nodup) :
    storeState (represent (initialState plan memory)) = represent (initialState (storeResult plan location) memory) := by
  have uniqueNew := enumeration_sum_unique plan.component.enumeration (.fin 2) unique (enumeration_fin_unique 2)
  simp only [storeState, represent, initialState, List.dedup_eq_self.mpr unique,
    storeResult, List.dedup_eq_self.mpr uniqueNew, mapCache, List.map_nil, Option.map_none]
  rfl

theorem SemanticHistory.append [DecidableEq Index] {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before middle after : SemanticState Index model} {first second : List (Occurrence Index model)}
    (earlier : SemanticHistory policy plan before first middle)
    (suffix : SemanticHistory policy plan middle second after) :
    SemanticHistory policy plan before (first ++ second) after := by
  induction earlier with
  | nil state => exact suffix
  | cons before middle after event events step following ih => exact .cons _ _ _ _ _ step (ih suffix)

theorem storeResult_complete [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (location : ObjectAccessMemory.Lvalue) (before after : ObjectAccessMemory.State model.characters)
    (scalar : IntegerScalar.Value model.parameters)
    (clean : ¬ (storeResult plan location).component.evaluation.Undefined)
    (unique : plan.component.enumeration.items.Nodup)
    (events : List (Occurrence Index model)) (final : SemanticState Index model)
    (history : SemanticHistory policy plan (represent (initialState plan before)) events final)
    (drained : final.pending = []) (active : final.halted = none)
    (sameMemory : final.memory = ObjectAccessMemory.represent before)
    (partition : Partition plan final.pending final.cache)
    (value : lookupScalar final.cache plan.component.result = some scalar)
    (writing : Writing model (ObjectAccessMemory.represent before) (ObjectAccessMemory.represent after) location scalar) :
    ∃ allEvents saved,
      SemanticHistory policy (storeResult plan location) (represent (initialState (storeResult plan location) before))
        allEvents saved ∧ saved.pending = [] ∧ saved.halted = none ∧
      saved.memory = ObjectAccessMemory.represent after ∧
      lookupScalar saved.cache (Sum.inr (1 : Fin 2)) = some scalar ∧
      Partition (storeResult plan location) saved.pending saved.cache := by
  let initial := storeState final
  let stored : SemanticState (Index ⊕ Fin 2) model :=
    ⟨[.inr 1], ObjectAccessMemory.represent after, (.inr 0, .stored scalar) :: mapCache final.cache, none⟩
  let saved : SemanticState (Index ⊕ Fin 2) model :=
    ⟨[], ObjectAccessMemory.represent after, (.inr 1, .value scalar) :: stored.cache, none⟩
  have pending : initial.pending = [.inr 0, .inr 1] := by simp [initial, storeState, storePending, drained]
  have available : Available initial.cache (.inl plan.component.result) scalar :=
    mapCache_available _ _ _ ((lookupScalar_iff _ _ _).mp value)
  have storeStep : Reduction policy (storeResult plan location) initial (.inr 0) (.stored scalar) stored := by
    refine .execute _ _ _ _ (storePending_partition _ _ _ _ partition)
      (by simp [initial, storeState, active]) clean ?_ ?_ rfl rfl
    · rw [pending]
      exact .consume _ _ _ ⟨by simp, by
        intro predecessor present prior
        simp only [List.mem_cons, List.not_mem_nil, or_false] at present
        rcases present with rfl | rfl <;> cases prior⟩ (.here _)
    · change OperationEvaluation model policy initial.cache final.memory (.store location (.inl plan.component.result))
        (.stored scalar) (ObjectAccessMemory.represent after)
      rw [sameMemory]
      exact .store _ _ _ _ _ available writing
  have inputAfterStore : Available stored.cache (.inl plan.component.result) scalar := by
    rcases available with ⟨outcome, found, scalarValue⟩
    refine ⟨outcome, ?_, scalarValue⟩
    simpa only [stored, initial, storeState, List.lookup_cons, show ((Sum.inl plan.component.result : Index ⊕ Fin 2) == .inr 0) = false from rfl] using found
  have resultStep : Reduction policy (storeResult plan location) stored (.inr 1) (.value scalar) saved := by
    refine .execute _ _ _ _ storeStep.partition rfl clean ?_ (.copy _ _ _ inputAfterStore) rfl rfl
    exact .consume _ _ _ ⟨by simp [stored], by intro predecessor present prior; simp_all [stored, storeResult, Order.Precedes, afterRoots]⟩ (.here _)
  have earlier := history.storeState location clean
  rw [storeState_initial _ _ _ unique] at earlier
  refine ⟨_, saved, earlier.append (.cons initial stored saved ⟨.inr 0, .stored scalar⟩ [⟨.inr 1, .value scalar⟩] storeStep
      (.cons stored saved saved ⟨.inr 1, .value scalar⟩ [] resultStep (.nil _))),
    rfl, rfl, rfl, ?_, resultStep.partition⟩
  simp only [saved, lookupScalar, List.lookup_cons, beq_self_eq_true, Option.bind_some, Outcome.scalar]

end StoreCompletion


section StoreInvariant
open ExpressionEvents ExpressionEventExecution IntegerMemoryModel ExpressionPlanConstruction Sequencing ValueSequencing
variable {Index : Type} {model : Model}
local instance [DecidableEq Index] : BEq (Index ⊕ Fin 2) := instBEqOfDecidableEq

theorem removal_other {selected other : Index} {before after : List Index}
    (removed : SequencingSchedule.Removal selected before after) (different : other ≠ selected) :
    other ∈ after ↔ other ∈ before := by
  induction removed with
  | here tail => simp [different]
  | there head before after distinct following ih => simp only [List.mem_cons, ih]

def storeValues (plan : Plan Index model)
    (values : Index → Option (IntegerScalar.Value model.parameters)) :
    Index ⊕ Fin 2 → Option (IntegerScalar.Value model.parameters) :=
  Sum.elim values (fun _ => values plan.component.result)

structure StoreAccount [DecidableEq Index] (plan : Plan Index model)
    (before : ObjectAccessMemory.State model.characters) (location : ObjectAccessMemory.Lvalue)
    (values : Index → Option (IntegerScalar.Value model.parameters))
    (state : SemanticState (Index ⊕ Fin 2) model) : Prop where
  cache : CacheAgrees (storeValues plan values) state.cache
  predecessors : ∀ old, Sum.inl old ∈ state.pending → Sum.inr 0 ∈ state.pending
  beforeStore : Sum.inr 0 ∈ state.pending → state.memory = ObjectAccessMemory.represent before
  afterStore : Sum.inr 0 ∉ state.pending → ∃ scalar, values plan.component.result = some scalar ∧
    Writing model (ObjectAccessMemory.represent before) state.memory location scalar

theorem StoreAccount.initial [DecidableEq Index] (plan : Plan Index model)
    (before : ObjectAccessMemory.State model.characters) (location : ObjectAccessMemory.Lvalue)
    (values : Index → Option (IntegerScalar.Value model.parameters)) :
    StoreAccount plan before location values (represent (initialState (storeResult plan location) before)) := by
  have storePending : (Sum.inr (0 : Fin 2)) ∈
      (initialState (storeResult plan location) before).pending := by
    exact List.mem_dedup.mpr ((storeResult plan location).component.enumeration.complete _)
  exact ⟨(by intro index outcome found; cases found), fun _ _ => storePending, fun _ => rfl,
    fun absent => False.elim (absent storePending)⟩

theorem store_operation_result [DecidableEq Index] (policy : SignedConversionPolicy)
    (cache : Cache Index model) (before after : ObjectAccessMemory.SemanticState model.characters)
    (location : ObjectAccessMemory.Lvalue) (source : Index) (outcome : Outcome model)
    (operation : OperationEvaluation model policy cache before (.store location source) outcome after) :
    ∃ scalar, Available cache source scalar ∧ outcome = .stored scalar ∧ Writing model before after location scalar := by
  cases operation with
  | store after location source scalar available writing => exact ⟨scalar, available, rfl, writing⟩

theorem copy_operation_result [DecidableEq Index] (policy : SignedConversionPolicy)
    (cache : Cache Index model) (before after : ObjectAccessMemory.SemanticState model.characters)
    (source : Index) (outcome : Outcome model)
    (operation : OperationEvaluation model policy cache before (.copy source) outcome after) :
    ∃ scalar, Available cache source scalar ∧ outcome = .value scalar ∧ after = before := by
  cases operation with
  | copy source scalar available => exact ⟨scalar, available, rfl, rfl⟩

theorem StoreAccount.step [DecidableEq Index] {policy : SignedConversionPolicy} {plan : Plan Index model}
    {memory : ObjectAccessMemory.State model.characters} {location : ObjectAccessMemory.Lvalue}
    {values : Index → Option (IntegerScalar.Value model.parameters)}
    (readOnly : ReadOnly plan) (equations : ValueEquations policy plan memory values)
    (dominates : ∀ index, index = plan.component.result ∨ plan.component.evaluation.order.Precedes index plan.component.result)
    {before after : SemanticState (Index ⊕ Fin 2) model} {index : Index ⊕ Fin 2} {outcome : Outcome model}
    (account : StoreAccount plan memory location values before)
    (step : Reduction policy (storeResult plan location) before index outcome after) :
    StoreAccount plan memory location values after := by
  cases step with
  | execute _ _ _ partition continuing clean scheduled operation cached halted =>
    cases scheduled with
    | consume _ _ ready removed =>
      have newPredecessor (old : Index) (fresh : Fin 2) :
          (storeResult plan location).component.evaluation.order.Precedes (.inl old) (.inr fresh) :=
        (afterRoots_follows _ _ _ _ _).mpr ⟨_, by simp, dominates old⟩
      cases index with
      | inl index =>
        have pendingStore := account.predecessors index ready.1
        have unchangedBefore := account.beforeStore pendingStore
        have storeRemains := (removal_other removed (by simp)).mpr pendingStore
        change OperationEvaluation model policy before.cache before.memory ((plan.operation index).map Sum.inl) outcome after.memory at operation
        rw [unchangedBefore] at operation
        obtain ⟨unchangedAfter, value⟩ := operation_evaluation_agrees policy memory (storeValues plan values)
          before.cache _ outcome after.memory (operation_map_ne_store _ _ (readOnly index)) account.cache operation
        rw [operationValue_map] at value
        have observed : outcome.scalar = storeValues plan values (.inl index) := value.trans (equations index).symm
        refine ⟨?_, ?_, fun _ => unchangedAfter, fun absent => False.elim (absent storeRemains)⟩
        · rw [cached]; exact account.cache.cons _ _ observed
        · intro old _; exact storeRemains
      | inr index =>
        have allOldGone : ∀ old, Sum.inl old ∉ before.pending :=
          fun old present => ready.2 _ present (newPredecessor old index)
        have noOldAfter : ∀ old, Sum.inl old ∉ after.pending :=
          fun old present => allOldGone old (removed.sublist.subset present)
        have casesIndex : index = 0 ∨ index = 1 := by omega
        rcases casesIndex with rfl | rfl
        · have unchangedBefore := account.beforeStore ready.1
          change OperationEvaluation model policy before.cache before.memory
            (.store location (.inl plan.component.result)) outcome after.memory at operation
          obtain ⟨scalar, available, observed, written⟩ := store_operation_result policy _ _ _ _ _ _ operation
          have value := account.cache.lookup ((lookupScalar_iff _ _ _).mpr available)
          have assignedValue : values plan.component.result = some scalar := value
          rw [unchangedBefore] at written
          refine ⟨?_, fun old present => False.elim (noOldAfter old present), ?_, fun _ => ⟨scalar, assignedValue, written⟩⟩
          · rw [cached]; exact account.cache.cons _ _ (by rw [observed]; exact value.symm)
          · intro impossible
            exact False.elim (removed.absent (List.nodup_append.mp partition.1).1 impossible)
        · change OperationEvaluation model policy before.cache before.memory
            (.copy (.inl plan.component.result)) outcome after.memory at operation
          obtain ⟨scalar, available, observed, unchanged⟩ := copy_operation_result policy _ _ _ _ _ operation
          have value := account.cache.lookup ((lookupScalar_iff _ _ _).mpr available)
          have retained : Sum.inr (0 : Fin 2) ∈ after.pending ↔ Sum.inr (0 : Fin 2) ∈ before.pending :=
            removal_other removed (by simp)
          refine ⟨?_, fun old present => False.elim (noOldAfter old present), ?_, ?_⟩
          · rw [cached]; exact account.cache.cons _ _ (by rw [observed]; exact value.symm)
          · intro present; exact unchanged.trans (account.beforeStore (retained.mp present))
          · intro absent
            obtain ⟨scalar, value, written⟩ := account.afterStore (fun present => absent (retained.mpr present))
            exact ⟨scalar, value, by rw [unchanged]; exact written⟩

theorem SemanticHistory.storeAccount [DecidableEq Index] {policy : SignedConversionPolicy} {plan : Plan Index model}
    {memory : ObjectAccessMemory.State model.characters} {location : ObjectAccessMemory.Lvalue}
    {values : Index → Option (IntegerScalar.Value model.parameters)}
    (readOnly : ReadOnly plan) (equations : ValueEquations policy plan memory values)
    (dominates : ∀ index, index = plan.component.result ∨ plan.component.evaluation.order.Precedes index plan.component.result)
    {before after : SemanticState (Index ⊕ Fin 2) model} {events : List (Occurrence (Index ⊕ Fin 2) model)}
    (history : SemanticHistory policy (storeResult plan location) before events after)
    (account : StoreAccount plan memory location values before) : StoreAccount plan memory location values after := by
  induction history with
  | nil state => exact account
  | cons before middle after event events step following ih =>
    exact ih (account.step readOnly equations dominates step)

theorem storeResult_history_sound [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (memory : ObjectAccessMemory.State model.characters) (location : ObjectAccessMemory.Lvalue)
    (values : Index → Option (IntegerScalar.Value model.parameters))
    (readOnly : ReadOnly plan) (equations : ValueEquations policy plan memory values)
    (dominates : ∀ index, index = plan.component.result ∨ plan.component.evaluation.order.Precedes index plan.component.result)
    (events : List (Occurrence (Index ⊕ Fin 2) model)) (final : SemanticState (Index ⊕ Fin 2) model)
    (history : SemanticHistory policy (storeResult plan location)
      (represent (initialState (storeResult plan location) memory)) events final)
    (drained : final.pending = []) (scalar : IntegerScalar.Value model.parameters)
    (value : lookupScalar final.cache (.inr 1) = some scalar) :
    values plan.component.result = some scalar ∧
      Writing model (ObjectAccessMemory.represent memory) final.memory location scalar := by
  have account := history.storeAccount readOnly equations dominates (StoreAccount.initial plan memory location values)
  have observed : values plan.component.result = some scalar := account.cache.lookup value
  obtain ⟨written, writtenValue, writing⟩ := account.afterStore (by simp [drained])
  have same := Option.some.inj (writtenValue.symm.trans observed)
  subst written
  exact ⟨observed, writing⟩
end StoreInvariant

end Mettapedia.Languages.C11.ExpressionEventHistory
