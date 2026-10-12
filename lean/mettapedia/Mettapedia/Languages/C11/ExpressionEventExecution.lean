import Mettapedia.Languages.C11.ExpressionEvents
import Mettapedia.Languages.C11.SequencingSchedule
import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mathlib.Data.List.Dedup

/-!
# Executable integer expression occurrences

Operations consume retained typed values and apply the independent arithmetic,
conversion and owned-memory judgments. Value production and memory modification
are separate occurrences. Scheduling checks the original source relation and
its scalar conflicts before selecting an occurrence; chronological selection
never creates a source sequencing edge.

Configurations retain the complete plan, pending occurrences, memory, cached
observations and scheduler input. Arithmetic faults, conversion signals and
object representation traps retain their exact outcome and endpoint. Missing
inputs or refused accesses remain model refusals. This does not implement
signal delivery, volatile interactions or host publication authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ExpressionEventExecution

open ExpressionEvents IntegerMemoryModel
open Mettapedia.GSLT.Distinction.ProductiveBlocks (Machine Transition)

variable {Index : Type} {model : Model}

inductive OperationEvaluation [DecidableEq Index] (model : Model)
    (policy : SignedConversionPolicy) (cache : Cache Index model) :
    ObjectAccessMemory.SemanticState model.characters → Operation Index model → Outcome model →
      ObjectAccessMemory.SemanticState model.characters → Prop where
  | constant (memory : ObjectAccessMemory.SemanticState model.characters)
      (scalar : IntegerScalar.Value model.parameters) :
      OperationEvaluation model policy cache memory (.constant scalar) (.value scalar) memory
  | copy (memory : ObjectAccessMemory.SemanticState model.characters) (source : Index)
      (scalar : IntegerScalar.Value model.parameters) (available : Available cache source scalar) :
      OperationEvaluation model policy cache memory (.copy source) (.value scalar) memory
  | load (memory : ObjectAccessMemory.SemanticState model.characters) (location : ObjectAccessMemory.Lvalue)
      (loaded : Loaded model) (reading : Loading model memory location loaded) :
      OperationEvaluation model policy cache memory (.load location) (loadedOutcome model loaded) memory
  | binary (memory : ObjectAccessMemory.SemanticState model.characters) (operator : IntegerBinaryOperator)
      (first second : Index) (left right : IntegerScalar.Value model.parameters)
      (result : IntegerScalar.ArithmeticResult model.parameters)
      (leftAvailable : Available cache first left) (rightAvailable : Available cache second right)
      (arithmetic : IntegerScalar.ArithmeticEvaluation model.parameters policy operator left right result) :
      OperationEvaluation model policy cache memory (.binary operator first second)
        (arithmeticOutcome model result) memory
  | cast (memory : ObjectAccessMemory.SemanticState model.characters) (type : IntegerType IntegerExtension)
      (source : Index) (input : IntegerScalar.Value model.parameters)
      (result : IntegerScalar.CastResult model.parameters) (available : Available cache source input)
      (conversion : IntegerScalar.CastEvaluation model.parameters policy type input result) :
      OperationEvaluation model policy cache memory (.cast type source) (castOutcome model result) memory
  | store (before after : ObjectAccessMemory.SemanticState model.characters)
      (location : ObjectAccessMemory.Lvalue) (source : Index) (scalar : IntegerScalar.Value model.parameters)
      (available : Available cache source scalar) (writing : Writing model before after location scalar) :
      OperationEvaluation model policy cache before (.store location source) (.stored scalar) after

def executeOperation [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (cache : Cache Index model) :
    Operation Index model → Option (Outcome model × ObjectAccessMemory.State model.characters)
  | .constant scalar => some (.value scalar, memory)
  | .copy source => do
      let scalar ← lookupScalar cache source
      some (.value scalar, memory)
  | .load location => (load model memory location).map (fun loaded => (loadedOutcome model loaded, memory))
  | .binary operator first second => do
      let left ← lookupScalar cache first
      let right ← lookupScalar cache second
      some (arithmeticOutcome model (IntegerScalar.binary model.parameters operator left right), memory)
  | .cast type source => do
      let input ← lookupScalar cache source
      some (castOutcome model (IntegerScalar.cast model.parameters policy type input), memory)
  | .store location source => do
      let scalar ← lookupScalar cache source
      let after ← store model memory location scalar
      some (.stored scalar, after)

theorem executeOperation_sound [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (before after : ObjectAccessMemory.State model.characters) (cache : Cache Index model)
    (operation : Operation Index model) (outcome : Outcome model)
    (computed : executeOperation model policy before cache operation = some (outcome, after)) :
    OperationEvaluation model policy cache (ObjectAccessMemory.represent before) operation outcome
      (ObjectAccessMemory.represent after) := by
  cases operation with
  | constant scalar =>
      simp only [executeOperation, Option.some.injEq, Prod.mk.injEq] at computed
      obtain ⟨rfl, rfl⟩ := computed
      exact .constant _ _
  | copy source =>
      obtain ⟨scalar, available, same⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact .copy _ _ _ ((lookupScalar_iff _ _ _).mp available)
  | load location =>
      obtain ⟨loaded, observed, same⟩ := Option.map_eq_some_iff.mp computed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact .load _ _ _ (load_sound _ _ _ _ observed)
  | binary operator first second =>
      obtain ⟨left, leftAvailable, following⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨right, rightAvailable, same⟩ := Option.bind_eq_some_iff.mp following
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact .binary _ _ _ _ _ _ _ ((lookupScalar_iff _ _ _).mp leftAvailable)
        ((lookupScalar_iff _ _ _).mp rightAvailable) ((IntegerScalar.binary_iff _ _ _ _ _ _).mp rfl)
  | cast type source =>
      obtain ⟨input, available, same⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact .cast _ _ _ _ _ ((lookupScalar_iff _ _ _).mp available) (IntegerScalar.cast_sound _ _ _ _)
  | store location source =>
      obtain ⟨scalar, available, following⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨saved, written, same⟩ := Option.bind_eq_some_iff.mp following
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact .store _ _ _ _ _ ((lookupScalar_iff _ _ _).mp available) (store_sound _ _ _ _ _ written)

theorem executeOperation_complete [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (before : ObjectAccessMemory.State model.characters) (after : ObjectAccessMemory.SemanticState model.characters)
    (cache : Cache Index model) (operation : Operation Index model) (outcome : Outcome model)
    (evaluated : OperationEvaluation model policy cache (ObjectAccessMemory.represent before) operation outcome after) :
    ∃ saved, executeOperation model policy before cache operation = some (outcome, saved) ∧
      ObjectAccessMemory.represent saved = after := by
  cases evaluated with
  | constant scalar => exact ⟨before, rfl, rfl⟩
  | copy source scalar available =>
      exact ⟨before, by simp [executeOperation, (lookupScalar_iff _ _ _).mpr available], rfl⟩
  | load location loaded reading =>
      exact ⟨before, by simp [executeOperation, load_complete _ _ _ _ reading], rfl⟩
  | binary operator first second left right result leftAvailable rightAvailable arithmetic =>
      refine ⟨before, ?_, rfl⟩
      simp only [executeOperation, (lookupScalar_iff _ _ _).mpr leftAvailable,
        (lookupScalar_iff _ _ _).mpr rightAvailable, bind, Option.bind_some,
        (IntegerScalar.binary_iff _ _ _ _ _ _).mpr arithmetic]
  | cast type source input result available conversion =>
      refine ⟨before, ?_, rfl⟩
      simp only [executeOperation, (lookupScalar_iff _ _ _).mpr available, bind, Option.bind_some,
        IntegerScalar.cast_complete _ _ _ _ _ conversion]
  | store after location source scalar available writing =>
      obtain ⟨saved, written, represented⟩ := store_complete _ _ _ _ _ writing
      exact ⟨saved, by simp [executeOperation, (lookupScalar_iff _ _ _).mpr available, written], represented⟩

theorem executeOperation_iff [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (before : ObjectAccessMemory.State model.characters) (after : ObjectAccessMemory.SemanticState model.characters)
    (cache : Cache Index model) (operation : Operation Index model) (outcome : Outcome model) :
    (∃ saved, executeOperation model policy before cache operation = some (outcome, saved) ∧
      ObjectAccessMemory.represent saved = after) ↔
    OperationEvaluation model policy cache (ObjectAccessMemory.represent before) operation outcome after := by
  constructor
  · rintro ⟨saved, computed, rfl⟩
    exact executeOperation_sound _ _ _ _ _ _ _ computed
  · exact executeOperation_complete _ _ _ _ _ _ _

structure State (Index : Type) (model : Model) where
  pending : List Index
  memory : ObjectAccessMemory.State model.characters
  cache : Cache Index model
  halted : Option (Index × Outcome model) := none

structure SemanticState (Index : Type) (model : Model) where
  pending : List Index
  memory : ObjectAccessMemory.SemanticState model.characters
  cache : Cache Index model
  halted : Option (Index × Outcome model) := none

def represent (state : State Index model) : SemanticState Index model :=
  ⟨state.pending, ObjectAccessMemory.represent state.memory, state.cache, state.halted⟩

def Partition (plan : Plan Index model) (pending : List Index) (cache : Cache Index model) : Prop :=
  (pending ++ cache.map Prod.fst).Nodup ∧
    ∀ index ∈ plan.component.enumeration.items, index ∈ pending ∨ index ∈ cache.map Prod.fst

def partitionCheck [DecidableEq Index] (plan : Plan Index model) (pending : List Index)
    (cache : Cache Index model) : Bool :=
  decide (pending ++ cache.map Prod.fst).Nodup &&
    plan.component.enumeration.items.all (fun index => decide (index ∈ pending ∨ index ∈ cache.map Prod.fst))

theorem partitionCheck_iff [DecidableEq Index] (plan : Plan Index model) (pending : List Index)
    (cache : Cache Index model) : partitionCheck plan pending cache = true ↔ Partition plan pending cache := by
  simp only [partitionCheck, Partition, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]

def initialState [DecidableEq Index] (plan : Plan Index model)
    (memory : ObjectAccessMemory.State model.characters) : State Index model :=
  ⟨plan.component.enumeration.items.dedup, memory, [], none⟩

theorem initial_partition [DecidableEq Index] (plan : Plan Index model)
    (memory : ObjectAccessMemory.State model.characters) :
    Partition plan (initialState plan memory).pending (initialState plan memory).cache := by
  constructor
  · simpa only [initialState, List.map_nil, List.append_nil] using
      List.nodup_dedup plan.component.enumeration.items
  · intro index present
    exact Or.inl (List.mem_dedup.mpr present)

theorem ready_inputs_cached [DecidableEq Index] (plan : Plan Index model)
    (pending : List Index) (cache : Cache Index model) (index : Index)
    (partition : Partition plan pending cache) (ordered : plan.InputsOrdered)
    (ready : SequencingSchedule.Ready plan.component.evaluation.order pending index) :
    ∀ source ∈ (plan.operation index).inputs, source ∈ cache.map Prod.fst := by
  intro source present
  obtain pending | cached := partition.2 source (plan.component.enumeration.complete source)
  · exact False.elim (ready.2 source pending (ordered index source present))
  · exact cached

def haltAfter (index : Index) (outcome : Outcome model) : Option (Index × Outcome model) :=
  if outcome.terminal then some (index, outcome) else none

inductive Reduction [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model) :
    SemanticState Index model → Index → Outcome model → SemanticState Index model → Prop where
  | execute (before after : SemanticState Index model) (index : Index) (outcome : Outcome model)
      (partition : Partition plan before.pending before.cache)
      (continuing : before.halted = none)
      (clean : ¬ plan.component.evaluation.Undefined)
      (scheduled : SequencingSchedule.Step plan.component.evaluation.order before.pending index after.pending)
      (operation : OperationEvaluation model policy before.cache before.memory (plan.operation index) outcome after.memory)
      (cached : after.cache = (index, outcome) :: before.cache)
      (halted : after.halted = haltAfter index outcome) : Reduction policy plan before index outcome after

def admissible [DecidableEq Index] (plan : Plan Index model) : Bool :=
  decide (plan.component.evaluation.findConflict plan.component.enumeration = none)

theorem admissible_iff [DecidableEq Index] (plan : Plan Index model) :
    admissible plan = true ↔ ¬ plan.component.evaluation.Undefined := by
  simp only [admissible, decide_eq_true_eq]
  exact plan.component.evaluation.findConflict_none_iff plan.component.enumeration

def permitted [DecidableEq Index] (plan : Plan Index model) (before : State Index model) : Bool :=
  admissible plan && partitionCheck plan before.pending before.cache

def execute [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (before : State Index model) (index : Index) : Option (Outcome model × State Index model) := do
  if permitted plan before then
    match before.halted with
    | some _ => none
    | none =>
        let pending ← SequencingSchedule.select plan.component.evaluation.order before.pending index
        let (outcome, memory) ← executeOperation model policy before.memory before.cache (plan.operation index)
        some (outcome, ⟨pending, memory, (index, outcome) :: before.cache, haltAfter index outcome⟩)
  else none

theorem execute_sound [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (before after : State Index model) (index : Index) (outcome : Outcome model)
    (computed : execute policy plan before index = some (outcome, after)) :
    Reduction policy plan (represent before) index outcome (represent after) := by
  by_cases allowed : permitted plan before = true
  · cases halted : before.halted with
    | some stopped => simp [execute, allowed, halted] at computed
    | none =>
        cases selected : SequencingSchedule.select plan.component.evaluation.order before.pending index with
        | none => simp [execute, allowed, halted, selected] at computed
        | some pending =>
            cases operated : executeOperation model policy before.memory before.cache (plan.operation index) with
            | none => simp [execute, allowed, halted, selected, operated] at computed
            | some result =>
                rcases result with ⟨result, memory⟩
                simp [execute, allowed, halted, selected, operated] at computed
                obtain ⟨rfl, rfl⟩ := computed
                obtain ⟨clean, partition⟩ := Bool.and_eq_true_iff.mp allowed
                exact .execute _ _ index result ((partitionCheck_iff _ _ _).mp partition) halted
                  ((admissible_iff _).mp clean)
                  (SequencingSchedule.select_sound _ _ _ _ selected)
                  (executeOperation_sound _ _ _ _ _ _ _ operated) rfl rfl
  · simp [execute, allowed] at computed

theorem execute_complete [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (before : State Index model) (after : SemanticState Index model) (index : Index) (outcome : Outcome model)
    (reduced : Reduction policy plan (represent before) index outcome after) :
    ∃ saved, execute policy plan before index = some (outcome, saved) ∧ represent saved = after := by
  cases reduced with
  | execute _ after _ partition continuing clean scheduled operation cached halted =>
      obtain ⟨memory, operated, finalMemory⟩ := executeOperation_complete _ _ _ _ _ _ _ operation
      change executeOperation model policy before.memory before.cache (plan.operation index) = some (outcome, memory) at operated
      have selected : SequencingSchedule.select plan.component.evaluation.order before.pending index = some after.pending :=
        SequencingSchedule.select_complete _ _ _ _ scheduled
      have checked : partitionCheck plan before.pending before.cache = true := (partitionCheck_iff _ _ _).mpr partition
      have allowed := (admissible_iff _).mpr clean
      have permitted : permitted plan before = true := by simp only [permitted, allowed, checked]; rfl
      refine ⟨⟨after.pending, memory, (index, outcome) :: before.cache, haltAfter index outcome⟩, ?_, ?_⟩
      · simp only [execute, permitted, ↓reduceIte,
          show before.halted = none from continuing, selected, operated, bind, Option.bind_some]
      · cases after
        dsimp only [represent] at cached halted
        simp only [represent, finalMemory]
        rw [cached, halted]

theorem execute_iff [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (before : State Index model) (after : SemanticState Index model) (index : Index) (outcome : Outcome model) :
    (∃ saved, execute policy plan before index = some (outcome, saved) ∧ represent saved = after) ↔
      Reduction policy plan (represent before) index outcome after := by
  constructor
  · rintro ⟨saved, computed, rfl⟩
    exact execute_sound _ _ _ _ _ _ computed
  · exact execute_complete _ _ _ _ _ _

theorem Partition.consume [DecidableEq Index] (plan : Plan Index model)
    (before after : List Index) (cache : Cache Index model) (index : Index) (outcome : Outcome model)
    (partition : Partition plan before cache) (removed : SequencingSchedule.Removal index before after) :
    Partition plan after ((index, outcome) :: cache) := by
  obtain ⟨pendingUnique, cacheUnique, disjoint⟩ := List.nodup_append.mp partition.1
  constructor
  · simp only [List.map_cons, List.nodup_append, List.nodup_cons]
    refine ⟨removed.unique pendingUnique, ⟨?_, cacheUnique⟩, ?_⟩
    · intro cached
      exact disjoint index removed.present index cached rfl
    · intro first present second cached
      rcases List.mem_cons.mp cached with rfl | cached
      · intro same
        subst first
        exact removed.absent pendingUnique present
      · exact disjoint first (removed.sublist.subset present) second cached
  · intro selected present
    obtain pending | cached := partition.2 selected present
    · by_cases same : selected = index
      · exact Or.inr (by simp [same])
      · have afterPresent : selected ∈ after := by
          rw [← removed.erase]
          exact (List.mem_erase_of_ne same).mpr pending
        exact Or.inl afterPresent
    · exact Or.inr (by simp [cached])

theorem Reduction.partition [DecidableEq Index] {policy : SignedConversionPolicy}
    {plan : Plan Index model} {before after : SemanticState Index model} {index : Index} {outcome : Outcome model}
    (reduced : Reduction policy plan before index outcome after) : Partition plan after.pending after.cache := by
  cases reduced with
  | execute _ _ _ partition continuing clean scheduled operation cached halted =>
      rw [cached]
      cases scheduled with
      | consume _ _ ready removed => exact partition.consume _ _ _ _ _ _ removed

theorem executed_consumes_once [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (before after : State Index model) (index : Index) (outcome : Outcome model)
    (computed : execute policy plan before index = some (outcome, after)) :
    after.pending.length + 1 = before.pending.length ∧ after.pending.Nodup ∧ index ∉ after.pending := by
  cases execute_sound _ _ _ _ _ _ computed with
  | execute _ _ _ partition continuing clean scheduled operation cached halted =>
      have unique := (List.nodup_append.mp partition.1).1
      cases scheduled with
      | consume _ _ ready removed => exact ⟨removed.length, removed.unique unique, removed.absent unique⟩

theorem executed_fresh_cache [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (before after : State Index model) (index : Index) (outcome : Outcome model)
    (computed : execute policy plan before index = some (outcome, after)) :
    before.cache.lookup index = none ∧ after.cache.lookup index = some outcome := by
  cases execute_sound _ _ _ _ _ _ computed with
  | execute _ _ _ partition continuing clean scheduled operation cached halted =>
      have disjoint := (List.nodup_append.mp partition.1).2.2
      cases scheduled with
      | consume _ _ ready removed =>
          constructor
          · apply List.lookup_eq_none_iff.mpr
            intro pair present
            have different := disjoint index ready.1 pair.1 (List.mem_map_of_mem (f := Prod.fst) present)
            simpa only [bne_iff_ne] using different
          · change after.cache = (index, outcome) :: before.cache at cached
            rw [cached]
            simp

theorem Reduction.available_preserved [DecidableEq Index] {policy : SignedConversionPolicy}
    {plan : Plan Index model} {before after : SemanticState Index model} {index source : Index}
    {outcome : Outcome model} {scalar : IntegerScalar.Value model.parameters}
    (reduced : Reduction policy plan before index outcome after) (different : source ≠ index)
    (available : Available before.cache source scalar) : Available after.cache source scalar := by
  cases reduced with
  | execute _ _ _ partition continuing clean scheduled operation cached halted =>
      obtain ⟨observed, found, value⟩ := available
      have distinct : (source == index) = false := by simpa only [beq_eq_false_iff_ne] using different
      exact ⟨observed, by simp [cached, List.lookup_cons, distinct, found], value⟩

structure Configuration (Index : Type) (model : Model) where
  plan : Plan Index model
  state : State Index model
  selections : List Index

structure Receipt (Index : Type) (model : Model) where
  index : Index
  outcome : Outcome model
  before : State Index model
  after : State Index model

inductive Verdict (Index : Type) (model : Model) where
  | returned (scalar : IntegerScalar.Value model.parameters) (saved : Configuration Index model)
  | terminal (index : Index) (outcome : Outcome model) (saved : Configuration Index model)
  | unsequenced (first second : Index) (saved : Configuration Index model)
  | refused (saved : Configuration Index model)

structure SelectionRequest (Index : Type) where
  enabled : List Index
  deriving DecidableEq, Repr

def machine [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy) :
    Machine (Configuration Index model) (Receipt Index model) (Verdict Index model) (SelectionRequest Index) where
  step configuration := some <|
    match configuration.plan.component.evaluation.findConflict configuration.plan.component.enumeration with
    | some (first, second) => .finish (.unsequenced first second configuration)
    | none => if partitionCheck configuration.plan configuration.state.pending configuration.state.cache then
      match configuration.state.halted with
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
                  | some (outcome, after) =>
                      .publish [⟨index, outcome, configuration.state, after⟩]
                        ⟨configuration.plan, after, rest⟩
    else .finish (.refused configuration)

theorem conflict_reported [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (configuration : Configuration Index model) (first second : Index)
    (found : configuration.plan.component.evaluation.findConflict configuration.plan.component.enumeration =
      some (first, second)) :
    (machine model policy).step configuration = some (.finish (.unsequenced first second configuration)) ∧
      configuration.plan.component.evaluation.BadPair first second := by
  exact ⟨by simp only [machine, found],
    configuration.plan.component.evaluation.findConflict_sound configuration.plan.component.enumeration _ found⟩

theorem conflict_no_commits [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (configuration : Configuration Index model) (first second : Index) (fuel : Nat)
    (found : configuration.plan.component.evaluation.findConflict configuration.plan.component.enumeration =
      some (first, second)) : ((machine model policy).run fuel configuration).1 = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [(machine model policy).run_succ_finish (conflict_reported _ _ _ _ _ found).1]

def ValidReceipt [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (receipt : Receipt Index model) : Prop :=
  Reduction policy plan (represent receipt.before) receipt.index receipt.outcome (represent receipt.after)

theorem step_of_execute [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (before after : State Index model) (index : Index) (rest : List Index) (outcome : Outcome model)
    (computed : execute policy plan before index = some (outcome, after)) :
    (machine model policy).step ⟨plan, before, index :: rest⟩ =
      some (.publish [⟨index, outcome, before, after⟩] ⟨plan, after, rest⟩) := by
  cases execute_sound _ _ _ _ _ _ computed with
  | execute _ _ _ partition continuing clean scheduled operation cached halted =>
      have allowed := (admissible_iff _).mpr clean
      have checked : partitionCheck plan before.pending before.cache = true := (partitionCheck_iff _ _ _).mpr partition
      have noConflict : plan.component.evaluation.findConflict plan.component.enumeration = none :=
        of_decide_eq_true allowed
      have continuing : before.halted = none := continuing
      have nonempty : before.pending ≠ [] := by
        cases scheduled with
        | consume _ _ ready removed =>
            intro empty
            change SequencingSchedule.Ready plan.component.evaluation.order before.pending index at ready
            rw [empty] at ready
            cases ready.1
      cases pending : before.pending with
      | nil => exact False.elim (nonempty pending)
      | cons head tail =>
          simp only [machine, noConflict, checked, ↓reduceIte]
          simp [continuing, pending, computed]

theorem run_receipts_valid [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (initial : Configuration Index model) :
    ∀ receipt ∈ ((machine model policy).run fuel initial).1, ValidReceipt policy initial.plan receipt := by
  induction fuel generalizing initial with
  | zero => simp [Machine.run]
  | succ fuel ih =>
      cases conflict : initial.plan.component.evaluation.findConflict initial.plan.component.enumeration with
      | some pair => cases pair; simp [Machine.run, machine, conflict]
      | none =>
        by_cases checked : partitionCheck initial.plan initial.state.pending initial.state.cache = true
        · cases halted : initial.state.halted with
        | some stopped =>
            rcases stopped with ⟨index, outcome⟩
            simp only [Machine.run, machine, conflict, checked, ↓reduceIte, halted]
            by_cases terminal : outcome.terminal = true <;>
              simp [terminal]
        | none =>
            cases pending : initial.state.pending with
            | nil =>
                have checked : partitionCheck initial.plan [] initial.state.cache = true := by
                  simpa only [pending] using checked
                simp only [Machine.run, machine, conflict, checked, ↓reduceIte, halted, pending]
                cases lookupScalar initial.state.cache initial.plan.component.result <;> simp
            | cons head tail =>
                cases selections : initial.selections with
                | nil =>
                    simp only [Machine.run, machine, conflict, checked, ↓reduceIte]
                    simp [halted, pending, selections]
                | cons index rest =>
                    cases computed : execute policy initial.plan initial.state index with
                    | none =>
                        simp only [Machine.run, machine, conflict, checked, ↓reduceIte]
                        simp [halted, pending, selections, computed]
                    | some result =>
                        rcases result with ⟨outcome, after⟩
                        have stepped := step_of_execute policy initial.plan initial.state after index rest outcome computed
                        have initialForm : initial = ⟨initial.plan, initial.state, index :: rest⟩ := by
                          cases initial
                          simp_all
                        rw [initialForm, (machine model policy).run_succ_publish stepped]
                        intro receipt present
                        rcases List.mem_cons.mp present with rfl | present
                        · exact execute_sound _ _ _ _ _ _ computed
                        · exact ih ⟨initial.plan, after, rest⟩ receipt present
        · simp [Machine.run, machine, conflict, checked]

theorem resume_after_prefix [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (first second : Nat) (initial saved : Configuration Index model) (events : List (Receipt Index model))
    (paused : (machine model policy).run first initial = (events, .exhausted saved)) :
    (machine model policy).run (first + second) initial =
      (events ++ ((machine model policy).run second saved).1, ((machine model policy).run second saved).2) :=
  (machine model policy).established_and_pending first second initial saved events paused

theorem resumed_accounts [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (price : Configuration Index model → Nat) (first second : Nat)
    (initial saved : Configuration Index model) (events : List (Receipt Index model))
    (paused : (machine model policy).run first initial = (events, .exhausted saved)) :
    (machine model policy).spent price (first + second) initial =
      (machine model policy).spent price first initial + (machine model policy).spent price second saved := by
  rw [(machine model policy).spent_add, paused]
  rfl

def productive [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy) :
    (machine (Index := Index) model policy).Productive where
  rank _ := 0
  moves configuration := by simp [machine]
  silent_decreases := by
    intro configuration next silent
    simp only [machine, Option.some.injEq] at silent
    split at silent
    · contradiction
    · split at silent
      · split at silent
        · split at silent <;> contradiction
        · split at silent
          · split at silent <;> contradiction
          · split at silent
            · contradiction
            · split at silent <;> contradiction
      · contradiction

end Mettapedia.Languages.C11.ExpressionEventExecution
