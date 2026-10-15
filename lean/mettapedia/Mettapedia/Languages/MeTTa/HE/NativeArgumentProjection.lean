import Mettapedia.Languages.MeTTa.HE.TypedApplyEncoding
import Mettapedia.Languages.MeTTa.HE.RetainedArgumentSpecification

/-!
# Projection of native HE argument-consumer phases

The semantic fields follow `InterpretFunctionArgsFrame` and its shared
argument registers: source/domains, selected prefix/index, caller bindings,
original argument, resolved domain, ordered outcomes and outcome cursor.
The borrowed child selection is retained until the after-child cleanup.

The projection constructs the existing typed-application consumer. Each
outcome advance has its independent transition witness, including failed
merges, changed errors and failed binder extension. Domain demand is stated
separately from consumption: HE's raw gate checks the substituted value,
rather than assuming that a variable-shaped source is still unbound.

This is a checked semantic snapshot schema and phase projection. No native
export hook, ABI/allocator verification, or whole evaluator refinement is
asserted. Native binding projection, substitution, domain refinement, merge,
extension and callback suspension remain explicit implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeArgumentProjection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open TypedApplyEncoding (stateData readState resultsData readResults index readIndex
  bindingsData readBindings)

inductive Phase where
  | iterate
  | afterChild
  deriving Repr, DecidableEq

structure Snapshot where
  state : TypedApplyState
  original : Atom
  domain : Atom
  outcomes : ResultList
  nextOutcome : Nat
  phase : Phase
  activeValue : Option Atom
  activeBindings : Option Bindings
  deriving Repr

def Snapshot.pending (snapshot : Snapshot) : ResultList :=
  snapshot.outcomes.drop snapshot.nextOutcome

def Snapshot.consumer (snapshot : Snapshot) : TypedApplyFrame :=
  .argConsumer snapshot.pending snapshot.original snapshot.domain snapshot.state

def Snapshot.configuration (snapshot : Snapshot) (rest : List TypedApplyFrame)
    (history : ResultList) : TypedApplyConfig := ⟨snapshot.consumer :: rest, history⟩

def Snapshot.afterOutcome (snapshot : Snapshot) : Snapshot :=
  {snapshot with nextOutcome := snapshot.nextOutcome + 1}

theorem pending_afterOutcome (snapshot : Snapshot) :
    snapshot.afterOutcome.pending = snapshot.pending.tail := by
  simp only [Snapshot.pending, Snapshot.afterOutcome]
  rw [← List.drop_drop]
  cases snapshot.outcomes.drop snapshot.nextOutcome <;> rfl

/-- The callback result is already available at this phase. Merge and binder
extension are distinct operations, with distinct failure branches. -/
inductive Action where
  | exhausted
  | skipped (saved : Snapshot)
  | failure (result : ResultPair) (saved : Snapshot)
  | child (selected : ResultPair) (saved : Snapshot)

def consume (merge : Bindings → Bindings → Option Bindings)
    (extend : Bindings → Atom → Atom → Option Bindings) (snapshot : Snapshot) : Action :=
  match snapshot.pending with
  | [] => .exhausted
  | (value, evaluated) :: _ =>
      let saved := snapshot.afterOutcome
      match merge snapshot.state.env evaluated with
      | none => .skipped saved
      | some merged =>
          if isEmptyOrError value && decide (value ≠ snapshot.original) then
            .failure (value, merged) saved
          else match extend merged snapshot.domain value with
            | none => .skipped saved
            | some extended => .child (value, extended)
                {saved with phase := .afterChild, activeValue := some value, activeBindings := some extended}

def actionConfiguration (before : Snapshot) (rest : List TypedApplyFrame)
    (history : ResultList) : Action → TypedApplyConfig
  | .exhausted => ⟨rest, history⟩
  | .skipped saved => saved.configuration rest history
  | .failure result saved => saved.configuration rest (history ++ [result])
  | .child selected saved =>
      ⟨.apply (before.state.advance selected.1 selected.2) :: saved.consumer :: rest, history⟩

/-- The source loop and the existing consumer have different representations;
their computed successors agree after the constructed projection. -/
theorem consume_projection
    (merge : Bindings → Bindings → Option Bindings)
    (extend : Bindings → Atom → Atom → Option Bindings)
    (snapshot : Snapshot) (rest : List TypedApplyFrame) (history : ResultList) :
    actionConfiguration snapshot rest history (consume merge extend snapshot) =
      processConsumerFrame merge extend snapshot.pending snapshot.original snapshot.domain
        snapshot.state rest history := by
  unfold consume processConsumerFrame
  cases pending : snapshot.pending with
  | nil => rfl
  | cons selected remaining =>
      obtain ⟨value, evaluated⟩ := selected
      have after : snapshot.afterOutcome.pending = remaining := by
        rw [pending_afterOutcome, pending]
        rfl
      have afterExpanded : snapshot.outcomes.drop (snapshot.nextOutcome + 1) = remaining := after
      cases merged : merge snapshot.state.env evaluated with
      | none => simp [merged, actionConfiguration, Snapshot.configuration, Snapshot.consumer,
          Snapshot.pending, Snapshot.afterOutcome, afterExpanded]
      | some bindings =>
          by_cases failed : isEmptyOrError value = true ∧ value ≠ snapshot.original
          · simp [merged, failed, actionConfiguration, Snapshot.configuration, Snapshot.consumer,
              Snapshot.pending, Snapshot.afterOutcome, afterExpanded]
          · simp only [merged, Bool.and_eq_true, decide_eq_true_eq, if_neg failed]
            cases extended : extend bindings snapshot.domain value with
            | none => simp [actionConfiguration, Snapshot.configuration, Snapshot.consumer,
                Snapshot.pending, Snapshot.afterOutcome, afterExpanded]
            | some bindings =>
                simp [actionConfiguration, Snapshot.consumer,
                  Snapshot.pending, Snapshot.afterOutcome, afterExpanded]

/-- Every projected source advance constructs an independent typed consumer
transition for arbitrary values, domains, bindings and surrounding stacks. -/
theorem consume_transition (evaluate apply merge extend raw)
    (snapshot : Snapshot) (rest : List TypedApplyFrame) (history : ResultList) :
    TypedApplyStep evaluate apply merge extend raw
      (snapshot.configuration rest history)
      (actionConfiguration snapshot rest history (consume merge extend snapshot)) := by
  rw [consume_projection]
  exact processConsumerFrame_spec evaluate apply merge extend raw
    snapshot.pending snapshot.original snapshot.domain snapshot.state rest history

private theorem consumer_successor_unique (evaluate apply merge extend raw)
    (pending : ResultList) (original domain : Atom) (state : TypedApplyState)
    (rest : List TypedApplyFrame) (history : ResultList) {target : TypedApplyConfig}
    (transition : TypedApplyStep evaluate apply merge extend raw
      ⟨.argConsumer pending original domain state :: rest, history⟩ target) :
    target = processConsumerFrame merge extend pending original domain state rest history := by
  cases transition <;> simp_all [processConsumerFrame]
  all_goals
    rcases ‹isEmptyOrError _ = false ∨ _ = _› with clean | unchanged <;> simp_all

/-- The backward direction determines the source successor from any legal
consumer transition. It introduces no extra choice at this phase. -/
theorem consume_correspondence (evaluate apply merge extend raw)
    (snapshot : Snapshot) (rest : List TypedApplyFrame) (history : ResultList)
    (target : TypedApplyConfig) :
    TypedApplyStep evaluate apply merge extend raw (snapshot.configuration rest history) target ↔
      target = actionConfiguration snapshot rest history (consume merge extend snapshot) := by
  constructor
  · intro transition
    rw [consume_projection]
    exact consumer_successor_unique evaluate apply merge extend raw snapshot.pending
      snapshot.original snapshot.domain snapshot.state rest history transition
  · intro equal
    rw [equal]
    exact consume_transition evaluate apply merge extend raw snapshot rest history

def Action.retained : Action → Option Snapshot
  | .exhausted => none
  | .skipped saved | .failure _ saved | .child _ saved => some saved

/-- Advancing a reply keeps the parent argument and binding state intact.
Only the occurrence cursor and the selected child's fields change. -/
theorem consume_retains_parent (merge extend) {snapshot saved : Snapshot}
    (retained : (consume merge extend snapshot).retained = some saved) :
    saved.state = snapshot.state ∧ saved.original = snapshot.original ∧
      saved.domain = snapshot.domain ∧ saved.outcomes = snapshot.outcomes ∧
      saved.nextOutcome = snapshot.nextOutcome + 1 := by
  unfold consume at retained
  cases pending : snapshot.pending with
  | nil => simp [pending, Action.retained] at retained
  | cons selected remaining =>
      obtain ⟨value, evaluated⟩ := selected
      simp only [pending] at retained
      split at retained
      · cases retained
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · split at retained
        · cases retained
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        · split at retained <;> cases retained <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem consume_cursor_strict (merge extend) {snapshot saved : Snapshot}
    (retained : (consume merge extend snapshot).retained = some saved) :
    snapshot.nextOutcome < saved.nextOutcome := by
  rw [(consume_retains_parent merge extend retained).2.2.2.2]
  exact Nat.lt_succ_self _

/-- Cleanup of a returned child restores its parent's alternative traversal.
It does not acquire another callback result or re-evaluate the selected value. -/
def returnedChild (snapshot : Snapshot) : Option Snapshot :=
  if snapshot.phase = .afterChild then
    some {snapshot with phase := .iterate, activeValue := none, activeBindings := none}
  else none

theorem returnedChild_preserves_consumer {snapshot saved : Snapshot}
    (returned : returnedChild snapshot = some saved) : saved.consumer = snapshot.consumer := by
  unfold returnedChild at returned
  split at returned
  · cases returned
    rfl
  · simp at returned

theorem returnedChild_preserves_history {snapshot saved : Snapshot}
    (returned : returnedChild snapshot = some saved)
    (rest : List TypedApplyFrame) (history : ResultList) :
    saved.configuration rest history = snapshot.configuration rest history := by
  simp only [Snapshot.configuration, returnedChild_preserves_consumer returned]

/-- Enter only a stable consumer phase: a child must return before another
outcome is selected. This is semantic sequencing, not a native ownership proof. -/
def step (merge : Bindings → Bindings → Option Bindings)
    (extend : Bindings → Atom → Atom → Option Bindings) (snapshot : Snapshot) : Option Action :=
  if snapshot.phase = .iterate ∧ snapshot.activeValue = none ∧ snapshot.activeBindings = none
  then some (consume merge extend snapshot) else none

theorem active_child_cannot_advance (merge extend) (snapshot : Snapshot)
    (active : snapshot.phase = .afterChild) : step merge extend snapshot = none := by
  simp [step, active]

theorem step_projection (evaluate apply merge extend raw)
    {snapshot : Snapshot} {action : Action} (rest : List TypedApplyFrame) (history : ResultList)
    (advanced : step merge extend snapshot = some action) :
    TypedApplyStep evaluate apply merge extend raw (snapshot.configuration rest history)
      (actionConfiguration snapshot rest history action) := by
  unfold step at advanced
  split at advanced
  · cases advanced
    exact consume_transition evaluate apply merge extend raw snapshot rest history
  · simp at advanced

/-! ## Independently stated HE argument demand -/

inductive RawDemandRel (normalized explicitData : Bool) (expected bound : Atom) : Prop where
  | atom : normalized = false → expected = Atom.atomType →
      RawDemandRel normalized explicitData expected bound
  | explicit : normalized = false → explicitData = true →
      RawDemandRel normalized explicitData expected bound
  | variable (name : String) : normalized = false → bound = .var name →
      RawDemandRel normalized explicitData expected bound

def rawDemand (normalized explicitData : Bool) (expected bound : Atom) : Bool :=
  !normalized && (explicitData || expected == Atom.atomType || bound.isVariable)

private theorem variable_iff (value : Atom) : value.isVariable = true ↔ ∃ name, value = .var name := by
  cases value <;> simp [Atom.isVariable]

theorem rawDemand_iff (normalized explicitData : Bool) (expected bound : Atom) :
    rawDemand normalized explicitData expected bound = true ↔
      RawDemandRel normalized explicitData expected bound := by
  simp only [rawDemand, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq, variable_iff]
  constructor
  · rintro ⟨notNormalized, (isExplicit | atomType) | ⟨name, variableShape⟩⟩
    · exact .explicit notNormalized isExplicit
    · exact .atom notNormalized atomType
    · exact .variable name notNormalized variableShape
  · intro raw
    cases raw with
    | atom notNormalized atomType => exact ⟨notNormalized, Or.inl (Or.inr atomType)⟩
    | explicit notNormalized isExplicit => exact ⟨notNormalized, Or.inl (Or.inl isExplicit)⟩
    | «variable» name notNormalized variableShape => exact ⟨notNormalized, Or.inr ⟨name, variableShape⟩⟩

/-! ## Lossless snapshot data -/

def phaseData : Phase → Atom
  | .iterate => .symbol "he-native-args-iterate-v1"
  | .afterChild => .symbol "he-native-args-after-child-v1"

def readPhase : Atom → Option Phase
  | .symbol "he-native-args-iterate-v1" => some .iterate
  | .symbol "he-native-args-after-child-v1" => some .afterChild
  | _ => none

@[simp] theorem readPhase_phaseData (phase : Phase) : readPhase (phaseData phase) = some phase := by
  cases phase <;> rfl

def optionalAtomData : Option Atom → Atom
  | none => .expression [.symbol "he-native-none-v1"]
  | some value => .expression [.symbol "he-native-some-v1", value]

def readOptionalAtom : Atom → Option (Option Atom)
  | .expression [.symbol "he-native-none-v1"] => some none
  | .expression [.symbol "he-native-some-v1", value] => some (some value)
  | _ => none

@[simp] theorem readOptionalAtom_optionalAtomData (value : Option Atom) :
    readOptionalAtom (optionalAtomData value) = some value := by
  cases value <;> rfl

def optionalBindingsData : Option Bindings → Atom
  | none => .expression [.symbol "he-native-none-v1"]
  | some bindings => .expression [.symbol "he-native-some-v1", bindingsData bindings]

def readOptionalBindings : Atom → Option (Option Bindings)
  | .expression [.symbol "he-native-none-v1"] => some none
  | .expression [.symbol "he-native-some-v1", value] => do return some (← readBindings value)
  | _ => none

@[simp] theorem readOptionalBindings_optionalBindingsData (value : Option Bindings) :
    readOptionalBindings (optionalBindingsData value) = some value := by
  cases value <;> simp [readOptionalBindings, optionalBindingsData]

def snapshotData (snapshot : Snapshot) : Atom :=
  .expression [.symbol "he-native-argument-snapshot-v1", stateData snapshot.state,
    snapshot.original, snapshot.domain, resultsData snapshot.outcomes, index snapshot.nextOutcome,
    phaseData snapshot.phase, optionalAtomData snapshot.activeValue,
    optionalBindingsData snapshot.activeBindings]

def readSnapshot : Atom → Option Snapshot
  | .expression [.symbol "he-native-argument-snapshot-v1", state, original, domain,
      outcomes, cursor, phase, selected, active] => do
        return ⟨← readState state, original, domain, ← readResults outcomes, ← readIndex cursor,
          ← readPhase phase, ← readOptionalAtom selected, ← readOptionalBindings active⟩
  | _ => none

@[simp] theorem readSnapshot_snapshotData (snapshot : Snapshot) :
    readSnapshot (snapshotData snapshot) = some snapshot := by
  cases snapshot
  simp [readSnapshot, snapshotData]

theorem snapshotData_injective : Function.Injective snapshotData := by
  intro left right equal
  have decoded := congrArg readSnapshot equal
  simpa using decoded

end Mettapedia.Languages.MeTTa.HE.NativeArgumentProjection
