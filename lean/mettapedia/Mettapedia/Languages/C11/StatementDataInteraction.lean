import Mettapedia.Languages.C11.StatementDataExecution

/-!
# Checked occurrence scheduling with exact retained snapshots

A request describes a source-defined, partitioned, unhalted expression with
pending work. A reply selects a source-ready occurrence and retains all
memory, cache and control. The response is checked against both the current
packet and the exact request snapshot. This is a scheduling contract; its
structural checks do not establish earned cache values or external ownership.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.StatementDataInteraction

open IntegerMemoryModel LocatedExpressions LocatedStatements
open LocatedExpressionData (IndexData encodeIndex decodeIndex)
open StatementData StatementDataExecution

variable {model : Model}

structure Suspensible (expression : Expression model)
    (saved : ExpressionEventExecution.SemanticState (Index expression) model) : Prop where
  partition : ExpressionEventExecution.Partition (compile expression) saved.pending saved.cache
  continuing : saved.halted = none
  pending : saved.pending ≠ []
  defined : ¬ ExpressionSourceExecution.Undefined expression

inductive Delivery : SemanticConfiguration model → IndexData → SemanticConfiguration model → Prop where
  | selected (expression : Expression model) (saved : ExpressionEventExecution.SemanticState (Index expression) model)
      (following : AfterExpression model) (index : Index expression)
      (suspensible : Suspensible expression saved)
      (ready : ExpressionSourceExecution.Ready expression saved.pending index) :
      Delivery (.expression expression saved following []) (encodeIndex expression index)
        (.expression expression saved following [encodeIndex expression index])

def suspensionCheck (expression : Expression model) (saved : ExpressionEventExecution.State (Index expression) model) : Bool :=
  ExpressionEventExecution.admissible (compile expression) &&
    ExpressionEventExecution.partitionCheck (compile expression) saved.pending saved.cache &&
      decide (saved.halted = none) && decide (saved.pending ≠ [])

theorem suspensionCheck_iff (expression : Expression model) (saved : ExpressionEventExecution.State (Index expression) model) :
    suspensionCheck expression saved = true ↔ Suspensible expression (ExpressionEventExecution.represent saved) := by
  simp only [suspensionCheck, Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨defined, partition⟩, continuing⟩, pending⟩
    exact ⟨(ExpressionEventExecution.partitionCheck_iff _ _ _).mp partition, continuing, pending,
      fun undefined => (ExpressionEventExecution.admissible_iff _).mp defined
        ((ExpressionSourceExecution.compiled_conflict_iff _).mpr undefined)⟩
  · intro admitted
    exact ⟨⟨⟨(ExpressionEventExecution.admissible_iff _).mpr (fun undefined => admitted.defined
      ((ExpressionSourceExecution.compiled_conflict_iff _).mp undefined)),
      (ExpressionEventExecution.partitionCheck_iff _ _ _).mpr admitted.partition⟩,
      admitted.continuing⟩, admitted.pending⟩

structure RequestPacket where
  request : RequestData
  saved : ConfigurationData
  deriving DecidableEq, Repr

def offer (model : Model) (data : ConfigurationData) : Option RequestPacket := do
  let source ← decodeConfiguration model data
  match source with
  | .expression expression saved _ [] => if suspensionCheck expression saved then
      some ⟨⟨LocatedExpressionData.encodeExpression expression,
        (SequencingSchedule.choices (compile expression).component.evaluation.order saved.pending).map
          (encodeIndex expression)⟩, data⟩ else none
  | _ => none

theorem offer_sound (model : Model) (data : ConfigurationData) (request : RequestPacket)
    (computed : offer model data = some request) :
    ∃ expression saved following,
      decodeConfiguration model data = some (.expression expression saved following []) ∧
      Suspensible expression (ExpressionEventExecution.represent saved) ∧
      request = ⟨⟨LocatedExpressionData.encodeExpression expression,
        (SequencingSchedule.choices (compile expression).component.evaluation.order saved.pending).map
          (encodeIndex expression)⟩, data⟩ := by
  simp only [offer, bind, Option.bind_eq_some_iff] at computed
  obtain ⟨source, decoded, computed⟩ := computed
  cases source with
  | statement statement continuation memory selections | flow flow continuation memory selections
  | returned value memory selections => cases computed
  | expression expression saved following selections =>
      cases selections with
      | cons choice rest => cases computed
      | nil =>
          by_cases checked : suspensionCheck expression saved = true
          · simp only [checked, ↓reduceIte, Option.some.injEq] at computed
            exact ⟨expression, saved, following, decoded, (suspensionCheck_iff _ _).mp checked, computed.symm⟩
          · simp only [checked, Bool.false_eq_true, ↓reduceIte] at computed
            contradiction

theorem offer_complete (model : Model) (expression : Expression model)
    (saved : ExpressionEventExecution.State (Index expression) model) (following : AfterExpression model)
    (admitted : Suspensible expression (ExpressionEventExecution.represent saved)) :
    offer model (encodeConfiguration (.expression expression saved following [])) =
      some ⟨⟨LocatedExpressionData.encodeExpression expression,
        (SequencingSchedule.choices (compile expression).component.evaluation.order saved.pending).map
          (encodeIndex expression)⟩, encodeConfiguration (.expression expression saved following [])⟩ := by
  simp only [offer, decodeConfiguration_encode, bind, Option.bind_some, (suspensionCheck_iff _ _).mpr admitted, ↓reduceIte]

theorem offer_machine_call (model : Model) (policy : SignedConversionPolicy) (data : ConfigurationData) (request : RequestPacket)
    (offered : offer model data = some request) :
    stepData model policy data = some (.call request.request request.saved) := by
  obtain ⟨expression, saved, following, decoded, admitted, rfl⟩ := offer_sound _ _ _ offered
  have checked : ExpressionEventExecution.partitionCheck (compile expression) saved.pending saved.cache = true :=
    (ExpressionEventExecution.partitionCheck_iff _ _ _).mpr admitted.partition
  have clean : (compile expression).component.evaluation.findConflict (compile expression).component.enumeration = none := by
    have allowed := (ExpressionEventExecution.admissible_iff _).mpr (fun undefined => admitted.defined
      ((ExpressionSourceExecution.compiled_conflict_iff _).mp undefined))
    simpa only [ExpressionEventExecution.admissible, decide_eq_true_eq] using allowed
  have continuing : saved.halted = none := admitted.continuing
  have unfinished : StatementExecution.finishedExpression? expression saved = none := by
    cases pending : saved.pending with
    | nil => exact False.elim (admitted.pending pending)
    | cons first rest =>
        unfold StatementExecution.finishedExpression?
        split
        · simp only [continuing, pending]
        · rfl
  have native : (StatementMachine.machine model policy).step (.expression expression saved following []) =
      some (.call ⟨expression, (SequencingSchedule.choices (compile expression).component.evaluation.order
        saved.pending).map (encodeIndex expression)⟩ (.expression expression saved following [])) := by
    simp only [StatementMachine.machine, StatementExecution.execute, unfinished, StatementMachine.classify,
      clean, checked, ↓reduceIte, continuing]
    cases pending : saved.pending with
    | nil => exact False.elim (admitted.pending pending)
    | cons first rest => rfl
  have same : encodeConfiguration (.expression expression saved following []) = data :=
    encodeConfiguration_decode _ _ _ decoded
  rw [← same]
  exact stepData_on_encoded _ _ _ _ native

def deliverData (model : Model) (data : ConfigurationData) (choice : IndexData) : Option ConfigurationData := do
  let source ← decodeConfiguration model data
  match source with
  | .expression expression saved following [] =>
      if suspensionCheck expression saved then (do
        let index ← decodeIndex expression choice
        if index ∈ SequencingSchedule.choices (compile expression).component.evaluation.order saved.pending then
          some (encodeConfiguration (.expression expression saved following [choice])) else none)
      else none
  | _ => none

theorem deliverData_sound (model : Model) (before after : ConfigurationData) (choice : IndexData)
    (computed : deliverData model before choice = some after) :
    ∃ source target, decodeConfiguration model before = some source ∧ after = encodeConfiguration target ∧
      Delivery (represent source) choice (represent target) := by
  simp only [deliverData, bind, Option.bind_eq_some_iff] at computed
  obtain ⟨source, decoded, computed⟩ := computed
  cases source with
  | statement statement continuation memory selections | flow flow continuation memory selections
  | returned value memory selections => cases computed
  | expression expression saved following selections =>
      cases selections with
      | cons first rest => cases computed
      | nil =>
          by_cases checked : suspensionCheck expression saved = true
          · simp only [checked, ↓reduceIte, Option.bind_eq_some_iff] at computed
            obtain ⟨index, indexed, computed⟩ := computed
            by_cases enabled : index ∈ SequencingSchedule.choices (compile expression).component.evaluation.order saved.pending
            · simp only [if_pos enabled, Option.some.injEq] at computed
              have same : encodeIndex expression index = choice := LocatedExpressionData.encodeIndex_decode _ _ _ indexed
              have ready : ExpressionSourceExecution.Ready expression saved.pending index :=
                (ExpressionSourceExecution.ready_iff _ _ _).mp ((SequencingSchedule.mem_choices_iff _ _ _).mp enabled)
              refine ⟨.expression expression saved following [], .expression expression saved following [choice], decoded, computed.symm, ?_⟩
              rw [← same]
              exact .selected _ _ _ _ ((suspensionCheck_iff _ _).mp checked) ready
            · simp only [if_neg enabled] at computed
              contradiction
          · simp only [checked, Bool.false_eq_true, ↓reduceIte] at computed
            contradiction


theorem deliverData_complete (model : Model) (before : Configuration model) (after : SemanticConfiguration model)
    (choice : IndexData) (delivered : Delivery (represent before) choice after) :
    ∃ target, represent target = after ∧ deliverData model (encodeConfiguration before) choice = some (encodeConfiguration target) := by
  cases before with
  | statement statement continuation memory selections | flow flow continuation memory selections
  | returned value memory selections => cases delivered
  | expression expression saved following selections =>
      cases delivered with
      | selected expression savedSemantic following index admitted ready =>
          refine ⟨.expression expression saved following [encodeIndex expression index], rfl, ?_⟩
          have enabled : index ∈ SequencingSchedule.choices (compile expression).component.evaluation.order saved.pending :=
            (SequencingSchedule.mem_choices_iff _ _ _).mpr ((ExpressionSourceExecution.ready_iff _ _ _).mpr ready)
          simp only [deliverData, decodeConfiguration_encode, bind, Option.bind_some,
            (suspensionCheck_iff _ _).mpr admitted, ↓reduceIte, LocatedExpressionData.decodeIndex_encode, if_pos enabled]

structure ResponseData where
  snapshot : ConfigurationData
  choice : IndexData
  deriving DecidableEq, Repr


structure NativeRequestPacket (model : Model) where
  request : StatementMachine.SelectionRequest model
  saved : Configuration model

structure NativeResponse (model : Model) where
  snapshot : Configuration model
  choice : IndexData

def encodeRequestPacket (request : NativeRequestPacket model) : RequestPacket :=
  ⟨encodeRequest request.request, encodeConfiguration request.saved⟩

def decodeRequestPacket (model : Model) (data : RequestPacket) : Option (NativeRequestPacket model) := do
  some ⟨← decodeRequest model data.request, ← decodeConfiguration model data.saved⟩

theorem decodeRequestPacket_encode (model : Model) (request : NativeRequestPacket model) :
    decodeRequestPacket model (encodeRequestPacket request) = some request := by
  cases request
  simp only [encodeRequestPacket, decodeRequestPacket, decodeRequest_encode, decodeConfiguration_encode, bind, Option.bind_some]

theorem encodeRequestPacket_decode (model : Model) (data : RequestPacket) (request : NativeRequestPacket model)
    (decoded : decodeRequestPacket model data = some request) : encodeRequestPacket request = data := by
  simp only [decodeRequestPacket, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
  obtain ⟨source, sourceRead, saved, savedRead, rfl⟩ := decoded
  cases data
  simp only [encodeRequestPacket, encodeRequest_decode _ _ _ sourceRead, encodeConfiguration_decode _ _ _ savedRead]

def encodeResponse (response : NativeResponse model) : ResponseData :=
  ⟨encodeConfiguration response.snapshot, response.choice⟩

def decodeResponse (model : Model) (data : ResponseData) : Option (NativeResponse model) :=
  (decodeConfiguration model data.snapshot).map (fun snapshot => ⟨snapshot, data.choice⟩)

theorem decodeResponse_encode (model : Model) (response : NativeResponse model) :
    decodeResponse model (encodeResponse response) = some response := by
  cases response
  simp only [encodeResponse, decodeResponse, decodeConfiguration_encode, Option.map_some]

theorem encodeResponse_decode (model : Model) (data : ResponseData) (response : NativeResponse model)
    (decoded : decodeResponse model data = some response) : encodeResponse response = data := by
  obtain ⟨source, sourceRead, rfl⟩ := Option.map_eq_some_iff.mp decoded
  cases data
  simp only [encodeResponse, encodeConfiguration_decode _ _ _ sourceRead]

def respond (model : Model) (current : ConfigurationData) (request : RequestPacket) (response : ResponseData) :
    Option ConfigurationData :=
  if current = request.saved ∧ response.snapshot = request.saved then
    if offer model current = some request then deliverData model current response.choice else none
  else none

theorem respond_sound (model : Model) (current after : ConfigurationData) (request : RequestPacket) (response : ResponseData)
    (computed : respond model current request response = some after) :
    current = request.saved ∧ response.snapshot = request.saved ∧ offer model current = some request ∧
      ∃ source target, decodeConfiguration model current = some source ∧ after = encodeConfiguration target ∧
        Delivery (represent source) response.choice (represent target) := by
  unfold respond at computed
  split at computed
  · rename_i snapshots
    split at computed
    · rename_i offered
      exact ⟨snapshots.1, snapshots.2, offered, deliverData_sound _ _ _ _ computed⟩
    · contradiction
  · contradiction

theorem respond_complete (model : Model) (current : ConfigurationData) (request : RequestPacket) (response : ResponseData)
    (after : ConfigurationData) (snapshots : current = request.saved ∧ response.snapshot = request.saved)
    (offered : offer model current = some request) (delivered : deliverData model current response.choice = some after) :
    respond model current request response = some after := by
  simp only [respond, if_pos snapshots, if_pos offered, delivered]

theorem stale_current_refused (model : Model) (current : ConfigurationData) (request : RequestPacket) (response : ResponseData)
    (stale : current ≠ request.saved) : respond model current request response = none := by
  have snapshots : ¬ (current = request.saved ∧ response.snapshot = request.saved) := fun h => stale h.1
  simp only [respond, if_neg snapshots]

theorem spliced_snapshot_refused (model : Model) (current : ConfigurationData) (request : RequestPacket) (response : ResponseData)
    (spliced : response.snapshot ≠ request.saved) : respond model current request response = none := by
  have snapshots : ¬ (current = request.saved ∧ response.snapshot = request.saved) := fun h => spliced h.2
  simp only [respond, if_neg snapshots]

theorem fabricated_request_refused (model : Model) (current : ConfigurationData) (request : RequestPacket) (response : ResponseData)
    (forged : offer model current ≠ some request) : respond model current request response = none := by
  simp only [respond, if_neg forged]
  split <;> rfl

end Mettapedia.Languages.C11.StatementDataInteraction
