import Mettapedia.Languages.C11.CestaLocatedExpressions
import Mettapedia.Languages.C11.ExpressionSourceHistory

/-!
# Cesta syntax, occurrence packets and source advances

Admission joins the sorted canonical expression, scope/type elaboration and
the existing complete residual packet. A packet with another expression is
refused even when that packet can execute on its own. Occurrence inspection
uses the existing source-generated occurrence paths, with independent action
and sequencing rules at every admitted nesting depth.

Each executable packet step corresponds to a source advance. Conversely a
source advance constructs a returned packet with the prescribed semantic
memory/cache endpoint. That endpoint law does not choose a particular list
representation of a resource heap. Codec admission is distinct from a source
declaration history, world currentness, resource ownership and publication
authority. The byte parser and native compiled execution remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.CestaExpressionCorrespondence

open Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec
open ObjectAccessMemory IntegerMemoryModel LocatedExpressions ExpressionEvents ExpressionEventExecution
open CestaLocatedExpressions

abbrev OccurrencePacket (model : Model) := (expression : Expression model) × Index expression

def occurrence? (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (path : LocatedExpressionData.IndexData) :
    Option (OccurrencePacket model) := do
  let expression ← CestaLocatedExpressions.read schema codecProfile sort model environment wire
  let index ← LocatedExpressionData.decodeIndex expression path
  some ⟨expression, index⟩

def OccurrenceReading (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (path : LocatedExpressionData.IndexData)
    (packet : OccurrencePacket model) : Prop :=
  CestaLocatedExpressions.Reading schema codecProfile sort model environment wire packet.1 ∧
    LocatedExpressionData.encodeIndex packet.1 packet.2 = path

theorem occurrence_sound (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (path : LocatedExpressionData.IndexData)
    (packet : OccurrencePacket model)
    (parsed : occurrence? schema codecProfile sort model environment wire path = some packet) :
    OccurrenceReading schema codecProfile sort model environment wire path packet := by
  simp only [occurrence?, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
  obtain ⟨expression, read, index, indexed, rfl⟩ := parsed
  exact ⟨CestaLocatedExpressions.read_sound _ _ _ _ _ _ _ read,
    LocatedExpressionData.encodeIndex_decode _ _ _ indexed⟩

theorem occurrence_complete (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (path : LocatedExpressionData.IndexData)
    (packet : OccurrencePacket model)
    (reading : OccurrenceReading schema codecProfile sort model environment wire path packet) :
    occurrence? schema codecProfile sort model environment wire path = some packet := by
  obtain ⟨formed, rfl⟩ := reading
  cases packet
  simp only [occurrence?, CestaLocatedExpressions.read_complete _ _ _ _ _ _ _ formed,
    LocatedExpressionData.decodeIndex_encode, bind, Option.bind_some]

theorem occurrence_iff (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (path : LocatedExpressionData.IndexData)
    (packet : OccurrencePacket model) :
    occurrence? schema codecProfile sort model environment wire path = some packet ↔
      OccurrenceReading schema codecProfile sort model environment wire path packet :=
  ⟨occurrence_sound schema codecProfile sort model environment wire path packet,
    occurrence_complete schema codecProfile sort model environment wire path packet⟩

theorem occurrence_has_source_action (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (path : LocatedExpressionData.IndexData)
    (packet : OccurrencePacket model)
    (parsed : occurrence? schema codecProfile sort model environment wire path = some packet) :
    OccurrenceReading schema codecProfile sort model environment wire path packet ∧
      ExpressionSourceActions.Action packet.1 packet.2 ((compile packet.1).operation packet.2) :=
  ⟨occurrence_sound _ _ _ _ _ _ _ _ parsed, ExpressionSourceActions.compiled_action _ _⟩

theorem admitted_source_laws (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (expression : Expression model)
    (parsed : CestaLocatedExpressions.read schema codecProfile sort model environment wire = some expression) :
    CestaLocatedExpressions.Reading schema codecProfile sort model environment wire expression ∧
      (compile expression).InputsOrdered ∧ (compile expression).component.enumeration.items.Nodup ∧
      (∀ index operation, (compile expression).operation index = operation ↔
        ExpressionSourceActions.Action expression index operation) ∧
      (∀ first second, (compile expression).component.evaluation.order.Precedes first second ↔
        ExpressionSourceOrder.Before expression first second) :=
  ⟨CestaLocatedExpressions.read_sound _ _ _ _ _ _ _ parsed, compiled_inputs_ordered expression,
    compiled_occurrences_unique expression, ExpressionSourceActions.compiled_action_iff expression,
    ExpressionSourceOrder.compiled_order_iff expression⟩

def configuration? (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (data : LocatedExpressionData.ConfigurationData) :
    Option (LocatedExpressionData.SourcePacket model) := do
  let expression ← CestaLocatedExpressions.read schema codecProfile sort model environment wire
  let packet ← LocatedExpressionData.decodeConfiguration model data
  if packet.1 = expression then some packet else none

def ConfigurationReading (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (data : LocatedExpressionData.ConfigurationData)
    (packet : LocatedExpressionData.SourcePacket model) : Prop :=
  CestaLocatedExpressions.Reading schema codecProfile sort model environment wire packet.1 ∧
    LocatedExpressionData.encodeConfiguration packet = data

theorem configuration_sound (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (data : LocatedExpressionData.ConfigurationData)
    (packet : LocatedExpressionData.SourcePacket model)
    (admitted : configuration? schema codecProfile sort model environment wire data = some packet) :
    ConfigurationReading schema codecProfile sort model environment wire data packet := by
  obtain ⟨expression, read, following⟩ := Option.bind_eq_some_iff.mp admitted
  obtain ⟨source, decoded, accepted⟩ := Option.bind_eq_some_iff.mp following
  by_cases same : source.1 = expression
  · simp only [if_pos same, Option.some.injEq] at accepted
    cases accepted
    exact ⟨same.symm ▸ CestaLocatedExpressions.read_sound _ _ _ _ _ _ _ read,
      LocatedExpressionData.encodeConfiguration_decode _ _ _ decoded⟩
  · simp only [if_neg same] at accepted
    cases accepted

theorem configuration_complete (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (data : LocatedExpressionData.ConfigurationData)
    (packet : LocatedExpressionData.SourcePacket model)
    (reading : ConfigurationReading schema codecProfile sort model environment wire data packet) :
    configuration? schema codecProfile sort model environment wire data = some packet := by
  obtain ⟨formed, rfl⟩ := reading
  simp only [configuration?, CestaLocatedExpressions.read_complete _ _ _ _ _ _ _ formed,
    LocatedExpressionData.decodeConfiguration_encode, bind, Option.bind_some, ite_true]

theorem configuration_iff (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (data : LocatedExpressionData.ConfigurationData)
    (packet : LocatedExpressionData.SourcePacket model) :
    configuration? schema codecProfile sort model environment wire data = some packet ↔
      ConfigurationReading schema codecProfile sort model environment wire data packet :=
  ⟨configuration_sound schema codecProfile sort model environment wire data packet,
    configuration_complete schema codecProfile sort model environment wire data packet⟩

def step (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (policy : SignedConversionPolicy) (environment : ScopedLvalues.Environment) (wire : Wire)
    (data : LocatedExpressionData.ConfigurationData) :
    Option (LocatedExpressionData.EntryData × LocatedExpressionData.ConfigurationData) := do
  let _packet ← configuration? schema codecProfile sort model environment wire data
  LocatedExpressionData.stepData model policy data

theorem step_sound (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (policy : SignedConversionPolicy) (environment : ScopedLvalues.Environment) (wire : Wire)
    (before after : LocatedExpressionData.ConfigurationData) (event : LocatedExpressionData.EntryData)
    (stepped : step schema codecProfile sort model policy environment wire before = some (event, after)) :
    ∃ (expression : Expression model) (source target : LocatedExpressionData.SourceConfiguration expression)
      (index : Index expression) (outcome : Outcome model),
      ConfigurationReading schema codecProfile sort model environment wire before ⟨expression, source⟩ ∧
      ConfigurationReading schema codecProfile sort model environment wire after ⟨expression, target⟩ ∧
      LocatedExpressionData.decodeEntry expression event = some (index, outcome) ∧
      source.selections = index :: target.selections ∧
      ExpressionSourceExecution.Advance policy expression (represent source.state) index outcome (represent target.state) := by
  obtain ⟨packet, admitted, advanced⟩ := Option.bind_eq_some_iff.mp stepped
  have retained := configuration_sound _ _ _ _ _ _ _ _ admitted
  have decoded : LocatedExpressionData.decodeConfiguration model before = some packet := by
    rw [← retained.2]
    exact LocatedExpressionData.decodeConfiguration_encode _ _
  obtain ⟨expression, source, target, index, outcome, initial, final, observed, selected, reduction⟩ :=
    LocatedExpressionData.stepData_sound _ _ _ _ _ advanced
  have same : packet = ⟨expression, source⟩ := Option.some.inj (decoded.symm.trans initial)
  cases same
  exact ⟨expression, source, target, index, outcome, retained,
    ⟨retained.1, LocatedExpressionData.encodeConfiguration_decode _ _ _ final⟩,
    observed, selected, reduction⟩

theorem step_complete (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (policy : SignedConversionPolicy) (environment : ScopedLvalues.Environment) (wire : Wire)
    (expression : Expression model) (reading : CestaLocatedExpressions.Reading schema codecProfile sort model environment wire expression)
    (before : State (Index expression) model) (after : SemanticState (Index expression) model)
    (index : Index expression) (outcome : Outcome model) (rest : List (Index expression))
    (advanced : ExpressionSourceExecution.Advance policy expression (represent before) index outcome after) :
    ∃ saved : ExpressionEventExecution.State (Index expression) model,
      ExpressionEventExecution.represent saved = after ∧
      step schema codecProfile sort model policy environment wire
        (LocatedExpressionData.encodeConfiguration ⟨expression, ⟨before, index :: rest⟩⟩) =
      some (LocatedExpressionData.encodeEntry expression (index, outcome),
        LocatedExpressionData.encodeConfiguration ⟨expression, ⟨saved, rest⟩⟩) ∧
      ConfigurationReading schema codecProfile sort model environment wire
        (LocatedExpressionData.encodeConfiguration ⟨expression, ⟨saved, rest⟩⟩) ⟨expression, ⟨saved, rest⟩⟩ := by
  obtain ⟨saved, represented, executed⟩ := LocatedExpressionData.stepData_complete model policy
    expression before after index outcome rest advanced
  have admitted := configuration_complete schema codecProfile sort model environment wire _
    ⟨expression, ⟨before, index :: rest⟩⟩ ⟨reading, rfl⟩
  exact ⟨saved, represented, by simp only [step, admitted, executed, bind, Option.bind_some], ⟨reading, rfl⟩⟩

end Mettapedia.Languages.C11.CestaExpressionCorrespondence
