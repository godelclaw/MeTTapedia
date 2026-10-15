import Mettapedia.Languages.C11.IntegerMemoryModel

/-!
# Integer assignment conversion joined to typed byte stores

The operand value and destination lvalue are already evaluated. Assignment
selects the lvalue's canonical integer type, performs the selected C value
conversion and writes the converted value with the checked layout for that
type. The stored result retains the assignment expression's value. A selected
implementation-defined conversion signal reports an interaction boundary
without changing memory; signal delivery and handling need their own rules.

The independent assignment judgment joins lvalue type formation, integer
conversion and owned memory writing. Its executable operation has soundness
and constructive completeness for arbitrary layout families and admitted
states. This is the conversion/store component; operand evaluation, pending
modification sequencing, full expression contexts and host publication
authority are not supplied by this component.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerAssignment

open ObjectAccessMemory IntegerMemoryModel

inductive Observation (model : Model) where
  | stored (value : IntegerScalar.Value model.parameters)
  | conversionSignal (identifier : Nat)
  deriving DecidableEq, Repr

inductive Assigning (model : Model) (policy : SignedConversionPolicy) :
    SemanticState model.characters → Lvalue → IntegerScalar.Value model.parameters →
      Observation model → SemanticState model.characters → Prop where
  | stored (before after : SemanticState model.characters) (location : Lvalue)
      (input converted : IntegerScalar.Value model.parameters) (type : IntegerType IntegerExtension)
      (formed : location.view.type = .scalar (.integer type))
      (conversion : IntegerScalar.CastEvaluation model.parameters policy type input (.value converted))
      (writing : IntegerMemoryModel.Writing model before after location converted) :
      Assigning model policy before location input (.stored converted) after
  | signal (before : SemanticState model.characters) (location : Lvalue)
      (input : IntegerScalar.Value model.parameters) (type : IntegerType IntegerExtension) (identifier : Nat)
      (formed : location.view.type = .scalar (.integer type))
      (conversion : IntegerScalar.CastEvaluation model.parameters policy type input (.signal identifier)) :
      Assigning model policy before location input (.conversionSignal identifier) before

def assign (model : Model) (policy : SignedConversionPolicy) (memory : State model.characters)
    (location : Lvalue) (input : IntegerScalar.Value model.parameters) :
    Option (Observation model × State model.characters) := do
  let type ← integerView location.view.type
  match IntegerScalar.cast model.parameters policy type input with
  | .signal identifier => some (.conversionSignal identifier, memory)
  | .value converted => (IntegerMemoryModel.store model memory location converted).map (fun saved => (.stored converted, saved))

theorem assign_sound (model : Model) (policy : SignedConversionPolicy)
    (before after : State model.characters) (location : Lvalue) (input : IntegerScalar.Value model.parameters)
    (observed : Observation model) (executed : assign model policy before location input = some (observed, after)) :
    Assigning model policy (represent before) location input observed (represent after) := by
  cases selected : integerView location.view.type with
  | none => simp [assign, selected] at executed
  | some type =>
      have formed := (integerView_iff _ _).mp selected
      have conversion := IntegerScalar.cast_sound model.parameters policy type input
      cases converted : IntegerScalar.cast model.parameters policy type input with
      | signal identifier =>
          simp only [assign, selected, converted, bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at executed
          obtain ⟨rfl, rfl⟩ := executed
          rw [converted] at conversion
          exact .signal _ _ _ type identifier formed conversion
      | value value =>
          cases written : IntegerMemoryModel.store model before location value with
          | none => simp [assign, selected, converted, written] at executed
          | some saved =>
              simp only [assign, selected, converted, written, bind, Option.bind_some, Option.map_some,
                Option.some.injEq, Prod.mk.injEq] at executed
              obtain ⟨rfl, rfl⟩ := executed
              rw [converted] at conversion
              exact .stored _ _ _ _ value type formed conversion (IntegerMemoryModel.store_sound _ _ _ _ _ written)

theorem assign_complete (model : Model) (policy : SignedConversionPolicy) (before : State model.characters)
    (after : SemanticState model.characters) (location : Lvalue) (input : IntegerScalar.Value model.parameters)
    (observed : Observation model) (assigned : Assigning model policy (represent before) location input observed after) :
    ∃ saved, assign model policy before location input = some (observed, saved) ∧ represent saved = after := by
  cases assigned with
  | stored after location input converted type formed conversion writing =>
      obtain ⟨saved, written, endpoint⟩ := IntegerMemoryModel.store_complete _ _ _ _ _ writing
      have selected := (integerView_iff _ _).mpr formed
      have convertedValue := IntegerScalar.cast_complete _ _ _ _ _ conversion
      exact ⟨saved, by simp only [assign, selected, convertedValue, written, bind, Option.bind_some, Option.map_some], endpoint⟩
  | signal location input type identifier formed conversion =>
      have selected := (integerView_iff _ _).mpr formed
      have convertedValue := IntegerScalar.cast_complete _ _ _ _ _ conversion
      exact ⟨before, by simp only [assign, selected, convertedValue, bind, Option.bind_some], rfl⟩

theorem stored_type {model : Model} {policy : SignedConversionPolicy}
    {before after : SemanticState model.characters} {location : Lvalue}
    {input converted : IntegerScalar.Value model.parameters}
    (assigned : Assigning model policy before location input (.stored converted) after) :
    location.view.type = .scalar (.integer converted.type) := by
  cases assigned with
  | stored _ _ _ _ type formed conversion writing => exact writing.1

theorem signal_memory_unchanged {model : Model} {policy : SignedConversionPolicy}
    {before after : SemanticState model.characters} {location : Lvalue}
    {input : IntegerScalar.Value model.parameters} {identifier : Nat}
    (assigned : Assigning model policy before location input (.conversionSignal identifier) after) : after = before := by
  cases assigned
  rfl

theorem assigned_value_readback (model : Model) (policy : SignedConversionPolicy)
    (before after : State model.characters) (location : Lvalue) (input converted : IntegerScalar.Value model.parameters)
    (executed : assign model policy before location input = some (.stored converted, after)) :
    IntegerMemoryModel.load model after location = some (.value converted false) := by
  have assigned := assign_sound _ _ _ _ _ _ _ executed
  cases assigned with
  | stored _ _ _ _ type formed conversion writing =>
      have selected := (integerView_iff _ _).mpr formed
      have cast := IntegerScalar.cast_complete _ _ _ _ _ conversion
      have saved : IntegerMemoryModel.store model before location converted = some after := by
        simpa only [assign, selected, cast, bind, Option.bind_some, Option.map_eq_some_iff,
          Prod.mk.injEq, true_and, exists_eq_right] using executed
      exact IntegerMemoryModel.load_after_store _ _ _ _ _ saved

end Mettapedia.Languages.C11.IntegerAssignment
