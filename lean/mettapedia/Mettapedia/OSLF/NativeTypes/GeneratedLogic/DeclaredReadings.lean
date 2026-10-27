import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Set readings declared with a language

A rule `{x, ...rest} ⇒ …` can read a set three ways (`SetReadings`): **consume** a matched member, **keep** it, or
**either**, the language's own semantics modulo the set laws. A language now declares which (`DeclaredLanguage`), and
the front door answers by the declaration.

- **The structure a declaration fixes** (`nativeStructure`): consume, keep or either.
- **The front door of a declared language** (`askDeclared`): consume and keep are decided by closed regions of their
  readings at the canonical form, either is asked as the language's own semantics; every answer is exact in the
  declared structure (`askDeclared_sound`).
- **Either is consume over all presentations** (`either_step_iff`): a step of the language's own semantics fires the
  rules at some presentation of the state, as consume fires them at the canonical one, and reaches an equivalent of
  the target.

TODO (integration with the reference relation's boundary policies): the declaration is read here beside the
reference relation. `ReferenceStep.InternalBoundaryPolicy` (`OSLF/MeTTaIL/ReferenceStep.lean`) chooses how the
reference relation matches at internal premise boundaries; the set readings belong there as policies, so that the
reference relation itself reads a declared language's sets and `nativeStructure` becomes its reference structure under
the declared policy. Until then the declared readings are the structures of `SetReadings`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open SetReadings (consumeStructure keepStructure eitherStructure saturate setWidth)

/-- **How a language reads its sets.** -/
inductive SetReading where
  /-- A member a rule matches leaves the set. -/
  | consume
  /-- A member a rule matches stays. -/
  | keep
  /-- Either, as the set laws allow: the language's own semantics. -/
  | either
  deriving DecidableEq, Repr

/-- **A language with the set reading it declares.** -/
structure DeclaredLanguage where
  language : LanguageDef
  sets : SetReading := .either

variable (relEnv : RelationEnv) (declared : DeclaredLanguage)

/-- **The structure a declaration fixes.** -/
def nativeStructure : NativeStructure Pattern :=
  match declared.sets with
  | .consume => consumeStructure relEnv declared.language
  | .keep => keepStructure relEnv declared.language
  | .either => eitherStructure relEnv declared.language

/-- **Where a verdict is about**: the canonical form, whose sets the readings of consume and keep write their own way;
the term itself for the language's own semantics. -/
def pointOf (term : Pattern) : Pattern :=
  match declared.sets with
  | .either => term
  | _ => BagForms.sortBags term

/-- **The front door of a declared language**: consume and keep by closed regions of their readings, either by the
front door of the language. -/
def askDeclared (fuel rounds : ℕ) (formula : Formula 0) (term : Pattern) : Option Bool :=
  match declared.sets with
  | .consume => decideReading relEnv declared.language fuel id BagForms.sortBags formula term rounds
  | .keep => decideReading relEnv declared.language fuel (saturate (setWidth declared.language + 1)) BagForms.sortBags
      formula term rounds
  | .either =>
    match ask relEnv [] declared.language fuel formula term none rounds with
    | .proved _ => some true
    | .refuted _ => some false
    | _ => none

variable {relEnv declared}

/-- **Every answer of a declared language's front door is exact** in the declared structure. -/
theorem askDeclared_sound {fuel rounds : ℕ} {formula : Formula 0} (behavioural : formula.behaviouralForward = true)
    {term : Pattern} {verdict : Bool} (decided : askDeclared relEnv declared fuel rounds formula term = some verdict) :
    (verdict = true ↔ (nativeStructure relEnv declared).sat Env.closed formula (pointOf declared term)) := by
  unfold askDeclared at decided
  unfold nativeStructure pointOf
  split at decided
  · rename_i reading
    rw [reading]
    exact decideReading_sound behavioural decided
  · rename_i reading
    rw [reading]
    exact decideReading_sound behavioural decided
  · rename_i reading
    rw [reading]
    split at decided
    · rename_i answered
      cases decided
      exact iff_of_true rfl (ask_proved (forms := none) answered)
    · rename_i answered
      cases decided
      exact iff_of_false (fun same => Bool.false_ne_true same) (ask_refuted (forms := none) answered)
    · cases decided

/-! ## Either is consume over all presentations -/

/-- **Either is consume over all presentations**: under the language's own labels, a step of its own semantics fires
the rules at some presentation of the state, as consume fires them at the canonical one, and reaches an equivalent of
the target. -/
theorem either_step_iff (relEnv : RelationEnv) (language : LanguageDef) {label : StepLabel}
    (own : label.isContext = false) {source target : Pattern} :
    (eitherStructure relEnv language).step source label target ↔
      IsState source ∧ IsState target ∧ ∃ presentation, ObjectEquivalent relEnv language .syntax source presentation ∧
        IsState presentation ∧ ∃ contractum,
          (readingStructure relEnv language (fun _ => presentation) id).step source label contractum ∧
            ObjectEquivalent relEnv language .syntax contractum target := by
  constructor
  · rintro ⟨sourceState, targetState, redex, contractum, witness, placed, redexState, valid, contractumState, after,
      admits⟩
    rw [placed_iff own] at placed
    rw [StepLabel.base_of_isContext own] at admits
    exact ⟨sourceState, targetState, redex, placed, redexState, contractum,
      ⟨sourceState, contractumState, witness, contractum, valid, admits, rfl⟩, after⟩
  · rintro ⟨sourceState, targetState, presentation, presents, presentationState, contractum,
      ⟨-, contractumState, witness, reached, valid, admits, same⟩, after⟩
    subst same
    refine ⟨sourceState, targetState, presentation, reached, witness, (placed_iff own).mpr presents, presentationState,
      valid, contractumState, after, ?_⟩
    rw [StepLabel.base_of_isContext own]
    exact admits

/-- **Consume is the reading at the canonical presentation**: its steps are the reading's steps at the canonical form,
taken to canonical targets. -/
theorem consume_step_iff (relEnv : RelationEnv) (language : LanguageDef) {label : StepLabel} {source target : Pattern} :
    (consumeStructure relEnv language).step source label target ↔
      IsState source ∧ IsState target ∧ ∃ witness contractum, StepValid relEnv language source witness contractum ∧
        label.admits witness = true ∧ BagForms.sortBags contractum = target :=
  Iff.rfl

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings
