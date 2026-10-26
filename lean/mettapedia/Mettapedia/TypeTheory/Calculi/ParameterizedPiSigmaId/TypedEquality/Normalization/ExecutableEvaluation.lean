import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableChecking

/-!
# Checked computation and proposed readback

The existing synthesis, reduction and equality procedures compute a result from
source syntax. A printer or adapter may propose the returned term, but that term
is checked against the computed term at the inferred type before it is returned.
Neither source typing nor a readback correctness proof is an execution input.

The soundness result is uniform in the qualified rule package and in the
untrusted readback function. It survives typed substitution and context
extension. This is a symbolic algorithm contract; it does not identify the fuel
of these recursive procedures with a native implementation's work counter.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableEvaluation

open ExecutableChecking

variable {Head : Type}

/-- Readback proposes syntax, without claiming that it preserves meaning. -/
abbrev Readback (Head : Type) := {n : Nat} → Tm Head n → Option (Tm Head n)

/-- Evidence constructed by the three existing procedures, retaining the
source, intermediate computation and the exact returned endpoint. -/
structure Result (R : Rules Head) {n : Nat} (context : Ctx Head n) (source : Tm Head n) where
  value : Tm Head n
  type : Tm Head n
  computed : Tm Head n
  sourceChecked : JudgmentCertificate R context source type
  reduction : Reduces R source computed
  readbackChecked : EqualityCertificate R context computed value type

variable (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq]
  [∀ head, Decidable (R.isUniverse head)] [DecidableRel R.cumulative]
  (heads : HeadChoices R) (reducer : ExecutableReduction.Reducer R)

def evaluate (readback : Readback Head) (fuel : Nat) {n : Nat}
    (context : Ctx Head n) (source : Tm Head n) : Option (Result R context source) := do
  let inferred ← synth R heads reducer fuel context source
  let sourceChecked ← judgment R heads reducer fuel context source inferred.1
  let computed ← reducer fuel source
  let value ← readback computed.val
  let readbackChecked ← equality R heads reducer fuel context computed.val value inferred.1
  return ⟨value, inferred.1, computed.val, sourceChecked, computed.property, readbackChecked⟩

/-- The programming interface exposes a value and its inferred type. -/
def run (readback : Readback Head) (fuel : Nat) {n : Nat}
    (context : Ctx Head n) (source : Tm Head n) : Option (Tm Head n × Tm Head n) :=
  (evaluate R heads reducer readback fuel context source).map fun result =>
    (result.value, result.type)

@[simp] theorem zero_budget (readback : Readback Head) {n : Nat}
    (context : Ctx Head n) (source : Tm Head n) :
    run R heads reducer readback 0 context source = none := by
  simp [run, evaluate, synth]

section Soundness

open UniverseLevel (LevelOrder)

variable {L : Type} [LevelOrder L] {S : Setting Head L}
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (headSteps : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R)

include facts roots headSteps algebra declared

omit [DecidableEq Head] in
theorem Result.sound {n : Nat} {context : Ctx Head n} {source : Tm Head n}
    (result : Result S.R context source) :
    Typed S.R context source result.type ∧ Typed S.R context result.value result.type ∧
      Equal S.R context source result.value result.type := by
  have sourceTyped := result.sourceChecked.sound facts roots headSteps algebra declared
  have formed := result.sourceChecked.contextChecked.sound facts roots headSteps algebra declared
  have computedEqual := (Reduces.preserve facts roots headSteps formed result.reduction sourceTyped).2
  exact ⟨sourceTyped,
    result.readbackChecked.secondChecked.sound facts roots headSteps algebra declared,
    .trans computedEqual (result.readbackChecked.sound facts roots headSteps algebra declared)⟩

variable [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
  (choices : HeadChoices S.R) (evaluator : ExecutableReduction.Reducer S.R)

/-- Actual successful execution gives typing of both endpoints and their
typed equality. Arbitrary proposed readbacks are subject to the same theorem. -/
theorem run_sound (readback : Readback Head) {fuel n : Nat} {context : Ctx Head n}
    {source value type : Tm Head n}
    (returned : run S.R choices evaluator readback fuel context source = some (value, type)) :
    Typed S.R context source type ∧ Typed S.R context value type ∧
      Equal S.R context source value type := by
  unfold run at returned
  cases computed : evaluate S.R choices evaluator readback fuel context source with
  | none => simp [computed] at returned
  | some result =>
      simp only [computed, Option.map_some, Option.some.injEq, Prod.mk.injEq] at returned
      obtain ⟨rfl, rfl⟩ := returned
      exact result.sound facts roots headSteps algebra declared

/-- Moving accepted values through a typed substitution preserves the exact
source/result equality; no claim about equal search budgets is made. -/
theorem run_substitution (readback : Readback Head) {fuel n m : Nat}
    {context : Ctx Head n} {target : Ctx Head m} {σ : Sub Head n m}
    {source value type : Tm Head n}
    (returned : run S.R choices evaluator readback fuel context source = some (value, type))
    (typed : SubstMor S.R context target σ) :
    Typed S.R target (subst σ value) (subst σ type) ∧
      Equal S.R target (subst σ source) (subst σ value) (subst σ type) := by
  have sound := run_sound facts roots headSteps algebra declared choices evaluator readback returned
  exact ⟨sound.2.1.substitute typed, sound.2.2.substitute typed⟩

theorem run_context_extension (readback : Readback Head) {fuel n : Nat}
    {context : Ctx Head n} {source value type extension : Tm Head n}
    (returned : run S.R choices evaluator readback fuel context source = some (value, type)) :
    Typed S.R (.snoc context extension) (rename wk value) (rename wk type) ∧
      Equal S.R (.snoc context extension) (rename wk source) (rename wk value) (rename wk type) := by
  have sound := run_sound facts roots headSteps algebra declared choices evaluator readback returned
  exact ⟨sound.2.1.weaken, sound.2.2.weaken⟩

/-- A forged endpoint cannot be returned under the selected rule package. -/
theorem refuses_unequal_readback (readback : Readback Head) {fuel n : Nat}
    {context : Ctx Head n} {source value type : Tm Head n}
    (unequal : ¬ Equal S.R context source value type) :
    run S.R choices evaluator readback fuel context source ≠ some (value, type) := by
  intro returned
  exact unequal (run_sound facts roots headSteps algebra declared choices evaluator readback returned).2.2

end Soundness
end TypedEquality.Normalization.ExecutableEvaluation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
