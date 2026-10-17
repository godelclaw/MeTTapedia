import Mettapedia.Machines.CategoricalAbstractMachineGraph

/-!
# Historical CAM controls

Independent source derivations meet actual instruction execution. Raw code
may stop without being compiled or without exposing a completed answer.
Neutral and strict projections remain different profiles. Captured
environments, instruction suffixes, stacks and resumed occurrences stay
explicit. A closed self-application cycle gives divergence for every finite
budget; no source termination assumption is used.

The value-graph controls run CCM's factorial through `wind` to its exact
answer and show the cyclic couple and closure it builds; run the laziness
example of Section 4 without forcing its frozen work; force a recursive stream
twice; and count the two forcings of a laze used twice (call by name). A
recursive loop is exhausted at every budget while it keeps allocating. Negative
controls keep `wind` without a couple, strict primitives on non-integers and
non-Boolean conditions stuck, refuse raw code at the loader, and keep the tree
machine stopped at the value-graph instructions.

The scoped readback controls also cover quotation and selected conditional
branches. Memoizing controls exercise a separate Need profile: two uses of one
producer, independent allocations of equal bodies, nested updates, persistent
checkpoint isolation, exact resumption, failed production and wrong-origin
refusal. Instruction-count comparisons name the programs and the two strategies;
they make no physical runtime claim.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CategoricalAbstractMachineControls

open CategoricalAbstractMachine
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ProductiveCoreAdapters

def identity : Expr := .lam (.var 0)
def identityValue : Value := .closure (.var 0) .unit
def identityApplication : Expr := .app identity identity
def identityStart : State := (core .neutral).load (identityApplication, .unit)
def identityFinal : State := ⟨encodeValue identityValue, [], []⟩

theorem identity_source_derivation : Evaluation identityApplication .unit identityValue :=
  .app (.lam _ _) (.lam _ _) (.closure (.varZero (.pair _ _)))

theorem identity_proposition_3_1 :
    CombinatorySteps (.question identityApplication .unit) (.answer identityValue) ∧
      Steps .neutral identityStart identityFinal :=
  ⟨identity_source_derivation.combinatory, identity_source_derivation.execution⟩

theorem identity_execution_keeps_compiled_closure :
    ((machine .neutral).run 8 identityStart).2 = .finished (encodeValue identityValue) := rfl

theorem identity_cost_has_seven_instructions_and_one_completion :
    (machine .neutral).spent (computationalPrice (core .neutral) (fun _ => 1)) 8 identityStart = 7 ∧
      (machine .neutral).spent (fun _ => 1) 8 identityStart = 8 := ⟨rfl, rfl⟩

theorem distinct_bodies_remain_distinct : compile (.lam (.var 0)) ≠ compile (.lam (.var 1)) := by
  intro collapsed
  have same := compile_injective collapsed
  cases same

theorem arbitrary_compiled_bodies_decode (body : Expr) :
    decodeCode (compile (.lam (.first (.pair body (.var 2))))) =
      some (.lam (.first (.pair body (.var 2)))) := decode_compile _

theorem arbitrary_nested_values_decode (body : Expr) (environment argument : Value) :
    decodeValue (encodeValue (.pair (.closure body environment) (.app argument))) =
      some (.pair (.closure body environment) (.app argument)) := decode_encodeValue _

def redundantRawCode : Code := [.cur [.second], .push, .swap, .cons, .first]

theorem redundant_raw_work_is_not_canonical_compilation : decodeCode redundantRawCode = none := by
  simp [decodeCode, decodeSourceCode, redundantRawCode, compileSource]

theorem redundant_raw_work_can_still_finish :
    ((machine .neutral).run 6 ⟨.unit, redundantRawCode, []⟩).2 =
      .finished (.closure [.second] .unit) := rfl

theorem stopped_raw_code_does_not_certify_source_body :
    decodeCode [.cur [.swap]] = none ∧ decodeValue (.closure [.swap] .unit) = none := by
  simp [decodeCode, decodeSourceCode, decodeValue, decodeSourceValue]

theorem observed_raw_closure_does_not_certify_source_body :
    ((machine .neutral).run 2 ⟨.unit, [.cur [.swap]], []⟩).2 = .finished (.closure [.swap] .unit) ∧
      decodeValue (.closure [.swap] .unit) = none := by
  exact ⟨rfl, by simp [decodeSourceCode, decodeValue, decodeSourceValue]⟩

theorem swap_underflow_is_stuck :
    (machine .neutral).run 1 ⟨.unit, [.swap], []⟩ = ([], .stuck ⟨.unit, [.swap], []⟩) := rfl

theorem cons_underflow_is_stuck :
    (machine .neutral).run 1 ⟨.unit, [.cons], []⟩ = ([], .stuck ⟨.unit, [.cons], []⟩) := rfl

theorem empty_code_with_pending_stack_is_not_an_answer :
    answer ⟨.unit, [], [.unit]⟩ = none ∧
      (machine .neutral).run 1 ⟨.unit, [], [.unit]⟩ = ([], .stuck ⟨.unit, [], [.unit]⟩) := ⟨rfl, rfl⟩

theorem zero_budget_does_not_poll_a_final_value :
    (machine .neutral).run 0 identityFinal = ([], .exhausted identityFinal) := rfl

theorem completed_value_needs_a_separate_observation_boundary :
    (machine .neutral).run 1 identityFinal = ([], .finished (encodeValue identityValue)) := rfl

def inactiveProjection : State := ⟨.unit, [.first], []⟩

theorem table_1_does_not_add_inactive_projection :
    (machine .strict).run 2 inactiveProjection = ([], .stuck inactiveProjection) := rfl

theorem table_5_retains_inactive_projection_as_neutral :
    ((machine .neutral).run 2 inactiveProjection).2 = .finished (.first .unit) := rfl

theorem inactive_application_profiles_are_distinct :
    (step .strict ⟨.pair .unit .unit, [.app], []⟩ = none) ∧
      (step .neutral ⟨.pair .unit .unit, [.app], []⟩ = some ⟨.app (.pair .unit .unit), [], []⟩) := ⟨rfl, rfl⟩

theorem active_projection_does_not_turn_neutral :
    step .neutral ⟨.pair (.first .unit) (.second .unit), [.first], []⟩ =
      some ⟨.first .unit, [], []⟩ := rfl

def twoClosures : Expr := .pair (.lam (.var 0)) (.lam (.var 1))
def twoClosureValues : Value := .pair (.closure (.var 0) .unit) (.closure (.var 1) .unit)

theorem ordered_pair_has_independent_source_derivation : Evaluation twoClosures .unit twoClosureValues :=
  .pair (.lam _ _) (.lam _ _)

theorem ordered_pair_execution_does_not_swap_results :
    ((machine .neutral).run 6 ((core .neutral).load (twoClosures, .unit))).2 =
      .finished (encodeValue twoClosureValues) := rfl

theorem saving_a_closure_does_not_run_its_body :
    ((machine .neutral).run 2 ((core .neutral).load (.lam (.app (.var 0) (.var 0)), .unit))).2 =
      .finished (.closure (compile (.app (.var 0) (.var 0))) .unit) := rfl

def capturedEnvironment : Value := .pair .unit (.first .unit)
def capturedArgument : Value := .second .unit

theorem shadowing_preserves_outer_and_inner_slots :
    Evaluation (.var 0) (.pair capturedEnvironment capturedArgument) capturedArgument ∧
      Evaluation (.var 1) (.pair capturedEnvironment capturedArgument) (.first .unit) :=
  ⟨.varZero (.pair _ _), .varSucc (.pair _ _) (.varZero (.pair _ _))⟩

theorem capture_uses_the_saved_environment :
    Invocation (.closure (.var 1) capturedEnvironment) capturedArgument (.first .unit) :=
  .closure (.varSucc (.pair _ _) (.varZero (.pair _ _)))

theorem arbitrary_suffix_and_stack_survive_identity (suffix : Code) (stack : List NativeValue) :
    Steps .neutral ⟨.unit, compile identityApplication ++ suffix, stack⟩
      ⟨encodeValue identityValue, suffix, stack⟩ := identity_source_derivation.execution_tail suffix stack

def identityResidual : State := ⟨.unit, [.cur [.second], .cons, .app], [.closure [.second] .unit]⟩
def identityPrefix : List CategoricalAbstractMachine.Occurrence := ((machine .neutral).run 3 identityStart).1

theorem prefix_retains_pending_argument_and_saved_function :
    (machine .neutral).run 3 identityStart = (identityPrefix, .exhausted identityResidual) := rfl

theorem resumption_preserves_order_and_complete_residual :
    (machine .neutral).run 8 identityStart =
      (identityPrefix ++ ((machine .neutral).run 5 identityResidual).1,
        ((machine .neutral).run 5 identityResidual).2) :=
  (machine .neutral).established_and_pending 3 5 identityStart identityResidual identityPrefix
    prefix_retains_pending_argument_and_saved_function

theorem restarting_repeats_computational_occurrences :
    (identityPrefix ++ ((machine .neutral).run 8 identityStart).1).length = 10 ∧
      ((machine .neutral).run 8 identityStart).1.length = 7 := ⟨rfl, rfl⟩

def deltaBody : Expr := .app (.var 0) (.var 0)
def delta : Expr := .lam deltaBody
def omega : Expr := .app delta delta
def deltaNative : NativeValue := .closure (compile deltaBody) .unit
def omegaEnvironment : NativeValue := .pair .unit deltaNative
def omegaStart : State := (core .neutral).load (omega, .unit)
def omegaCycle0 : State := ⟨omegaEnvironment, compile deltaBody, []⟩
def omegaCycle1 : State := ⟨omegaEnvironment, [.second, .swap, .second, .cons, .app], [omegaEnvironment]⟩
def omegaCycle2 : State := ⟨deltaNative, [.swap, .second, .cons, .app], [omegaEnvironment]⟩
def omegaCycle3 : State := ⟨omegaEnvironment, [.second, .cons, .app], [deltaNative]⟩
def omegaCycle4 : State := ⟨deltaNative, [.cons, .app], [deltaNative]⟩
def omegaCycle5 : State := ⟨.pair deltaNative deltaNative, [.app], []⟩

def omegaRegion (state : State) : Prop := state = omegaCycle0 ∨ state = omegaCycle1 ∨ state = omegaCycle2 ∨
  state = omegaCycle3 ∨ state = omegaCycle4 ∨ state = omegaCycle5

theorem omega_region_closed (state : State) (inside : omegaRegion state) :
    ∃ next, (core .neutral).StepRel state next ∧ omegaRegion next := by
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨omegaCycle1, rfl, .inr (.inl rfl)⟩
  · exact ⟨omegaCycle2, rfl, .inr (.inr (.inl rfl))⟩
  · exact ⟨omegaCycle3, rfl, .inr (.inr (.inr (.inl rfl)))⟩
  · exact ⟨omegaCycle4, rfl, .inr (.inr (.inr (.inr (.inl rfl))))⟩
  · exact ⟨omegaCycle5, rfl, .inr (.inr (.inr (.inr (.inr rfl))))⟩
  · exact ⟨omegaCycle0, rfl, .inl rfl⟩

theorem omega_prefix_reaches_the_cycle :
    ((machine .neutral).run 6 omegaStart).2 = .exhausted omegaCycle0 := rfl

theorem omega_cycle_diverges_with_computational_steps (budget : Nat) :
    ∃ events residual, (machine .neutral).run budget omegaCycle0 = (events, .exhausted residual) ∧
      events.length = budget ∧ omegaRegion residual := by
  obtain ⟨events, residual, ran, _, count, remains⟩ :=
    perpetual_computation (answerCore .neutral) omegaRegion omega_region_closed budget omegaCycle0 (.inl rfl)
  exact ⟨events, residual, ran, count, remains⟩

theorem loaded_omega_diverges (budget : Nat) :
    ∃ residual, ((machine .neutral).run budget omegaStart).2 = .exhausted residual := by
  by_cases enough : 6 ≤ budget
  · obtain ⟨second, rfl⟩ := Nat.exists_eq_add_of_le enough
    obtain ⟨events, residual, ran, _, _⟩ := omega_cycle_diverges_with_computational_steps second
    have paused : (machine .neutral).run 6 omegaStart =
        (((machine .neutral).run 6 omegaStart).1, .exhausted omegaCycle0) := rfl
    have resumed := (machine .neutral).established_and_pending 6 second omegaStart omegaCycle0
      ((machine .neutral).run 6 omegaStart).1 paused
    exact ⟨residual, by rw [resumed, ran]⟩
  · have choices : budget = 0 ∨ budget = 1 ∨ budget = 2 ∨ budget = 3 ∨ budget = 4 ∨ budget = 5 := by omega
    rcases choices with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem omega_has_no_completed_source_result (value : Value) : ¬ Evaluation omega .unit value := by
  intro evaluated
  obtain ⟨budget, events, finished⟩ := (evaluation_iff_finished omega .unit value).mp evaluated
  obtain ⟨residual, pending⟩ := loaded_omega_diverges budget
  change ((machine .neutral).run budget ⟨encodeValue .unit, compile omega, []⟩).2 = _ at pending
  rw [finished] at pending
  cases pending

private def silentlyClassifiedCAM : Machine State CategoricalAbstractMachine.Occurrence NativeValue Empty where
  step state := (CategoricalAbstractMachine.step .neutral state).map .silent

theorem all_computation_cannot_be_silent_administration : IsEmpty silentlyClassifiedCAM.Productive := by
  refine silentlyClassifiedCAM.not_productive_of_silent_region omegaRegion ?_ omegaCycle0 (.inl rfl)
  intro state inside
  obtain ⟨next, stepped, remains⟩ := omega_region_closed state inside
  change CategoricalAbstractMachine.step .neutral state = some next at stepped
  exact ⟨next, by simp only [silentlyClassifiedCAM, stepped]; rfl, remains⟩

theorem raw_underflow_prevents_a_global_productive_rank : IsEmpty (machine .neutral).Productive :=
  ⟨fun productive => productive.moves ⟨.unit, [.swap], []⟩ rfl⟩


namespace ScopedControls

open Mettapedia.OSLF.Binding

/-- Scoped instances of the existing source grammar; no free natural-number
variable is supplied as evidence of source formation. -/
def identityBody : Lambda.Scoped [()] := .var .zero
def scopedIdentity : Lambda.Closed := Lambda.lam identityBody
def scopedApplication : Lambda.Closed := Lambda.app scopedIdentity scopedIdentity

theorem identity_has_exact_readback : Lambda.Readback identityValue scopedIdentity :=
  .closure (values := []) (body := identityBody) .nil

theorem identity_source_beta : Lambda.Step scopedApplication scopedIdentity :=
  .beta identityBody scopedIdentity (.lam identityBody)

theorem identity_weak_evaluation : Lambda.CBV scopedApplication scopedIdentity :=
  .app (.lam identityBody) (.lam identityBody) (.beta (.lam identityBody))

theorem identity_proposition_3_2 :
    Lambda.Steps scopedApplication scopedIdentity ∧ Lambda.Normal scopedIdentity ∧
      CombinatorySteps (.question identityApplication .unit) (.answer identityValue) ∧
        Lambda.nativeReadback (extended := false) (encodeValue identityValue) = some identity :=
  ⟨identity_weak_evaluation.steps, identity_weak_evaluation.normal,
    identity_source_derivation.combinatory, Lambda.nativeReadback_encode identity_has_exact_readback⟩

theorem substitution_does_not_capture_the_inner_binder :
    Lambda.erase (inst (Lambda.lam (.var (.succ .zero))) scopedIdentity) =
      .lam (.lam (.var 0)) := rfl

def scopedConstant : Lambda.Closed := Lambda.lam (Lambda.lam (.var (.succ .zero)))
def scopedConstantIdentity : Lambda.Closed := Lambda.lam (Lambda.lam (.var .zero))
def scopedCapture : Lambda.Closed :=
  Lambda.app (Lambda.app scopedConstant scopedIdentity) (Lambda.pair scopedIdentity scopedIdentity)

theorem capture_keeps_the_saved_outer_value : Lambda.CBV scopedCapture scopedIdentity :=
  .app (.app (.lam _) (.lam _) (.beta (.lam _)))
    (.pair (.lam _) (.lam _)) (.beta (.lam _))

theorem shadowed_argument_remains_the_inner_argument :
    Lambda.erase (inst (Lambda.lam (.var .zero)) (Lambda.pair scopedIdentity scopedIdentity)) =
      .lam (.var 0) := rfl

theorem captured_closure_substitutes_the_retained_environment :
    Lambda.nativeReadback (extended := false) (encodeValue (.closure (.var 1) (.pair .unit identityValue))) =
      some (.lam (.lam (.var 0))) := by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl

theorem reversed_capture_slot_is_refused :
    Lambda.nativeReadback (extended := false) (encodeValue (.closure (.lam (.var 3)) (.pair .unit identityValue))) = none := by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl

theorem binder_shadowing_is_distinct_from_capturing :
    Lambda.nativeReadback (extended := false) (encodeValue (.closure (.var 0) (.pair .unit identityValue))) = some identity ∧
    Lambda.nativeReadback (extended := false) (encodeValue (.closure (.var 1) (.pair .unit identityValue))) =
      some (.lam (.lam (.var 0))) ∧ identity ≠ .lam (.lam (.var 0)) :=
  ⟨by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl,
   by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl, by decide⟩

theorem captured_environment_order_is_retained :
    Lambda.nativeReadback (extended := false) (encodeValue (.closure (.var 2)
      (.pair (.pair .unit identityValue) (.pair identityValue identityValue)))) = some (.lam identity) ∧
    Lambda.nativeReadback (extended := false) (encodeValue (.closure (.var 1)
      (.pair (.pair .unit identityValue) (.pair identityValue identityValue)))) =
        some (.lam (.pair identity identity)) :=
  ⟨by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl,
   by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl⟩

theorem environment_unit_is_not_a_source_value :
    Lambda.realize (extended := false) .unit = none ∧ Lambda.realizeEnvironment (extended := false) .unit = some [] := ⟨rfl, rfl⟩

theorem unscoped_code_is_not_granted_closed_readback :
    decodeValue (encodeValue (.closure (.var 1) .unit)) = some (.closure (.var 1) .unit) ∧
      Lambda.nativeReadback (extended := false) (encodeValue (.closure (.var 1) .unit)) = none :=
  ⟨decode_encodeValue _, by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl⟩

theorem unscoped_closure_may_finish_without_source_validity :
    ((machine .neutral).run 2 ((core .neutral).load (.lam (.var 1), .unit))).2 =
      .finished (encodeValue (.closure (.var 1) .unit)) ∧
        Lambda.nativeReadback (extended := false) (encodeValue (.closure (.var 1) .unit)) = none :=
  ⟨rfl, by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl⟩

theorem noncanonical_closure_is_not_granted_source_readback :
    Lambda.nativeReadback (extended := false) (.closure [.swap] .unit) = none := by
  simp [Lambda.nativeReadback, decodeSourceValue, decodeSourceCode]

theorem active_projection_cannot_be_supplied_as_a_neutral_value :
    Lambda.realize (.first (.pair identityValue identityValue)) = none := rfl

theorem active_application_cannot_be_supplied_as_a_neutral_value :
    Lambda.realize (.app (.pair identityValue identityValue)) = none := rfl

theorem malformed_application_payload_is_refused : Lambda.realize (.app identityValue) = none := rfl

def projectedIdentity : Lambda.Closed := Lambda.first scopedIdentity
def neutralApplication : Lambda.Closed := Lambda.app (Lambda.pair scopedIdentity scopedIdentity) scopedIdentity

theorem inactive_projection_is_an_exact_weak_value :
    Lambda.CBV projectedIdentity projectedIdentity ∧
      Lambda.nativeReadback (extended := false) (encodeValue (.first identityValue)) = some (.first identity) :=
  ⟨.first (.lam _) (.neutral _ (by simp [Lambda.NotPair])), by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl⟩

theorem inactive_application_is_an_exact_weak_value : Lambda.Normal neutralApplication :=
  .app (.pair (.lam _) (.lam _)) (.lam _) (by simp [Lambda.NotLam, scopedIdentity])

theorem closed_neutral_projection_profiles_remain_distinct :
    ((machine .strict).run 3 ((core .strict).load (.first identity, .unit))).2 =
      .stuck ⟨encodeValue identityValue, [.first], []⟩ ∧
    ((machine .neutral).run 3 ((core .neutral).load (.first identity, .unit))).2 =
      .finished (encodeValue (.first identityValue)) := ⟨rfl, rfl⟩

theorem weak_lambda_does_not_reduce_its_body :
    ¬ Lambda.Step (extended := false) (Lambda.lam (Lambda.app (Lambda.lam (.var .zero)) (.var .zero)))
      (Lambda.lam (.var .zero)) := Lambda.Normal.inert (.lam _)

theorem active_application_is_not_already_normal : ¬ Lambda.Normal scopedApplication := by
  intro normal
  cases normal with
  | app _ _ inactive => simp [Lambda.NotLam, scopedIdentity] at inactive

theorem source_right_argument_cannot_advance_first :
    ¬ Lambda.Step (Lambda.app scopedApplication scopedApplication)
      (Lambda.app scopedApplication scopedIdentity) := by
  intro transition
  apply active_application_is_not_already_normal
  exact transition.right_demand (by intro same; have erased := congrArg Lambda.erase same; cases erased)

theorem pair_right_component_cannot_advance_first :
    ¬ Lambda.Step (Lambda.pair scopedApplication scopedApplication)
      (Lambda.pair scopedApplication scopedIdentity) := by
  intro transition
  apply active_application_is_not_already_normal
  exact transition.pair_right_demand (by intro same; have erased := congrArg Lambda.erase same; cases erased)

def scopedDelta : Lambda.Closed := Lambda.lam (Lambda.app (.var .zero) (.var .zero))
def scopedOmega : Lambda.Closed := Lambda.app scopedDelta scopedDelta

theorem weak_self_application_is_a_computational_source_step : Lambda.Step scopedOmega scopedOmega :=
  .beta _ _ (.lam _)

theorem divergent_closed_source_has_no_normal_result (result : Lambda.Closed) :
    ¬ (Lambda.Steps scopedOmega result ∧ Lambda.Normal result) := by
  intro reduction
  obtain ⟨value, combinatory, _⟩ := (Lambda.proposition_3_2 scopedOmega result).mp reduction
  exact omega_has_no_completed_source_result value ((combinatory_iff_evaluation _ _ _).mp combinatory)

theorem general_nested_binders_are_retained (source : Lambda.Closed) :
    Lambda.represent [] (Lambda.erase source) = some source := Lambda.represent_erase source

theorem general_environment_extension_is_exact {values : List Lambda.Closed}
    (body : Lambda.Scoped (() :: Lambda.Context values))
    (argument : Lambda.Closed) :
    inst (bind (liftSub (Lambda.substitution values) [()]) body) argument =
      bind (Lambda.substitution (argument :: values)) body := by
  simpa only [Lambda.substitution_cons] using Lambda.instantiate_closed (Lambda.substitution values) body argument

end ScopedControls


noncomputable section

namespace TypedControls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory
open Typed

universe u v a
variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}

def typedIdentity (argument : TypeOf signature) :
    Typing [] identity (exponentialObject argument argument) :=
  .lam (.varZero [] argument)

def typedApplication (argument : TypeOf signature) :
    Typing [] identityApplication (exponentialObject argument argument) :=
  .app (typedIdentity (exponentialObject argument argument)) (typedIdentity argument)

theorem identity_type_preserves_domain (argument : TypeOf signature) :
    (typedIdentity argument).denote =
      abstraction (GeneratedCategory.second (terminal signature) argument) := rfl

theorem identity_value_at_arbitrary_ambient (argument ambient : TypeOf signature) :
    ValueMeaning ambient identityValue (exponentialObject argument argument)
      (toTerminal ambient ≫ (typedIdentity argument).denote) :=
  .closure (.varZero [] argument) .nil

theorem identity_application_categorical_meaning (argument ambient : TypeOf signature) :
    ValueMeaning ambient identityValue (exponentialObject argument argument)
      (toTerminal ambient ≫ (typedApplication argument).denote) :=
  evaluation_meaning identity_source_derivation (typedApplication argument) .nil

theorem identity_application_runs_table_1 (argument : TypeOf signature) :
    Steps .strict identityStart identityFinal :=
  strict_execution identity_source_derivation (typedApplication argument)
    (EnvironmentMeaning.nil (ambient := terminal signature))

theorem identity_strict_and_neutral_same_native_payload :
    ((machine .strict).run 8 identityStart).2 = .finished (encodeValue identityValue) ∧
      ((machine .neutral).run 8 identityStart).2 = .finished (encodeValue identityValue) := ⟨rfl, rfl⟩

theorem typed_native_result_meaning (argument ambient : TypeOf signature) :
    ∃ value, encodeValue value = encodeValue identityValue ∧
      ValueMeaning ambient value (exponentialObject argument argument)
        (toTerminal ambient ≫ (typedApplication argument).denote) :=
  strict_finished_meaning (typedApplication argument) (EnvironmentMeaning.nil (ambient := ambient))
    (budget := 8) (events := ((machine .strict).run 8 identityStart).1) rfl

theorem typed_body_scope_at_all_depths {rest : List (TypeOf signature)} {body : Expr}
    {argument result : TypeOf signature} (typed : Typing (argument :: rest) body result) :
    ∃ source : Lambda.Scoped (List.replicate (rest.length + 1) ()), Lambda.erase source = body :=
  typed.scoped

def typedCaptured (argument captured : TypeOf signature) :
    Typing [captured] (.lam (.var 1)) (exponentialObject argument captured) :=
  .lam (.varSucc argument (.varZero [] captured))

theorem captured_body_uses_old_coordinate (argument captured : TypeOf signature) :
    (typedCaptured argument captured).denote = abstraction
      (GeneratedCategory.first (product (terminal signature) captured) argument ≫
        GeneratedCategory.second (terminal signature) captured) := rfl

theorem closure_meaning_retains_captured_value {ambient argument captured : TypeOf signature}
    {value : Value} {arrow : ambient ⟶ captured}
    (meaning : ValueMeaning ambient value captured arrow) :
    ValueMeaning ambient (.closure (.var 1) (.pair .unit value))
      (exponentialObject argument captured)
      (pairing (toTerminal ambient) arrow ≫ (typedCaptured argument captured).denote) :=
  .closure (.varSucc argument (.varZero [] captured)) (.cons .nil meaning)

def typedSwap (left right : TypeOf signature) :
    Typing [right, left] (.pair (.var 1) (.var 0)) (product left right) :=
  .pair (.varSucc right (.varZero [] left)) (.varZero [left] right)

theorem pair_compilation_retains_coordinate_order (left right : TypeOf signature) :
    (typedSwap left right).denote = pairing
      (GeneratedCategory.first (product (terminal signature) left) right ≫
        GeneratedCategory.second (terminal signature) left)
      (GeneratedCategory.second (product (terminal signature) left) right) := rfl

theorem pair_native_evaluation_retains_both_values (left right : Value) :
    Evaluation (.pair (.var 1) (.var 0)) (.pair (.pair .unit left) right) (.pair left right) :=
  .pair (.varSucc (.pair _ _) (.varZero (.pair _ _))) (.varZero (.pair _ _))

theorem pair_categorical_execution {ambient left right : TypeOf signature}
    {leftValue rightValue : Value} {leftArrow : ambient ⟶ left} {rightArrow : ambient ⟶ right}
    (leftMeaning : ValueMeaning ambient leftValue left leftArrow)
    (rightMeaning : ValueMeaning ambient rightValue right rightArrow) :
    ValueMeaning ambient (.pair leftValue rightValue) (product left right)
      ((pairing (pairing (toTerminal ambient) leftArrow) rightArrow) ≫ (typedSwap left right).denote) :=
  evaluation_meaning (pair_native_evaluation_retains_both_values _ _) (typedSwap left right)
    (.cons (.cons .nil leftMeaning) rightMeaning)

theorem typed_projection_follows_active_table {ambient left right : TypeOf signature}
    {leftValue rightValue : Value} {leftArrow : ambient ⟶ left} {rightArrow : ambient ⟶ right}
    (leftMeaning : ValueMeaning ambient leftValue left leftArrow)
    (rightMeaning : ValueMeaning ambient rightValue right rightArrow) :
    Steps .strict
      ⟨encodeValue (.pair (.pair .unit leftValue) rightValue),
        compile (.first (.pair (.var 1) (.var 0))), []⟩
      ⟨encodeValue leftValue, [], []⟩ :=
  strict_execution (.first (pair_native_evaluation_retains_both_values _ _) (.pair _ _))
    (.first (typedSwap left right)) (.cons (.cons .nil leftMeaning) rightMeaning)

theorem beta_uses_complete_source_environment {rest : List (TypeOf signature)}
    {body argument : Expr} {domain result : TypeOf signature}
    (bodyTyped : Typing (domain :: rest) body result)
    (argumentTyped : Typing rest argument domain) :
    (Typing.app (.lam bodyTyped) argumentTyped).denote =
      pairing (𝟙 (context rest)) argumentTyped.denote ≫ bodyTyped.denote :=
  Typing.beta bodyTyped argumentTyped

theorem pure_beta_equality_has_no_instruction_count :
    ((machine .strict).run 2 ((core .strict).load (identity, .unit))).2 =
      .finished (encodeValue identityValue) ∧
      ((machine .strict).run 2 identityStart).2 ≠ .finished (encodeValue identityValue) := by
  constructor
  · rfl
  · intro impossible; cases impossible

theorem beta_equivalent_source_has_equal_categorical_meaning (argument : TypeOf signature) :
    (typedApplication argument).denote = (typedIdentity argument).denote := by
  have beta := Typing.beta (.varZero [] (exponentialObject argument argument)) (typedIdentity argument)
  simpa only [typedApplication, typedIdentity, Typing.denote, GeneratedCategory.pairing_second] using beta

theorem categorical_equality_does_not_erase_compiled_work (argument : TypeOf signature) :
    (typedApplication argument).denote = (typedIdentity argument).denote ∧
      compile identityApplication ≠ compile identity := by
  refine ⟨beta_equivalent_source_has_equal_categorical_meaning argument, ?_⟩
  intro collapsed
  have sourceSame := compile_injective collapsed
  cases sourceSame

theorem typed_execution_suffix_retains_stack (argument : TypeOf signature)
    (code : Code) (stack : List NativeValue) :
    Steps .strict ⟨.unit, compile identityApplication ++ code, stack⟩
      ⟨encodeValue identityValue, code, stack⟩ :=
  strict_execution_tail identity_source_derivation (typedApplication argument)
    (EnvironmentMeaning.nil (ambient := terminal signature)) code stack

theorem no_type_for_closed_free_variable (result : TypeOf signature) :
    ¬ Nonempty (Typing [] (.var 0) result) := by
  rintro ⟨typed⟩
  obtain ⟨source, represented⟩ := typed.represented
  simp [Lambda.represent, Lambda.slot?] at represented

theorem no_type_for_canonical_unscoped_body (result : TypeOf signature) :
    ¬ Nonempty (Typing [] (.lam (.var 1)) result) := by
  rintro ⟨typed⟩
  obtain ⟨source, represented⟩ := typed.represented
  simp [Lambda.represent, Lambda.slot?] at represented

theorem projection_of_function_has_no_type (result : TypeOf signature) :
    ¬ Nonempty (Typing [] (.first identity) result) := by
  rintro ⟨typed⟩
  cases typed with
  | first functionTyped =>
      obtain ⟨argument, result, same⟩ := functionTyped.lambda_type
      have codeSame := congrArg Object.code same
      cases codeSame

theorem neutral_projection_has_no_categorical_value (ambient result : TypeOf signature)
    (arrow : ambient ⟶ result) : ¬ ValueMeaning ambient (.first identityValue) result arrow := by
  intro meaning
  cases meaning

theorem neutral_application_has_no_categorical_value (ambient result : TypeOf signature)
    (arrow : ambient ⟶ result) :
    ¬ ValueMeaning ambient (.app (.pair identityValue identityValue)) result arrow := by
  intro meaning
  cases meaning

theorem canonical_but_unscoped_closure_has_no_meaning (ambient result : TypeOf signature)
    (arrow : ambient ⟶ result) :
    ¬ ValueMeaning ambient (.closure (.var 1) .unit) result arrow := by
  intro meaning
  cases meaning with
  | closure typed captured =>
      cases captured
      obtain ⟨source, represented⟩ := typed.represented
      simp [Lambda.represent, Lambda.slot?] at represented

theorem strict_refuses_the_untyped_neutral_projection :
    ((machine .strict).run 3 ((core .strict).load (.first identity, .unit))).2 =
      .stuck ⟨encodeValue identityValue, [.first], []⟩ := rfl

theorem type_object_tags_are_not_erased (argument result : TypeOf signature) :
    product argument result ≠ exponentialObject argument result := by
  intro collapsed
  have codes := congrArg Object.code collapsed
  cases codes

theorem simple_types_do_not_contain_themselves (argument result : TypeOf signature) :
    argument ≠ exponentialObject argument result := by
  intro recursiveType
  have sizes := congrArg (fun object : TypeOf signature => sizeOf object.code) recursiveType
  simp only [exponentialObject, ObjectCode.exponential.sizeOf_spec] at sizes
  omega

theorem untyped_self_application_stays_outside_the_typed_profile (result : TypeOf signature) :
    ¬ Nonempty (Typing [] delta result) := by
  rintro ⟨typed⟩
  cases typed with
  | lam bodyTyped =>
      cases bodyTyped with
      | app functionTyped argumentTyped =>
          have functionSame := functionTyped.variable_zero_type
          have argumentSame := argumentTyped.variable_zero_type
          rw [argumentSame] at functionSame
          exact simple_types_do_not_contain_themselves _ _ functionSame.symm

end TypedControls

end

/-! ## Operational quotation and Boolean selection -/

namespace ConstantControls

def trueArm : Code := [.quote (.integer 37)]
def falseArm : Code := [.quote (.integer (-11))]
def branchStart (selected : Bool) : State :=
  ⟨.unit, [.push, .quote (.boolean selected), .branch trueArm falseArm], []⟩
def branchDecision (selected : Bool) : State :=
  ⟨.literal (.boolean selected), [.branch trueArm falseArm], [.unit]⟩
def chosenStart (selected : Bool) : State :=
  ⟨.unit, if selected then trueArm else falseArm, []⟩
def branchResult (selected : Bool) : NativeValue :=
  .literal (.integer (if selected then 37 else -11))

theorem quote_keeps_arbitrary_suffix_and_stack (profile : Profile) (saved : NativeValue)
    (literal : Literal) (suffix : Code) (stack : List NativeValue) :
    step profile ⟨saved, .quote literal :: suffix, stack⟩ =
      some ⟨.literal literal, suffix, stack⟩ := quote_step _ _ _ _ _

theorem quote_is_independently_judged (profile : Profile) (saved : NativeValue)
    (literal : Literal) (suffix : Code) (stack : List NativeValue) :
    Transition profile ⟨saved, .quote literal :: suffix, stack⟩ ⟨.literal literal, suffix, stack⟩ :=
  .quote _ _ _ _ _

theorem selection_restores_exact_saved_environment (profile : Profile) (selected : Bool)
    (environment : NativeValue) (left right suffix : Code) (stack : List NativeValue) :
    step profile ⟨.literal (.boolean selected), .branch left right :: suffix, environment :: stack⟩ =
      some ⟨environment, (if selected then left else right) ++ suffix, stack⟩ := branch_step _ _ _ _ _ _ _

theorem strict_true_arm_finishes :
    ((machine .strict).run 5 (branchStart true)).2 = .finished (branchResult true) := rfl

theorem strict_false_arm_finishes :
    ((machine .strict).run 5 (branchStart false)).2 = .finished (branchResult false) := rfl

theorem neutral_true_arm_finishes :
    ((machine .neutral).run 5 (branchStart true)).2 = .finished (branchResult true) := rfl

theorem quote_branch_cost_is_four_instructions_and_completion :
    (machine .strict).spent (computationalPrice (core .strict) (fun _ => 1)) 5 (branchStart true) = 4 ∧
      (machine .strict).spent (fun _ => 1) 5 (branchStart true) = 5 := ⟨rfl, rfl⟩

theorem selection_pause_keeps_entire_packet :
    ((machine .strict).run 2 (branchStart true)).2 = .exhausted (branchDecision true) := rfl

theorem selection_resume_delivers_only_selected_arm :
    ((machine .strict).run 3 (branchDecision true)).2 = .finished (branchResult true) := rfl

theorem full_and_resumed_occurrences_agree :
    ((machine .strict).run 5 (branchStart true)).1 =
      ((machine .strict).run 2 (branchStart true)).1 ++
        ((machine .strict).run 3 (branchDecision true)).1 := rfl

theorem selection_is_one_productive_occurrence :
    (machine .strict).run 1 (branchDecision true) =
      ([(branchDecision true, chosenStart true)], .exhausted (chosenStart true)) := rfl

theorem branch_underflow_is_stuck :
    (machine .strict).run 1 ⟨.literal (.boolean true), [.branch trueArm falseArm], []⟩ =
      ([], .stuck ⟨.literal (.boolean true), [.branch trueArm falseArm], []⟩) := rfl

theorem integer_zero_does_not_acquire_boolean_truthiness :
    step .neutral ⟨.literal (.integer 0), [.branch trueArm falseArm], [.unit]⟩ = none := rfl

theorem nonzero_integer_does_not_acquire_boolean_truthiness :
    step .neutral ⟨.literal (.integer 73), [.branch trueArm falseArm], [.unit]⟩ = none := rfl

theorem neutral_term_does_not_acquire_boolean_truthiness :
    step .neutral ⟨.first .unit, [.branch trueArm falseArm], [.unit]⟩ = none := rfl

theorem empty_selected_arm_retains_saved_value :
    (machine .strict).run 2 ⟨.literal (.boolean false), [.branch [.swap] []],
      [encodeValue identityValue]⟩ =
      ([(⟨.literal (.boolean false), [.branch [.swap] []], [encodeValue identityValue]⟩,
          ⟨encodeValue identityValue, [], []⟩)], .finished (encodeValue identityValue)) := rfl

theorem unselected_malformed_arm_is_not_executed :
    ((machine .strict).run 3 ⟨.literal (.boolean true), [.branch trueArm [.swap]], [.unit]⟩).2 =
      .finished (branchResult true) := rfl

theorem selected_malformed_arm_does_get_stuck :
    ((machine .strict).run 2 ⟨.literal (.boolean false), [.branch trueArm [.swap]], [.unit]⟩).2 =
      .stuck ⟨.unit, [.swap], []⟩ := rfl

theorem branch_uses_saved_pair_and_consumes_only_one_stack_entry :
    step .strict ⟨.literal (.boolean true), [.branch [.first] [.second], .push],
      [.pair (.literal (.integer 5)) (.literal (.integer 9)), encodeValue identityValue]⟩ =
      some ⟨.pair (.literal (.integer 5)) (.literal (.integer 9)), [.first, .push],
        [encodeValue identityValue]⟩ := rfl

theorem selected_arm_then_suffix_keep_older_stack :
    ((machine .strict).run 3 ⟨.literal (.boolean true), [.branch [.first] [.second], .push],
      [.pair (.literal (.integer 5)) (.literal (.integer 9)), encodeValue identityValue]⟩).2 =
      .exhausted ⟨.literal (.integer 5), [], [.literal (.integer 5), encodeValue identityValue]⟩ := rfl

theorem selected_arm_suffix_can_leave_a_nonanswer :
    answer ⟨.literal (.integer 5), [], [.literal (.integer 5), encodeValue identityValue]⟩ = none := rfl

theorem missing_code_does_not_discard_retained_stack :
    ((machine .strict).run 4 ⟨.literal (.boolean true), [.branch [.first] [.second], .push],
      [.pair (.literal (.integer 5)) (.literal (.integer 9)), encodeValue identityValue]⟩).2 =
      .stuck ⟨.literal (.integer 5), [], [.literal (.integer 5), encodeValue identityValue]⟩ := rfl

theorem completed_answers_do_not_determine_unselected_code :
    ((machine .strict).run 3 ⟨.literal (.boolean true), [.branch trueArm [.swap]], [.unit]⟩).2 =
      ((machine .strict).run 3 ⟨.literal (.boolean true), [.branch trueArm [.cons]], [.unit]⟩).2 ∧
    ((machine .strict).run 3 ⟨.literal (.boolean true), [.branch trueArm [.swap]], [.unit]⟩).1 ≠
      ((machine .strict).run 3 ⟨.literal (.boolean true), [.branch trueArm [.cons]], [.unit]⟩).1 := by
  exact ⟨rfl, by decide⟩

theorem old_compiled_reachable_packets_remain_constant_free (term : Expr) (environment : Value)
    (state : State) (reached : Steps .neutral ((core .neutral).load (term, environment)) state) :
    ConstantFreeState state := compiled_constantFree reached

theorem extended_native_closure_is_not_old_source_readback :
    decodeValue (.closure [.quote (.integer 5)] .unit) = none ∧
      Lambda.nativeReadback (extended := false) (.literal (.boolean true)) = none := by
  exact ⟨by simp [decodeValue, decodeSourceValue, decodeSourceCode], rfl⟩

theorem successful_quote_does_not_certify_old_source :
    ((machine .strict).run 2 ⟨.unit, [.quote (.integer 5)], []⟩).2 =
      .finished (.literal (.integer 5)) ∧ decodeCode [.quote (.integer 5)] = none :=
  ⟨rfl, decode_quote _ _⟩

theorem constant_free_is_not_compiler_authority :
    ConstantFreeCode redundantRawCode ∧ decodeCode redundantRawCode = none := by
  refine ⟨?_, redundant_raw_work_is_not_canonical_compilation⟩
  exact .cons (.cur (.singleton .second))
    (.cons .push (.cons .swap (.cons .cons (.singleton .first))))

theorem arbitrary_old_compiled_answers_cannot_be_quoted (term : Expr) (environment : Value)
    (literal : Literal) :
    ¬ (answerCore .neutral).Produces (term, environment) (.literal literal) := by
  intro produced
  obtain ⟨source, _, same⟩ := (produces_iff_evaluation term environment (.literal literal)).mp produced
  exact (encodeValue_constantFree source).not_literal literal same

end ConstantControls

namespace LoadingControls

/-- Canonical code loading retains arbitrarily supplied captured environments. -/
theorem captured_environment_is_loaded (environment : Value) :
    loadImage .strict (compile (.lam (.var 0)), environment) =
      some ⟨encodeValue environment, compile (.lam (.var 0)), []⟩ := by
  exact loadImage_compileImage .strict (.lam (.var 0), environment)

/-- Canonical source-image admission does not prove an open term executable. -/
theorem admitted_open_term_still_stuck :
    loadImage .strict (compile (.var 0), .unit) = some ⟨.unit, [.second], []⟩ ∧
      step .strict ⟨.unit, [.second], []⟩ = none ∧
      ¬ InstructionLegal .strict ⟨.unit, [.second], []⟩ .second := by
  refine ⟨?_, rfl, ?_⟩
  · simpa only [compileImage, core, sourceCore, compile, compileSource, List.replicate_zero, List.nil_append, encodeValue, encodeSourceValue] using
      loadImage_compileImage .strict (.var 0, .unit)
  rintro ⟨rest, next, _, transition⟩
  have impossible := step_complete transition
  cases impossible

/-- Raw extension code can execute while remaining outside the old compiler image. -/
theorem raw_quote_needs_an_extended_source_image (profile : Profile) :
    step profile ⟨.unit, [.quote (.integer 7)], []⟩ =
      some ⟨.literal (.integer 7), [], []⟩ ∧
      loadImage profile ([.quote (.integer 7)], .unit) = none := by
  refine ⟨rfl, ?_⟩
  exact (loadImage_refused_iff profile _ .unit).mpr (decode_quote _ _)

/-- An instruction requiring a saved register cannot advance with an empty stack. -/
theorem stack_underflow_is_an_illegal_instruction (profile : Profile) :
    ¬ InstructionLegal profile ⟨.unit, [.swap], []⟩ .swap := by
  rintro ⟨rest, next, _, transition⟩
  have impossible := step_complete transition
  cases impossible

/-- A fetched instruction with its required stack entry constructs a successor. -/
theorem saved_register_licenses_swap (profile : Profile) :
    ∃ next, (core profile).step ⟨.unit, [.swap], [.literal (.integer 7)]⟩ = some next := by
  apply (instructionContract profile).legal_advances (opcode := .swap) (by rfl)
  exact ⟨[], _, rfl, .swap profile .unit (.literal (.integer 7)) [] []⟩

end LoadingControls

/-! ## The compiled quotation/conditional source fragment -/

namespace ExtendedControls

abbrev E := CategoricalAbstractMachine.Extended.Expr
abbrev V := CategoricalAbstractMachine.Extended.Value

def number (value : Int) : E := Extended.quote (.integer value)
def boolean (value : Bool) : E := Extended.quote (.boolean value)
def numberValue (value : Int) : V := .literal rfl (.integer value)

/-- The test condition itself evaluates an application. Neither arm is run
while the outer closure is being constructed. -/
def selectedBody : E := Extended.conditional
  (.app (.lam (.var 0)) (boolean true))
  (.pair (.var 1) (Extended.conditional (boolean false) (number 4) (number 3)))
  omega.enable

def capturedProgram : E := .app
  (.app (.lam (.lam selectedBody))
    (Extended.conditional (boolean true) (number 7) (number 8)))
  (number 99)

def capturedResult : V := .pair (numberValue 7) (numberValue 3)
def outerEnvironment : V := .pair .unit (numberValue 7)
def innerEnvironment : V := .pair outerEnvironment (numberValue 99)

theorem selected_body_source : Evaluation selectedBody innerEnvironment capturedResult := by
  apply Evaluation.conditional (selected := true)
  · exact .app (.lam _ _) (.literal rfl _ _) (.closure (.varZero (.pair _ _)))
  · apply Evaluation.pair
    · exact .varSucc (.pair _ _) (.varZero (.pair _ _))
    · exact .conditional (selected := false) (.literal rfl _ _) (.literal rfl _ _)

theorem captured_program_source : Evaluation capturedProgram .unit capturedResult := by
  apply Evaluation.app
  · apply Evaluation.app
    · exact .lam _ _
    · exact .conditional (selected := true) (.literal rfl _ _) (.literal rfl _ _)
    · exact .closure (.lam _ _)
  · exact .literal rfl _ _
  · exact .closure selected_body_source

theorem nested_source_decodes (body : E) :
    Extended.decodeCode (compileSource (.lam (.pair body selectedBody))) =
      some (.lam (.pair body selectedBody)) := decode_compile _

theorem captured_closure_and_environment_decode :
    Extended.decodeValue (encodeSourceValue (.closure selectedBody outerEnvironment)) =
      some (.closure selectedBody outerEnvironment) := decode_encodeValue _

theorem source_execution_keeps_caller (suffix : Code) (stack : List NativeValue) :
    Steps .neutral ⟨.unit, compileSource capturedProgram ++ suffix, stack⟩
      ⟨encodeSourceValue capturedResult, suffix, stack⟩ :=
  captured_program_source.execution_tail suffix stack

theorem compiled_nested_capture_finishes :
    ((machine .neutral).run 60 ⟨.unit, compileSource capturedProgram, []⟩).2 =
      .finished (encodeSourceValue capturedResult) := rfl

theorem strict_nested_capture_finishes :
    ((machine .strict).run 60 ⟨.unit, compileSource capturedProgram, []⟩).2 =
      .finished (encodeSourceValue capturedResult) := rfl

theorem selected_branch_does_not_replace_captured_outer_slot :
    ((machine .neutral).run 60 ⟨.unit, compileSource capturedProgram, []⟩).2 ≠
      .finished (.pair (.literal (.integer 99)) (.literal (.integer 3))) := by
  rw [compiled_nested_capture_finishes]
  intro same
  cases same

theorem source_and_actual_readback_agree :
    ∃ native, Steps .neutral ⟨.unit, compileSource capturedProgram, []⟩ ⟨native, [], []⟩ ∧
      Extended.decodeValue native = some capturedResult :=
  (evaluation_iff_nativeReadback capturedProgram .unit capturedResult).mp captured_program_source

theorem extended_source_is_admitted :
    Extended.loadImage .neutral (compileSource capturedProgram, .unit) =
      some ⟨.unit, compileSource capturedProgram, []⟩ :=
  Extended.loadImage_compileImage .neutral (capturedProgram, .unit)

def badCondition : E := Extended.conditional (number 7) (number 1) (number 2)
def badConditionDecision : State :=
  ⟨.literal (.integer 7), [.branch (compileSource (number 1)) (compileSource (number 2))], [.unit]⟩

theorem non_boolean_source_has_no_completed_evaluation (value : V) :
    ¬ Evaluation badCondition .unit value := by
  intro evaluation
  cases evaluation with
  | conditional conditionEval _ => cases conditionEval

theorem non_boolean_compiled_condition_is_stuck :
    (machine .neutral).run 3 ⟨.unit, compileSource badCondition, []⟩ =
      ([ (⟨.unit, compileSource badCondition, []⟩,
           ⟨.unit, [.quote (.integer 7), .branch (compileSource (number 1)) (compileSource (number 2))], [.unit]⟩),
         (⟨.unit, [.quote (.integer 7), .branch (compileSource (number 1)) (compileSource (number 2))], [.unit]⟩,
           badConditionDecision) ], .stuck badConditionDecision) := rfl

theorem stopped_non_boolean_packet_is_not_an_answer :
    step .neutral badConditionDecision = none ∧ answer badConditionDecision = none := ⟨rfl, rfl⟩

theorem unselected_ill_formed_condition_is_not_evaluated :
    Evaluation (Extended.conditional (boolean true) (number 12) badCondition) .unit
      (numberValue 12) :=
  .conditional (selected := true) (.literal rfl _ _) (.literal rfl _ _)

theorem quote_is_an_extended_image_but_not_a_historical_image :
    Extended.decodeCode [.quote (.integer 7)] = some (number 7) ∧
      decodeCode [.quote (.integer 7)] = none := ⟨decode_compile (number 7), decode_quote _ _⟩

theorem arbitrary_historical_source_is_conservative (term : Expr) (environment value : Value) :
    Evaluation term.enable environment.enable value.enable ↔ Evaluation term environment value :=
  evaluation_enable_iff _ _ _

theorem redundant_quote_work_does_not_pass_extended_admission :
    Extended.decodeCode [.quote (.integer 1), .quote (.integer 2)] = none := by
  simp [Extended.decodeCode, decodeSourceCode]

/-- Extending source literals does not collapse strict and neutral projections. -/
theorem strict_and_neutral_remain_distinct_on_literal_projection :
    (step .strict ⟨.literal (.integer 7), [.first], []⟩ = none) ∧
      (step .neutral ⟨.literal (.integer 7), [.first], []⟩ =
        some ⟨.first (.literal (.integer 7)), [], []⟩) := ⟨rfl, rfl⟩

end ExtendedControls


/-! ## The value graph: recursion by update and delayed evaluation -/

namespace GraphControls

abbrev T := Graph.Term

def int (value : Int) : T := .literal (.integer value)

/-- The root word of a finished run. -/
def finishedRoot : Outcome Graph.State Graph.Answer Empty → Option Graph.Word
  | .finished completed => some completed.root
  | _ => none

/-- The completed answer of a finished run. -/
def finishedAnswer : Outcome Graph.State Graph.Answer Empty → Option Graph.Answer
  | .finished completed => some completed
  | _ => none

/-- The residual configuration of an exhausted run. -/
def exhaustedState : Outcome Graph.State Graph.Answer Empty → Option Graph.State
  | .exhausted residual => some residual
  | _ => none

/-- The remaining code of a stuck run. -/
def stuckCode : Outcome Graph.State Graph.Answer Empty → Option Code
  | .stuck state => some state.code
  | _ => none

theorem finishedRoot_some {outcome : Outcome Graph.State Graph.Answer Empty} {root : Graph.Word}
    (found : finishedRoot outcome = some root) : ∃ heap, outcome = .finished ⟨root, heap⟩ := by
  cases outcome with
  | finished completed =>
      simp only [finishedRoot, Option.some.injEq] at found
      exact ⟨completed.heap, by rw [← found]⟩
  | faulted | suspended _ _ | stuck _ | exhausted _ => simp [finishedRoot] at found

/-- A source value is certified by a finished run of its loaded question. -/
theorem source_value_of_run {term : T} {budget : Nat} {value : Literal}
    (ran : finishedRoot (Graph.machine.run budget (Graph.load (term, .unit))).2 = some (.literal value)) :
    Graph.Evaluation term .unit (.literal value) := by
  obtain ⟨heap, finished⟩ := finishedRoot_some ran
  obtain ⟨result, evaluated, represented⟩ := Graph.finished_evaluation (Prod.ext rfl finished)
  cases represented
  exact evaluated

/-- A configuration at which `unfreeze` meets a laze cell. -/
def forcesLaze : Graph.State → Bool
  | ⟨.ref address, .unfreeze :: _, _, heap⟩ =>
      match heap[address]? with
      | some (.laze _ _) => true
      | _ => false
  | _ => false

/-- The number of forcing occurrences in a run. -/
def forcings (events : List Graph.Occurrence) : Nat := events.countP fun event => forcesLaze event.1

/-! ### Recursion by `wind` (Section 4, Table 6) -/

/-- CCM's factorial body `if n = 0 then 1 else n * f (n - 1)`; `n` is index 0, `f` index 1. -/
def factorialBody : T :=
  .conditional (.primitive .equal (.pair (.var 0) (int 0))) (int 1)
    (.primitive .times (.pair (.var 0) (.app (.var 1) (.primitive .minus (.pair (.var 0) (int 1))))))

def factorialProgram : T := .app (.fix factorialBody) (int 3)
def factorialStart : Graph.State := Graph.load (factorialProgram, .unit)

theorem factorial_of_three_is_six :
    finishedRoot (Graph.machine.run 204 factorialStart).2 = some (.literal (.integer 6)) := by decide +kernel

theorem factorial_runs_203_instructions :
    (Graph.machine.run 204 factorialStart).1.length = 203 := by decide +kernel

/-- Completeness turns the finished run into the independent source derivation. -/
theorem factorial_source_evaluation : Graph.Evaluation factorialProgram .unit (.literal (.integer 6)) :=
  source_value_of_run factorial_of_three_is_six

/-- `F(C) = push; quote (); cons; push; cur C; wind`. -/
theorem recursion_code_is_table_6 :
    Graph.compile (.fix factorialBody) =
      [.push, .quote .unit, .cons, .push, .cur (Graph.compile factorialBody), .wind] := rfl

def cycleHeap : Graph.Heap := [.pair .unit (.ref 1), .closure (Graph.compile factorialBody) (.ref 0)]

/-- After `wind` the couple holds the closure and the closure holds the couple:
the register is `c = C:((), c)` and the run has used six instructions. -/
theorem wind_builds_the_cycle :
    finishedAnswer (Graph.machine.run 7 (Graph.load (.fix factorialBody, .unit))).2 = some ⟨.ref 1, cycleHeap⟩ ∧
      (Graph.machine.run 7 (Graph.load (.fix factorialBody, .unit))).1.length = 6 := by decide +kernel

/-- Before `wind` the couple still holds the dummy `()`. -/
theorem before_wind_the_couple_holds_the_dummy :
    exhaustedState (Graph.machine.run 5 (Graph.load (.fix factorialBody, .unit))).2 =
      some ⟨.ref 1, [.wind], [.ref 0],
        [.pair .unit (.literal .unit), .closure (Graph.compile factorialBody) (.ref 0)]⟩ := by decide +kernel

theorem cycle_represents_the_recursive_value :
    Graph.Represents cycleHeap (.ref 1) (.recursive factorialBody .unit) :=
  .recursive rfl rfl .unit

/-- The cyclic node also represents the one-step unfolding; the representation is
a relation, and only the recursive value is the source value of `fix`. -/
theorem cycle_also_represents_its_unfolding :
    Graph.Represents cycleHeap (.ref 1)
        (.closure factorialBody (.pair .unit (.recursive factorialBody .unit))) ∧
      ¬ Graph.Evaluation (.fix factorialBody) .unit
        (.closure factorialBody (.pair .unit (.recursive factorialBody .unit))) := by
  refine ⟨cycle_represents_the_recursive_value.unfolding, ?_⟩
  intro evaluated
  cases evaluated

theorem fix_evaluates_to_the_recursive_value :
    Graph.Evaluation (.fix factorialBody) .unit (.recursive factorialBody .unit) := .fix _ _

/-- The cycle refers forward, so it is not topologically ordered, and it has no
finite unfolding to a tree value. -/
theorem wind_breaks_order_and_tree_unfolding (native : NativeValue) :
    ¬ Graph.Ordered cycleHeap ∧ ¬ Graph.Unfolds cycleHeap (.ref 1) native :=
  ⟨Graph.windHeap_not_ordered [] .unit _, Graph.windHeap_no_unfolding [] .unit _ native⟩

/-! ### Delayed evaluation (Section 4, Table 7) -/

/-- `let z = 2 in (λx.z)(freeze((λy.y) 1))` and its eager variant. -/
def frozenWork : T := .app (.lam (.var 0)) (int 1)
def lazyProgram : T := .app (.lam (.app (.lam (.var 1)) (.freeze frozenWork))) (int 2)
def eagerProgram : T := .app (.lam (.app (.lam (.var 1)) frozenWork)) (int 2)

theorem lazy_program_source_evaluation : Graph.Evaluation lazyProgram .unit (.literal (.integer 2)) :=
  .app (.lam _ _) (.literal _ _) (.value _ trivial)
    (.closure (.app (.lam _ _) (.freeze _ _) (.value _ trivial) (.closure (.varSucc _ (.varZero _ _)))))

theorem lazy_program_returns_two :
    finishedRoot (Graph.machine.run 27 (Graph.load (lazyProgram, .unit))).2 = some (.literal (.integer 2)) := by
  decide +kernel

theorem eager_program_returns_two :
    finishedRoot (Graph.machine.run 39 (Graph.load (eagerProgram, .unit))).2 = some (.literal (.integer 2)) := by
  decide +kernel

/-- The frozen work is never forced, and the lazy run is twelve instructions
shorter: thirteen instructions of `(λy.y) 1` against one `freeze`. -/
theorem frozen_work_is_never_executed :
    forcings (Graph.machine.run 27 (Graph.load (lazyProgram, .unit))).1 = 0 ∧
      (Graph.machine.run 27 (Graph.load (lazyProgram, .unit))).1.length = 26 ∧
      (Graph.machine.run 39 (Graph.load (eagerProgram, .unit))).1.length = 38 := by decide +kernel

/-- A recursive stream `fix (λn. (n, freeze (f (n + 1))))`, forced twice. -/
def streamBody : T := .pair (.var 0) (.freeze (.app (.var 1) (.primitive .plus (.pair (.var 0) (int 1)))))
def streamProgram : T := .first (.second (.second (.app (.fix streamBody) (int 0))))

theorem stream_third_element_after_two_forcings :
    finishedRoot (Graph.machine.run 93 (Graph.load (streamProgram, .unit))).2 = some (.literal (.integer 2)) ∧
      forcings (Graph.machine.run 93 (Graph.load (streamProgram, .unit))).1 = 2 := by decide +kernel

theorem stream_source_evaluation : Graph.Evaluation streamProgram .unit (.literal (.integer 2)) :=
  source_value_of_run stream_third_element_after_two_forcings.1

/-- Call by name: a laze used twice is forced twice; used once, once; the eager
argument is never forced. All three return 12. -/
def sharedWork : T := .primitive .times (.pair (int 2) (int 3))
def twiceProgram : T := .app (.lam (.primitive .plus (.pair (.var 0) (.var 0)))) (.freeze sharedWork)
def onceProgram : T := .app (.lam (.primitive .plus (.pair (.var 0) (int 6)))) (.freeze sharedWork)
def eagerTwiceProgram : T := .app (.lam (.primitive .plus (.pair (.var 0) (.var 0)))) sharedWork

theorem laze_used_twice_runs_twice :
    finishedRoot (Graph.machine.run 57 (Graph.load (twiceProgram, .unit))).2 = some (.literal (.integer 12)) ∧
      forcings (Graph.machine.run 57 (Graph.load (twiceProgram, .unit))).1 = 2 ∧
      finishedRoot (Graph.machine.run 42 (Graph.load (onceProgram, .unit))).2 = some (.literal (.integer 12)) ∧
      forcings (Graph.machine.run 42 (Graph.load (onceProgram, .unit))).1 = 1 ∧
      finishedRoot (Graph.machine.run 40 (Graph.load (eagerTwiceProgram, .unit))).2 =
        some (.literal (.integer 12)) ∧
      forcings (Graph.machine.run 40 (Graph.load (eagerTwiceProgram, .unit))).1 = 0 := by decide +kernel

/-- Primitive operands keep their places: `5 - 3 = 2` and `5 ≤ 3` is false. -/
theorem primitive_operands_keep_their_places :
    finishedRoot (Graph.machine.run 15 (Graph.load (.primitive .minus (.pair (int 5) (int 3)), .unit))).2 =
        some (.literal (.integer 2)) ∧
      finishedRoot (Graph.machine.run 15
        (Graph.load (.primitive .lessEqual (.pair (int 5) (int 3)), .unit))).2 =
        some (.literal (.boolean false)) := by decide +kernel

/-! ### Divergence: a recursive loop that keeps allocating -/

/-- `f n = f n`: the body applies index 1, the function itself, to index 0. -/
def loopBody : T := .app (.var 1) (.var 0)
def loopProgram : T := .app (.fix loopBody) (int 0)
def loopStart : Graph.State := Graph.load (loopProgram, .unit)

def loopCode : Code := Graph.compile loopBody
def loopCell : Graph.Cell := .pair (.ref 1) (.literal (.integer 0))

/-- The cyclic function at addresses 0 and 1 and a body environment couple. -/
def LoopHeap (heap : Graph.Heap) (environment : Nat) : Prop :=
  heap[0]? = some (.pair .unit (.ref 1)) ∧ heap[1]? = some (.closure loopCode (.ref 0)) ∧
    heap[environment]? = some (.pair (.ref 0) (.literal (.integer 0)))

/-- The thirteen configurations of one iteration of the loop body. -/
def loopState (heap : Graph.Heap) (environment : Nat) : Nat → Graph.State
  | 0 => ⟨.ref environment, loopCode, [], heap⟩
  | 1 => ⟨.ref environment, loopCode.drop 1, [.ref environment], heap⟩
  | 2 => ⟨.ref 0, loopCode.drop 2, [.ref environment], heap⟩
  | 3 => ⟨.ref 1, loopCode.drop 3, [.ref environment], heap⟩
  | 4 => ⟨.ref environment, loopCode.drop 4, [.ref 1], heap⟩
  | 5 => ⟨.literal (.integer 0), loopCode.drop 5, [.ref 1], heap⟩
  | 6 => ⟨.ref heap.length, loopCode.drop 6, [], heap ++ [loopCell]⟩
  | 7 => ⟨.ref heap.length, loopCode.drop 7, [.ref heap.length], heap ++ [loopCell]⟩
  | 8 => ⟨.ref 1, loopCode.drop 8, [.ref heap.length], heap ++ [loopCell]⟩
  | 9 => ⟨.ref 1, loopCode.drop 9, [.ref heap.length], heap ++ [loopCell]⟩
  | 10 => ⟨.ref heap.length, loopCode.drop 10, [.ref 1], heap ++ [loopCell]⟩
  | 11 => ⟨.literal (.integer 0), loopCode.drop 11, [.ref 1], heap ++ [loopCell]⟩
  | _ => ⟨.ref (heap ++ [loopCell]).length, [.app], [], heap ++ [loopCell] ++ [loopCell]⟩

def LoopRegion (state : Graph.State) : Prop :=
  ∃ heap environment phase, LoopHeap heap environment ∧ phase < 13 ∧ state = loopState heap environment phase

theorem loop_region_closed (state : Graph.State) (inside : LoopRegion state) :
    ∃ next, Graph.answerCore.toMachineCore.StepRel state next ∧ LoopRegion next := by
  obtain ⟨heap, environment, phase, ⟨cell₀, cell₁, cellEnvironment⟩, bounded, rfl⟩ := inside
  have extended : heap <+: heap ++ [loopCell] := List.prefix_append _ _
  have extended₂ : heap ++ [loopCell] <+: heap ++ [loopCell] ++ [loopCell] := List.prefix_append _ _
  have advance : ∀ next, Graph.Transition (loopState heap environment phase) next →
      LoopRegion next → ∃ next, Graph.answerCore.toMachineCore.StepRel (loopState heap environment phase) next ∧
        LoopRegion next :=
    fun next transition inside => ⟨next, Graph.step_complete transition, inside⟩
  have same (next : Nat) (smaller : next < 13) :
      LoopRegion (loopState heap environment next) :=
    ⟨heap, environment, next, ⟨cell₀, cell₁, cellEnvironment⟩, smaller, rfl⟩
  interval_cases phase
  · exact advance _ (.push _ _ _ _) (same 1 (by omega))
  · exact advance _ (.first _ _ _ cellEnvironment) (same 2 (by omega))
  · exact advance _ (.second _ _ _ cell₀) (same 3 (by omega))
  · exact advance _ (.swap _ _ _ _ _) (same 4 (by omega))
  · exact advance _ (.second _ _ _ cellEnvironment) (same 5 (by omega))
  · exact advance _ (.cons _ _ _ _ _) (same 6 (by omega))
  · exact advance _ (.push _ _ _ _) (same 7 (by omega))
  · exact advance _ (.first _ _ _ Graph.allocated) (same 8 (by omega))
  · refine advance _ (.skip _ _ _ _ ?_) (same 9 (by omega))
    rintro ⟨address, body, captured, same', found⟩
    cases same'
    rw [Graph.lookup_prefix extended cell₁] at found
    cases found
  · exact advance _ (.swap _ _ _ _ _) (same 10 (by omega))
  · exact advance _ (.second _ _ _ Graph.allocated) (same 11 (by omega))
  · exact advance _ (.cons _ _ _ _ _) (same 12 (by omega))
  · have extended₃ : heap ++ [loopCell] ++ [loopCell] <+:
        heap ++ [loopCell] ++ [loopCell] ++ [Graph.Cell.pair (.ref 0) (.literal (.integer 0))] :=
      List.prefix_append _ _
    refine advance _ (.app _ _ _ Graph.allocated (Graph.lookup_prefix extended₂ (Graph.lookup_prefix extended cell₁)))
      ⟨heap ++ [loopCell] ++ [loopCell] ++ [Graph.Cell.pair (.ref 0) (.literal (.integer 0))],
        (heap ++ [loopCell] ++ [loopCell]).length, 0, ⟨?_, ?_, Graph.allocated⟩, by omega, ?_⟩
    · exact Graph.lookup_prefix extended₃ (Graph.lookup_prefix extended₂ (Graph.lookup_prefix extended cell₀))
    · exact Graph.lookup_prefix extended₃ (Graph.lookup_prefix extended₂ (Graph.lookup_prefix extended cell₁))
    · rfl

/-- From any loop entry, every finite budget is spent on computational occurrences. -/
theorem loop_iteration_diverges (budget : Nat) {heap : Graph.Heap} {environment : Nat}
    (entry : LoopHeap heap environment) :
    ∃ events residual, Graph.machine.run budget (loopState heap environment 0) = (events, .exhausted residual) ∧
      events.length = budget ∧ LoopRegion residual := by
  obtain ⟨events, residual, ran, _, count, remains⟩ :=
    perpetual_computation Graph.answerCore LoopRegion loop_region_closed budget _
      ⟨heap, environment, 0, entry, by omega, rfl⟩
  exact ⟨events, residual, ran, count, remains⟩

def loopEntryHeap : Graph.Heap :=
  [.pair .unit (.ref 1), .closure loopCode (.ref 0), loopCell, loopCell, .pair (.ref 0) (.literal (.integer 0))]

theorem loop_prefix_reaches_the_entry :
    exhaustedState (Graph.machine.run 17 loopStart).2 = some (loopState loopEntryHeap 4 0) := by decide +kernel

theorem loop_short_budgets_are_exhausted :
    ∀ budget < 17, (exhaustedState (Graph.machine.run budget loopStart).2).isSome = true := by decide +kernel

theorem exhaustedState_some {outcome : Outcome Graph.State Graph.Answer Empty} {residual : Graph.State}
    (found : exhaustedState outcome = some residual) : outcome = .exhausted residual := by
  cases outcome <;> simp_all [exhaustedState]

/-- The loaded loop is exhausted at every budget: it diverges, distinct from a stuck run. -/
theorem loaded_loop_diverges (budget : Nat) :
    ∃ residual, (Graph.machine.run budget loopStart).2 = .exhausted residual := by
  by_cases enough : 17 ≤ budget
  · obtain ⟨second, rfl⟩ := Nat.exists_eq_add_of_le enough
    obtain ⟨events, residual, ran, _, _⟩ :=
      loop_iteration_diverges second (heap := loopEntryHeap) (environment := 4) ⟨rfl, rfl, rfl⟩
    have paused : Graph.machine.run 17 loopStart =
        ((Graph.machine.run 17 loopStart).1, .exhausted (loopState loopEntryHeap 4 0)) :=
      Prod.ext rfl (exhaustedState_some loop_prefix_reaches_the_entry)
    have resumed := Graph.machine.established_and_pending 17 second loopStart _ _ paused
    exact ⟨residual, by rw [resumed, ran]⟩
  · obtain ⟨residual, found⟩ :=
      Option.isSome_iff_exists.mp (loop_short_budgets_are_exhausted budget (by omega))
    exact ⟨residual, exhaustedState_some found⟩

theorem loop_has_no_source_value (value : Graph.Value) : ¬ Graph.Evaluation loopProgram .unit value := by
  intro evaluated
  obtain ⟨budget, events, completed, ran⟩ := (Graph.evaluates_iff_finished loopProgram .unit).mp ⟨value, evaluated⟩
  obtain ⟨residual, exhausted⟩ := loaded_loop_diverges budget
  change (Graph.machine.run budget loopStart).2 = _ at exhausted
  unfold loopStart at exhausted
  rw [ran] at exhausted
  cases exhausted

/-! ### Negative controls -/

theorem wind_without_a_couple_is_stuck :
    Graph.step ⟨.unit, [.wind], [.unit], []⟩ = none ∧
      Graph.step ⟨.unit, [.wind], [.ref 0], [.closure [] .unit]⟩ = none ∧
      Graph.step ⟨.unit, [.wind], [], []⟩ = none := ⟨rfl, rfl, rfl⟩

theorem wind_is_legal_exactly_over_a_couple :
    Graph.InstructionLegal ⟨.unit, [.wind], [.ref 0], [.pair .unit .unit]⟩ .wind ∧
      ¬ Graph.InstructionLegal ⟨.unit, [.wind], [.ref 0], [.closure [] .unit]⟩ .wind := by
  constructor
  · exact (Graph.wind_legal_iff _).mpr ⟨[], 0, [], .unit, .unit, rfl, rfl, rfl⟩
  · rw [Graph.wind_legal_iff]
    rintro ⟨rest, address, stack, left, right, -, stackSame, cell⟩
    simp only [List.cons.injEq, Graph.Word.ref.injEq] at stackSame
    obtain ⟨rfl, -⟩ := stackSame
    cases cell

theorem unfreeze_is_a_skip_on_other_terms :
    Graph.step ⟨.literal (.integer 5), [.unfreeze], [], []⟩ = some ⟨.literal (.integer 5), [], [], []⟩ ∧
      Graph.step ⟨.ref 0, [.unfreeze], [], [.pair .unit .unit]⟩ = some ⟨.ref 0, [], [], [.pair .unit .unit]⟩ :=
  ⟨rfl, rfl⟩

def badPrimitive : T := .primitive .plus (.pair (.literal (.boolean true)) (int 1))

theorem strict_primitive_on_non_integers_is_stuck :
    Graph.step ⟨.ref 0, [.operation .plus], [], [.pair (.literal (.boolean true)) (.literal (.integer 1))]⟩ =
        none ∧
      stuckCode (Graph.machine.run 14 (Graph.load (badPrimitive, .unit))).2 = some [.operation .plus] := by
  exact ⟨rfl, by decide +kernel⟩

theorem strict_primitive_on_non_integers_has_no_value (value : Graph.Value) :
    ¬ Graph.Evaluation badPrimitive .unit value := by
  intro evaluated
  cases evaluated with
  | primitive argumentEval forced leftForced _ =>
      cases argumentEval with
      | pair leftEval _ =>
          cases leftEval
          cases forced with
          | value _ _ => cases leftForced

/-- The condition is forced (Section 5's rule applied to `branch`); a laze that
yields 7 is still not a Boolean. -/
def badCondition : T := .conditional (.freeze (int 7)) (int 1) (int 2)

theorem non_boolean_condition_is_stuck_after_forcing :
    stuckCode (Graph.machine.run 6 (Graph.load (badCondition, .unit))).2 =
        some [.branch [.quote (.integer 1)] [.quote (.integer 2)]] ∧
      forcings (Graph.machine.run 6 (Graph.load (badCondition, .unit))).1 = 1 := by decide +kernel

theorem non_boolean_condition_has_no_value (value : Graph.Value) :
    ¬ Graph.Evaluation badCondition .unit value := by
  intro evaluated
  cases evaluated with
  | conditional conditionEval forced _ =>
      cases conditionEval
      cases forced with
      | laze bodyEval again =>
          cases bodyEval
          cases again

theorem raw_code_is_refused_by_the_loader :
    Graph.loadImage ([.wind], .unit) = none ∧ Graph.loadImage ([.unfreeze], .unit) = none ∧
      Graph.loadImage ([.push, .quote .unit, .cons, .push, .cur [.second], .swap, .wind], .unit) = none := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [Graph.loadImage_refused_iff] <;> simp [Graph.decode]

theorem compiled_recursion_is_admitted :
    Graph.loadImage (Graph.compile (.fix factorialBody), .unit) =
      some (Graph.core.load (.fix factorialBody, .unit)) :=
  Graph.loadImage_compileImage (.fix factorialBody, .unit)

theorem tree_machine_is_stuck_at_value_graph_instructions (profile : Profile) :
    step profile ⟨.unit, [.wind], [.pair .unit .unit]⟩ = none ∧
      step profile ⟨.unit, [.freeze [.second]], []⟩ = none ∧
      step profile ⟨.unit, [.unfreeze], []⟩ = none ∧
      step profile ⟨.pair (.literal (.integer 1)) (.literal (.integer 2)), [.operation .plus], []⟩ = none := by
  cases profile <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem value_graph_code_is_not_tree_code : ¬ Graph.TreeCode (Graph.compile (.fix factorialBody)) := by
  intro tree
  have last := tree.tail.tail.tail.tail.tail.head
  cases last

/-! ### The tree source inside the graph source -/

theorem neutral_tree_rule_has_no_graph_counterpart :
    CategoricalAbstractMachine.Evaluation (identity.enable.first) .unit (.first identityValue.enable) ∧
      ∀ value, ¬ Graph.Evaluation (Graph.embed identity.enable.first) .unit value := by
  constructor
  · exact .first (.lam _ _) (.neutral _ trivial)
  · intro value evaluated
    cases evaluated with
    | first termEval forced =>
        cases termEval
        cases forced

theorem embedded_identity_application_is_active :
    Graph.TreeStrict identityApplication.enable .unit identityValue.enable ∧
      Graph.Evaluation (Graph.embed identityApplication.enable) .unit (.closure (.var 0) .unit) := by
  have derivation : Graph.TreeStrict identityApplication.enable .unit identityValue.enable :=
    .app (.lam _ _) (.lam _ _) (.varZero _ _)
  obtain ⟨value, found, evaluated⟩ := derivation.graph (environment' := .unit) rfl
  simp only [Graph.embedValue, identityValue, SourceValue.enable, Graph.embed, Source.enable,
    Option.map_some, Option.some.injEq] at found
  subst found
  exact ⟨derivation, evaluated⟩

/-! ### Finite observation -/

def unrolledHeap : Graph.Heap :=
  cycleHeap ++ [.pair .unit (.ref 1), .closure (Graph.compile factorialBody) (.ref 2)]

/-- The cyclic closure and a separately allocated one-step unrolling agree at every depth. -/
theorem cycle_equals_its_unrolling_at_every_depth (depth : Nat) :
    (Graph.reader unrolledHeap).observe depth (.ref 1) = (Graph.reader unrolledHeap).observe depth (.ref 3) := by
  have recursiveRep : Graph.Represents unrolledHeap (.ref 1) (.recursive factorialBody .unit) :=
    cycle_represents_the_recursive_value.mono (List.prefix_append _ _)
  have unrolledRep : Graph.Represents unrolledHeap (.ref 3)
      (.closure factorialBody (.pair .unit (.recursive factorialBody .unit))) :=
    .closure rfl (.pair rfl .unit recursiveRep)
  rw [recursiveRep.observe, unrolledRep.observe, Graph.unfold_recursive]

/-- Recursive closures over different bodies already differ at depth one. -/
theorem different_bodies_differ_at_depth_one :
    Graph.unfold 1 (.recursive factorialBody .unit) ≠ Graph.unfold 1 (.recursive streamBody .unit) := by
  intro same
  have labels := (RationalTermGraph.Observation.node.inj same).1
  have bodies := Graph.compile_injective (Graph.Label.closure.inj labels)
  exact absurd bodies (by decide)

/-! ### Refinement on tree code -/

/-- The tree compiler's identity application runs on the value graph in the same
seven instructions as on the tree machine, and its answer unfolds to the tree answer. -/
theorem tree_code_runs_in_lock_step :
    (Graph.machine.run 8 ⟨.unit, compile identityApplication, [], []⟩).1.length = 7 ∧
      ((machine .strict).run 8 identityStart).1.length = 7 ∧
      finishedAnswer (Graph.machine.run 8 ⟨.unit, compile identityApplication, [], []⟩).2 =
        some ⟨.ref 1, [.closure [.second] .unit, .closure [.second] .unit,
          .pair (.ref 0) (.ref 1), .pair .unit (.ref 1)]⟩ := by decide +kernel

theorem lock_step_answer_unfolds :
    Graph.Unfolds [.closure [.second] .unit, .closure [.second] .unit, .pair (.ref 0) (.ref 1),
      .pair .unit (.ref 1)] (.ref 1) (encodeValue identityValue) :=
  .closure rfl (.cons (.second) .nil) .unit

end GraphControls


namespace ExtendedScopedControls

open Mettapedia.OSLF.Binding

def seven : Lambda.Closed true := Lambda.literal rfl (.integer 7)
def truth : Lambda.Closed true := Lambda.literal rfl (.boolean true)
def unselectedBad : Lambda.Closed true := Lambda.conditional rfl seven seven seven

def selectedLiteral : Lambda.Closed true := Lambda.conditional rfl truth seven unselectedBad

theorem selected_branch_only : Lambda.CBV selectedLiteral seven :=
  .conditional (.literal rfl (.boolean true)) (.literal rfl (.integer 7))

theorem selected_branch_proposition_3_2 :
    ∃ value, CombinatorySteps (.question (Lambda.erase selectedLiteral) .unit) (.answer value) ∧
      Lambda.Readback value seven :=
  (Lambda.proposition_3_2 selectedLiteral seven).mp
    ⟨selected_branch_only.steps, selected_branch_only.normal⟩

theorem extended_source_reaches_native_readback :
    ∃ native, CategoricalAbstractMachine.Steps .neutral
      ⟨.unit, compileSource (Lambda.erase selectedLiteral), []⟩ ⟨native, [], []⟩ ∧
        Lambda.nativeReadback native = some (.literal rfl (.integer 7)) :=
  (Lambda.closed_iff_nativeReadback selectedLiteral seven).mp
    ⟨selected_branch_only.steps, selected_branch_only.normal⟩

def capturedConditional : Lambda.Scoped [()] true :=
  Lambda.conditional rfl (Lambda.literal rfl (.boolean false))
    (Lambda.literal rfl (.integer 99)) (.var .zero)

theorem conditional_captured_scope_is_retained :
    Lambda.erase (bind (Lambda.substitution [seven]) capturedConditional) =
      .conditional rfl (.literal rfl (.boolean false))
        (.literal rfl (.integer 99)) (.literal rfl (.integer 7)) := rfl

theorem non_boolean_condition_has_no_completed_evaluation (result : Lambda.Closed true) :
    ¬ Lambda.CBV unselectedBad result := by
  intro evaluation
  cases evaluation with
  | conditional conditionEval _ => cases conditionEval

theorem non_boolean_condition_is_not_normal : ¬ Lambda.Normal unselectedBad := by
  intro normal
  cases normal

theorem constants_remain_closed_under_an_extra_binder :
    Lambda.erase (inst (Lambda.lam (Lambda.literal rfl (.integer 7))) truth) =
      .lam (.literal rfl (.integer 7)) := rfl

theorem extended_reader_refuses_free_variable :
    Lambda.represent [] (Source.conditional rfl (.literal rfl (.boolean true))
      (.literal rfl (.integer 7)) (.var 0)) = none := rfl

end ExtendedScopedControls


namespace MemoizingControls

open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Machines.BranchLocalNeed.NeedReference

/-- The delayed producer computes 6 * 7 and returns a pair. -/
def producer : Graph.Term :=
  .pair (.primitive .times (.pair (.literal (.integer 6)) (.literal (.integer 7)))) (.literal .unit)

def twoUses : Graph.Term :=
  .lam (.primitive .plus (.pair (.first (.var 0)) (.first (.var 0))))

def shared : Graph.Term := .app twoUses (.freeze producer)
def nested : Graph.Term := .app twoUses (.freeze (.freeze producer))
def independent : Graph.Term := .pair (.first (.freeze producer)) (.first (.freeze producer))

/-- Inspect the retained answer without comparing finite-map functions. -/
def summary (budget : Nat) (term : Graph.Term) :
    Option (Graph.Word × Nat × Nat × List (Nat × Graph.Word)) :=
  match (Graph.Need.machine.run budget (Graph.Need.load term)).2 with
  | .finished final => some (final.graph.register, final.nextOwner,
      final.store.spine.length,
      final.store.spine.filterMap fun update => match update with
        | .cache cell (.value word) => some (cell.slot, word)
        | _ => none)
  | _ => none

theorem two_uses_have_one_producer :
    summary 80 shared = some (.literal (.integer 84), 1, 3, [(1, .ref 7)]) := by decide +kernel

/-- Nested forcing keeps two update frames; both completed cells share the
same forced graph word. The second outer use starts neither producer again. -/
theorem nested_forcing_updates_both_cells :
    summary 80 nested = some (.literal (.integer 84), 2, 6, [(1, .ref 8), (5, .ref 8)]) := by decide +kernel

theorem equal_bodies_do_not_merge_independent_allocations :
    summary 80 independent = some (.ref 8, 2, 6, [(4, .ref 7), (0, .ref 3)]) := by decide +kernel

theorem shared_memoizing_instruction_cost :
    (Graph.Need.machine.run 80 (Graph.Need.load shared)).1.length = 51 ∧
      (Graph.machine.run 80 (Graph.load (shared, .unit))).1.length = 68 := by decide +kernel

theorem nested_memoizing_instruction_cost :
    (Graph.Need.machine.run 80 (Graph.Need.load nested)).1.length = 55 ∧
      (Graph.machine.run 80 (Graph.load (nested, .unit))).1.length = 72 := by decide +kernel

/-- Resumption uses the complete retained state, including active producers;
the equality is the general runner law, not a separate checkpoint evaluator. -/
theorem nested_resume_preserves_the_whole_execution :
    Graph.Need.machine.run (25 + 55) (Graph.Need.load nested) =
      Graph.Need.machine.continueRun 55 (Graph.Need.machine.run 25 (Graph.Need.load nested)) :=
  Graph.Need.machine.run_add 25 55 _

def updatesWhilePaused : Option Nat :=
  match (Graph.Need.machine.run 25 (Graph.Need.load nested)).2 with
  | .exhausted residual => some residual.updates.length
  | _ => none

/-- A finite pause during nested evaluation is not a completed empty answer. -/
theorem nested_pause_retains_both_updates : updatesWhilePaused = some 2 := by decide +kernel

def failingProducer : Graph.Term := .first (.freeze (.first (.literal (.integer 3))))

theorem failed_producer_is_not_published : summary 30 failingProducer = none := by decide +kernel

def failedCache : Option (Nat × Nat) :=
  match (Graph.Need.machine.run 30 (Graph.Need.load failingProducer)).2 with
  | .stuck residual => some (residual.updates.length,
      residual.store.spine.countP fun entry => match entry with
        | .cache _ (.value _) => true
        | _ => false)
  | _ => none

theorem blocked_producer_retains_ownership_and_no_value : failedCache = some (1, 0) := by decide +kernel

/-- The producer has the same independent arithmetic meaning in the historical
call-by-name source semantics. -/
theorem producer_source (environment : Graph.Value) : Graph.Evaluation producer environment
    (.pair (.literal (.integer 42)) (.literal .unit)) :=
  .pair (.primitive (.pair (.literal _ _) (.literal _ _))
    (.value _ trivial) (.value _ trivial) (.value _ trivial)) (.literal _ _)

theorem shared_cbn_source : Graph.Evaluation shared .unit (.literal (.integer 84)) := by
  have one : Graph.Evaluation (.first (.var 0)) (.pair .unit (.laze producer .unit))
      (.literal (.integer 42)) :=
    .first (.varZero _ _) (.laze (producer_source .unit) (.value _ trivial))
  exact .app (.lam _ _) (.freeze _ _) (.value _ trivial)
    (.closure (.primitive (.pair one one) (.value _ trivial) (.value _ trivial) (.value _ trivial)))

theorem nested_cbn_source : Graph.Evaluation nested .unit (.literal (.integer 84)) := by
  have one : Graph.Evaluation (.first (.var 0)) (.pair .unit (.laze (.freeze producer) .unit))
      (.literal (.integer 42)) :=
    .first (.varZero _ _) (.laze (.freeze _ _)
      (.laze (producer_source .unit) (.value _ trivial)))
  exact .app (.lam _ _) (.freeze _ _) (.value _ trivial)
    (.closure (.primitive (.pair one one) (.value _ trivial) (.value _ trivial) (.value _ trivial)))

private theorem source_of_summary {budget : Nat} {term : Graph.Term} {root : Graph.Word}
    {owners entries : Nat} {commits : List (Nat × Graph.Word)}
    (found : summary budget term = some (root, owners, entries, commits)) :
    ∃ world, Graph.Need.Evaluation term .unit Graph.Need.World.empty root world := by
  cases outcome : (Graph.Need.machine.run budget (Graph.Need.load term)).2 with
  | finished final =>
      simp only [summary, outcome, Option.some.injEq, Prod.mk.injEq] at found
      have ran : Graph.Need.machine.run budget (Graph.Need.load term) =
          ((Graph.Need.machine.run budget (Graph.Need.load term)).1, .finished final) :=
        Prod.ext rfl outcome
      obtain ⟨value, world, evaluated, same⟩ := Graph.Need.run_source_sound ran
      have value_eq : value = root := (congrArg (fun state => state.graph.register) same).symm.trans found.1
      subst value
      exact ⟨world, evaluated⟩
  | faulted | suspended _ _ | stuck _ | exhausted _ => simp [summary, outcome] at found

/-- These source judgments follow from the full reverse theorem, including
the second cached demand, rather than from a special program evaluator. -/
theorem shared_has_need_source_evaluation :
    ∃ world, Graph.Need.Evaluation shared .unit Graph.Need.World.empty (.literal (.integer 84)) world :=
  source_of_summary two_uses_have_one_producer

theorem nested_has_need_source_evaluation :
    ∃ world, Graph.Need.Evaluation nested .unit Graph.Need.World.empty (.literal (.integer 84)) world :=
  source_of_summary nested_forcing_updates_both_cells

theorem memoizing_recursion_preserves_factorial :
    summary 204 GraphControls.factorialProgram = some (.literal (.integer 6), 0, 0, []) := by decide +kernel

theorem recursive_need_source_evaluation :
    ∃ world, Graph.Need.Evaluation GraphControls.factorialProgram .unit Graph.Need.World.empty
      (.literal (.integer 6)) world := source_of_summary memoizing_recursion_preserves_factorial

/-- Fork the same actual suspended checkpoint into two retained worlds. The
left finishes; one step on the right starts its own producer. The original
checkpoint remains suspended throughout. Cell numbers are arena-local. -/
def forkIsolation : Option
    (Cache Graph.Word Empty × Cache Graph.Word Empty × Cache Graph.Word Empty × Nat × Nat) :=
  match (Graph.Need.machine.run 15 (Graph.Need.load shared)).2 with
  | .exhausted snapshot =>
      match (Graph.Need.machine.run 60 snapshot).2, (Graph.Need.machine.run 1 snapshot).2 with
      | .finished left, .exhausted right => do
          let original ← snapshot.store.lookup (Graph.Need.cellId 1)
          let leftCell ← left.store.lookup (Graph.Need.cellId 1)
          let rightCell ← right.store.lookup (Graph.Need.cellId 1)
          pure (original.cache, leftCell.cache, rightCell.cache, left.nextOwner, right.nextOwner)
      | _, _ => none
  | _ => none

theorem retained_snapshots_do_not_share_updates :
    forkIsolation = some (.suspended, .value (.ref 7), .evaluating 0, 1, 1) := by decide +kernel

/-- A completed value from another origin cannot satisfy this demand. -/
def wrongOrigin : Graph.Need.State :=
  ⟨⟨.ref 0, [.unfreeze], [], [.laze (Graph.compile (.literal (.integer 4))) .unit]⟩,
    Heap.empty.setKnownCache (Graph.Need.cellId 0)
      ⟨(Graph.compile (.literal (.integer 3)), .unit), .suspended⟩ (.value (.literal (.integer 99))), [], 0⟩

theorem wrong_origin_cache_is_not_delivered :
    Graph.Need.step wrongOrigin = none ∧ Graph.Need.completed wrongOrigin = none := by decide +kernel

/-- This is a raw blocked configuration, not a source value or a finished
failure. The generic `force_busy` law covers every active owner. -/
def busyDemand : Graph.Need.State :=
  ⟨⟨.ref 0, [.unfreeze], [], [.laze (Graph.compile producer) .unit]⟩,
    Heap.empty.setKnownCache (Graph.Need.cellId 0)
      ⟨(Graph.compile producer, .unit), .suspended⟩ (.evaluating 3), [], 4⟩

theorem active_demand_is_not_a_finished_answer :
    Graph.Need.step busyDemand = none ∧ Graph.Need.completed busyDemand = none := by decide +kernel

theorem arbitrary_empty_laze_code_is_not_source_admitted :
    ¬ Graph.Need.SourceHeap [.laze [] .unit] := by
  intro admitted
  obtain ⟨term, empty⟩ := admitted (.laze [] .unit) (by simp)
  exact Graph.compile_nonempty term empty.symm

end MemoizingControls

end Mettapedia.Machines.CategoricalAbstractMachineControls
