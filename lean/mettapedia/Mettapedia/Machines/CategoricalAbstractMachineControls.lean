import Mettapedia.Machines.CategoricalAbstractMachine

/-!
# Historical CAM controls

Independent source derivations meet actual instruction execution. Raw code
may stop without being compiled or without exposing a completed answer.
Neutral and strict projections remain different profiles. Captured
environments, instruction suffixes, stacks and resumed occurrences stay
explicit. A closed self-application cycle gives divergence for every finite
budget; no source termination assumption is used.
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
  simp [decodeCode, redundantRawCode, compile]

theorem redundant_raw_work_can_still_finish :
    ((machine .neutral).run 6 ⟨.unit, redundantRawCode, []⟩).2 =
      .finished (.closure [.second] .unit) := rfl

theorem stopped_raw_code_does_not_certify_source_body :
    decodeCode [.cur [.swap]] = none ∧ decodeValue (.closure [.swap] .unit) = none := by
  simp [decodeCode, decodeValue]

theorem observed_raw_closure_does_not_certify_source_body :
    ((machine .neutral).run 2 ⟨.unit, [.cur [.swap]], []⟩).2 = .finished (.closure [.swap] .unit) ∧
      decodeValue (.closure [.swap] .unit) = none := by
  exact ⟨rfl, by simp [decodeCode, decodeValue]⟩

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
        Lambda.nativeReadback (encodeValue identityValue) = some identity :=
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
    Lambda.nativeReadback (encodeValue (.closure (.var 1) (.pair .unit identityValue))) =
      some (.lam (.lam (.var 0))) := by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl

theorem reversed_capture_slot_is_refused :
    Lambda.nativeReadback (encodeValue (.closure (.lam (.var 3)) (.pair .unit identityValue))) = none := by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl

theorem binder_shadowing_is_distinct_from_capturing :
    Lambda.nativeReadback (encodeValue (.closure (.var 0) (.pair .unit identityValue))) = some identity ∧
    Lambda.nativeReadback (encodeValue (.closure (.var 1) (.pair .unit identityValue))) =
      some (.lam (.lam (.var 0))) ∧ identity ≠ .lam (.lam (.var 0)) :=
  ⟨by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl,
   by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl, by decide⟩

theorem captured_environment_order_is_retained :
    Lambda.nativeReadback (encodeValue (.closure (.var 2)
      (.pair (.pair .unit identityValue) (.pair identityValue identityValue)))) = some (.lam identity) ∧
    Lambda.nativeReadback (encodeValue (.closure (.var 1)
      (.pair (.pair .unit identityValue) (.pair identityValue identityValue)))) =
        some (.lam (.pair identity identity)) :=
  ⟨by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl,
   by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl⟩

theorem environment_unit_is_not_a_source_value :
    Lambda.realize .unit = none ∧ Lambda.realizeEnvironment .unit = some [] := ⟨rfl, rfl⟩

theorem unscoped_code_is_not_granted_closed_readback :
    decodeValue (encodeValue (.closure (.var 1) .unit)) = some (.closure (.var 1) .unit) ∧
      Lambda.nativeReadback (encodeValue (.closure (.var 1) .unit)) = none :=
  ⟨decode_encodeValue _, by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl⟩

theorem unscoped_closure_may_finish_without_source_validity :
    ((machine .neutral).run 2 ((core .neutral).load (.lam (.var 1), .unit))).2 =
      .finished (encodeValue (.closure (.var 1) .unit)) ∧
        Lambda.nativeReadback (encodeValue (.closure (.var 1) .unit)) = none :=
  ⟨rfl, by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl⟩

theorem noncanonical_closure_is_not_granted_source_readback :
    Lambda.nativeReadback (.closure [.swap] .unit) = none := by
  simp [Lambda.nativeReadback, decodeValue, decodeCode]

theorem active_projection_cannot_be_supplied_as_a_neutral_value :
    Lambda.realize (.first (.pair identityValue identityValue)) = none := rfl

theorem active_application_cannot_be_supplied_as_a_neutral_value :
    Lambda.realize (.app (.pair identityValue identityValue)) = none := rfl

theorem malformed_application_payload_is_refused : Lambda.realize (.app identityValue) = none := rfl

def projectedIdentity : Lambda.Closed := Lambda.first scopedIdentity
def neutralApplication : Lambda.Closed := Lambda.app (Lambda.pair scopedIdentity scopedIdentity) scopedIdentity

theorem inactive_projection_is_an_exact_weak_value :
    Lambda.CBV projectedIdentity projectedIdentity ∧
      Lambda.nativeReadback (encodeValue (.first identityValue)) = some (.first identity) :=
  ⟨.first (.lam _) (.neutral _ (by simp [Lambda.NotPair])), by simp only [Lambda.nativeReadback, decode_encodeValue]; rfl⟩

theorem inactive_application_is_an_exact_weak_value : Lambda.Normal neutralApplication :=
  .app (.pair (.lam _) (.lam _)) (.lam _) (by simp [Lambda.NotLam, scopedIdentity])

theorem closed_neutral_projection_profiles_remain_distinct :
    ((machine .strict).run 3 ((core .strict).load (.first identity, .unit))).2 =
      .stuck ⟨encodeValue identityValue, [.first], []⟩ ∧
    ((machine .neutral).run 3 ((core .neutral).load (.first identity, .unit))).2 =
      .finished (encodeValue (.first identityValue)) := ⟨rfl, rfl⟩

theorem weak_lambda_does_not_reduce_its_body :
    ¬ Lambda.Step (Lambda.lam (Lambda.app (Lambda.lam (.var .zero)) (.var .zero)))
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
      Lambda.nativeReadback (.literal (.boolean true)) = none := by
  exact ⟨by simp [decodeValue], rfl⟩

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
  · simpa only [compileImage, core, compile, List.replicate_zero, List.nil_append, encodeValue] using
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

end Mettapedia.Machines.CategoricalAbstractMachineControls
