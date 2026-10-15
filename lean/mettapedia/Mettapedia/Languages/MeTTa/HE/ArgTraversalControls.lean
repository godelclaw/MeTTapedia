import Mettapedia.Languages.MeTTa.HE.ArgTraversal

/-!
# Argument traversal controls

These controls check branch correlation, independent arguments, binding
threading and ordered resumption of the argument-product traversal. The raw
argument example uses an explicit argument policy, rather than claiming an
implementation correspondence for the complete HE type dispatcher.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.ArgTraversal.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def pick : Atom := .symbol "pick"
def valueType : Atom := .symbol "Value"
def rawType : Atom := .symbol "Atom"

def evaluate : ArgumentEvaluator
  | argument, .symbol "Atom", env => [(argument, env)]
  | .symbol "pick", _, env => [(a, env), (b, env)]
  | .symbol "duplicates", _, env => [(a, env), (a, env), (b, env)]
  | .symbol "bind-pick", _, env =>
      [(a, env.assign "selected" a), (b, env.assign "selected" b)]
  | .symbol "read-selected", _, env =>
      match env.lookup "selected" with
      | some value => [(value, env)]
      | none => []
  | argument, _, env => [(argument, env)]

def oneChoice : ArgSourceFrame := ⟨[], [(pick, valueType)], Bindings.empty⟩
def twoChoices : ArgSourceFrame :=
  ⟨[], [(pick, valueType), (pick, valueType)], Bindings.empty⟩

def savedAfterFirst : Configuration :=
  [.body ⟨[(b, Bindings.empty)], ⟨[], [], Bindings.empty⟩⟩]

def results (source : ArgSourceFrame) : ResultList :=
  ((machine evaluate).run (work evaluate [.source source] + 1) [.source source]).1

@[simp]
theorem results_eq_reference (source : ArgSourceFrame) :
    results source = ArgEvalFrame.runFromSource evaluate source :=
  run_initial_eq_reference evaluate source

theorem one_choice_keeps_order :
    results oneChoice =
      [(.expression [a], Bindings.empty), (.expression [b], Bindings.empty)] := by
  simp [oneChoice, ArgEvalFrame.runFromSource, evaluate, pick, valueType]

/-- Duplication consumes an already selected value. It cannot select again. -/
def useTwice (result : ResultPair) : Atom :=
  match result.1 with
  | .expression [value] => .expression [.symbol "Same", value, value]
  | other => other

theorem chosen_once_reused_twice :
    (results oneChoice).map useTwice =
      [.expression [.symbol "Same", a, a], .expression [.symbol "Same", b, b]] := by
  rw [one_choice_keeps_order]
  rfl

theorem independently_chosen_arguments :
    (results twoChoices).map Prod.fst =
      [.expression [a, a], .expression [a, b],
        .expression [b, a], .expression [b, b]] := by
  simp [twoChoices, ArgEvalFrame.runFromSource, evaluate, pick, valueType]

theorem correlated_and_independent_observations_differ :
    (results oneChoice).length ≠ (results twoChoices).length := by
  have independent := congrArg List.length independently_chosen_arguments
  simp only [List.length_map, List.length_cons, List.length_nil] at independent
  rw [one_choice_keeps_order, independent]
  decide

theorem prefix_pause_keeps_siblings :
    (machine evaluate).run 3 [.source oneChoice] =
      ([(.expression [a], Bindings.empty)], .exhausted savedAfterFirst) := rfl

theorem resumed_suffix_does_not_repeat_first :
    ((machine evaluate).run 4 savedAfterFirst).1 =
      [(.expression [b], Bindings.empty)] := rfl

theorem resumed_prefix_equals_uninterrupted :
    (machine evaluate).run 7 [.source oneChoice] =
      ([(.expression [a], Bindings.empty)] ++
          ((machine evaluate).run 4 savedAfterFirst).1,
        ((machine evaluate).run 4 savedAfterFirst).2) :=
  resume_after_prefix evaluate 3 4 [.source oneChoice] savedAfterFirst
    [(.expression [a], Bindings.empty)] prefix_pause_keeps_siblings

theorem restarting_is_not_resuming :
    ((machine evaluate).run 4 savedAfterFirst).1 ≠
      ((machine evaluate).run 4 [.source oneChoice]).1 := by decide

theorem repeated_equal_values_remain_occurrences :
    (results ⟨[], [(.symbol "duplicates", valueType)], Bindings.empty⟩).map Prod.fst =
      [.expression [a], .expression [a], .expression [b]] := by
  simp [ArgEvalFrame.runFromSource, evaluate, valueType]

theorem later_argument_uses_selected_bindings :
    results ⟨[], [(.symbol "bind-pick", valueType),
        (.symbol "read-selected", valueType)], Bindings.empty⟩ =
      [(.expression [a, a], Bindings.empty.assign "selected" a),
        (.expression [b, b], Bindings.empty.assign "selected" b)] := by
  simp [ArgEvalFrame.runFromSource, evaluate, valueType, Bindings.assign,
    Bindings.empty, Bindings.lookup, Bindings.isBound]

theorem raw_argument_policy_holds_the_source :
    (results ⟨[], [(pick, rawType)], Bindings.empty⟩).map Prod.fst =
      [.expression [pick]] := by
  simp [ArgEvalFrame.runFromSource, evaluate, rawType]

theorem wrong_raw_policy_changes_answers :
    results ⟨[], [(pick, rawType)], Bindings.empty⟩ ≠ results oneChoice := by
  rw [one_choice_keeps_order]
  simp [ArgEvalFrame.runFromSource, evaluate, rawType]

/-- Exhausting one argument's candidates never advances to another argument
without the selected value which starts that child traversal. -/
theorem exhausted_candidate_cursor_does_not_enter_next_argument :
    ArgEvalFrame.resume? evaluate
      (.body ⟨[], ⟨[], [(pick, valueType)], Bindings.empty⟩⟩) = none := rfl

theorem derived_work_bounds :
    work evaluate [.source oneChoice] = 6 ∧
      work evaluate [.source twoChoices] = 16 := by
  constructor <;>
    simp [work, frameWork, sourceWork, oneChoice, twoChoices, evaluate, pick, valueType]

end Mettapedia.Languages.MeTTa.HE.ArgTraversal.Controls
