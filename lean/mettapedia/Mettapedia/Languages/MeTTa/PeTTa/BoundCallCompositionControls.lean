import Mettapedia.Languages.MeTTa.PeTTa.CoreExecution
import Mettapedia.Languages.MeTTa.PeTTa.BoundCallControls

/-! Positive and negative boundaries for conservative captured-call transport.
The authored program is the pinned fixture, except for the explicitly separate
control-word example. These controls do not equate distinct dialects. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BoundCallCompositionControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval (Configuration finished)

def bindings : Subst := [("f", .symbol "bound-call:increment")]

/-- The actual authored function shares its argument entry and complete
observations with the ordinary literal spelling, at every positive budget. -/
theorem authored_same_budget (source : Configuration) (fuel : Nat) :
    BoundCalls.run BoundCallControls.program (fuel + 1)
      { source with control := .evaluate bindings BoundCallControls.call } =
    BoundCalls.run BoundCallControls.program (fuel + 1)
      { source with control := .evaluate bindings (.expression [.symbol "bound-call:increment", BoundCallControls.seven]) } :=
  BoundCalls.captured_literal_run BoundCallControls.program source bindings "f" "bound-call:increment"
    [BoundCallControls.seven] fuel rfl (by decide) rfl

/-- There is no conservative old-path certificate through this actual
captured-call entry, regardless of the proposed returned answer. -/
theorem captured_entry_not_conservative (state after : Effects.State) (answers : List Atom) :
    ¬ BoundCalls.CorePath BoundCallControls.program
      { state, control := .evaluate bindings BoundCallControls.call }
      (finished after answers [] []) := by
  intro certificate
  have different : ({ state, control := .evaluate bindings BoundCallControls.call } : Configuration) ≠
      finished after answers [] [] := by
    intro same
    have impossible := congrArg Configuration.control same
    cases impossible
  have unchanged := certificate.starts_unchanged different
  have captured := BoundCalls.target_captured BoundCallControls.program bindings "f" "bound-call:increment"
    [BoundCallControls.seven] rfl (by decide)
  change BoundCalls.target BoundCallControls.program
    (.evaluate bindings (.expression [.var "f", BoundCallControls.seven])) = none at unchanged
  rw [captured] at unchanged
  contradiction

/-- Explicit quotation remains data even when its captured head names an
admitted authored function. No evaluation of the quoted code is authorized. -/
theorem quoted_call_remains_data (state : Effects.State) :
    BoundCalls.PureReturns BoundCallControls.program bindings state
      (.expression [.symbol "quote", BoundCallControls.call]) state
      (.expression [.symbol "bound-call:increment", BoundCallControls.seven]) :=
  (BoundCalls.CorePath.quote_returns BoundCallControls.program bindings state BoundCallControls.call).extended

/-- Returning two captured code values as tuple fields does not execute either
value or merge the two occurrences. The expression head stays inert here. -/
theorem captured_code_fields_stay_data (state : Effects.State) :
    BoundCalls.PureReturns BoundCallControls.program
      [("left", .expression [.symbol "bound-call:increment", BoundCallControls.seven]),
       ("right", .expression [.symbol "bound-call:increment", BoundCallControls.seven])]
      state (.expression [.var "left", .var "right"]) state
      (.expression [.expression [.symbol "bound-call:increment", BoundCallControls.seven],
        .expression [.symbol "bound-call:increment", BoundCallControls.seven]]) :=
  (BoundCalls.CorePath.tuple_variables_return BoundCallControls.program _ state ["left", "right"] rfl).extended

/-- A tuple with an admitted captured function in its head cannot satisfy the
data guard. Variable spelling does not license a blanket tuple theorem. -/
theorem captured_function_refuses_data_guard :
    BoundCalls.target BoundCallControls.program
      (.evaluate [("f", .symbol "bound-call:increment"), ("x", BoundCallControls.seven)]
        (.expression [.var "f", .var "x"])) ≠ none := by decide

def controlWordProgram : SpaceSemantics.Program :=
  { equations := [⟨"quote", [.var "x"], .grounded (.int 99)⟩], declarations := [] }

/-- Admission of an authored name alone does not erase literal control syntax.
The captured and literal spellings take different first transitions here. -/
theorem control_word_requires_shape_condition (state : Effects.State) :
    BoundCalls.admitted controlWordProgram "quote" [BoundCallControls.seven] = true ∧
    DeclarativeSpec.controlForm (.expression [.symbol "quote", BoundCallControls.seven]) = true ∧
    BoundCalls.step controlWordProgram
      { state, control := .evaluate [("f", .symbol "quote")] (.expression [.var "f", BoundCallControls.seven]) } =
      some { state, control := .arguments [("f", .symbol "quote")] (.function "quote") [BoundCallControls.seven] [] 0 } ∧
    BoundCalls.step controlWordProgram
      { state, control := .evaluate [("f", .symbol "quote")] (.expression [.symbol "quote", BoundCallControls.seven]) } =
      some { state, control := .returned [BoundCallControls.seven] } := by
  refine ⟨by decide, rfl, ?_, rfl⟩
  exact (BoundCalls.step_iff ..).mpr
    (.captured [("f", .symbol "quote")] "f" "quote" [BoundCallControls.seven] rfl rfl (by decide))

end Mettapedia.Languages.MeTTa.PeTTa.BoundCallCompositionControls
