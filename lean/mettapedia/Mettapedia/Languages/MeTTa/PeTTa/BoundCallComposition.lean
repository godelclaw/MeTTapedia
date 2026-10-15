import Mettapedia.Languages.MeTTa.PeTTa.BoundCalls

/-!
# Composition and conservative transport for captured authored calls

Captured calls use the same argument configuration as ordinary authored
applications. Caller frames, bindings, the complete store and I/O remain in
the configuration. Literal control syntax has its own entry rules, so replacing
a captured head by a literal head requires an ordinary application shape.

Old execution paths transport only when none of their source controls requests
captured dispatch. This is an explicit path certificate, not an assumption that
the two evaluators agree on every program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BoundCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program)
open Eval (Configuration Control Frame Target finished withFrames)
open Effects (State)

theorem transition_with_caller_frames {program : Program} {source selected : Configuration}
    (caller : List Frame) (transition : Transition program source selected) :
    Transition program (withFrames source caller) (withFrames selected caller) := by
  cases transition with
  | captured bindings name head arguments shape resolved authorized =>
      simpa [withFrames] using
        (Transition.captured (source := withFrames source caller) bindings name head arguments
          shape resolved authorized)
  | core unchanged original =>
      exact .core unchanged (Eval.step_transition
        (Eval.step_with_caller_frames program _ _ caller (Eval.transition_step original)))

theorem path_with_caller_frames (program : Program) (caller : List Frame) :
    {source selected : Configuration} → (theory program).MultiStep source selected →
      (theory program).MultiStep (withFrames source caller) (withFrames selected caller)
  | _, _, .refl _ => .refl _
  | _, _, .step transition rest =>
      .step (transition_with_caller_frames caller transition)
        (path_with_caller_frames program caller rest)

theorem path_trans {program : Program} {first middle last : Configuration}
    (one : (theory program).MultiStep first middle)
    (two : (theory program).MultiStep middle last) :
    (theory program).MultiStep first last := by
  exact @Mettapedia.GSLT.GSLT.MultiStep.rec (theory program)
    (fun first middle _ => (theory program).MultiStep middle last →
      (theory program).MultiStep first last)
    (fun _ continuation => continuation)
    (fun {_ _ _} transition _ ih continuation => .step transition (ih continuation))
    first middle one two

abbrev Returns (program : Program) (bindings : Subst)
    (before : State) (expression : Atom) (after : State) (answers : List Atom) : Prop :=
  (theory program).MultiStep { state := before, control := .evaluate bindings expression }
    (finished after answers [] [])

abbrev PureReturns (program : Program) (bindings : Subst)
    (before : State) (expression : Atom) (after : State) (value : Atom) : Prop :=
  Returns program bindings before expression after [value]

theorem variable_returns (program : Program) (bindings : Subst) (state : State) (name : String) :
    PureReturns program bindings state (.var name) state (applySubst bindings (.var name)) :=
  .step (.core rfl (Eval.step_transition rfl)) (.refl _)

theorem symbol_returns (program : Program) (bindings : Subst) (state : State) (name : String) :
    PureReturns program bindings state (.symbol name) state (.symbol name) :=
  .step (.core rfl (Eval.step_transition rfl)) (.refl _)

theorem single_sequence_returns (program : Program) (before after : State)
    (control : Control) (answer : Atom)
    (computed : (theory program).MultiStep { state := before, control }
      (finished after [answer] [] [])) :
    (theory program).MultiStep { state := before, control := .sequence [control] [] }
      (finished after [answer] [] []) := by
  refine .step (.core rfl (Eval.step_transition rfl))
    (path_trans (path_with_caller_frames program [.sequence [] []] computed) ?_)
  exact .step (.core rfl (Eval.step_transition rfl))
    (.step (.core rfl (Eval.step_transition rfl)) (.refl _))

theorem let_returns (program : Program) (bindings bound : Subst)
    (before middle after : State) (pattern expression body value answer : Atom)
    (computed : PureReturns program bindings before expression middle value)
    (matched : SpaceSemantics.matchBinding bindings pattern value = some bound)
    (continued : PureReturns program bound middle body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "let", pattern, expression, body]) after answer := by
  refine .step (.core rfl (Eval.step_transition rfl))
    (path_trans (path_with_caller_frames program [.bind bindings pattern body] computed) ?_)
  refine .step ?_ (single_sequence_returns program middle after (.evaluate bound body) answer continued)
  apply Transition.core rfl
  apply Eval.step_transition
  simp [withFrames, finished, Eval.step, matched]

/-- Sequential bindings enter the existing nested-let machine, retaining
the same caller environment, state and eventual answer. -/
theorem let_star_returns (program : Program) (bindings : Subst)
    (before after : State) (pairs : List Atom) (body nested answer : Atom)
    (expanded : Eval.nestedLets pairs body = some nested)
    (returned : PureReturns program bindings before nested after answer) :
    PureReturns program bindings before
      (.expression [.symbol "let*", .expression pairs, body]) after answer := by
  refine .step (.core rfl ?_) returned
  apply Eval.step_transition
  simp [Eval.step, expanded]

theorem case_returns (program : Program) (bindings bound : Subst)
    (before middle after : State) (expression value body answer : Atom)
    (rows : List Atom) (cases : SpaceSemantics.Cases)
    (decoded : Eval.readCases rows = some cases)
    (computed : PureReturns program bindings before expression middle value)
    (selected : SpaceSemantics.selectCase bindings value cases = some (bound, body))
    (continued : PureReturns program bound middle body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "case", expression, .expression rows]) after answer := by
  refine .step ?_
    (path_trans (path_with_caller_frames program [.select bindings cases] computed) ?_)
  · apply Transition.core rfl
    apply Eval.step_transition
    simp [Eval.step, decoded, withFrames]
  · refine .step ?_ (single_sequence_returns program middle after (.evaluate bound body) answer continued)
    apply Transition.core rfl
    apply Eval.step_transition
    simp [withFrames, finished, Eval.step, selected]

/-- Both call spellings enter exactly the same argument machine. The ordinary
shape condition keeps literal control forms outside this correspondence. -/
theorem captured_literal_entry (program : Program) (source : Configuration)
    (bindings : Subst) (name head : String) (arguments : List Atom)
    (captured : applySubst bindings (.var name) = .symbol head)
    (authorized : admitted program head arguments = true)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    step program { source with control := .evaluate bindings (.expression (.var name :: arguments)) } =
      some { source with control := .arguments bindings (.function head) arguments [] 0 } ∧
    step program { source with control := .evaluate bindings (.expression (.symbol head :: arguments)) } =
      some { source with control := .arguments bindings (.function head) arguments [] 0 } := by
  constructor
  · exact (step_iff ..).mpr (.captured bindings name head arguments rfl captured authorized)
  · apply (step_iff ..).mpr
    apply Transition.core rfl
    apply DeclarativeSpec.Transition.call_enter rfl ordinary
    obtain ⟨_, _, ⟨equation, member, same, _⟩, _⟩ := (admitted_iff ..).mp authorized
    have existsHead : program.equations.any (·.head == head) = true := by
      simp only [List.any_eq_true]
      exact ⟨equation, member, by simp [same]⟩
    simp [existsHead]

/-- Equal transition budgets give equal complete observations or the same
residual after call entry, including all pending caller work and I/O. -/
theorem captured_literal_run (program : Program) (source : Configuration)
    (bindings : Subst) (name head : String) (arguments : List Atom) (fuel : Nat)
    (captured : applySubst bindings (.var name) = .symbol head)
    (authorized : admitted program head arguments = true)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    run program (fuel + 1)
      { source with control := .evaluate bindings (.expression (.var name :: arguments)) } =
    run program (fuel + 1)
      { source with control := .evaluate bindings (.expression (.symbol head :: arguments)) } := by
  obtain ⟨left, right⟩ := captured_literal_entry program source bindings name head arguments
    captured authorized ordinary
  rw [run_succ_of_step program _ _ fuel left, run_succ_of_step program _ _ fuel right]

/-- An old path carries a checked noninterference condition at every source
step. Its transitions remain the existing declarative transitions. -/
inductive CorePath (program : Program) : Configuration → Configuration → Prop where
  | refl (source : Configuration) : CorePath program source source
  | step {source middle selected : Configuration}
      (unchanged : target program source.control = none)
      (original : DeclarativeSpec.Transition program source middle)
      (rest : CorePath program middle selected) : CorePath program source selected

theorem CorePath.original {program : Program} {source selected : Configuration}
    (path : CorePath program source selected) : (Eval.theory program).MultiStep source selected := by
  induction path with
  | refl source => exact @Mettapedia.GSLT.GSLT.MultiStep.refl (Eval.theory program) source
  | step _ original _ ih => exact .step original ih

theorem CorePath.extended {program : Program} {source selected : Configuration}
    (path : CorePath program source selected) : (theory program).MultiStep source selected := by
  induction path with
  | refl source => exact @Mettapedia.GSLT.GSLT.MultiStep.refl (theory program) source
  | step unchanged original _ ih => exact .step (.core unchanged original) ih

theorem CorePath.with_caller_frames {program : Program} {source selected : Configuration}
    (path : CorePath program source selected) (caller : List Frame) :
    CorePath program (withFrames source caller) (withFrames selected caller) := by
  induction path with
  | refl source => exact .refl _
  | step unchanged original _ ih =>
      exact .step unchanged (Eval.step_transition
        (Eval.step_with_caller_frames program _ _ caller (Eval.transition_step original))) ih

theorem CorePath.trans {program : Program} {first middle last : Configuration}
    (one : CorePath program first middle) (two : CorePath program middle last) :
    CorePath program first last := by
  induction one with
  | refl _ => exact two
  | step unchanged original _ ih => exact .step unchanged original (ih two)

/-- Returning through one pending clause adds one suspended sequence frame.
The frame is retained in a prefix; it is discharged only when the body returns. -/
def callerCells (count : Nat) : List Frame := List.replicate count (.sequence [] [])

theorem CorePath.variable_argument_enters (program : Program) (bindings : Subst)
    (state : State) (destination : Target) (name : String) (remaining values : List Atom)
    (index : Nat) :
    CorePath program
      { state, control := .arguments bindings destination (.var name :: remaining) values index }
      { state, control := .arguments bindings destination remaining
          (values ++ [applySubst bindings (.var name)]) (index + 1), frames := callerCells 1 } := by
  let frame := Frame.argument bindings destination remaining values index
  let returned : Configuration :=
    { state, control := .returned [applySubst bindings (.var name)], frames := [frame] }
  have finish : CorePath program returned
      { state, control := .arguments bindings destination remaining
          (values ++ [applySubst bindings (.var name)]) (index + 1), frames := callerCells 1 } :=
    .step rfl (Eval.step_transition rfl)
      (.step rfl (Eval.step_transition rfl) (.refl _))
  cases demand : (match destination with
    | .function head => Eval.argumentIsRaw program head index
    | .data => false) with
  | false =>
      refine .step (middle := { state, control := .evaluate bindings (.var name), frames := [frame] })
        rfl ?_ (.step rfl (Eval.step_transition rfl) finish)
      apply Eval.step_transition
      simp [Eval.step, frame]
      exact demand
  | true =>
      refine .step rfl ?_ finish
      apply Eval.step_transition
      simp [Eval.step, frame, returned]
      exact demand

/-- Variable arguments are captured once in source order. Both raw and strict
positions preserve the same captured value and pending caller frames. -/
theorem CorePath.variable_prefix_enters (program : Program) (bindings : Subst)
    (state : State) (destination : Target) (names : List String) (remaining values : List Atom)
    (index : Nat) :
    CorePath program
      { state, control := .arguments bindings destination (names.map Atom.var ++ remaining) values index }
      { state, control := .arguments bindings destination remaining
          (values ++ names.map (fun name => applySubst bindings (.var name)))
          (index + names.length), frames := callerCells names.length } := by
  induction names generalizing values index with
  | nil => simpa [callerCells] using
      (CorePath.refl (program := program)
        ({ state, control := .arguments bindings destination remaining values index } : Configuration))
  | cons name names ih =>
      have first := CorePath.variable_argument_enters program bindings state destination name
        (names.map Atom.var ++ remaining) values index
      have rest := (ih (values ++ [applySubst bindings (.var name)]) (index + 1)).with_caller_frames
        (callerCells 1)
      have composed := first.trans rest
      simpa [withFrames, callerCells, List.replicate_add, List.append_assoc,
        Nat.add_assoc, Nat.add_comm 1] using composed

/-- The source call prefix is certified before any body computation is
assumed. Argument capture and clause selection retain the exact caller stack. -/
theorem CorePath.authored_call_enters (program : Program) (bindings callee : Subst)
    (state : State) (head : String) (names : List String) (body : Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: names.map Atom.var)) = false)
    (notIO : Eval.ioHead head = false) (notNative : StdLib.known head = false)
    (registered : program.equations.any (·.head == head) = true)
    (selected : Eval.clauses program head
      (names.map (fun name => applySubst bindings (.var name))) = [.evaluate callee body]) :
    CorePath program
      { state, control := .evaluate bindings (.expression (.symbol head :: names.map Atom.var)) }
      { state, control := .evaluate callee body, frames := callerCells (names.length + 1) } := by
  have arguments := CorePath.variable_prefix_enters program bindings state (.function head) names [] [] 0
  have enter : CorePath program
      { state, control := .arguments bindings (.function head) []
          (names.map (fun name => applySubst bindings (.var name))) names.length }
      { state, control := .evaluate callee body, frames := callerCells 1 } := by
    refine .step (middle := { state, control := .sequence [.evaluate callee body] [] })
      rfl ?_ (.step rfl (Eval.step_transition rfl) (.refl _))
    apply Eval.step_transition
    simp [Eval.step, notIO, notNative, selected]
  refine .step rfl (DeclarativeSpec.Transition.call_enter rfl ordinary (by simp [registered])) ?_
  have framed : CorePath program
      { state, control := .arguments bindings (.function head) []
          ([] ++ names.map (fun name => applySubst bindings (.var name)))
          (0 + names.length), frames := callerCells names.length }
      (withFrames { state, control := .evaluate callee body, frames := callerCells 1 }
        (callerCells names.length)) := by
    simpa [withFrames] using enter.with_caller_frames (callerCells names.length)
  have composed := arguments.trans framed
  simpa [withFrames, callerCells, List.replicate_succ] using composed

theorem let_enters (program : Program) (bindings bound : Subst)
    (before after : State) (pattern expression body value : Atom)
    (computed : PureReturns program bindings before expression after value)
    (matched : SpaceSemantics.matchBinding bindings pattern value = some bound) :
    (theory program).MultiStep
      { state := before, control := .evaluate bindings (.expression [.symbol "let", pattern, expression, body]) }
      { state := after, control := .evaluate bound body, frames := callerCells 1 } := by
  refine .step (.core rfl (Eval.step_transition rfl))
    (path_trans (path_with_caller_frames program [.bind bindings pattern body] computed) ?_)
  refine .step (u := ({ state := after, control := .sequence [.evaluate bound body] [] } : Configuration))
    ?_ (.step (.core rfl (Eval.step_transition rfl)) (.refl _))
  apply Transition.core rfl
  apply Eval.step_transition
  simp [withFrames, finished, Eval.step, matched]

theorem case_enters (program : Program) (bindings bound : Subst)
    (before after : State) (expression value body : Atom)
    (rows : List Atom) (cases : SpaceSemantics.Cases)
    (decoded : Eval.readCases rows = some cases)
    (computed : PureReturns program bindings before expression after value)
    (selected : SpaceSemantics.selectCase bindings value cases = some (bound, body)) :
    (theory program).MultiStep
      { state := before, control := .evaluate bindings (.expression [.symbol "case", expression, .expression rows]) }
      { state := after, control := .evaluate bound body, frames := callerCells 1 } := by
  refine .step ?_
    (path_trans (path_with_caller_frames program [.select bindings cases] computed) ?_)
  · apply Transition.core rfl
    apply Eval.step_transition
    simp [Eval.step, decoded, withFrames]
  · refine .step (u := ({ state := after, control := .sequence [.evaluate bound body] [] } : Configuration))
      ?_ (.step (.core rfl (Eval.step_transition rfl)) (.refl _))
    apply Transition.core rfl
    apply Eval.step_transition
    simp [withFrames, finished, Eval.step, selected]

end Mettapedia.Languages.MeTTa.PeTTa.BoundCalls
