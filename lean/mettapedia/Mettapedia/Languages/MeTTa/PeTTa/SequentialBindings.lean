import Mettapedia.Languages.MeTTa.PeTTa.CoreExecution

/-!
# Source execution of sequential variable bindings

A path computes every initializer in its actual preceding environment and
retains the environment produced by matching. The source let* form expands
to the existing nested lets; no bindings are projected away and no initializer
execution is supplied by a separate evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SequentialBindings

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom)
open SpaceSemantics (Program)
open Effects (State)

def bindingSyntax (pairs : List (String × Atom)) : List Atom :=
  pairs.map fun row => .expression [.var row.1, row.2]

def nested (pairs : List (String × Atom)) (body : Atom) : Atom :=
  pairs.foldr (fun row rest => .expression [.symbol "let", .var row.1, row.2, rest]) body

theorem source_expansion (pairs : List (String × Atom)) (body : Atom) :
    Eval.nestedLets (bindingSyntax pairs) body = some (nested pairs body) := by
  induction pairs with
  | nil => rfl
  | cons row rest ih =>
      simpa [bindingSyntax, nested, Eval.nestedLets] using
        (congrArg (Option.map fun tail => Atom.expression [.symbol "let", .var row.1, row.2, tail]) ih)

/-- Every initializer is an existing source execution, checked in its live
environment. Fresh variable names preserve source matching's capture test. -/
inductive Path (program : Program) (state : State) :
    Subst → List (String × Atom) → Subst → Prop where
  | nil (bindings : Subst) : Path program state bindings [] bindings
  | cons {bindings final : Subst} {name : String} {expression value : Atom}
      {rest : List (String × Atom)}
      (computed : BoundCalls.PureReturns program bindings state expression state value)
      (fresh : Subst.lookup bindings name = none)
      (continued : Path program state ((name, value) :: bindings) rest final) :
      Path program state bindings ((name, expression) :: rest) final

theorem nested_returns {program : Program} {state : State} {bindings final : Subst}
    {pairs : List (String × Atom)} (path : Path program state bindings pairs final)
    (body answer : Atom) (continued : BoundCalls.PureReturns program final state body state answer) :
    BoundCalls.PureReturns program bindings state (nested pairs body) state answer := by
  induction path with
  | nil => exact continued
  | @cons bindings final name expression value rest computed fresh _ ih =>
      simp only [nested, List.foldr_cons]
      apply BoundCalls.let_returns program bindings ((name, value) :: bindings) state state state
        (.var name) expression _ value answer computed _ (ih continued)
      simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

/-- The complete source binding form composes with the checked continuation
and leaves its state and remaining environment intact. -/
theorem source_returns {program : Program} {state : State} {bindings final : Subst}
    {pairs : List (String × Atom)} (path : Path program state bindings pairs final)
    (body answer : Atom) (continued : BoundCalls.PureReturns program final state body state answer) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "let*", .expression (bindingSyntax pairs), body]) state answer :=
  BoundCalls.let_star_returns program bindings state state _ body (nested pairs body) answer
    (source_expansion pairs body) (nested_returns path body answer continued)

/-- Rebinding a captured variable to a different value does not silently
overwrite its meaning in the source matcher. -/
theorem captured_variable_refuses_rebinding :
    SpaceSemantics.matchBinding [("x", .grounded (.int 1))]
      (.var "x") (.grounded (.int 2)) = none := by
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]

end Mettapedia.Languages.MeTTa.PeTTa.SequentialBindings
