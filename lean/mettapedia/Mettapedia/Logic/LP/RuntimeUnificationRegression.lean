import Mettapedia.Logic.LP.RuntimeUnification

/-!
# Runtime-unification regressions

The fixtures pin the cases where a tree-only or non-transactional unifier is
wrong: rational-tree binding, variable orientation, left-to-right compound
work, exact rollback after a later mismatch, and termination on two cyclic
compound graphs.
-/

namespace Mettapedia.Logic.LP.RuntimeUnificationRegression

open RuntimeTerm RuntimeUnification

inductive UConst where
  | a | b | c
deriving DecidableEq, Repr

inductive UVar where
  | x | y
deriving DecidableEq, Repr

inductive URel where
  | p
deriving DecidableEq, Repr

inductive UFun where
  | pair | loop
deriving DecidableEq, Repr

def uSig : LPSignature where
  constants := UConst
  vars := UVar
  relationSymbols := URel
  relationArity := fun _ => 0
  functionSymbols := UFun
  functionArity
    | .pair => 2
    | .loop => 1

instance : DecidableEq uSig.constants := inferInstanceAs (DecidableEq UConst)
instance : DecidableEq uSig.functionSymbols := inferInstanceAs (DecidableEq UFun)

def rationalBase : Memory uSig := {
  heap := #[.var .x none, .app .loop #[0]]
  trail := #[]
}

def rationalBound : Memory uSig := {
  heap := #[.var .x (some 1), .app .loop #[0]]
  trail := #[{ address := 0, previous := .var .x none }]
}

/-- `occurs_check=false`: binding `X` to `loop(X)` succeeds and retains the
rational graph rather than rejecting it or trying to unfold it. -/
theorem rational_tree_binding_succeeds :
    runSteps 2 (start rationalBase 0 1) =
      .terminal (.success rationalBound) := by
  rfl

def twoVariables : Memory uSig := {
  heap := #[.var .x none, .var .y none]
  trail := #[]
}

def twoVariablesUnified : Memory uSig := {
  heap := #[.var .x none, .var .y (some 0)]
  trail := #[{ address := 1, previous := .var .y none }]
}

/-- Like SWI's simple-pointer case, two variables point downward by address. -/
theorem variables_are_oriented_downward :
    runSteps 2 (start twoVariables 0 1) =
      .terminal (.success twoVariablesUnified) := by
  rfl

def lateMismatchBase : Memory uSig := {
  heap := #[
    .var .x none,
    .const .b,
    .const .a,
    .const .c,
    .app .pair #[0, 2],
    .app .pair #[1, 3]
  ]
  trail := #[]
}

/-- The first pair argument binds `X`; the second then conflicts.  Failure
unwinds the earlier write exactly, rather than leaking a partial binding. -/
theorem later_mismatch_rolls_back_exactly :
    runSteps 5 (start lateMismatchBase 4 5) =
      .terminal (.failure lateMismatchBase) := by
  rfl

/-- A short budget exposes a resumable running state, never false failure. -/
theorem budget_exhaustion_is_not_failure :
    match runSteps 1 (start lateMismatchBase 4 5) with
    | .running _ => True
    | .terminal _ => False := by
  trivial

def twoRationalCycles : Memory uSig := {
  heap := #[
    .var .x (some 1), .app .loop #[0],
    .var .y (some 3), .app .loop #[2]
  ]
  trail := #[]
}

/-- Visited compound pairs make bisimilar rational cycles terminate. -/
theorem equal_rational_cycles_terminate :
    runSteps 3 (start twoRationalCycles 0 2) =
      .terminal (.success twoRationalCycles) := by
  rfl

def variableOnlyCycle : Memory uSig := {
  heap := #[.var .x (some 1), .var .y (some 0)]
  trail := #[]
}

/-- A corrupt cycle consisting only of variable links is a structured error,
not a rational term and not an infinite dereference loop. -/
theorem variable_only_cycle_is_visible :
    runSteps 2 (start variableOnlyCycle 0 0) =
      .terminal (.runtimeError (.variableReferenceCycle 1) variableOnlyCycle) := by
  rfl

end Mettapedia.Logic.LP.RuntimeUnificationRegression
