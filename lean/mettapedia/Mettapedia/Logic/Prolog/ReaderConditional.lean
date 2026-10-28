import Mettapedia.Logic.Prolog.ReaderDirective

/-!
# Conditional Prolog source loading

SWI processes literal `if/1`, `elif/1`, `else/0`, and `endif/0` directives
before ordinary term expansion.  Inactive forms disappear and cannot change
the reader environment.  This module implements that source-loading rule as
a stateful processor over `ReaderLoader`; it does not add a runtime goal or a
second clause representation.

The condition evaluator is explicit.  A pinned-source profile may recognize
only conditions whose truth it can establish, while malformed nesting and
unknown conditions fail closed.  This is intentionally stricter than SWI's
recovery for repeated `else` or `elif` after `else`: such malformed regions
are rejected rather than tolerated.
-/

namespace Mettapedia.Logic.Prolog.ReaderConditional

open ReaderSource SourceSignature

/-- Evaluate one read-time conditional goal. -/
abbrev ConditionProfile (rho : Type) :=
  SourceSignature.Goal -> Except rho Bool

inductive Error (epsilon rho : Type) where
  | effect (error : epsilon)
  | condition (error : rho)
  | malformed (name : String)
  | noIf (name : String)
  | duplicateElse
  | unterminated

/-- One open conditional region.  `parentActive` records whether the
surrounding region admits code; `taken` prevents a later `elif` or `else`
from becoming active after a successful arm. -/
structure Frame where
  parentActive : Bool
  taken : Bool
  active : Bool
  elseSeen : Bool
deriving DecidableEq, Repr

abbrev State := List Frame

private def active : State -> Bool
  | [] => true
  | frame :: _ => frame.active

private def arguments (atom : SourceSignature.Atom) :
    List SourceSignature.Term :=
  List.ofFn atom.args

private inductive Control where
  | ifThen (condition : SourceSignature.Goal)
  | elif (condition : SourceSignature.Goal)
  | else
  | endif

private def decodeControl : ReaderSource.Form ->
    Except (Error epsilon rho) (Option Control)
  | .directive (.call atom) =>
      match atom.symbol.name, arguments atom with
      | "if", [condition] =>
          match ReaderSource.toGoal condition with
          | .ok goal => .ok (some (.ifThen goal))
          | .error _ => .error (.malformed "if")
      | "if", _ => .error (.malformed "if")
      | "elif", [condition] =>
          match ReaderSource.toGoal condition with
          | .ok goal => .ok (some (.elif goal))
          | .error _ => .error (.malformed "elif")
      | "elif", _ => .error (.malformed "elif")
      | "else", [] => .ok (some .else)
      | "else", _ => .error (.malformed "else")
      | "endif", [] => .ok (some .endif)
      | "endif", _ => .error (.malformed "endif")
      | _, _ => .ok none
  | _ => .ok none

private def evaluateWhenActive (profile : ConditionProfile rho)
    (parentActive : Bool) (condition : SourceSignature.Goal) :
    Except (Error epsilon rho) Bool :=
  if parentActive then (profile condition).mapError .condition else .ok false

private def enterIf (profile : ConditionProfile rho) (condition : SourceSignature.Goal)
    (state : State) : Except (Error epsilon rho) State := do
  let parentActive := active state
  let selected <- evaluateWhenActive profile parentActive condition
  let frame : Frame := {
    parentActive := parentActive
    taken := selected
    active := parentActive && selected
    elseSeen := false
  }
  pure (frame :: state)

private def enterElif (profile : ConditionProfile rho)
    (condition : SourceSignature.Goal) : State ->
    Except (Error epsilon rho) State
  | [] => .error (.noIf "elif")
  | frame :: rest => do
      if frame.elseSeen then .error .duplicateElse else
        let eligible := frame.parentActive && !frame.taken
        let selected <- evaluateWhenActive profile eligible condition
        pure ({ frame with
          taken := frame.taken || selected
          active := eligible && selected
        } :: rest)

private def enterElse : State -> Except (Error epsilon rho) State
  | [] => .error (.noIf "else")
  | frame :: rest =>
      if frame.elseSeen then .error .duplicateElse else
        .ok ({ frame with
          taken := true
          active := frame.parentActive && !frame.taken
          elseSeen := true
        } :: rest)

private def leaveIf : State -> Except (Error epsilon rho) State
  | [] => .error (.noIf "endif")
  | _ :: rest => .ok rest

/-- Combine conditional compilation with an ordinary read-time effect.
Conditional directives and inactive forms are removed.  The ordinary effect
runs exactly once for each retained non-conditional form and never runs for
an inactive form. -/
def processor (profile : ConditionProfile rho)
    (effect : ReaderLoader.Effect epsilon) :
    ReaderLoader.Processor State (Error epsilon rho) :=
  fun form state operators => do
    match <- decodeControl form with
    | some (.ifThen condition) =>
        let next <- enterIf profile condition state
        pure { state := next, operators, retain := false }
    | some (.elif condition) =>
        let next <- enterElif profile condition state
        pure { state := next, operators, retain := false }
    | some .else =>
        let next <- enterElse state
        pure { state := next, operators, retain := false }
    | some .endif =>
        let next <- leaveIf state
        pure { state := next, operators, retain := false }
    | none =>
        if active state then
          let nextOperators <- (effect form operators).mapError .effect
          pure { state, operators := nextOperators, retain := true }
        else
          pure { state, operators, retain := false }

/-- Sequentially load one source buffer with conditional compilation.
An unterminated region fails after reading rather than silently dropping the
rest of the file. -/
def loadSourceWith (profile : ConditionProfile rho)
    (effect : ReaderLoader.Effect epsilon)
    (operators : ReaderOperator.Table) (source : String) :
    Except (ReaderLoader.Error (Error epsilon rho)) ReaderLoader.Result := do
  let loaded <- ReaderLoader.loadSourceStateWith
    (processor profile effect) [] operators source
  if loaded.state.isEmpty then
    pure { forms := loaded.forms, operators := loaded.operators }
  else
    .error (.effect .unterminated)

end Mettapedia.Logic.Prolog.ReaderConditional
