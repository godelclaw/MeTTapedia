import Mettapedia.Languages.MeTTa.HE.TypeCheck
import Mettapedia.Languages.MeTTa.HE.ArgumentResult

/-!
# Declarative model for the recursive HE evaluator

Mutual inductive relations for the six recursive evaluation functions and
their ordinary-call return boundary. Matching and typing leaves in this model
are computable premises. The separate `Spec.Eval` judgments supply the
executable-independent language specification; this file does not establish
native HE, CeTTa or PeTTa correspondence.

## Source of Truth
- `https://trueagi-io.github.io/hyperon-experimental/metta/`

## Architecture
- **Layer 1** (computable leaves): `Types.lean`, `Space.lean`, `Matching.lean`, `TypeCheck.lean`
- **Layer 2** (this file): Declarative inductive relations — no fuel, no computation,
  pure `Prop`-valued. Nondeterminism = multiple valid derivation trees.
- **Layer 3** (downstream): `Conformance.lean` (derivation witnesses), `Properties.lean`
  (universal theorems by induction on derivations).

## Design
Each relation produces a single `ResultPair`. Multiple results from the spec's
pseudocode correspond to multiple valid derivation trees for the same input.
Result ordering (spec line 210: `$tuples + $errors`) is an implementation
detail, not captured here — the relation is order-free by construction.

Producer-completed values have a separate provenance contract in `Spec.Eval`.
This recursive model describes ordinary raw emissions. Its return boundary
restores the post-argument call on `NotReducible`, retains Empty and Error,
and recursively evaluates other emissions under the saved demand.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Core Evaluation Relations

Six evaluation relations and their shared ordinary call-return judgment.
The evaluation relations follow the six core functions in the HE spec
(lines 105-389); the return judgment handles the raw emission protocol.

Parameters shared by all relations:
- `space : Space` — the context atomspace (read-only; space mutation is in MinimalMeTTa)
- `dispatch : GroundedDispatch` — grounded operation dispatch table

The computable leaf functions (`matchAtoms`, `mergeBindings`, `matchTypes`,
`typeCast`, `checkIfFunctionTypeIsApplicable`, `getAtomTypes`,
`queryEquationsAvoiding`) are referenced as hypotheses in constructors. -/

mutual

/-- Evaluate an atom to a single result.
    Ref: spec lines 105-136 "Evaluate atom (metta)".

    Input: atom, expected type, bindings.
    Output: one (result_atom, result_bindings) pair. -/
inductive EvalAtom (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Bindings → ResultPair → (live : List Atom := []) → Prop where
  /-- Spec line 117-118: Empty or Error atoms pass through unchanged.
      ```
      if $atom == Empty or $atom ~ (Error ...):
          return [($atom, $bindings)]
      ``` -/
  | empty_or_error (atom type_ : Atom) (b : Bindings)
      (h : isEmptyOrError atom = true) :
      EvalAtom space dispatch (live := live) atom type_ b (atom, b)
  /-- Spec line 119: Type matches meta-type, or meta-type is Variable.
      ```
      elif $type == Atom or $type == $metatype or $metatype == Variable:
          return [($atom, $bindings)]
      ``` -/
  | type_pass (atom type_ : Atom) (b : Bindings)
      (h_not_empty : isEmptyOrError atom = false)
      (h_pass : type_ = Atom.atomType
              ∨ type_ = getMetaType atom
              ∨ getMetaType atom = Atom.variableType) :
      EvalAtom space dispatch (live := live) atom type_ b (atom, b)
  /-- Spec lines 123-124: Symbol, Grounded, or empty-expression → typeCast.
      ```
      elif $metatype == Symbol or $metatype == Grounded or $atom == ():
          return type_cast($atom, $bindings, $type, $space)
      ```
      One derivation per element of `typeCast`'s result list. -/
  | type_cast (atom type_ : Atom) (b : Bindings) (r : ResultPair) (fuel : Nat)
      (h_not_empty : isEmptyOrError atom = false)
      (h_not_pass : ¬(type_ = Atom.atomType
                     ∨ type_ = getMetaType atom
                     ∨ getMetaType atom = Atom.variableType))
      (h_cast_branch : getMetaType atom = Atom.symbolType
                     ∨ getMetaType atom = Atom.groundedType
                     ∨ atom = Atom.unit)
      (h_result : r ∈ typeCast atom type_ space b fuel) :
      EvalAtom space dispatch (live := live) atom type_ b r
  /-- Spec lines 126-134: Expression → interpret, filter successes.
      ```
      $results = interpret_expression($atom, $type, $space, $bindings)
      $success = filter(not Error, $results)
      if len($success) > 0: return $success
      ```
      One derivation per successful (non-error) intermediate result. -/
  | interpret_success (atom type_ : Atom) (b : Bindings) (r : ResultPair)
      (h_not_empty : isEmptyOrError atom = false)
      (h_not_pass : ¬(type_ = Atom.atomType
                     ∨ type_ = getMetaType atom
                     ∨ getMetaType atom = Atom.variableType))
      (h_expr : getMetaType atom = Atom.expressionType)
      (h_not_unit : atom ≠ Atom.unit)
      (h_interp : InterpretExpression space dispatch (live := live) atom type_ b r)
      (h_not_error : isErrorAtom r.1 = false) :
      EvalAtom space dispatch (live := live) atom type_ b r
  /-- Spec lines 135-136: Interpret produces an error result.
      ```
      $error = filter(lambda $a: $a ~ (Error ...), $results)
      ...
      else: return $error
      ```
      Note: The spec filters ONLY on `Error`, not `Empty`. `Empty` is treated
      as a success. The spec returns errors ONLY when no successes exist. This
      constructor allows error results from any derivation tree. The
      success-priority filtering (spec lines 129-134) is captured by
      `EvalAtomFiltered` below, which adds the negative condition as
      a separate Prop (avoiding non-positive occurrence in the inductive). -/
  | interpret_error (atom type_ : Atom) (b : Bindings) (r : ResultPair)
      (h_not_empty : isEmptyOrError atom = false)
      (h_not_pass : ¬(type_ = Atom.atomType
                     ∨ type_ = getMetaType atom
                     ∨ getMetaType atom = Atom.variableType))
      (h_expr : getMetaType atom = Atom.expressionType)
      (h_not_unit : atom ≠ Atom.unit)
      (h_interp : InterpretExpression space dispatch (live := live) atom type_ b r)
      (h_is_error : isErrorAtom r.1 = true) :
      EvalAtom space dispatch (live := live) atom type_ b r

/-- Interpret an expression (dispatch to function or tuple path).
    Ref: spec lines 172-210 "Interpret expression (interpret_expression)".

    Input: expression atom, expected type, bindings.
    Output: one result pair (after metta_call on the interpret result). -/
inductive InterpretExpression (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Bindings → ResultPair → (live : List Atom := []) → Prop where
  /-- Spec lines 190-203: Operator has a valid function type, type check passes.
      ```
      for $f in <function types>:
          match check_if_function_type_is_applicable(...): case Ok($succs):
              for $b in $succs:
                  for ($a, $b) in interpret_function(...):
                      result += metta_call($a, $ret_type, $space, $b)
      ```
      `funcType` is one of the operator's types that is a valid function type.
      `retType` is the return type of `funcType` (or %Undefined% if Expression). -/
  | function_path (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (funcType retType : Atom) (b' : Bindings)
      (interpResult callResult : ResultPair) (fuel : Nat)
      (h_shape : atom = .expression (op :: args))
      (h_op_type : funcType ∈ getAtomTypes space op)
      (h_is_func : isFunctionType funcType = true)
      (succs : List Bindings)
      (h_check : checkIfFunctionTypeIsApplicable atom funcType type_ space b fuel = .inr succs)
      (h_check_b : b' ∈ succs)
      -- retType adjustment: if return type is Expression, use %Undefined%
      (h_ret : retType = (if getFunctionRetType funcType = some Atom.expressionType
                           then Atom.undefinedType
                           else (getFunctionRetType funcType).getD Atom.undefinedType))
      (h_interp : InterpretFunction space dispatch (live := retType :: live) atom funcType type_ b' interpResult)
      (h_call : MettaCall space dispatch (live := live) interpResult.1 retType interpResult.2 callResult) :
      InterpretExpression space dispatch (live := live) atom type_ b callResult
  /-- Spec lines 205-209: Tuple fallback path.
      ```
      if <$actual_types contains non function types or %Undefined%>:
          for ($a, $b) in interpret_tuple($atom, $space, $bindings):
              $tuples += metta_call($a, $type, $space, $b)
      ``` -/
  | tuple_path (atom type_ : Atom) (b : Bindings)
      (tupleResult callResult : ResultPair)
      (h_has_non_func : ∃ t ∈ getAtomTypes space (match atom with
                          | .expression (op :: _) => op | _ => atom),
                        isFunctionType t = false ∨ t = Atom.undefinedType)
      (h_tuple : InterpretTuple space dispatch (live := type_ :: live) atom b tupleResult)
      (h_call : MettaCall space dispatch (live := live) tupleResult.1 type_ tupleResult.2 callResult)
      (h_nonempty : atom ≠ Atom.unit) :
      InterpretExpression space dispatch (live := live) atom type_ b callResult
  /-- Spec line 184-186: Operator has incorrect type → error.
      ```
      if <$op is an atom with incorrect type>:
          return <list of (Error $op (BadArgType ...))>
      ```
      `errAtom` is tied to an actual failing `checkIfFunctionTypeIsApplicable` result
      via `failedType` and `errs`. This prevents vacuous instantiation (e.g. fuel=0). -/
  | op_type_error (atom type_ : Atom) (b : Bindings) (op : Atom) (args : List Atom)
      (errAtom : Atom) (fuel : Nat) (failedType : Atom) (errs : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_all_fail : ∀ ft ∈ getAtomTypes space op,
        isFunctionType ft = true →
        ∃ errs, checkIfFunctionTypeIsApplicable atom ft type_ space b fuel = .inl errs)
      (h_no_non_func : ∀ t ∈ getAtomTypes space op,
        isFunctionType t = true ∧ t ≠ Atom.undefinedType)
      (h_failed_type : failedType ∈ getAtomTypes space op)
      (h_failed_func : isFunctionType failedType = true)
      (h_check_fail : checkIfFunctionTypeIsApplicable atom failedType type_ space b fuel = .inl errs)
      (h_err_mem : errAtom ∈ errs) :
      InterpretExpression space dispatch (live := live) atom type_ b (errAtom, b)

/-- Interpret a function call (evaluate head, then args).
    Ref: spec lines 296-321 "Interpret function (interpret_function)".

    Input: expression, function type, return type, bindings.
    Output: one result pair. -/
inductive InterpretFunction (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Atom → Bindings → ResultPair → (live : List Atom := []) → Prop where
  /-- Spec lines 312-314: Head evaluates to Empty/Error → propagate.
      ```
      for ($h, $hb) in metta($op, $op_type, $space, $bindings):
          if $h == Empty or $h ~ (Error ...):
              $result += [($h, $hb)]
      ``` -/
  | head_error (atom opType retType : Atom) (b : Bindings)
      (op : Atom) (args : List Atom) (headResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_head : EvalAtom space dispatch (live := opType :: args ++ live) op opType b headResult)
      (h_err : isEmptyOrError headResult.1 = true) :
      InterpretFunction space dispatch (live := live) atom opType retType b headResult
  /-- Propagate a failed argument computation. Successful lists use the
      interpreter's `Ok` packet; the contents are not tested as an error. -/
  | head_ok_tail_error (atom opType retType : Atom) (b : Bindings)
      (op : Atom) (args argTypes : List Atom) (headResult tailResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_arg_types : getFunctionArgTypes opType = some argTypes)
      (h_head : EvalAtom space dispatch (live := opType :: args ++ live) op opType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretArgs space dispatch (live := headResult.1 :: live) args argTypes headResult.2 tailResult)
      (h_tail_err : argumentsSucceeded tailResult.1 = false) :
      InterpretFunction space dispatch (live := live) atom opType retType b tailResult
  | head_ok_tail_ok (atom opType retType : Atom) (b : Bindings)
      (op : Atom) (args argTypes : List Atom) (headResult tailResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_arg_types : getFunctionArgTypes opType = some argTypes)
      (h_head : EvalAtom space dispatch (live := opType :: args ++ live) op opType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretArgs space dispatch (live := headResult.1 :: live) args argTypes headResult.2 tailResult)
      (h_tail_ok : argumentsSucceeded tailResult.1 = true) :
      InterpretFunction space dispatch (live := live) atom opType retType b
        (.expression (headResult.1 :: argumentValues tailResult.1), tailResult.2)

/-- Interpret argument list (recursive evaluation of each arg with its type).
    Ref: spec lines 322-347 "Interpret arguments (interpret_args)".

    Input: args list, types list, bindings.
    Output: a tagged argument-list success, or a propagated changed error. -/
inductive InterpretArgs (space : Space) (dispatch : GroundedDispatch) :
    List Atom → List Atom → Bindings → ResultPair → (live : List Atom := []) → Prop where
  /-- Empty arguments produce the tagged empty list. -/
  | nil :
      InterpretArgs space dispatch (live := live) [] [] b (argumentPacket [], b)
  /-- Spec lines 338-340: Head evaluates to Empty/Error AND changed → propagate.
      ```
      for ($h, $hb) in metta($atom, $type, $space, $bindings):
          if ($h == Empty or $h ~ (Error ...)) and $h != $atom:
              $result += [($h, $hb)]
      ``` -/
  | head_changed_error (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult : ResultPair)
      (h_head : EvalAtom space dispatch (live := as ++ ts ++ live) a t b headResult)
      (h_err : isEmptyOrError headResult.1 = true)
      (h_changed : headResult.1 ≠ a) :
      InterpretArgs space dispatch (live := live) (a :: as) (t :: ts) b headResult
  /-- Spec lines 341-346: Head ok (or unchanged error), recurse on tail.
      ```
      else:
          for ($t, $tb) in interpret_args($args_tail, $types_tail, $space, $hb):
              ...
      ``` -/
  | cons_tail_error (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult tailResult : ResultPair)
      (h_head : EvalAtom space dispatch (live := as ++ ts ++ live) a t b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false ∨ headResult.1 = a)
      (h_tail : InterpretArgs space dispatch (live := headResult.1 :: live) as ts headResult.2 tailResult)
      (h_tail_err : argumentsSucceeded tailResult.1 = false) :
      InterpretArgs space dispatch (live := live) (a :: as) (t :: ts) b tailResult
  | cons_ok (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult tailResult : ResultPair)
      (h_head : EvalAtom space dispatch (live := as ++ ts ++ live) a t b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false ∨ headResult.1 = a)
      (h_tail : InterpretArgs space dispatch (live := headResult.1 :: live) as ts headResult.2 tailResult)
      (h_tail_ok : argumentsSucceeded tailResult.1 = true) :
      InterpretArgs space dispatch (live := live) (a :: as) (t :: ts) b
        (argumentPacket (headResult.1 :: argumentValues tailResult.1), tailResult.2)

/-- Interpret a tuple (recursive element-wise evaluation).
    Ref: spec lines 211-233 "Interpret tuple (interpret_tuple)".

    Input: expression atom, bindings.
    Output: one result pair. -/
inductive InterpretTuple (space : Space) (dispatch : GroundedDispatch) :
    Atom → Bindings → ResultPair → (live : List Atom := []) → Prop where
  /-- The empty tuple is the base of tuple construction. -/
  | nil (b : Bindings) :
      InterpretTuple space dispatch (live := live) Atom.unit b (Atom.unit, b)
  /-- A successful single element retains its tuple wrapper. -/
  | singleton (a : Atom) (b : Bindings) (r : ResultPair)
      (h_eval : EvalAtom space dispatch (live := live) a Atom.undefinedType b r)
      (h_ok : isEmptyOrError r.1 = false) :
      InterpretTuple space dispatch (live := live) (.expression [a]) b (.expression [r.1], r.2)
  /-- Empty or Error from the single element propagates without a wrapper. -/
  | singleton_error (a : Atom) (b : Bindings) (r : ResultPair)
      (h_eval : EvalAtom space dispatch (live := live) a Atom.undefinedType b r)
      (h_error : isEmptyOrError r.1 = true) :
      InterpretTuple space dispatch (live := live) (.expression [a]) b r
  /-- Spec lines 224-226: Head evaluates to Empty/Error → propagate.
      ```
      for ($h, $hb) in metta($head, %Undefined%, $space, $bindings):
          if $h == Empty or $h ~ (Error ...):
              $result += [($h, $hb)]
      ``` -/
  | head_error (hd : Atom) (tl : List Atom) (b : Bindings)
      (headResult : ResultPair)
      (h_tl_nonempty : tl ≠ [])
      (h_head : EvalAtom space dispatch (live := .expression tl :: live) hd Atom.undefinedType b headResult)
      (h_err : isEmptyOrError headResult.1 = true) :
      InterpretTuple space dispatch (live := live) (.expression (hd :: tl)) b headResult
  /-- Spec lines 228-230: Head ok, tail evaluates to Empty/Error → propagate.
      ```
      for ($t, $tb) in interpret_tuple($tail, $space, $hb):
          if $t == Empty or $t ~ (Error ...):
              $result += [($t, $tb)]
      ``` -/
  | tail_error (hd : Atom) (tl : List Atom) (b : Bindings)
      (headResult tailResult : ResultPair)
      (h_tl_nonempty : tl ≠ [])
      (h_head : EvalAtom space dispatch (live := .expression tl :: live) hd Atom.undefinedType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretTuple space dispatch (live := headResult.1 :: live) (.expression tl) headResult.2 tailResult)
      (h_tail_err : isEmptyOrError tailResult.1 = true) :
      InterpretTuple space dispatch (live := live) (.expression (hd :: tl)) b tailResult
  /-- Spec lines 231-232: Both head and tail ok → combine.
      ```
      $result += [(<tuple with head $h and tail $t>, $tb)]
      ``` -/
  | success (hd : Atom) (tl : List Atom) (b : Bindings)
      (headResult tailResult : ResultPair)
      (h_tl_nonempty : tl ≠ [])
      (h_head : EvalAtom space dispatch (live := .expression tl :: live) hd Atom.undefinedType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretTuple space dispatch (live := headResult.1 :: live) (.expression tl) headResult.2 tailResult)
      (h_tail_ok : isEmptyOrError tailResult.1 = false) :
      InterpretTuple space dispatch (live := live) (.expression (hd :: tl)) b
        (.expression (headResult.1 :: match tailResult.1 with
          | .expression es => es | a => [a]), tailResult.2)

/-- Call a MeTTa expression (grounded dispatch or equation matching).
    Ref: spec lines 348-389 "Call MeTTa expression (metta_call)".

    Equation instances: the equation branches query with rule instances fresh
    for a name list `avoid` that covers the call, expected type, bindings, and
    every atom retained by its surrounding computation (`CoversEvaluation`).
    The live index follows the pending continuation through all six judgments.

    Compatibility note: the `equation_match` branch below embeds the HE
    executable `queryEquationsAvoiding` and `mergeBindings` functions as premises.
    Consequently this relation is not the executable-independent target for
    equation-query conformance.  `Spec.Eval.EquationQueryStep` is the separate
    spec-specification relation at the one-step query boundary; recursive
    evaluator/call conformance is a later, separately named layer.

    Input: atom, expected type, bindings.
    Output: one result pair. -/
inductive MettaCall (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Bindings → ResultPair → (live : List Atom := []) → Prop where
  /-- Spec lines 359-360: Error atoms pass through.
      ```
      if $atom ~ (Error ...):
          return [($atom, $bindings)]
      ``` -/
  | error_passthrough (atom type_ : Atom) (b : Bindings)
      (h_err : isErrorAtom atom = true) :
      MettaCall space dispatch (live := live) atom type_ b (atom, b)
  /-- Primitive `unify`: successful raw branch result.
      Upstream `unify` itself only chooses a branch and threads bindings; it
      does not recursively evaluate the chosen branch to completion.
      The raw success lane is exactly `unifySuccessResults`.
      ````
      (unify target pattern then else)
        ↦ apply merged bindings to then
      ``` -/
  | unify_success_raw (atom type_ : Atom) (b : Bindings)
      (target pattern thenBranch elseBranch : Atom)
      (finalResult : ResultPair) (fuel : Nat)
      (h_shape : atom = .expression [.symbol "unify",
        target, pattern, thenBranch, elseBranch])
      (h_not_error : isErrorAtom atom = false)
      (h_raw : finalResult ∈ unifySuccessResults target pattern thenBranch b fuel) :
      MettaCall space dispatch (live := live) atom type_ b finalResult
  /-- Primitive `unify`: no surviving raw success results, so upstream falls
      back to the else branch unchanged under the original bindings.
      ````
      (unify target pattern then else)
        ↦ else
      ``` -/
  | unify_no_match_raw (atom type_ : Atom) (b : Bindings)
      (target pattern thenBranch elseBranch : Atom) (fuel : Nat)
      (h_shape : atom = .expression [.symbol "unify",
        target, pattern, thenBranch, elseBranch])
      (h_not_error : isErrorAtom atom = false)
      (h_empty : unifySuccessResults target pattern thenBranch b fuel = []) :
      MettaCall space dispatch (live := live) atom type_ b (elseBranch, b)
  /-- Primitive `unify`: wrong arity is reported as the
      hyperon-experimental minimal-instruction parser message. -/
  | unify_bad_arity (atom type_ : Atom) (b : Bindings)
      (tail : List Atom)
      (h_shape : atom = .expression (.symbol "unify" :: tail))
      (h_arity : tail.length ≠ 4)
      (h_not_error : isErrorAtom atom = false) :
      MettaCall space dispatch (live := live) atom type_ b (mkUnifyBadArityError atom, b)
  /-- `switch-minimal`: exact-shape direct result lane.
      This packages the observable behavior of the stdlib helper:
      first viable branch wins, the selected raw template is returned with its
      surviving merged bindings, and a raw `NotReducible` witness is collapsed
      to `Empty`.  If no branch produces any surviving result, the overall
      result is also `Empty` under the original seed bindings. -/
  | switch_minimal_result (atom type_ : Atom) (b : Bindings)
      (scrut : Atom) (branches : List Atom)
      (finalResult : ResultPair) (fuel : Nat)
      (h_shape : atom = .expression [.symbol "switch-minimal",
        scrut, .expression branches])
      (h_not_error : isErrorAtom atom = false)
      (h_result : finalResult ∈ switchMinimalResults scrut branches b fuel) :
      MettaCall space dispatch (live := live) atom type_ b finalResult
  /-- `switch-minimal`: any non-canonical source form (wrong arity or
      non-expression cases argument) is reported as
      `IncorrectNumberOfArguments`, matching the executable evaluator's
      direct pattern split. -/
  | switch_minimal_bad_shape (atom type_ : Atom) (b : Bindings)
      (tail : List Atom)
      (h_shape : atom = .expression (.symbol "switch-minimal" :: tail))
      (h_noncanonical : ¬ ∃ scrut branches, tail = [scrut, .expression branches])
      (h_not_error : isErrorAtom atom = false) :
      MettaCall space dispatch (live := live) atom type_ b (mkError atom .incorrectNumberOfArguments, b)
  /-- Spec lines 365-368: Grounded op, native call succeeds → recurse with metta.
      ```
      if <$op is executable grounded atom>:
          match <call $op native function>: case Ok($results):
              $results = [metta($r, $type, $space, $mb)
                          for ($r, $rb) in $results
                          for $mb in merge_bindings($rb, $bindings)]
      ``` -/
  | grounded_ok (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (nativeResults : ResultSet) (nativeResult : ResultPair)
      (merged : Bindings) (finalResult : ResultPair) (fuel : Nat)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_unify : op ≠ .symbol "unify")
      (h_not_switch : op ≠ .symbol "switch-minimal")
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .ok nativeResults)
      (h_native_mem : nativeResult ∈ nativeResults)
      (h_merge : merged ∈ mergeBindings nativeResult.2 b fuel)
      (h_recurse : OrdinaryCallReturnRel space dispatch atom nativeResult.1 type_ merged finalResult live) :
      MettaCall space dispatch (live := live) atom type_ b finalResult
  /-- Spec lines 369-370: Grounded op, runtime error.
      ```
      case RuntimeError($message):
          return [(Error $atom <message>)]
      ``` -/
  | grounded_runtime_error (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom) (msg : String)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_unify : op ≠ .symbol "unify")
      (h_not_switch : op ≠ .symbol "switch-minimal")
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .runtimeError msg) :
      MettaCall space dispatch (live := live) atom type_ b
        (Atom.error atom (.symbol msg), b)
  /-- Spec lines 371-372: Grounded op, NoReduce.
      ```
      case NoReduce: return [($atom, $bindings)]
      ``` -/
  | grounded_no_reduce (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_unify : op ≠ .symbol "unify")
      (h_not_switch : op ≠ .symbol "switch-minimal")
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .noReduce) :
      MettaCall space dispatch (live := live) atom type_ b (atom, b)
  /-- Spec lines 371-374: Grounded op, IncorrectArgument.
      ```
      case IncorrectArgument: return [($atom, $bindings)]
      ``` -/
  | grounded_incorrect_arg (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_unify : op ≠ .symbol "unify")
      (h_not_switch : op ≠ .symbol "switch-minimal")
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .incorrectArgument) :
      MettaCall space dispatch (live := live) atom type_ b (atom, b)
  /-- Spec lines 365-368 + 386-387: Grounded op returns empty result list → Empty.
      When `dispatch.execute` returns `.ok []`, the result list is empty, so
      the final `if len($results) == 0` branch applies.
      ```
      case Ok($results):
          ... (but $results is empty)
      if len($results) == 0:
          return [(Empty, $bindings)]
      ``` -/
  | grounded_empty_results (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_unify : op ≠ .symbol "unify")
      (h_not_switch : op ≠ .symbol "switch-minimal")
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .ok []) :
      MettaCall space dispatch (live := live) atom type_ b (Atom.empty, b)
  /-- Spec lines 376-382: Non-grounded, equation match found → recurse.
      ```
      $query_output = query($space, (= $atom $X))
      if len($query_output) > 0:
          for $rb in $query_output:
              for $mb in merge_bindings($rb, $bindings):
                  if not(<$mb has loop bindings>) and <$mb contains value for $X>:
                      $x = <value of $X from $mb>
                      $results += [metta($x, $type, $space, $mb)]
      ``` -/
  | equation_match (atom type_ : Atom) (b : Bindings)
      (rhs : Atom) (queryBindings merged : Bindings)
      (finalResult : ResultPair) (fuel : Nat)
      (h_not_error : isErrorAtom atom = false)
      (h_not_grounded : match atom with
        | .expression (op :: _) =>
            dispatch.isExecutable op = false ∧
            op ≠ .symbol "unify" ∧
            op ≠ .symbol "switch-minimal"
        | _ => True)
      {avoid : List String}
      (h_cover : CoversEvaluation avoid live atom type_ b)
      (h_query : (rhs, queryBindings) ∈ queryEquationsAvoiding avoid space atom fuel)
      (h_merge : merged ∈ mergeBindings queryBindings b fuel)
      (h_no_loop : merged.hasLoop = false)
      (h_recurse : OrdinaryCallReturnRel space dispatch atom (merged.applyFull rhs fuel) type_ merged finalResult live) :
      MettaCall space dispatch (live := live) atom type_ b finalResult
  /-- Spec lines 383-384: Non-grounded, no equation matches → return unchanged.
      ```
      else:
          $results += [($atom, $bindings)]
      ``` -/
  | no_match (atom type_ : Atom) (b : Bindings) (fuel : Nat)
      (h_not_error : isErrorAtom atom = false)
      (h_not_grounded : match atom with
        | .expression (op :: _) =>
            dispatch.isExecutable op = false ∧
            op ≠ .symbol "unify" ∧
            op ≠ .symbol "switch-minimal"
        | _ => True)
      {avoid : List String}
      (h_cover : CoversEvaluation avoid live atom type_ b)
      (h_no_eqs : queryEquationsAvoiding avoid space atom fuel = []) :
      MettaCall space dispatch (live := live) atom type_ b (atom, b)
  /-- Spec lines 386-387: All paths produced no results → return Empty.
      ```
      if len($results) == 0:
          return [(Empty, $bindings)]
      ``` -/
  | empty_results (atom type_ : Atom) (b : Bindings) (fuel : Nat)
      (h_not_error : isErrorAtom atom = false)
      (h_not_grounded : match atom with
        | .expression (op :: _) =>
            dispatch.isExecutable op = false ∧
            op ≠ .symbol "unify" ∧
            op ≠ .symbol "switch-minimal"
        | _ => True)
      {avoid : List String}
      (h_cover : CoversEvaluation avoid live atom type_ b)
      (h_has_eqs : queryEquationsAvoiding avoid space atom fuel ≠ [])
      (h_all_filtered : ∀ (rhs : Atom) (qb mb : Bindings),
        (rhs, qb) ∈ queryEquationsAvoiding avoid space atom fuel →
        mb ∈ mergeBindings qb b fuel →
        mb.hasLoop = true) :
      MettaCall space dispatch (live := live) atom type_ b (Atom.empty, b)


/-- Return a raw ordinary-call result under the saved demand. The call is the
post-argument invocation. Minimal instructions and completed producers retain
their own distinct return boundaries. -/
inductive OrdinaryCallReturnRel (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Atom → Bindings → ResultPair → (live : List Atom := []) → Prop where
  | notReducible (original value type_ : Atom) (bindings : Bindings)
      (same : value = Atom.notReducible) :
      OrdinaryCallReturnRel space dispatch original value type_ bindings (original, bindings) live
  | stopped (original value type_ : Atom) (bindings : Bindings)
      (different : value ≠ Atom.notReducible) (stopped : isEmptyOrError value = true) :
      OrdinaryCallReturnRel space dispatch original value type_ bindings (value, bindings) live
  | evaluated (original value type_ : Atom) (bindings : Bindings) (result : ResultPair)
      (different : value ≠ Atom.notReducible) (running : isEmptyOrError value = false)
      (child : EvalAtom space dispatch value type_ bindings result live) :
      OrdinaryCallReturnRel space dispatch original value type_ bindings result live

end

/-! ## Ordinary return observations -/

/-- A raw protocol reply restores the saved invocation and retains its reached
bindings. It is never evaluated as the bare protocol symbol. -/
theorem OrdinaryCallReturnRel.notReducible_iff
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {original type_ : Atom} {bindings : Bindings} {result : ResultPair} :
    OrdinaryCallReturnRel space dispatch original Atom.notReducible type_ bindings result live ↔
      result = (original, bindings) := by
  constructor
  · intro returned
    cases returned with
    | notReducible => rfl
    | stopped _ _ _ _ different _ => exact (different rfl).elim
    | evaluated _ _ _ _ _ different _ _ => exact (different rfl).elim
  · rintro rfl
    exact .notReducible _ _ _ _ rfl

/-- Ordinary successor evaluation composes across a call boundary only when
its raw result is not the protocol sentinel. Stopped values retain their exact
pair rather than introducing a recursive evaluation obligation. -/
theorem OrdinaryCallReturnRel.of_eval
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {original value type_ : Atom} {bindings : Bindings} {result : ResultPair}
    (different : value ≠ Atom.notReducible)
    (evaluation : EvalAtom space dispatch value type_ bindings result live) :
    OrdinaryCallReturnRel space dispatch original value type_ bindings result live := by
  by_cases stopped : isEmptyOrError value = true
  · have same : result = (value, bindings) := by
      cases evaluation <;> simp_all
    subst result
    exact .stopped _ _ _ _ different stopped
  · exact .evaluated _ _ _ _ _ different (by simpa using stopped) evaluation

/-- An Atom demand holds ordinary raw data after the call-return protocol has
been handled. In particular, this is not the same as holding the raw sentinel
before the call boundary. -/
theorem OrdinaryCallReturnRel.atom_type
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    (original value : Atom) (bindings : Bindings) :
    OrdinaryCallReturnRel space dispatch original value Atom.atomType bindings
      ((if value = Atom.notReducible then original else value), bindings) live := by
  by_cases same : value = Atom.notReducible
  · simp only [same]
    exact .notReducible _ _ _ _ rfl
  · simp only [if_neg same]
    by_cases stopped : isEmptyOrError value = true
    · exact .stopped _ _ _ _ same stopped
    · exact .evaluated _ _ _ _ _ same (by simpa using stopped)
        (.type_pass _ _ _ (by simpa using stopped) (Or.inl rfl))

/-! ## Context transport

Only names held by a continuation affect equation freshening. Replacing a
continuation by one with the same variable inventory preserves every judgment.
-/

private theorem coversEvaluation_of_scope_eq
    {avoid : List String} {live other : List Atom} {atom type_ : Atom} {b : Bindings}
    (covered : CoversEvaluation avoid live atom type_ b)
    (same : atomListVariables live = atomListVariables other) :
    CoversEvaluation avoid other atom type_ b := by
  simpa only [CoversEvaluation, equationScope, same] using covered

section
local macro "transport_scope " same:ident ea:ident ie:ident ifn:ident ia:ident it:ident mc:ident cr:ident : tactic => `(tactic|
  all_goals first
    | assumption
    | (apply coversEvaluation_of_scope_eq
       · assumption
       · exact $same)
    | (apply ($ea)
       · assumption
       · simp only [atomListVariables_append, atomListVariables, ($same)])
    | (apply ($ie)
       · assumption
       · simp only [atomListVariables_append, atomListVariables, ($same)])
    | (apply ($ifn)
       · assumption
       · simp only [atomListVariables_append, atomListVariables, ($same)])
    | (apply ($ia)
       · assumption
       · simp only [atomListVariables_append, atomListVariables, ($same)])
    | (apply ($it)
       · assumption
       · simp only [atomListVariables_append, atomListVariables, ($same)])
    | (apply ($mc)
       · assumption
       · simp only [atomListVariables_append, atomListVariables, ($same)])
    | (apply ($cr)
       · assumption
       · simp only [atomListVariables_append, atomListVariables, ($same)])

)

set_option linter.unusedSimpArgs false in
mutual

theorem EvalAtom.scope_congr {space : Space} {dispatch : GroundedDispatch}
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    {live other : List Atom} (h : EvalAtom space dispatch atom type_ b r live)
    (same : atomListVariables live = atomListVariables other) :
    EvalAtom space dispatch atom type_ b r other := by
  match h with
  | .empty_or_error .. =>
      apply EvalAtom.empty_or_error
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .type_pass .. =>
      apply EvalAtom.type_pass
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .type_cast .. =>
      apply EvalAtom.type_cast
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .interpret_success .. =>
      apply EvalAtom.interpret_success
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .interpret_error .. =>
      apply EvalAtom.interpret_error
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr

termination_by structural h

theorem InterpretExpression.scope_congr {space : Space} {dispatch : GroundedDispatch}
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    {live other : List Atom} (h : InterpretExpression space dispatch atom type_ b r live)
    (same : atomListVariables live = atomListVariables other) :
    InterpretExpression space dispatch atom type_ b r other := by
  match h with
  | .function_path .. =>
      apply InterpretExpression.function_path
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .tuple_path .. =>
      apply InterpretExpression.tuple_path
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .op_type_error .. =>
      apply InterpretExpression.op_type_error
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr

termination_by structural h

theorem InterpretFunction.scope_congr {space : Space} {dispatch : GroundedDispatch}
    {atom opType retType : Atom} {b : Bindings} {r : ResultPair}
    {live other : List Atom} (h : InterpretFunction space dispatch atom opType retType b r live)
    (same : atomListVariables live = atomListVariables other) :
    InterpretFunction space dispatch atom opType retType b r other := by
  match h with
  | .head_error .. =>
      apply InterpretFunction.head_error
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .head_ok_tail_error .. =>
      apply InterpretFunction.head_ok_tail_error
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .head_ok_tail_ok .. =>
      apply InterpretFunction.head_ok_tail_ok
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr

termination_by structural h

theorem InterpretArgs.scope_congr {space : Space} {dispatch : GroundedDispatch}
    {args types : List Atom} {b : Bindings} {r : ResultPair}
    {live other : List Atom} (h : InterpretArgs space dispatch args types b r live)
    (same : atomListVariables live = atomListVariables other) :
    InterpretArgs space dispatch args types b r other := by
  match h with
  | .nil .. =>
      apply InterpretArgs.nil
  | .head_changed_error .. =>
      apply InterpretArgs.head_changed_error
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .cons_tail_error .. =>
      apply InterpretArgs.cons_tail_error
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .cons_ok .. =>
      apply InterpretArgs.cons_ok
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr

termination_by structural h

theorem InterpretTuple.scope_congr {space : Space} {dispatch : GroundedDispatch}
    {atom : Atom} {b : Bindings} {r : ResultPair}
    {live other : List Atom} (h : InterpretTuple space dispatch atom b r live)
    (same : atomListVariables live = atomListVariables other) :
    InterpretTuple space dispatch atom b r other := by
  match h with
  | .nil .. =>
      apply InterpretTuple.nil
  | .singleton .. =>
      apply InterpretTuple.singleton
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .singleton_error .. =>
      apply InterpretTuple.singleton_error
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .head_error .. =>
      apply InterpretTuple.head_error
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .tail_error .. =>
      apply InterpretTuple.tail_error
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .success .. =>
      apply InterpretTuple.success
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr

termination_by structural h

theorem MettaCall.scope_congr {space : Space} {dispatch : GroundedDispatch}
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    {live other : List Atom} (h : MettaCall space dispatch atom type_ b r live)
    (same : atomListVariables live = atomListVariables other) :
    MettaCall space dispatch atom type_ b r other := by
  match h with
  | .error_passthrough .. =>
      apply MettaCall.error_passthrough
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .unify_success_raw .. =>
      apply MettaCall.unify_success_raw
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .unify_no_match_raw .. =>
      apply MettaCall.unify_no_match_raw
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .unify_bad_arity .. =>
      apply MettaCall.unify_bad_arity
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .switch_minimal_result .. =>
      apply MettaCall.switch_minimal_result
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .switch_minimal_bad_shape .. =>
      apply MettaCall.switch_minimal_bad_shape
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .grounded_ok .. =>
      apply MettaCall.grounded_ok
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .grounded_runtime_error .. =>
      apply MettaCall.grounded_runtime_error
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .grounded_no_reduce .. =>
      apply MettaCall.grounded_no_reduce
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .grounded_incorrect_arg .. =>
      apply MettaCall.grounded_incorrect_arg
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .grounded_empty_results .. =>
      apply MettaCall.grounded_empty_results
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .equation_match .. =>
      apply MettaCall.equation_match
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .no_match .. =>
      apply MettaCall.no_match
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr
  | .empty_results .. =>
      apply MettaCall.empty_results
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr

termination_by structural h


theorem OrdinaryCallReturnRel.scope_congr {space : Space} {dispatch : GroundedDispatch}
    {original value type_ : Atom} {bindings : Bindings} {result : ResultPair}
    {live other : List Atom}
    (h : OrdinaryCallReturnRel space dispatch original value type_ bindings result live)
    (same : atomListVariables live = atomListVariables other) :
    OrdinaryCallReturnRel space dispatch original value type_ bindings result other := by
  match h with
  | .notReducible .. =>
      apply OrdinaryCallReturnRel.notReducible
      assumption
  | .stopped .. =>
      apply OrdinaryCallReturnRel.stopped <;> assumption
  | .evaluated .. =>
      apply OrdinaryCallReturnRel.evaluated
      transport_scope same EvalAtom.scope_congr InterpretExpression.scope_congr
        InterpretFunction.scope_congr InterpretArgs.scope_congr InterpretTuple.scope_congr
        MettaCall.scope_congr OrdinaryCallReturnRel.scope_congr

end

end

/-! ## Success-Priority Filtering

The spec (lines 129-136) returns successes over errors. Since this requires
a negative condition ("no success derivation exists"), it cannot live inside
the mutual inductive. We define it as a separate Prop. -/

/-- Global filtered soundness (completeness target).
    A result is "filtered-valid" if either:
    1. It's a success (non-error) result from `interpret_success`, OR
    2. It's an error result AND no success derivation exists for this input.
    Requires: fuel-indexed filtered + completeness + monotonicity.
    Not provable from soundness alone — see Codex counterexample:
    `evalAtom ... fuel=7` → error, `evalAtom ... fuel=11` → success. -/
def EvalAtomFiltered (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  EvalAtom space dispatch (live := live) atom type_ b r ∧
  (isErrorAtom r.1 = true →
    ∀ r' : ResultPair,
      InterpretExpression space dispatch (live := live) atom type_ b r' →
      isErrorAtom r'.1 = true)

-- Introduce notation for readability in downstream files
set_option quotPrecheck false in
scoped notation:50 space " ⊢ₘ " atom " : " type_ " | " b " ⇒ " r =>
  EvalAtom space GroundedDispatch.none atom type_ b r

end Mettapedia.Languages.MeTTa.HE
