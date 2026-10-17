import Mettapedia.Languages.MeTTa.HE.Space

/-!
# HE MeTTa Type Checking

Type checking and type casting for the HE interpreter.

## Source Precedence
1. `interpreter.rs` (ground truth)
2. `metta.md` lines 275-450 (spec)

The runtime matches expected types before actual types and reports argument
positions starting at one. These two details differ from the pseudocode's
cast operand order and its `idx - 1` error position.

## Main Definitions
* `checkArgumentType` - Check argument type (metta.md lines 429-450)
* `checkIfFunctionTypeIsApplicable` - Check function type applicability (metta.md lines 384-427)
* `typeCast` - Cast atom to expected type (metta.md lines 275-296)
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Type queries receive the reached bindings and expected type. Raw declaration
inspection is the historical instance; invocation checking may instantiate it. -/
abbrev TypeLookup := Bindings → Atom → Atom → List Atom

def rawTypeLookup (space : Space) : TypeLookup :=
  fun _ subject _ => getAtomTypes space subject

/-! ## Check Argument Type

Ref: metta.md lines 429-450 "Check argument type (check_argument_type)".
Returns a list of `Sum Atom Bindings` where:
- `Sum.inl t` means type mismatch (actual type `t`)
- `Sum.inr b` means type match with resulting bindings `b` -/

/-- Check if an argument has the expected type.
    Ref: metta.md lines 429-450. -/
def checkArgumentType (space : Space) (arg expectedType : Atom) (b : Bindings)
    (fuel : Nat := 100) (lookup : TypeLookup := rawTypeLookup space) : List (Sum Atom Bindings) :=
  let actualTypes := lookup b arg expectedType
  actualTypes.flatMap fun t =>
    let matched := matchTypes expectedType t b fuel
    if matched.isEmpty then
      [Sum.inl t]  -- type mismatch: report actual type
    else
      matched.map Sum.inr

/-! ## Check Function Type Applicability

Ref: metta.md lines 384-427 "Check if function type is applicable".
Returns:
- `Sum.inl errors` if function type is NOT applicable (with error atoms)
- `Sum.inr bindings` if function type IS applicable (with resulting bindings) -/

/-- Check if a function type is applicable to an expression.
    Ref: metta.md lines 384-427.

    Checks:
    1. Argument count matches
    2. Each argument has correct type
    3. Return type matches expected type -/
def checkIfFunctionTypeIsApplicable (expr funcType expectedType : Atom)
    (space : Space) (b : Bindings) (fuel : Nat)
    (lookup : TypeLookup := rawTypeLookup space) : Sum (List Atom) (List Bindings) :=
  match fuel with
  | 0 => .inl []
  | n + 1 =>
    -- Extract expression args (everything after head/operator)
    let exprArgs := match expr with
      | .expression (_ :: args) => args
      | _ => []
    -- Extract function type arg types
    let funcArgTypes := match getFunctionArgTypes funcType with
      | some ts => ts
      | none => []
    -- Extract function return type
    let funcRetType := match getFunctionRetType funcType with
      | some t => t
      | none => Atom.undefinedType

    -- Step 1: Check argument count (metta.md line 397)
    if exprArgs.length != funcArgTypes.length then
      .inl [mkError expr .incorrectNumberOfArguments]
    else
      -- Step 2: Check each argument type (metta.md lines 400-412)
      let (errors, results) := checkArgLoop exprArgs funcArgTypes expr [b] [] space n 1 lookup

      -- Step 3: Check return type (metta.md lines 414-421)
      if results.isEmpty then
        .inl errors
      else
        let (retErrors, retResults) := results.foldl (fun (errs, succs) r =>
          let matched := matchTypes expectedType funcRetType r n
          if matched.isEmpty then
            (errs ++ [mkError expr (.badType expectedType funcRetType)], succs)
          else
            (errs, succs ++ matched)
        ) (errors, [])

        -- metta.md lines 423-426
        if retResults.isEmpty then
          .inl retErrors
        else
          .inr retResults
where
  /-- Process each argument position, accumulating errors and successful bindings. -/
  checkArgLoop (args argTypes : List Atom) (expr : Atom) (results errors : List _)
      (space : Space) (fuel idx : Nat) (lookup : TypeLookup := rawTypeLookup space) :
      List Atom × List Bindings :=
    match args, argTypes with
    | [], [] => (errors, results)
    | arg :: args', argTy :: argTys' =>
      let (newErrors, newResults) := results.foldl (fun (errs, succs) r =>
        let checks := checkArgumentType space arg argTy r fuel lookup
        checks.foldl (fun (errs', succs') c =>
          match c with
          | .inl t =>
            (errs' ++ [mkError expr (.badArgType idx argTy t)], succs')
          | .inr b =>
            (errs', succs' ++ [b])
        ) (errs, succs)
      ) (errors, [])
      checkArgLoop args' argTys' expr newResults newErrors space fuel (idx + 1) lookup
    | _, _ => (errors, results)  -- length mismatch (shouldn't happen)

/-! ## Type Cast

Ref: metta.md lines 275-296 "Cast types (type_cast)".
Gets all types for atom from space, tries to match each against expected type.
Returns on first successful match; accumulates errors for failures. -/

/-- Cast an atom to an expected type.
    Ref: metta.md lines 275-296. -/
def typeCast (atom expectedType : Atom) (space : Space) (b : Bindings)
    (fuel : Nat := 100) (lookup : TypeLookup := rawTypeLookup space) : ResultSet :=
  let types := lookup b atom expectedType
  typeCastLoop types atom expectedType b fuel []
where
  /-- Iterate over types; return on first match, accumulate errors.
      Ref: metta.md lines 288-295. -/
  typeCastLoop (types : List Atom) (atom expectedType : Atom)
      (b : Bindings) (fuel : Nat) (noMatch : List Atom) : ResultSet :=
    match types with
    | [] =>
      -- No types matched: return errors for all
      noMatch.map fun t =>
        (mkError atom (.badType expectedType t), b)
    | t :: rest =>
      let mtch := matchTypes expectedType t b fuel
      if mtch.isEmpty then
        -- This type didn't match; record it and continue
        typeCastLoop rest atom expectedType b fuel (noMatch ++ [t])
      else
        -- Match found! Return atom with all successful bindings
        -- (metta.md line 294: early return)
        mtch.map fun m => (atom, m)


/-! ## Coverage of matching inside type checking

A completed type error requires completed matching, including all failed
alternatives that led to the error. These programs expose those actual calls;
the equations below check them against the existing type checker.
-/
namespace TypeCheckDepth

open Mettapedia.Machines.ReadOnlyQuery
open MatchDepth (Query typesQuery)

def argumentQuery (space : Space) (arg expectedType : Atom) (b : Bindings)
    (lookup : TypeLookup := rawTypeLookup space) :
    Query (List (Sum Atom Bindings)) :=
  flatTraverse (lookup b arg expectedType) fun t =>
    map (fun matched => if matched.isEmpty then [Sum.inl t] else matched.map Sum.inr)
      (typesQuery expectedType t b)

theorem run_argumentQuery (depth : Nat) (space : Space)
    (arg expectedType : Atom) (b : Bindings) (lookup : TypeLookup := rawTypeLookup space) :
    (run (evalMatch depth) (argumentQuery space arg expectedType b lookup)).answer =
      checkArgumentType space arg expectedType b depth lookup := by
  simp [argumentQuery, run_flatTraverse, run_map, MatchDepth.run_typesQuery,
    checkArgumentType]

def argumentsQuery (args argTypes : List Atom) (expr : Atom)
    (results : List Bindings) (errors : List Atom) (space : Space) (idx : Nat)
    (lookup : TypeLookup := rawTypeLookup space) :
    Query (List Atom × List Bindings) :=
  match args, argTypes with
  | [], [] => .pure (errors, results)
  | arg :: args', argTy :: argTys' =>
      bind (foldQueries results (errors, []) fun (errs, succs) r =>
        map (fun checks => checks.foldl (fun (errs', succs') c =>
          match c with
          | .inl t => (errs' ++ [mkError expr (.badArgType idx argTy t)], succs')
          | .inr b => (errs', succs' ++ [b])) (errs, succs))
          (argumentQuery space arg argTy r lookup)) fun (newErrors, newResults) =>
      argumentsQuery args' argTys' expr newResults newErrors space (idx + 1) lookup
  | _, _ => .pure (errors, results)

theorem run_argumentsQuery (depth : Nat) (args argTypes : List Atom) (expr : Atom)
    (results : List Bindings) (errors : List Atom) (space : Space) (idx : Nat)
    (lookup : TypeLookup := rawTypeLookup space) :
    (run (evalMatch depth)
      (argumentsQuery args argTypes expr results errors space idx lookup)).answer =
      checkIfFunctionTypeIsApplicable.checkArgLoop args argTypes expr results errors
        space depth idx lookup := by
  induction args generalizing argTypes results errors idx with
  | nil => cases argTypes <;> rfl
  | cons arg args ih =>
      cases argTypes with
      | nil => rfl
      | cons argTy argTypes =>
          simp [argumentsQuery, run_bind, run_foldQueries, run_map, run_argumentQuery,
            checkIfFunctionTypeIsApplicable.checkArgLoop, ih]

def functionQuery (expr funcType expectedType : Atom) (space : Space) (b : Bindings)
    (lookup : TypeLookup := rawTypeLookup space) :
    Query (Sum (List Atom) (List Bindings)) :=
  let exprArgs := match expr with | .expression (_ :: args) => args | _ => []
  let funcArgTypes := match getFunctionArgTypes funcType with | some ts => ts | none => []
  let funcRetType := match getFunctionRetType funcType with
    | some t => t | none => Atom.undefinedType
  if exprArgs.length != funcArgTypes.length then
    .pure (.inl [mkError expr .incorrectNumberOfArguments])
  else bind (argumentsQuery exprArgs funcArgTypes expr [b] [] space 1 lookup)
    fun (errors, results) =>
    if results.isEmpty then .pure (.inl errors)
    else map (fun (retErrors, retResults) =>
      if retResults.isEmpty then Sum.inl retErrors else Sum.inr retResults)
      (foldQueries results (errors, []) fun (errs, succs) r =>
        map (fun matched => if matched.isEmpty then
          (errs ++ [mkError expr (.badType expectedType funcRetType)], succs)
          else (errs, succs ++ matched)) (typesQuery expectedType funcRetType r))

set_option maxRecDepth 2000 in
theorem run_functionQuery (depth : Nat) (expr funcType expectedType : Atom)
    (space : Space) (b : Bindings) (lookup : TypeLookup := rawTypeLookup space) :
    (run (evalMatch depth) (functionQuery expr funcType expectedType space b lookup)).answer =
      checkIfFunctionTypeIsApplicable expr funcType expectedType space b (depth + 1) lookup := by
  simp only [functionQuery, checkIfFunctionTypeIsApplicable]
  generalize (match expr with | .expression (_ :: args) => args | _ => []) = args
  generalize (match getFunctionArgTypes funcType with | some ts => ts | none => []) = argTypes
  generalize (match getFunctionRetType funcType with
    | some t => t | none => Atom.undefinedType) = retType
  split
  · rfl
  · simp only [run_bind, run_argumentsQuery]
    split
    · rfl
    · simp only [run_map, run_foldQueries, MatchDepth.run_typesQuery]

def castLoopQuery (types : List Atom) (atom expectedType : Atom)
    (b : Bindings) (noMatch : List Atom) : Query ResultSet :=
  match types with
  | [] => .pure (noMatch.map fun t => (mkError atom (.badType expectedType t), b))
  | t :: rest => bind (typesQuery expectedType t b) fun matched =>
      if matched.isEmpty then castLoopQuery rest atom expectedType b (noMatch ++ [t])
      else .pure (matched.map fun m => (atom, m))

theorem run_castLoopQuery (depth : Nat) (types : List Atom) (atom expectedType : Atom)
    (b : Bindings) (noMatch : List Atom) :
    (run (evalMatch depth) (castLoopQuery types atom expectedType b noMatch)).answer =
      typeCast.typeCastLoop types atom expectedType b depth noMatch := by
  induction types generalizing noMatch with
  | nil => rfl
  | cons t rest ih =>
      simp only [castLoopQuery, run_bind, MatchDepth.run_typesQuery,
        typeCast.typeCastLoop]
      split <;> simp [run, ih]

def castQuery (atom expectedType : Atom) (space : Space) (b : Bindings)
    (lookup : TypeLookup := rawTypeLookup space) : Query ResultSet :=
  castLoopQuery (lookup b atom expectedType) atom expectedType b []

theorem run_castQuery (depth : Nat) (atom expectedType : Atom)
    (space : Space) (b : Bindings) (lookup : TypeLookup := rawTypeLookup space) :
    (run (evalMatch depth) (castQuery atom expectedType space b lookup)).answer =
      typeCast atom expectedType space b depth lookup := run_castLoopQuery _ _ _ _ _ _

end TypeCheckDepth

def typeCastCovered (atom expectedType : Atom) (space : Space) (b : Bindings)
    (depth : Nat) (lookup : TypeLookup := rawTypeLookup space) : Bool :=
  MatchDepth.queryCovered depth (TypeCheckDepth.castQuery atom expectedType space b lookup)

theorem typeCastCovered_stable (atom expectedType : Atom) (space : Space) (b : Bindings)
    (depth extra : Nat) {lookup : TypeLookup}
    (covered : typeCastCovered atom expectedType space b depth lookup = true) :
    typeCast atom expectedType space b (depth + extra) lookup =
      typeCast atom expectedType space b depth lookup := by
  rw [← TypeCheckDepth.run_castQuery (depth + extra) atom expectedType space b lookup,
    ← TypeCheckDepth.run_castQuery depth atom expectedType space b lookup]
  exact congrArg Mettapedia.Machines.ReadOnlyQuery.Observation.answer
    (MatchDepth.queryCovered_stable depth extra _ covered)

def functionTypeCovered (expr funcType expectedType : Atom) (space : Space) (b : Bindings)
    (fuel : Nat) (lookup : TypeLookup := rawTypeLookup space) : Bool :=
  match fuel with
  | 0 => false
  | depth + 1 => MatchDepth.queryCovered depth
      (TypeCheckDepth.functionQuery expr funcType expectedType space b lookup)

theorem functionTypeCovered_stable (expr funcType expectedType : Atom)
    (space : Space) (b : Bindings) (depth extra : Nat) {lookup : TypeLookup}
    (covered : functionTypeCovered expr funcType expectedType space b depth lookup = true) :
    checkIfFunctionTypeIsApplicable expr funcType expectedType space b (depth + extra) lookup =
      checkIfFunctionTypeIsApplicable expr funcType expectedType space b depth lookup := by
  cases depth with
  | zero => simp [functionTypeCovered] at covered
  | succ depth =>
      rw [Nat.succ_add,
        ← TypeCheckDepth.run_functionQuery (depth + extra) expr funcType expectedType space b lookup,
        ← TypeCheckDepth.run_functionQuery depth expr funcType expectedType space b lookup]
      exact congrArg Mettapedia.Machines.ReadOnlyQuery.Observation.answer
        (MatchDepth.queryCovered_stable depth extra _ covered)

namespace TypeCheckDepth.Controls

def space : Space := Space.ofList [
  .expression [.symbol ":", .symbol "x", .symbol "Int"]]

theorem truncated_cast_not_error_evidence :
    typeCastCovered (.symbol "x") (.symbol "Bool") space Bindings.empty 0 = false := by
  decide +kernel

theorem completed_cast_error_covered :
    typeCastCovered (.symbol "x") (.symbol "Bool") space Bindings.empty 2 = true := by
  decide +kernel

end TypeCheckDepth.Controls

/-! ## Unit Tests -/

section Tests

private def testSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "x", .symbol "Int"],
    .expression [.symbol ":", .symbol "y", .symbol "Int"],
    .expression [.symbol ":", .symbol "z", .symbol "Bool"],
    .expression [.symbol ":", .symbol "add",
      .expression [.symbol "->", .symbol "Int", .symbol "Int", .symbol "Int"]]
  ]

-- typeCast: matching type
example : typeCast (.symbol "x") (.symbol "Int") testSpace Bindings.empty 10 =
    [(.symbol "x", Bindings.empty)] := rfl

-- typeCast: any type (%Undefined%)
example : typeCast (.symbol "x") Atom.undefinedType testSpace Bindings.empty 10 =
    [(.symbol "x", Bindings.empty)] := rfl

-- typeCast: type mismatch
example : typeCast (.symbol "z") (.symbol "Int") testSpace Bindings.empty 10 =
    [(mkError (.symbol "z") (.badType (.symbol "Int") (.symbol "Bool")),
      Bindings.empty)] := rfl

-- typeCast: unknown atom gets %Undefined% type, which matches anything
example : typeCast (.symbol "unknown") (.symbol "Foo") testSpace Bindings.empty 10 =
    [(.symbol "unknown", Bindings.empty)] := rfl

-- checkArgumentType
example : checkArgumentType testSpace (.symbol "x") (.symbol "Int") Bindings.empty 10 =
    [Sum.inr Bindings.empty] := rfl
example : checkArgumentType testSpace (.symbol "z") (.symbol "Int") Bindings.empty 10 =
    [Sum.inl (.symbol "Bool")] := rfl

-- checkIfFunctionTypeIsApplicable: correct args
example : checkIfFunctionTypeIsApplicable
    (.expression [.symbol "add", .symbol "x", .symbol "y"])
    (.expression [.symbol "->", .symbol "Int", .symbol "Int", .symbol "Int"])
    Atom.undefinedType testSpace Bindings.empty 10 =
    .inr [Bindings.empty] := rfl

-- checkIfFunctionTypeIsApplicable: wrong arg count
example : checkIfFunctionTypeIsApplicable
    (.expression [.symbol "add", .symbol "x"])
    (.expression [.symbol "->", .symbol "Int", .symbol "Int", .symbol "Int"])
    Atom.undefinedType testSpace Bindings.empty 10 =
    .inl [mkError (.expression [.symbol "add", .symbol "x"]) .incorrectNumberOfArguments] := rfl

-- A later rejected argument keeps its one-based source position.
example : checkIfFunctionTypeIsApplicable
    (.expression [.symbol "add", .symbol "x", .symbol "z"])
    (.expression [.symbol "->", .symbol "Int", .symbol "Int", .symbol "Int"])
    Atom.undefinedType testSpace Bindings.empty 10 =
    .inl [mkError (.expression [.symbol "add", .symbol "x", .symbol "z"])
      (.badArgType 2 (.symbol "Int") (.symbol "Bool"))] := rfl

end Tests

end Mettapedia.Languages.MeTTa.HE
