-- LLM primer (proof engineering in this file):
-- * The evaluator is a mutual fuel recursion; unfold one layer with `rw [evalAtom]`
--   (`interpretExpression`, `interpretFunction`, `interpretArgs`, `invoke`) at a
--   fuel written `fuel + 1`.
-- * Keep fuel as `base + k + c` with one base on both sides: `5 + k + 1 + 1` and
--   `5 + k + 2` unify, `k + 6` and `5 + k + 1` time out in `whnf`. Rewrite with
--   `show … = … by omega` first.
-- * A concrete matcher or cast at symbolic fuel: `matchCovered_stable`,
--   `typeCastCovered_stable`, `functionTypeCovered_stable` with `decide +kernel`.
-- * Recursion over the nested `Atom` must be mutual and structural (as `matchFuel`)
--   for `decide` to reduce it; `List.map` recursion does not reduce in the kernel.
-- * `cases` on `Completed` solves its index; for `CompletedArguments` at concrete
--   parameters use `checked_head` / `head_cases`, since string literals in indices
--   do not unify.
import Mettapedia.Languages.MeTTa.HE.Eval
import Mettapedia.Machines.SharedSpineCost

/-!
# Completed values deliver themselves

A *completed value* is an application `(c v₁ … vₙ)` whose head symbol has exactly
one declared type, a ground arrow `(-> D₁ … Dₙ R)`; the head is neither `Empty`,
an executable grounded operation nor a minimal instruction; no stored equation
matches the value at any depth under any renaming; and every argument is its own
value under its parameter: held by an `Atom` parameter, a leaf, or a completed
value whose range the parameter accepts, with a parameter check that succeeds
exactly once and binds nothing.

## Main results

* `evalAtom_completed` (Theorem A): from some fuel on, uniformly in the
  bindings and the retained atoms, a completed value evaluated under
  `%Undefined%` or its range is exactly `[(value, bindings)]`.
  `evalAtom_completed_accepted` covers every expected type that accepts the range.
* Theorems C to H, in `Controls`, show the scope of such an answer, each at every
  sufficiently large fuel unless stated: it is a fact about one program
  (`completed_reopens_after_equation`, `completed_reopens_after_declaration`);
  equations whose body is `NotReducible` still multiply the answer
  (`notReducible_value_multiplies`); a produced value need not be its own value
  (`completedProvenance_not_fixpoint`); finite fuel changes the answer, at named
  fuels (`completed_fuel_sensitive`); an observation of an open value does not
  transfer between binding records (`completed_ground_only`); the expected type is
  part of the question (`evalAtom_completedMono_counterexample`).
* Every hypothesis of `Completed` is needed: dropping any one of them gives a
  concrete value whose evaluation is not `[(value, bindings)]`
  (`argumentChecked_once_required`, `argumentChecked_ground_required`,
  `value_fits_required`, `emptyHead_required`, `notExecutable_required`,
  `argument_value_required`, `arrow_ground_required`, `notInstruction_required`,
  with Theorems C, C′ and D for the equation and declaration hypotheses).
* `Sharing.certificates_linear_on_shared_spine`: on a value whose levels share
  their argument, memoized certification visits each distinct node once while
  the unfolded value has exponentially many occurrences.

## The CeTTa certificate rule

| CeTTa check | hypothesis here |
|---|---|
| one declared type, a variable-free arrow of the call's arity | `declared`, `ground` |
| each parameter `%Undefined%`, `Atom` or ground non-meta | part of `ground`; meta types need no exclusion |
| no equation matched the observed call | `noEquation`: no match at any depth under any renaming |
| head not a builtin nor a grounded operation | `notEmpty`, `notExecutable`, `notInstruction` |
| argument held by `Atom`, a symbol or scalar, or certified with the parameter as range | `held`, `leaf`, `value` with `fits` |
| issued at a single typed delivery: one applicability path, head outcome and argument path | `ArgumentChecked.once` |
| applicability bindings projected onto the variables visible in the call | `ArgumentChecked.rejectedGround`, `ground` |
| ground value | not needed for Theorem A; see `completed_ground_only` |

`completed_ground_only` shows that an empty equation query observed under one
binding record is no evidence of `NoEquationMatch` for an open value. For a
ground value the step from one observed query to `NoEquationMatch` is renaming
invariance of the matcher, which this file does not prove.

The evaluator here neither renames type variables of stored declarations nor
projects the bindings of a successful type match: they flow into the result. Its
ground conditions on parameters, range and rejected argument types stand in for
that projection; without them the incoming bindings come back extended
(`arrow_ground_required`, `argumentChecked_ground_required`). The single-path
condition is stated statically: a leaf with two accepted types passes its check
twice (`argumentChecked_once_required`).
-/

namespace Mettapedia.Languages.MeTTa.HE.CompletedDelivery

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE

/-! ## Type admission between ground types -/

/-- The decision `matchTypes` makes between ground types. -/
def accepts (expected actual : Atom) : Bool :=
  expected == Atom.undefinedType || expected == Atom.atomType ||
    actual == Atom.undefinedType || actual == Atom.atomType || expected == actual

theorem accepts_self (type : Atom) : accepts type type = true := by
  simp [accepts]

theorem accepts_undefined (actual : Atom) : accepts Atom.undefinedType actual = true := by
  simp [accepts]

theorem accepts_atom (actual : Atom) : accepts Atom.atomType actual = true := by
  simp [accepts]

/-! ## Fuel of a ground self-match -/

mutual
/-- Fuel after which matching a ground atom against itself has completed. -/
def matchFuel : Atom → Nat
  | .expression atoms => matchListFuel atoms + 1
  | _ => 1
/-- Fuel after which matching a ground list against itself has completed. -/
def matchListFuel : List Atom → Nat
  | [] => 1
  | atom :: atoms => max (matchFuel atom) (matchListFuel atoms) + 1
end

theorem one_le_matchFuel (atom : Atom) : 1 ≤ matchFuel atom := by
  cases atom <;> simp [matchFuel]

theorem one_le_matchListFuel (atoms : List Atom) : 1 ≤ matchListFuel atoms := by
  cases atoms <;> simp [matchListFuel]

theorem matchFuel_le_of_mem {atom : Atom} {atoms : List Atom} (member : atom ∈ atoms) :
    matchFuel atom ≤ matchListFuel atoms := by
  induction atoms with
  | nil => cases member
  | cons head tail ih =>
      simp only [matchListFuel]
      rcases List.mem_cons.mp member with rfl | member
      · omega
      · have := ih member
        omega

theorem matchFuel_lt_expression {atom : Atom} {atoms : List Atom} (member : atom ∈ atoms) :
    matchFuel atom < matchFuel (.expression atoms) := by
  have := matchFuel_le_of_mem member
  simp only [matchFuel]
  omega

/-! ## Ground variables -/

theorem atomVariables_nil_of_mem {atom : Atom} {atoms : List Atom}
    (ground : atomListVariables atoms = []) (member : atom ∈ atoms) : atomVariables atom = [] := by
  induction atoms with
  | nil => cases member
  | cons head tail ih =>
      simp only [atomListVariables, List.append_eq_nil_iff] at ground
      rcases List.mem_cons.mp member with rfl | member
      · exact ground.1
      · exact ih ground.2 member

/-! ## The executable matcher on ground atoms -/

theorem mergeBindings_empty (bindings : Bindings) (fuel : Nat) :
    mergeBindings bindings Bindings.empty (fuel + 1) = [bindings] := by
  simp [mergeBindings, Bindings.empty]

/-- A ground atom matches itself with the empty record once its fuel is spent. -/
theorem matchAtoms_self_ground : ∀ fuel : Nat,
    (∀ atom : Atom, atomVariables atom = [] → matchFuel atom ≤ fuel →
      matchAtoms atom atom fuel = [Bindings.empty]) ∧
    (∀ (atoms : List Atom) (acc : List Bindings), atomListVariables atoms = [] →
      matchListFuel atoms ≤ fuel → matchAtomsList atoms atoms acc fuel = acc)
  | 0 => by
      refine ⟨fun atom _ enough => ?_, fun atoms _ _ enough => ?_⟩
      · have := one_le_matchFuel atom
        omega
      · have := one_le_matchListFuel atoms
        omega
  | n + 1 => by
      obtain ⟨atomCase, listCase⟩ := matchAtoms_self_ground n
      refine ⟨fun atom ground enough => ?_, fun atoms acc ground enough => ?_⟩
      · cases atom with
        | symbol name =>
            simp [matchAtoms, getMetaType, Atom.symbolType, Bindings.hasLoop_empty]
        | var name => simp [atomVariables] at ground
        | grounded value =>
            simp [matchAtoms, getMetaType, Atom.groundedType, Bindings.hasLoop_empty]
        | expression atoms =>
            have inner : matchListFuel atoms ≤ n := by
              simp only [matchFuel] at enough
              omega
            rw [matchAtoms]
            simp only [getMetaType, Atom.expressionType]
            simp [listCase atoms [Bindings.empty] ground inner, Bindings.hasLoop_empty]
      · cases atoms with
        | nil => simp [matchAtomsList]
        | cons head tail =>
            simp only [atomListVariables, List.append_eq_nil_iff] at ground
            simp only [matchListFuel] at enough
            have headEnough : matchFuel head ≤ n := by omega
            have tailEnough : matchListFuel tail ≤ n := by omega
            have mergeEnough : 1 ≤ n := by
              have := one_le_matchFuel head
              omega
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            rw [matchAtomsList, atomCase head ground.1 headEnough]
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, mergeBindings_empty]
            simp only [List.flatMap_singleton']
            exact listCase tail acc ground.2 tailEnough

/-- Matching from an empty accumulator stays empty. -/
theorem matchAtomsList_nil_acc : ∀ (fuel : Nat) (lefts rights : List Atom),
    matchAtomsList lefts rights [] fuel = []
  | 0, _, _ => by simp [matchAtomsList]
  | _ + 1, [], [] => by simp [matchAtomsList]
  | _ + 1, [], _ :: _ => by simp [matchAtomsList]
  | _ + 1, _ :: _, [] => by simp [matchAtomsList]
  | n + 1, _ :: lefts, _ :: rights => by
      simp [matchAtomsList, matchAtomsList_nil_acc n lefts rights]

/-- Distinct ground atoms never match, at any fuel. -/
theorem matchAtoms_ground_ne : ∀ fuel : Nat,
    (∀ left right : Atom, atomVariables left = [] → atomVariables right = [] → left ≠ right →
      matchAtoms left right fuel = []) ∧
    (∀ (lefts rights : List Atom) (acc : List Bindings), atomListVariables lefts = [] →
      atomListVariables rights = [] → lefts ≠ rights → matchAtomsList lefts rights acc fuel = [])
  | 0 => ⟨fun _ _ _ _ _ => by simp [matchAtoms], fun _ _ _ _ _ _ => by simp [matchAtomsList]⟩
  | n + 1 => by
      obtain ⟨atomCase, listCase⟩ := matchAtoms_ground_ne n
      refine ⟨fun left right groundLeft groundRight distinct => ?_,
        fun lefts rights acc groundLefts groundRights distinct => ?_⟩
      · cases left <;> cases right <;>
          simp_all [matchAtoms, getMetaType, Atom.symbolType,
            Atom.groundedType, Atom.expressionType, atomVariables]
      · cases lefts with
        | nil => cases rights with
          | nil => exact absurd rfl distinct
          | cons _ _ => simp [matchAtomsList]
        | cons left lefts =>
            cases rights with
            | nil => simp [matchAtomsList]
            | cons right rights =>
                simp only [atomListVariables, List.append_eq_nil_iff] at groundLefts groundRights
                rw [matchAtomsList]
                by_cases same : left = right
                · subst same
                  have tails : lefts ≠ rights := fun h => distinct (h ▸ rfl)
                  exact listCase lefts rights _ groundLefts.2 groundRights.2 tails
                · rw [atomCase left right groundLefts.1 groundRights.1 same]
                  have empty : acc.flatMap (fun _ => ([] : List Bindings)) = [] :=
                    List.flatMap_eq_nil_iff.mpr fun _ _ => rfl
                  simp only [List.flatMap_nil, empty, matchAtomsList_nil_acc]

/-- `matchTypes` answers the incoming record for accepted types; when the
decision is a structural comparison, the compared type is ground. -/
private theorem matchTypes_accepted_core {expected actual : Atom}
    (accepted : accepts expected actual = true) (bindings : Bindings) {fuel : Nat}
    (compared : expected = actual → atomVariables actual = [] ∧ matchFuel actual ≤ fuel) :
    matchTypes expected actual bindings fuel = [bindings] := by
  unfold matchTypes
  by_cases special : (expected == Atom.undefinedType || expected == Atom.atomType ||
      actual == Atom.undefinedType || actual == Atom.atomType) = true
  · rw [if_pos special]
  · rw [if_neg special]
    have same : expected = actual := by
      simp only [accepts] at accepted
      simp only [Bool.not_eq_true] at special
      simp only [special, Bool.false_or] at accepted
      exact beq_iff_eq.mp accepted
    obtain ⟨ground, enough⟩ := compared same
    subst same
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by have := one_le_matchFuel expected; omega⟩
    rw [(matchAtoms_self_ground (n + 1)).1 expected ground enough]
    simp [mergeBindings_empty]

theorem matchTypes_accepted {expected actual : Atom} (ground : atomVariables expected = [])
    (accepted : accepts expected actual = true) (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel expected ≤ fuel) :
    matchTypes expected actual bindings fuel = [bindings] :=
  matchTypes_accepted_core accepted bindings fun same => same ▸ ⟨ground, enough⟩

theorem matchTypes_accepted_right {expected actual : Atom} (ground : atomVariables actual = [])
    (accepted : accepts expected actual = true) (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel actual ≤ fuel) :
    matchTypes expected actual bindings fuel = [bindings] :=
  matchTypes_accepted_core accepted bindings fun _ => ⟨ground, enough⟩

theorem matchTypes_rejected {expected actual : Atom} (groundExpected : atomVariables expected = [])
    (groundActual : atomVariables actual = []) (rejected : accepts expected actual = false)
    (bindings : Bindings) (fuel : Nat) :
    matchTypes expected actual bindings fuel = [] := by
  unfold matchTypes
  simp only [accepts, Bool.or_eq_false_iff] at rejected
  obtain ⟨⟨⟨⟨undefinedLeft, atomLeft⟩, undefinedRight⟩, atomRight⟩, distinct⟩ := rejected
  simp only [undefinedLeft, atomLeft, undefinedRight, atomRight, Bool.or_false, Bool.false_eq_true,
    if_false]
  rw [(matchAtoms_ground_ne fuel).1 expected actual groundExpected groundActual
    (by simpa using distinct)]
  rfl

/-! ## Arrows -/

/-- The arrow `(-> D₁ … Dₙ R)`. -/
def arrowType (params : List Atom) (range : Atom) : Atom :=
  .expression (.symbol "->" :: (params ++ [range]))

theorem isFunctionType_arrowType (params : List Atom) (range : Atom) :
    isFunctionType (arrowType params range) = true := by
  cases params <;> rfl

theorem getFunctionArgTypes_arrowType (params : List Atom) (range : Atom) :
    getFunctionArgTypes (arrowType params range) = some params := by
  simp [getFunctionArgTypes, arrowType]

theorem getFunctionRetType_arrowType (params : List Atom) (range : Atom) :
    getFunctionRetType (arrowType params range) = some range := by
  simp [getFunctionRetType, arrowType]

theorem arrowType_ground {params : List Atom} {range : Atom}
    (ground : atomVariables (arrowType params range) = []) :
    (∀ param ∈ params, atomVariables param = []) ∧ atomVariables range = [] := by
  have whole : atomListVariables (.symbol "->" :: (params ++ [range])) = [] := by
    simpa [arrowType, atomVariables] using ground
  exact ⟨fun param member => atomVariables_nil_of_mem whole (by simp [member]),
    atomVariables_nil_of_mem whole (by simp)⟩

theorem matchFuel_param_lt {params : List Atom} {range param : Atom} (member : param ∈ params) :
    matchFuel param < matchFuel (arrowType params range) :=
  matchFuel_lt_expression (by simp [member])

theorem matchFuel_range_lt (params : List Atom) (range : Atom) :
    matchFuel range < matchFuel (arrowType params range) :=
  matchFuel_lt_expression (by simp)

/-! ## Completed values -/

/-- The parameter check of one argument succeeds exactly once and binds
nothing: exactly one of the argument's types is accepted by the parameter, and
every rejected type is ground, so its rejection is a completed mismatch. -/
structure ArgumentChecked (space : Space) (param arg : Atom) : Prop where
  once : (getAtomTypes space arg).countP (accepts param) = 1
  rejectedGround : ∀ type ∈ getAtomTypes space arg, accepts param type = false →
    atomVariables type = []

/-- Symbols, variables and grounded atoms. Evaluation returns or casts them and
runs nothing. -/
def isLeaf : Atom → Bool
  | .expression _ => false
  | _ => true

mutual
/-- `Completed space dispatch value range`: `value` applies a symbol whose one
declared type is the ground arrow `(-> params… range)`, the head is neither
`Empty`, an executable grounded operation nor a minimal instruction, no stored
equation matches `value` at any depth under any renaming, and every argument is
its own value under its parameter. -/
inductive Completed (space : Space) (dispatch : GroundedDispatch) : Atom → Atom → Prop where
  | typed {head : String} {params args : List Atom} {range : Atom}
      (declared : getAtomTypes space (.symbol head) = [arrowType params range])
      (ground : atomVariables (arrowType params range) = [])
      (notEmpty : head ≠ "Empty")
      (notExecutable : dispatch.isExecutable (.symbol head) = false)
      (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
      (noEquation : NoEquationMatch space (.expression (.symbol head :: args)))
      (arguments : CompletedArguments space dispatch params args) :
      Completed space dispatch (.expression (.symbol head :: args)) range

/-- Each argument is held by an `Atom` parameter, is a leaf, or is a completed
value whose range the parameter accepts; and its parameter check succeeds once. -/
inductive CompletedArguments (space : Space) (dispatch : GroundedDispatch) :
    List Atom → List Atom → Prop where
  | nil : CompletedArguments space dispatch [] []
  | held {arg : Atom} {params args : List Atom}
      (checked : ArgumentChecked space Atom.atomType arg)
      (rest : CompletedArguments space dispatch params args) :
      CompletedArguments space dispatch (Atom.atomType :: params) (arg :: args)
  | leaf {param arg : Atom} {params args : List Atom}
      (leaf : isLeaf arg = true)
      (checked : ArgumentChecked space param arg)
      (rest : CompletedArguments space dispatch params args) :
      CompletedArguments space dispatch (param :: params) (arg :: args)
  | value {param arg range : Atom} {params args : List Atom}
      (completed : Completed space dispatch arg range)
      (fits : param = Atom.undefinedType ∨ param = range)
      (checked : ArgumentChecked space param arg)
      (rest : CompletedArguments space dispatch params args) :
      CompletedArguments space dispatch (param :: params) (arg :: args)
end

/-! ## The parameter check -/

theorem typeCastLoop_accepted {param atom : Atom} (ground : atomVariables param = [])
    {bindings : Bindings} {fuel : Nat} (enough : matchFuel param ≤ fuel) :
    ∀ (types noMatch : List Atom),
      (∀ type ∈ types, accepts param type = false → atomVariables type = []) →
      0 < types.countP (accepts param) →
      typeCast.typeCastLoop types atom param bindings fuel noMatch = [(atom, bindings)]
  | [], _, _, positive => by simp at positive
  | type :: types, noMatch, rejectedGround, positive => by
      rw [typeCast.typeCastLoop]
      cases accepted : accepts param type with
      | true =>
          rw [matchTypes_accepted ground accepted bindings enough]
          simp
      | false =>
          rw [matchTypes_rejected ground (rejectedGround type (by simp) accepted) accepted]
          simp only [List.isEmpty_nil, if_true]
          apply typeCastLoop_accepted ground enough types
          · intro other member rejected
            exact rejectedGround other (by simp [member]) rejected
          · simpa [List.countP_cons, accepted] using positive

theorem typeCast_checked {space : Space} {param atom : Atom} (ground : atomVariables param = [])
    (checked : ArgumentChecked space param atom) (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel param ≤ fuel) :
    typeCast atom param space bindings fuel = [(atom, bindings)] := by
  unfold typeCast
  simp only [rawTypeLookup]
  exact typeCastLoop_accepted ground enough _ _ checked.rejectedGround
    (by rw [checked.once]; omega)

/-- The successful records of a list of argument checks. -/
def checkSuccesses : List (Sum Atom Bindings) → List Bindings :=
  List.filterMap fun check => match check with
    | .inr bindings => some bindings
    | .inl _ => none

theorem checkSuccesses_append (left right : List (Sum Atom Bindings)) :
    checkSuccesses (left ++ right) = checkSuccesses left ++ checkSuccesses right :=
  List.filterMap_append

theorem checkSuccesses_types {param : Atom} (ground : atomVariables param = [])
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel param ≤ fuel) :
    ∀ types : List Atom, (∀ type ∈ types, accepts param type = false → atomVariables type = []) →
      checkSuccesses (types.flatMap fun type =>
        let matched := matchTypes param type bindings fuel
        if matched.isEmpty then [Sum.inl type] else matched.map Sum.inr) =
        List.replicate (types.countP (accepts param)) bindings
  | [], _ => by simp [checkSuccesses]
  | type :: types, rejectedGround => by
      have rest := checkSuccesses_types ground bindings enough types
        fun other member rejected => rejectedGround other (by simp [member]) rejected
      rw [List.flatMap_cons, checkSuccesses_append, rest]
      cases accepted : accepts param type with
      | true =>
          simp [matchTypes_accepted ground accepted bindings enough, checkSuccesses,
            accepted, List.replicate_succ]
      | false =>
          simp [matchTypes_rejected ground (rejectedGround type (by simp) accepted) accepted,
            checkSuccesses, accepted]

theorem checkArgumentType_checked {space : Space} {param arg : Atom}
    (ground : atomVariables param = []) (checked : ArgumentChecked space param arg)
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel param ≤ fuel) :
    checkSuccesses (checkArgumentType space arg param bindings fuel) = [bindings] := by
  unfold checkArgumentType
  simp only [rawTypeLookup]
  rw [checkSuccesses_types ground bindings enough _ checked.rejectedGround, checked.once]
  rfl

theorem foldl_checks_snd {E : Type}
    (step : List E × List Bindings → Sum Atom Bindings → List E × List Bindings)
    (onError : ∀ acc type, (step acc (.inl type)).2 = acc.2)
    (onSuccess : ∀ acc bindings, (step acc (.inr bindings)).2 = acc.2 ++ [bindings]) :
    ∀ (checks : List (Sum Atom Bindings)) (acc : List E × List Bindings),
      (checks.foldl step acc).2 = acc.2 ++ checkSuccesses checks
  | [], acc => by simp [checkSuccesses]
  | check :: checks, acc => by
      rw [List.foldl_cons, foldl_checks_snd step onError onSuccess checks]
      cases check with
      | inl type => simp [onError, checkSuccesses]
      | inr bindings => simp [onSuccess, checkSuccesses]

theorem checkArgLoop_checked {space : Space} {expr : Atom} {bindings : Bindings} {fuel : Nat}
    {params args : List Atom} (checked : List.Forall₂ (ArgumentChecked space) params args)
    (admissible : ∀ param ∈ params, atomVariables param = [] ∧ matchFuel param ≤ fuel)
    (errors : List Atom) (idx : Nat) :
    (checkIfFunctionTypeIsApplicable.checkArgLoop args params expr [bindings] errors space
      fuel idx).2 = [bindings] := by
  induction checked generalizing errors idx with
  | nil => rfl
  | @cons param arg params args first rest ih =>
      rw [checkIfFunctionTypeIsApplicable.checkArgLoop]
      simp only [List.foldl_cons, List.foldl_nil]
      have firstAdmissible := admissible param (by simp)
      rw [foldl_checks_snd _ (fun _ _ => rfl) (fun _ _ => rfl),
        checkArgumentType_checked firstAdmissible.1 first bindings firstAdmissible.2,
        List.nil_append]
      exact ih (fun other member => admissible other (by simp [member])) _ (idx + 1)

/-! ## One evaluation of a completed value -/

theorem isEmptyOrError_symbol {name : String} (notEmpty : name ≠ "Empty") :
    isEmptyOrError (.symbol name) = false := by
  simp [isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty, notEmpty]

theorem arrowType_beq_symbol (params : List Atom) (range : Atom) (name : String) :
    (arrowType params range == Atom.symbol name) = false := by
  simp [arrowType]

/-- The head evaluates to itself under its first declared arrow. -/
theorem evalAtom_head {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params : List Atom} {range : Atom} {others : List Atom}
    (declared : getAtomTypes space (.symbol head) = arrowType params range :: others)
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel (arrowType params range) ≤ fuel) (live : List Atom) :
    evalAtom space dispatch (.symbol head) (arrowType params range) bindings (fuel + 1) live =
      [(.symbol head, bindings)] := by
  have cast : typeCast (.symbol head) (arrowType params range) space bindings fuel =
      [(.symbol head, bindings)] := by
    unfold typeCast
    simp only [rawTypeLookup, declared]
    rw [typeCast.typeCastLoop, matchTypes_accepted ground (accepts_self _) bindings enough]
    simp
  rw [evalAtom]
  simp [isEmptyOrError_symbol notEmpty, getMetaType, Atom.atomType, Atom.symbolType,
    Atom.variableType, arrowType_beq_symbol, cast]

/-- A leaf evaluates to itself under a parameter that accepts one of its types,
when every type the parameter rejects is ground. -/
theorem evalAtom_leaf_of {space : Space} {dispatch : GroundedDispatch} {param arg : Atom}
    (leaf : isLeaf arg = true) (ground : atomVariables param = [])
    (accepted : 0 < (getAtomTypes space arg).countP (accepts param))
    (rejectedGround : ∀ type ∈ getAtomTypes space arg, accepts param type = false →
      atomVariables type = [])
    (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel param ≤ fuel) (live : List Atom) :
    evalAtom space dispatch arg param bindings (fuel + 1) live = [(arg, bindings)] := by
  have cast : typeCast arg param space bindings fuel = [(arg, bindings)] := by
    unfold typeCast
    simp only [rawTypeLookup]
    exact typeCastLoop_accepted ground enough _ _ rejectedGround accepted
  cases arg with
  | expression _ => simp [isLeaf] at leaf
  | var name =>
      rw [evalAtom]
      simp [getMetaType, Atom.variableType, isEmptyOrError, isEmptyAtom, isErrorAtom,
        Atom.empty]
  | symbol name =>
      rw [evalAtom]
      simp [getMetaType, Atom.symbolType, cast]
  | grounded value =>
      rw [evalAtom]
      simp [getMetaType, Atom.groundedType, Atom.symbolType, cast]

/-- A leaf evaluates to itself under a parameter that checks it once. -/
theorem evalAtom_leaf {space : Space} {dispatch : GroundedDispatch} {param arg : Atom}
    (leaf : isLeaf arg = true) (ground : atomVariables param = [])
    (checked : ArgumentChecked space param arg) (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel param ≤ fuel) (live : List Atom) :
    evalAtom space dispatch arg param bindings (fuel + 1) live = [(arg, bindings)] :=
  evalAtom_leaf_of leaf ground (by rw [checked.once]; omega) checked.rejectedGround bindings
    enough live

/-- A symbol other than `Empty`, under a type that is neither `Atom` nor
`Symbol`, is cast. -/
theorem evalAtom_symbol {space : Space} {dispatch : GroundedDispatch} {name : String}
    {param : Atom} (notEmpty : name ≠ "Empty") (notAtom : param ≠ Atom.atomType)
    (notSymbol : param ≠ Atom.symbolType) (bindings : Bindings) (fuel : Nat)
    (live : List Atom) :
    evalAtom space dispatch (.symbol name) param bindings (fuel + 1) live =
      typeCast (.symbol name) param space bindings fuel := by
  have notAtom' : ¬param = Atom.symbol "Atom" := notAtom
  have notSymbol' : ¬param = Atom.symbol "Symbol" := notSymbol
  rw [evalAtom]
  simp [isEmptyOrError_symbol notEmpty, getMetaType, notAtom', notSymbol', Atom.symbolType,
    Atom.atomType, Atom.variableType]

/-- An `Atom` parameter holds its argument. -/
theorem evalAtom_held {space : Space} {dispatch : GroundedDispatch} (arg : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    evalAtom space dispatch arg Atom.atomType bindings (fuel + 1) live = [(arg, bindings)] := by
  rw [evalAtom]
  by_cases failed : isEmptyOrError arg = true
  · simp [failed]
  · simp [failed]

theorem interpretArgs_nil_self {space : Space} {dispatch : GroundedDispatch}
    (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    interpretArgs space dispatch [] [] bindings (fuel + 1) live =
      [(argumentPacket [], bindings)] := by
  rw [interpretArgs]

theorem interpretArgs_cons_self {space : Space} {dispatch : GroundedDispatch}
    {param arg : Atom} {params args : List Atom} {bindings : Bindings} {fuel : Nat}
    (first : ∀ live, evalAtom space dispatch arg param bindings fuel live = [(arg, bindings)])
    (rest : ∀ live, interpretArgs space dispatch args params bindings fuel live =
      [(argumentPacket args, bindings)])
    (live : List Atom) :
    interpretArgs space dispatch (arg :: args) (param :: params) bindings (fuel + 1) live =
      [(argumentPacket (arg :: args), bindings)] := by
  rw [interpretArgs, first]
  simp [rest]

theorem interpretFunction_completed {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range : Atom} {others : List Atom}
    (declared : getAtomTypes space (.symbol head) = arrowType params range :: others)
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel (arrowType params range) ≤ fuel)
    (arguments : ∀ live, interpretArgs space dispatch args params bindings (fuel + 1) live =
      [(argumentPacket args, bindings)])
    (live : List Atom) :
    interpretFunction space dispatch (.expression (.symbol head :: args)) (arrowType params range)
      bindings (fuel + 2) live = [(.expression (.symbol head :: args), bindings)] := by
  rw [interpretFunction, evalAtom_head declared ground notEmpty bindings enough]
  simp [isEmptyOrError_symbol notEmpty, getFunctionArgTypes_arrowType, arguments]

theorem invoke_completed {space : Space} {dispatch : GroundedDispatch} {operator : Atom}
    {arguments : List Atom}
    (notExecutable : dispatch.isExecutable operator = false)
    (notInstruction : minimalInstruction (.expression (operator :: arguments)) = false)
    (noEquation : NoEquationMatch space (.expression (operator :: arguments)))
    (notError : isErrorAtom (.expression (operator :: arguments)) = false)
    (expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom)
    (caller : Option Atom) :
    invoke space dispatch (.ordinary expected) (.expression (operator :: arguments)) bindings
      (fuel + 1) live caller = [(.expression (operator :: arguments), bindings)] := by
  unfold NoEquationMatch at noEquation
  rw [invoke]
  simp [InvocationMode.errorPassthrough, notError, notExecutable, notInstruction,
    rawQueryResults, noEquation]

theorem checkIfFunctionTypeIsApplicable_completed {space : Space} {head : String}
    {params args : List Atom} {range expected : Atom}
    (ground : atomVariables (arrowType params range) = [])
    (checked : List.Forall₂ (ArgumentChecked space) params args)
    (returns : accepts expected range = true) (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel (arrowType params range) ≤ fuel) :
    checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args)) (arrowType params range)
      expected space bindings (fuel + 1) = .inr [bindings] := by
  obtain ⟨paramsGround, rangeGround⟩ := arrowType_ground ground
  have loop := checkArgLoop_checked (expr := .expression (.symbol head :: args))
    (bindings := bindings) (fuel := fuel) checked
    (fun param member => ⟨paramsGround param member,
      by have := matchFuel_param_lt (range := range) member; omega⟩) [] 1
  have lengths : args.length = params.length := checked.length_eq.symm
  have returned : matchTypes expected range bindings fuel = [bindings] :=
    matchTypes_accepted_right rangeGround returns bindings
      (by have := matchFuel_range_lt params range; omega)
  rw [checkIfFunctionTypeIsApplicable]
  simp only [getFunctionArgTypes_arrowType, getFunctionRetType_arrowType]
  simp [loop, lengths, returned]

/-- The demand under which a typed call's reply is returned: an `Expression`
range is returned undemanded. -/
def callReturnType (range : Atom) : Atom :=
  if range = Atom.expressionType then Atom.undefinedType else range

theorem callReturnType_arrowType (params : List Atom) (range : Atom) :
    (if getFunctionRetType (arrowType params range) == some Atom.expressionType then
        Atom.undefinedType
      else (getFunctionRetType (arrowType params range)).getD Atom.undefinedType) =
      callReturnType range := by
  by_cases same : range = Atom.expressionType <;>
    simp [getFunctionRetType_arrowType, callReturnType, same]

/-- One typed call under `copies + 1` equal declarations: each declaration
interprets the call and hands it to the invocation, whose answers are given. -/
theorem interpretExpression_typed {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range expected : Atom} {copies : Nat}
    (declared : getAtomTypes space (.symbol head) =
      List.replicate (copies + 1) (arrowType params range))
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty")
    (checked : List.Forall₂ (ArgumentChecked space) params args)
    (returns : accepts expected range = true) (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel (arrowType params range) ≤ fuel)
    (arguments : ∀ live, interpretArgs space dispatch args params bindings (fuel + 1) live =
      [(argumentPacket args, bindings)])
    {live : List Atom} {results : ResultSet}
    (invoked : invoke space dispatch (.ordinary (callReturnType range))
      (.expression (.symbol head :: args)) bindings (fuel + 2) live = results) :
    interpretExpression space dispatch (.expression (.symbol head :: args)) expected bindings
      (fuel + 3) live = (List.replicate (copies + 1) results).flatten := by
  have applicable : checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args))
      (arrowType params range) expected space bindings (fuel + 2) = .inr [bindings] :=
    checkIfFunctionTypeIsApplicable_completed ground checked returns bindings (by omega)
  have first : getAtomTypes space (.symbol head) =
      arrowType params range :: List.replicate copies (arrowType params range) := by
    rw [declared, List.replicate_succ]
  rw [interpretExpression]
  simp only [declared, List.flatMap_replicate, isFunctionType_arrowType, if_true, applicable,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    interpretFunction_completed first ground notEmpty bindings enough arguments,
    callReturnType_arrowType, invoked]
  have nonFunction : ((List.replicate (copies + 1) (arrowType params range)).any fun type =>
      !isFunctionType type || type == Atom.undefinedType) = false := by
    simp [isFunctionType_arrowType, arrowType_beq_symbol, Atom.undefinedType]
  simp only [nonFunction, Bool.false_eq_true, if_false, List.append_nil, Bool.not_false, if_true]
  simp [isFunctionType_arrowType, applicable]

/-- A typed call whose applicability check answers one record `m` times
interprets once per answer. -/
theorem interpretExpression_replicated {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range expected : Atom} {copies : Nat}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") {bindings other : Bindings} {fuel : Nat}
    (applicable : checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args))
      (arrowType params range) expected space bindings (fuel + 2) =
        .inr (List.replicate (copies + 1) other))
    (enough : matchFuel (arrowType params range) ≤ fuel)
    (arguments : ∀ live, interpretArgs space dispatch args params other (fuel + 1) live =
      [(argumentPacket args, other)])
    {live : List Atom} {results : ResultSet}
    (invoked : invoke space dispatch (.ordinary (callReturnType range))
      (.expression (.symbol head :: args)) other (fuel + 2) live = results) :
    interpretExpression space dispatch (.expression (.symbol head :: args)) expected bindings
      (fuel + 3) live = (List.replicate (copies + 1) results).flatten := by
  have first : getAtomTypes space (.symbol head) = arrowType params range :: [] := declared
  rw [interpretExpression]
  simp only [declared, isFunctionType_arrowType, if_true, applicable, List.flatMap_replicate,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    interpretFunction_completed first ground notEmpty other enough arguments,
    callReturnType_arrowType, invoked]
  have nonFunction : ([arrowType params range].any fun type =>
      !isFunctionType type || type == Atom.undefinedType) = false := by
    simp [isFunctionType_arrowType, arrowType_beq_symbol, Atom.undefinedType]
  simp only [nonFunction, Bool.false_eq_true, if_false, List.append_nil, Bool.not_false, if_true]
  simp [isFunctionType_arrowType, applicable]

/-- A completed call interprets to itself once. -/
theorem interpretExpression_completed {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (noEquation : NoEquationMatch space (.expression (.symbol head :: args)))
    (notError : isErrorAtom (.expression (.symbol head :: args)) = false)
    (checked : List.Forall₂ (ArgumentChecked space) params args)
    (returns : accepts expected range = true) (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel (arrowType params range) ≤ fuel)
    (arguments : ∀ live, interpretArgs space dispatch args params bindings (fuel + 1) live =
      [(argumentPacket args, bindings)])
    (live : List Atom) :
    interpretExpression space dispatch (.expression (.symbol head :: args)) expected bindings
      (fuel + 3) live = [(.expression (.symbol head :: args), bindings)] := by
  rw [interpretExpression_typed (copies := 0) declared ground notEmpty checked returns bindings
    enough arguments (invoke_completed notExecutable notInstruction noEquation notError _ _ _ _ _)]
  simp

/-- The evaluator keeps an error-free interpretation unchanged. -/
theorem evalAtom_of_interpretExpression {space : Space} {dispatch : GroundedDispatch}
    {value expected : Atom} {bindings : Bindings} {fuel : Nat} {live : List Atom}
    {results : ResultSet} (operands : ∃ head rest, value = .expression (head :: rest))
    (clean : isEmptyOrError value = false)
    (interpreted : (expected == Atom.atomType || expected == Atom.expressionType) = false)
    (interpretation : interpretExpression space dispatch value expected bindings fuel live =
      results)
    (successes : ∀ result ∈ results, isErrorAtom result.1 = false) :
    evalAtom space dispatch value expected bindings (fuel + 1) live = results := by
  obtain ⟨head, rest, rfl⟩ := operands
  have notAtom : ¬expected = Atom.symbol "Atom" := fun same => by
    simp [same, Atom.atomType] at interpreted
  have notExpression : ¬expected = Atom.symbol "Expression" := fun same => by
    simp [same, Atom.atomType, Atom.expressionType] at interpreted
  rw [evalAtom]
  simp only [clean, Bool.false_eq_true, if_false, interpretation]
  have kept : results.filter (fun result => !isErrorAtom result.1) = results :=
    List.filter_eq_self.mpr fun result member => by simp [successes result member]
  cases results with
  | nil => simp [getMetaType, Atom.expressionType, Atom.symbolType, Atom.groundedType,
      Atom.variableType, Atom.atomType, Atom.unit, notAtom, notExpression]
  | cons first others =>
      simp [getMetaType, Atom.expressionType, Atom.symbolType, Atom.groundedType,
        Atom.variableType, Atom.atomType, Atom.unit, notAtom, notExpression, kept]

/-- The value evaluates to itself, once, with the bindings it was asked under. -/
theorem evalAtom_completed_step {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (noEquation : NoEquationMatch space (.expression (.symbol head :: args)))
    (checked : List.Forall₂ (ArgumentChecked space) params args)
    (returns : accepts expected range = true) (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel (arrowType params range) ≤ fuel)
    (arguments : ∀ live, interpretArgs space dispatch args params bindings (fuel + 1) live =
      [(argumentPacket args, bindings)])
    (live : List Atom) :
    evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings (fuel + 4)
      live = [(.expression (.symbol head :: args), bindings)] := by
  rw [evalAtom]
  by_cases failed : isEmptyOrError (.expression (.symbol head :: args)) = true
  · simp [failed]
  · have clean : isEmptyOrError (.expression (.symbol head :: args)) = false := by
      simpa using failed
    have notError : isErrorAtom (.expression (.symbol head :: args)) = false := by
      simp only [isEmptyOrError, Bool.or_eq_false_iff] at clean
      exact clean.2
    simp only [clean, Bool.false_eq_true, if_false]
    rw [interpretExpression_completed declared ground notEmpty notExecutable notInstruction
      noEquation notError checked returns bindings enough arguments live]
    simp [notError, getMetaType, Atom.expressionType, Atom.symbolType, Atom.groundedType,
      Atom.variableType, Atom.unit]

/-! ## Stored equations with ground sides -/

/-- Every stored equation has ground sides. -/
def GroundEquations (space : Space) : Prop :=
  ∀ lhs rhs, Atom.expression [.symbol "=", lhs, rhs] ∈ space.atoms →
    atomVariables lhs = [] ∧ atomVariables rhs = []

/-- The right side a stored atom contributes to the equation query of `value`. -/
def equationRhs (value : Atom) : Atom → List Atom
  | .expression [.symbol "=", lhs, rhs] => if lhs = value then [rhs] else []
  | _ => []

theorem mem_equationRhs {value atom rhs : Atom} (member : rhs ∈ equationRhs value atom) :
    atom = .expression [.symbol "=", value, rhs] := by
  unfold equationRhs at member
  split at member
  · split_ifs at member with same
    · simp only [List.mem_singleton] at member
      subst same member
      rfl
    · simp at member
  · simp at member

theorem applyFull_ground (bindings : Bindings) :
    ∀ (fuel : Nat) (atom : Atom), atomVariables atom = [] → bindings.applyFull atom fuel = atom
  | 0, _, _ => by simp [Bindings.applyFull]
  | n + 1, atom, ground => by
      cases atom with
      | var _ => simp [atomVariables] at ground
      | symbol _ => simp [Bindings.applyFull]
      | grounded _ => simp [Bindings.applyFull]
      | expression atoms =>
          simp only [atomVariables] at ground
          simp only [Bindings.applyFull]
          congr 1
          conv_rhs => rw [← List.map_id atoms]
          exact List.map_congr_left fun atom member =>
            applyFull_ground bindings n atom (atomVariables_nil_of_mem ground member)

theorem flatMap_zipIdx {α β : Type} (f : α × Nat → List β) (g : α → List β) :
    ∀ (l : List α) (start : Nat), (∀ a ∈ l, ∀ i, f (a, i) = g a) →
      (l.zipIdx start).flatMap f = l.flatMap g
  | [], _, _ => rfl
  | a :: l, start, same => by
      rw [List.zipIdx_cons, List.flatMap_cons, List.flatMap_cons, same a (by simp),
        flatMap_zipIdx f g l (start + 1) fun b member => same b (by simp [member])]

/-- With ground equations, the query of a ground value returns the right sides
of the equations whose left side is the value, in stored order, unbound. -/
theorem queryEquationsAvoiding_ground {space : Space} {value : Atom}
    (groundValue : atomVariables value = []) (groundEquations : GroundEquations space)
    (avoid : List String) {fuel : Nat} (enough : matchFuel value ≤ fuel) :
    queryEquationsAvoiding avoid space value fuel =
      (space.atoms.flatMap (equationRhs value)).map fun rhs => (rhs, Bindings.empty) := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by have := one_le_matchFuel value; omega⟩
  unfold queryEquationsAvoiding
  rw [List.map_flatMap]
  apply flatMap_zipIdx
  intro atom member idx
  dsimp only
  split
  · rename_i lhs rhs
    obtain ⟨groundLhs, groundRhs⟩ := groundEquations lhs rhs member
    simp only [freshenEquationAvoiding, renameAtom_of_atomVariables_eq_nil _ lhs groundLhs,
      renameAtom_of_atomVariables_eq_nil _ rhs groundRhs, equationRhs]
    by_cases same : lhs = value
    · subst same
      rw [(matchAtoms_self_ground (n + 1)).1 lhs groundLhs enough]
      simp [mergeBindings_empty, Bindings.hasLoop_empty]
    · rw [(matchAtoms_ground_ne (n + 1)).1 value lhs groundValue groundLhs (Ne.symm same)]
      simp [same]
  · rename_i notEquation
    unfold equationRhs
    split
    · rename_i lhs rhs
      exact absurd rfl (notEquation lhs rhs)
    · rfl

theorem rawQueryResults_ground {space : Space} {value : Atom}
    (groundValue : atomVariables value = []) (groundEquations : GroundEquations space)
    (expected : Atom) {fuel : Nat} (enough : matchFuel value ≤ fuel) (live : List Atom) :
    rawQueryResults space value expected Bindings.empty fuel live =
      (space.atoms.flatMap (equationRhs value)).map fun rhs => (rhs, Bindings.empty) := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by have := one_le_matchFuel value; omega⟩
  unfold rawQueryResults
  rw [queryEquationsAvoiding_ground groundValue groundEquations _ enough, List.flatMap_map,
    List.map_eq_flatMap]
  apply List.flatMap_congr
  intro rhs member
  obtain ⟨atom, stored, contributed⟩ := List.mem_flatMap.mp member
  have shape := mem_equationRhs contributed
  subst shape
  have groundRhs := (groundEquations value rhs stored).2
  have aliased : Spec.Type.Presentation.BindingTheory.aliasConstraints Bindings.empty =
      Bindings.empty := rfl
  simp [aliased, mergeBindings_empty, Bindings.hasLoop_empty, applyFull_ground _ _ _ groundRhs]

/-- Only an emitted function block enters a function continuation. -/
theorem invocationResult_plain {space : Space} {dispatch : GroundedDispatch} {value : Atom}
    (plain : ∀ body, value ≠ .expression [.symbol "function", body]) (bindings : Bindings)
    (fuel : Nat) (live : List Atom) (caller : Option Atom) :
    invocationResult space dispatch value bindings (fuel + 1) live caller =
      [(value, bindings)] := by
  rw [invocationResult]
  have emitted : (InvocationProvenance.emitted == InvocationProvenance.completed) = false := rfl
  simp only [emitted, Bool.false_eq_true, if_false]
  exact fun body same => plain body same

/-- A typed call whose value stored equations rewrite: each right side is
returned through the ordinary call return, in stored order. -/
theorem invoke_equations {space : Space} {dispatch : GroundedDispatch} {operator : Atom}
    {arguments : List Atom}
    (notExecutable : dispatch.isExecutable operator = false)
    (notInstruction : minimalInstruction (.expression (operator :: arguments)) = false)
    (notError : isErrorAtom (.expression (operator :: arguments)) = false)
    (groundValue : atomVariables (.expression (operator :: arguments)) = [])
    (groundEquations : GroundEquations space)
    (matched : space.atoms.flatMap (equationRhs (.expression (operator :: arguments))) ≠ [])
    (plain : ∀ rhs ∈ space.atoms.flatMap (equationRhs (.expression (operator :: arguments))),
      ∀ body, rhs ≠ .expression [.symbol "function", body])
    (expected : Atom) {fuel : Nat}
    (enough : matchFuel (.expression (operator :: arguments)) ≤ fuel + 1)
    (live : List Atom) (caller : Option Atom) :
    invoke space dispatch (.ordinary expected) (.expression (operator :: arguments))
        Bindings.empty (fuel + 2) live caller =
      (space.atoms.flatMap (equationRhs (.expression (operator :: arguments)))).flatMap
        fun rhs => ordinaryCallReturn (.expression (operator :: arguments)) rhs Bindings.empty
          (fun value bindings => evalAtom space dispatch value expected bindings (fuel + 1) live) := by
  rw [invoke]
  simp only [InvocationMode.errorPassthrough, notError, Bool.false_eq_true, if_false,
    notExecutable, notInstruction, InvocationMode.expected,
    rawQueryResults_ground groundValue groundEquations expected enough live,
    List.isEmpty_map, List.flatMap_map]
  have nonempty : (space.atoms.flatMap
      (equationRhs (.expression (operator :: arguments)))).isEmpty = false := by
    cases found : space.atoms.flatMap (equationRhs (.expression (operator :: arguments))) with
    | nil => exact absurd found matched
    | cons _ _ => rfl
  simp only [nonempty, Bool.false_eq_true, if_false]
  apply List.flatMap_congr
  intro rhs member
  rw [invocationResult_plain (plain rhs member)]
  simp

/-- A typed call whose equation query, merged with the incoming record,
yields nothing is returned unchanged. -/
theorem invoke_refused {space : Space} {dispatch : GroundedDispatch} {operator : Atom}
    {arguments : List Atom}
    (notExecutable : dispatch.isExecutable operator = false)
    (notInstruction : minimalInstruction (.expression (operator :: arguments)) = false)
    (notError : isErrorAtom (.expression (operator :: arguments)) = false)
    {expected : Atom} {bindings : Bindings} {fuel : Nat} {live : List Atom}
    (refused : rawQueryResults space (.expression (operator :: arguments)) expected bindings fuel
      live = [])
    (caller : Option Atom) :
    invoke space dispatch (.ordinary expected) (.expression (operator :: arguments)) bindings
      (fuel + 1) live caller = [(.expression (operator :: arguments), bindings)] := by
  rw [invoke]
  simp [InvocationMode.errorPassthrough, notError, notExecutable, notInstruction,
    InvocationMode.expected, refused]

/-- A typed call whose merged equation query yields replies returns each reply
through the ordinary call return, in order. -/
theorem invoke_queried {space : Space} {dispatch : GroundedDispatch} {operator : Atom}
    {arguments : List Atom}
    (notExecutable : dispatch.isExecutable operator = false)
    (notInstruction : minimalInstruction (.expression (operator :: arguments)) = false)
    (notError : isErrorAtom (.expression (operator :: arguments)) = false)
    {expected : Atom} {bindings : Bindings} {fuel : Nat} {live : List Atom} {replies : ResultSet}
    (queried : rawQueryResults space (.expression (operator :: arguments)) expected bindings
      (fuel + 1) live = replies)
    (nonempty : replies ≠ [])
    (plain : ∀ reply ∈ replies, ∀ body, reply.1 ≠ .expression [.symbol "function", body])
    (caller : Option Atom) :
    invoke space dispatch (.ordinary expected) (.expression (operator :: arguments)) bindings
        (fuel + 2) live caller =
      replies.flatMap fun reply => ordinaryCallReturn (.expression (operator :: arguments))
        reply.1 reply.2
          (fun value bindings => evalAtom space dispatch value expected bindings (fuel + 1) live) := by
  rw [invoke]
  have full : replies.isEmpty = false := by
    cases replies with
    | nil => exact absurd rfl nonempty
    | cons _ _ => rfl
  simp only [InvocationMode.errorPassthrough, notError, Bool.false_eq_true, if_false,
    notExecutable, notInstruction, InvocationMode.expected, queried, full]
  apply List.flatMap_congr
  intro reply member
  rw [invocationResult_plain (plain reply member)]
  simp

/-! ## Rejected calls -/

theorem interpretExpression_rejected {space : Space} {dispatch : GroundedDispatch}
    {head : String} {args : List Atom} {type expected : Atom} {bindings : Bindings}
    {fuel : Nat} {live : List Atom} {errors : List Atom}
    (declared : getAtomTypes space (.symbol head) = [type])
    (function : isFunctionType type = true)
    (rejected : checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args)) type
      expected space bindings fuel = .inl errors) :
    interpretExpression space dispatch (.expression (.symbol head :: args)) expected bindings
      (fuel + 1) live = errors.map fun error => (error, bindings) := by
  have defined : (type == Atom.undefinedType) = false := by
    cases same : type == Atom.undefinedType with
    | false => rfl
    | true =>
        rw [beq_iff_eq] at same
        subst same
        simp [isFunctionType, Atom.undefinedType] at function
  rw [interpretExpression]
  simp [declared, function, rejected, defined]

/-- The evaluator returns an all-error interpretation as it is. -/
theorem evalAtom_of_interpretExpression_errors {space : Space} {dispatch : GroundedDispatch}
    {value expected : Atom} {bindings : Bindings} {fuel : Nat} {live : List Atom}
    {results : ResultSet} (operands : ∃ head rest, value = .expression (head :: rest))
    (clean : isEmptyOrError value = false)
    (interpreted : (expected == Atom.atomType || expected == Atom.expressionType) = false)
    (interpretation : interpretExpression space dispatch value expected bindings fuel live =
      results)
    (failures : ∀ result ∈ results, isErrorAtom result.1 = true) :
    evalAtom space dispatch value expected bindings (fuel + 1) live = results := by
  obtain ⟨head, rest, rfl⟩ := operands
  have notAtom : ¬expected = Atom.symbol "Atom" := fun same => by
    simp [same, Atom.atomType] at interpreted
  have notExpression : ¬expected = Atom.symbol "Expression" := fun same => by
    simp [same, Atom.atomType, Atom.expressionType] at interpreted
  rw [evalAtom]
  simp only [clean, Bool.false_eq_true, if_false, interpretation]
  have dropped : results.filter (fun result => !isErrorAtom result.1) = [] :=
    List.filter_eq_nil_iff.mpr fun result member => by simp [failures result member]
  have kept : results.filter (fun result => isErrorAtom result.1) = results :=
    List.filter_eq_self.mpr fun result member => failures result member
  simp [getMetaType, Atom.expressionType, Atom.symbolType, Atom.groundedType,
    Atom.variableType, Atom.atomType, Atom.unit, notAtom, notExpression, dropped, kept]

/-- Argument checks against an empty record keep it empty. -/
theorem checkArgLoop_none {space : Space} {expr : Atom} {fuel : Nat} :
    ∀ (args params : List Atom) (errors : List Atom) (idx : Nat),
      (checkIfFunctionTypeIsApplicable.checkArgLoop args params expr [] errors space fuel
        idx).2 = []
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: args, _ :: params, errors, idx => by
      rw [checkIfFunctionTypeIsApplicable.checkArgLoop]
      simp only [List.foldl_nil]
      exact checkArgLoop_none args params errors (idx + 1)

theorem checkArgLoop_none_errors {space : Space} {expr : Atom} {fuel : Nat} :
    ∀ (args params : List Atom) (errors : List Atom) (idx : Nat), args.length = params.length →
      (checkIfFunctionTypeIsApplicable.checkArgLoop args params expr [] errors space fuel
        idx).1 = errors
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, lengths => by simp at lengths
  | _ :: _, [], _, _, lengths => by simp at lengths
  | _ :: args, _ :: params, errors, idx, lengths => by
      rw [checkIfFunctionTypeIsApplicable.checkArgLoop]
      simp only [List.foldl_nil]
      exact checkArgLoop_none_errors args params errors (idx + 1) (by simpa using lengths)

/-- An argument check with one accepted type contributes exactly the record. -/
theorem checkArgLoop_exact {space : Space} {expr : Atom} {bindings : Bindings} {fuel : Nat}
    {params args : List Atom}
    (exact : List.Forall₂ (fun param arg => ∃ type, getAtomTypes space arg = [type] ∧
      accepts param type = true ∧ atomVariables param = [] ∧ matchFuel param ≤ fuel) params args)
    (errors : List Atom) (idx : Nat) :
    checkIfFunctionTypeIsApplicable.checkArgLoop args params expr [bindings] errors space
      fuel idx = (errors, [bindings]) := by
  induction exact generalizing errors idx with
  | nil => rfl
  | @cons param arg params args first rest ih =>
      obtain ⟨type, types, accepted, ground, enough⟩ := first
      rw [checkIfFunctionTypeIsApplicable.checkArgLoop]
      simp [checkArgumentType, rawTypeLookup, types,
        matchTypes_accepted ground accepted bindings enough, ih]

/-- A first argument whose only type is rejected stops the check with its error. -/
theorem checkArgLoop_rejected {space : Space} {expr : Atom} {bindings : Bindings} {fuel : Nat}
    {param arg type : Atom} {params args : List Atom}
    (types : getAtomTypes space arg = [type]) (rejected : accepts param type = false)
    (groundParam : atomVariables param = []) (groundType : atomVariables type = [])
    (lengths : args.length = params.length) (errors : List Atom) (idx : Nat) :
    checkIfFunctionTypeIsApplicable.checkArgLoop (arg :: args) (param :: params) expr [bindings]
      errors space fuel idx = (errors ++ [mkError expr (.badArgType idx param type)], []) := by
  rw [checkIfFunctionTypeIsApplicable.checkArgLoop]
  simp only [List.foldl_cons, List.foldl_nil, checkArgumentType, rawTypeLookup, types,
    matchTypes_rejected groundParam groundType rejected, List.flatMap_cons, List.flatMap_nil,
    List.isEmpty_nil, if_true, List.append_nil]
  exact Prod.ext (checkArgLoop_none_errors args params _ _ lengths)
    (checkArgLoop_none args params _ _)

/-- Leaves checked once by ground parameters are their own argument values. -/
theorem interpretArgs_leaves {space : Space} {dispatch : GroundedDispatch}
    {params args : List Atom}
    (leaves : List.Forall₂ (fun param arg => isLeaf arg = true ∧ ArgumentChecked space param arg ∧
      atomVariables param = []) params args)
    (bindings : Bindings) {fuel : Nat}
    (enough : ∀ param ∈ params, matchFuel param + params.length + 1 ≤ fuel)
    (long : params.length < fuel) (live : List Atom) :
    interpretArgs space dispatch args params bindings fuel live =
      [(argumentPacket args, bindings)] := by
  induction leaves generalizing fuel live with
  | nil =>
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at long; omega⟩
      exact interpretArgs_nil_self bindings f live
  | @cons param arg params args first rest ih =>
      obtain ⟨leaf, checked, ground⟩ := first
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at long; omega⟩
      have headEnough := enough param (by simp)
      simp only [List.length_cons] at headEnough
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      refine interpretArgs_cons_self (fun live => ?_) (fun live => ?_) live
      · exact evalAtom_leaf leaf ground checked bindings (by omega) live
      · refine ih (fun other member => ?_) (by simp at long; omega) live
        have := enough other (by simp [member])
        simp only [List.length_cons] at this
        omega

/-- A typed call that stored ground equations rewrite evaluates to the replies
of those equations, through the ordinary call return. -/
theorem evalAtom_rewritten {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (notError : isErrorAtom (.expression (.symbol head :: args)) = false)
    (groundValue : atomVariables (.expression (.symbol head :: args)) = [])
    (groundEquations : GroundEquations space)
    (matched : space.atoms.flatMap (equationRhs (.expression (.symbol head :: args))) ≠ [])
    (plain : ∀ rhs ∈ space.atoms.flatMap (equationRhs (.expression (.symbol head :: args))),
      ∀ body, rhs ≠ .expression [.symbol "function", body])
    (checked : List.Forall₂ (ArgumentChecked space) params args)
    (returns : accepts expected range = true)
    (interpreted : (expected == Atom.atomType || expected == Atom.expressionType) = false)
    {fuel : Nat} (enough : matchFuel (arrowType params range) ≤ fuel)
    (enoughValue : matchFuel (.expression (.symbol head :: args)) ≤ fuel + 1)
    (arguments : ∀ live, interpretArgs space dispatch args params Bindings.empty (fuel + 1) live =
      [(argumentPacket args, Bindings.empty)])
    (live : List Atom) {results : ResultSet}
    (returned : (space.atoms.flatMap (equationRhs (.expression (.symbol head :: args)))).flatMap
      (fun rhs => ordinaryCallReturn (.expression (.symbol head :: args)) rhs Bindings.empty
        (fun value bindings => evalAtom space dispatch value (callReturnType range) bindings
          (fuel + 1) live)) = results)
    (successes : ∀ result ∈ results, isErrorAtom result.1 = false) :
    evalAtom space dispatch (.expression (.symbol head :: args)) expected Bindings.empty
      (fuel + 4) live = results := by
  have clean : isEmptyOrError (.expression (.symbol head :: args)) = false := by
    simp [isEmptyOrError, isEmptyAtom, Atom.empty, notError]
  have invoked := invoke_equations notExecutable notInstruction notError groundValue
    groundEquations matched plain (callReturnType range) enoughValue live none
  rw [returned] at invoked
  have interpretation := interpretExpression_typed (copies := 0) (expected := expected)
    declared ground notEmpty checked returns Bindings.empty enough arguments invoked
  rw [show (List.replicate (0 + 1) results).flatten = results by simp] at interpretation
  exact evalAtom_of_interpretExpression ⟨_, _, rfl⟩ clean interpreted interpretation successes

/-- Arguments of exactly one accepted type pass, after which the range is
compared with the expected type; a rejected range is the only error. -/
theorem checkIfFunctionTypeIsApplicable_returnRejected {space : Space} {head : String}
    {params args : List Atom} {range expected : Atom}
    (ground : atomVariables (arrowType params range) = [])
    (exact : List.Forall₂ (fun param arg => ∃ type, getAtomTypes space arg = [type] ∧
      accepts param type = true) params args)
    (groundExpected : atomVariables expected = [])
    (rejected : accepts expected range = false) (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel (arrowType params range) ≤ fuel) :
    checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args)) (arrowType params range)
      expected space bindings (fuel + 1) =
        .inl [mkError (.expression (.symbol head :: args)) (.badType expected range)] := by
  obtain ⟨paramsGround, rangeGround⟩ := arrowType_ground ground
  have admissible : ∀ param ∈ params, atomVariables param = [] ∧ matchFuel param ≤ fuel :=
    fun param member => ⟨paramsGround param member,
      by have := matchFuel_param_lt (range := range) member; omega⟩
  have strengthened : List.Forall₂ (fun param arg =>
      (atomVariables param = [] ∧ matchFuel param ≤ fuel) ∧
        ∃ type, getAtomTypes space arg = [type] ∧ accepts param type = true) params args :=
    (List.forall₂_and_left params args).mpr ⟨admissible, exact⟩
  have loop := checkArgLoop_exact (expr := .expression (.symbol head :: args))
    (bindings := bindings) (strengthened.imp fun _ _ ⟨⟨groundParam, enoughParam⟩, type,
      types, accepted⟩ => ⟨type, types, accepted, groundParam, enoughParam⟩) [] 1
  have lengths : args.length = params.length := exact.length_eq.symm
  rw [checkIfFunctionTypeIsApplicable]
  simp [getFunctionArgTypes_arrowType, getFunctionRetType_arrowType, loop, lengths,
    matchTypes_rejected groundExpected rangeGround rejected]

/-- A first argument whose only type the parameter rejects makes the call a
`BadArgType` error at position one. -/
theorem checkIfFunctionTypeIsApplicable_argumentRejected {space : Space} {head : String}
    {param arg type range expected : Atom} {params args : List Atom}
    (types : getAtomTypes space arg = [type]) (rejected : accepts param type = false)
    (groundParam : atomVariables param = []) (groundType : atomVariables type = [])
    (lengths : args.length = params.length) (bindings : Bindings) (fuel : Nat) :
    checkIfFunctionTypeIsApplicable (.expression (.symbol head :: arg :: args))
      (arrowType (param :: params) range) expected space bindings (fuel + 1) =
        .inl [mkError (.expression (.symbol head :: arg :: args)) (.badArgType 1 param type)] := by
  rw [checkIfFunctionTypeIsApplicable]
  simp [getFunctionArgTypes_arrowType, lengths,
    checkArgLoop_rejected types rejected groundParam groundType lengths]

/-- With ground stored equations, a ground value that no left side equals has no
equation match at any depth under any renaming. -/
theorem noEquationMatch_ground {space : Space} {value : Atom}
    (groundValue : atomVariables value = []) (groundEquations : GroundEquations space)
    (unmatched : space.atoms.flatMap (equationRhs value) = []) :
    NoEquationMatch space value := by
  intro avoid fuel
  cases fuel with
  | zero => rfl
  | succ n =>
      unfold queryEquationsAvoiding
      apply List.flatMap_eq_nil_iff.mpr
      intro entry member
      obtain ⟨atom, idx⟩ := entry
      have stored : atom ∈ space.atoms := by
        have projected := List.mem_map_of_mem (f := Prod.fst) member
        rwa [List.zipIdx_map_fst] at projected
      dsimp only
      split
      · rename_i lhs rhs
        obtain ⟨groundLhs, groundRhs⟩ := groundEquations lhs rhs stored
        have distinct : lhs ≠ value := by
          intro same
          have contributed : rhs ∈ space.atoms.flatMap (equationRhs value) :=
            List.mem_flatMap.mpr ⟨_, stored, by simp [equationRhs, same]⟩
          rw [unmatched] at contributed
          cases contributed
        simp only [freshenEquationAvoiding, renameAtom_of_atomVariables_eq_nil _ lhs groundLhs,
          renameAtom_of_atomVariables_eq_nil _ rhs groundRhs]
        rw [(matchAtoms_ground_ne (n + 1)).1 value lhs groundValue groundLhs (Ne.symm distinct)]
        rfl
      · rfl

/-! ## Other paths of a typed call -/

/-- An argument that evaluates to a different atom contributes that atom. -/
theorem interpretArgs_cons_value {space : Space} {dispatch : GroundedDispatch}
    {param arg reply : Atom} {params args : List Atom} {bindings : Bindings} {fuel : Nat}
    (first : ∀ live, evalAtom space dispatch arg param bindings fuel live = [(reply, bindings)])
    (running : isEmptyOrError reply = false)
    (rest : ∀ live, interpretArgs space dispatch args params bindings fuel live =
      [(argumentPacket args, bindings)])
    (live : List Atom) :
    interpretArgs space dispatch (arg :: args) (param :: params) bindings (fuel + 1) live =
      [(argumentPacket (reply :: args), bindings)] := by
  rw [interpretArgs, first]
  simp [running, rest]

/-- An argument that fails stops the argument list with its failure. -/
theorem interpretArgs_cons_failed {space : Space} {dispatch : GroundedDispatch}
    {param arg failure : Atom} {params args : List Atom} {bindings : Bindings} {fuel : Nat}
    (first : ∀ live, evalAtom space dispatch arg param bindings fuel live = [(failure, bindings)])
    (changed : failure ≠ arg) (failed : isEmptyOrError failure = true) (live : List Atom) :
    interpretArgs space dispatch (arg :: args) (param :: params) bindings (fuel + 1) live =
      [(failure, bindings)] := by
  rw [interpretArgs, first]
  simp [changed, failed]

/-- The function path rebuilds the call from the head and the argument packet,
or returns the argument failure. -/
theorem interpretFunction_arguments {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range : Atom} {others : List Atom}
    (declared : getAtomTypes space (.symbol head) = arrowType params range :: others)
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel (arrowType params range) ≤ fuel) {tail : Atom} {tailBindings : Bindings}
    (arguments : ∀ live, interpretArgs space dispatch args params bindings (fuel + 1) live =
      [(tail, tailBindings)])
    (live : List Atom) :
    interpretFunction space dispatch (.expression (.symbol head :: args)) (arrowType params range)
      bindings (fuel + 2) live =
        [(if argumentsSucceeded tail = false then tail
          else .expression (.symbol head :: argumentValues tail), tailBindings)] := by
  rw [interpretFunction, evalAtom_head declared ground notEmpty bindings enough]
  simp only [isEmptyOrError_symbol notEmpty, Bool.false_eq_true, if_false,
    getFunctionArgTypes_arrowType, arguments, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.map_cons, List.map_nil]
  split <;> rfl

/-- A head that evaluates to `Empty` is the function path's answer. -/
theorem interpretFunction_emptyHead {space : Space} {dispatch : GroundedDispatch}
    {args : List Atom} {type : Atom} (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    interpretFunction space dispatch (.expression (Atom.empty :: args)) type bindings (fuel + 2)
      live = [(Atom.empty, bindings)] := by
  rw [interpretFunction, evalAtom]
  simp [isEmptyOrError, isEmptyAtom]

/-- Ordinary invocation passes an error through. -/
theorem invoke_passthrough {space : Space} {dispatch : GroundedDispatch} {error : Atom}
    (failed : isErrorAtom error = true) (expected : Atom) (bindings : Bindings) (fuel : Nat)
    (live : List Atom) (caller : Option Atom) :
    invoke space dispatch (.ordinary expected) error bindings (fuel + 1) live caller =
      [(error, bindings)] := by
  rw [invoke]
  simp [InvocationMode.errorPassthrough, failed]

/-- A symbol that no merged equation answers is returned unchanged. -/
theorem invoke_symbol_refused {space : Space} {dispatch : GroundedDispatch} {name : String}
    {expected : Atom} {bindings : Bindings} {fuel : Nat} {live : List Atom}
    (refused : rawQueryResults space (.symbol name) expected bindings fuel live = [])
    (caller : Option Atom) :
    invoke space dispatch (.ordinary expected) (.symbol name) bindings (fuel + 1) live caller =
      [(.symbol name, bindings)] := by
  rw [invoke]
  simp [InvocationMode.errorPassthrough, isErrorAtom, InvocationMode.expected, refused]

/-- An executable head runs: its replies are merged with the incoming record and
returned through the ordinary call return. -/
theorem invoke_executable {space : Space} {dispatch : GroundedDispatch} {operator : Atom}
    {arguments : List Atom} {replies : List (Atom × Bindings)}
    (executable : dispatch.isExecutable operator = true)
    (executes : dispatch.execute operator arguments = .ok replies)
    (notError : isErrorAtom (.expression (operator :: arguments)) = false)
    (expected : Atom) {fuel : Nat} (live : List Atom) (caller : Option Atom)
    {merged : List (Atom × Bindings)}
    (merging : (replies.flatMap fun reply => (mergeBindings reply.2 Bindings.empty (fuel + 1)).map
      fun bindings => (bindings.applyFull reply.1 (fuel + 1), bindings)) = merged)
    (nonempty : merged ≠ [])
    (plain : ∀ reply ∈ merged, ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    invoke space dispatch (.ordinary expected) (.expression (operator :: arguments))
        Bindings.empty (fuel + 2) live caller =
      merged.flatMap fun reply => ordinaryCallReturn (.expression (operator :: arguments))
        reply.1 reply.2
          (fun value bindings => evalAtom space dispatch value expected bindings (fuel + 1) live) := by
  rw [invoke]
  have full : merged.isEmpty = false := by
    cases merged with
    | nil => exact absurd rfl nonempty
    | cons _ _ => rfl
  simp only [InvocationMode.errorPassthrough, notError, Bool.false_eq_true, if_false,
    executable, if_true, executes, merging, full]
  apply List.flatMap_congr
  intro reply member
  rw [invocationResult_plain (plain reply member)]
  simp

/-- A typed call with one declaration and one applicable record follows its
function path and hands the rebuilt call, or the argument failure, to the
invocation. -/
theorem interpretExpression_single {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    {bindings other : Bindings} {fuel : Nat}
    (applicable : checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args))
      (arrowType params range) expected space bindings (fuel + 2) = .inr [other])
    {reply : Atom} {replyBindings : Bindings}
    (interpreted : ∀ live, interpretFunction space dispatch (.expression (.symbol head :: args))
      (arrowType params range) other (fuel + 2) live = [(reply, replyBindings)])
    {live : List Atom} {results : ResultSet}
    (invoked : invoke space dispatch (.ordinary (callReturnType range)) reply replyBindings
      (fuel + 2) live = results) :
    interpretExpression space dispatch (.expression (.symbol head :: args)) expected bindings
      (fuel + 3) live = results := by
  rw [interpretExpression]
  simp only [declared, isFunctionType_arrowType, if_true, applicable,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, interpreted,
    callReturnType_arrowType, invoked]
  have nonFunction : ([arrowType params range].any fun type =>
      !isFunctionType type || type == Atom.undefinedType) = false := by
    simp [isFunctionType_arrowType, arrowType_beq_symbol, Atom.undefinedType]
  simp only [nonFunction, Bool.false_eq_true, if_false, List.append_nil, Bool.not_false, if_true]
  cases results with
  | nil => simp [isFunctionType_arrowType, applicable]
  | cons _ _ => simp

/-- The function path with a head and arguments that may extend the record. -/
theorem interpretFunction_general {space : Space} {dispatch : GroundedDispatch} {op type : Atom}
    {params args : List Atom} {bindings headBindings : Bindings} {fuel : Nat} {tail : Atom}
    {tailBindings : Bindings}
    (head : ∀ live, evalAtom space dispatch op type bindings fuel live = [(op, headBindings)])
    (running : isEmptyOrError op = false)
    (argTypes : getFunctionArgTypes type = some params)
    (arguments : ∀ live, interpretArgs space dispatch args params headBindings fuel live =
      [(tail, tailBindings)])
    (live : List Atom) :
    interpretFunction space dispatch (.expression (op :: args)) type bindings (fuel + 1) live =
      [(if argumentsSucceeded tail = false then tail
        else .expression (op :: argumentValues tail), tailBindings)] := by
  rw [interpretFunction, head]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, running, Bool.false_eq_true,
    if_false, argTypes, arguments, List.map_cons, List.map_nil]
  split <;> rfl

/-- An argument evaluated to itself under a record that its check may extend. -/
theorem interpretArgs_cons_general {space : Space} {dispatch : GroundedDispatch}
    {param arg : Atom} {params args : List Atom} {bindings middle : Bindings} {fuel : Nat}
    {tail : Atom} {tailBindings : Bindings}
    (first : ∀ live, evalAtom space dispatch arg param bindings fuel live = [(arg, middle)])
    (rest : ∀ live, interpretArgs space dispatch args params middle fuel live =
      [(tail, tailBindings)])
    (live : List Atom) :
    interpretArgs space dispatch (arg :: args) (param :: params) bindings (fuel + 1) live =
      [(if argumentsSucceeded tail = false then tail
        else argumentPacket (arg :: argumentValues tail), tailBindings)] := by
  rw [interpretArgs, first]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, bne_self_eq_false,
    Bool.false_and, Bool.false_eq_true, if_false, rest, List.map_cons, List.map_nil]
  split <;> rfl

/-- Raw invocation of a ground call that stored ground equations rewrite. -/
theorem invoke_raw_equations {space : Space} {dispatch : GroundedDispatch} {operator : Atom}
    {arguments : List Atom}
    (notExecutable : dispatch.isExecutable operator = false)
    (notInstruction : minimalInstruction (.expression (operator :: arguments)) = false)
    (groundValue : atomVariables (.expression (operator :: arguments)) = [])
    (groundEquations : GroundEquations space)
    (matched : space.atoms.flatMap (equationRhs (.expression (operator :: arguments))) ≠ [])
    (plain : ∀ rhs ∈ space.atoms.flatMap (equationRhs (.expression (operator :: arguments))),
      ∀ body, rhs ≠ .expression [.symbol "function", body])
    {fuel : Nat} (enough : matchFuel (.expression (operator :: arguments)) ≤ fuel + 1)
    (live : List Atom) (caller : Option Atom) :
    invoke space dispatch .raw (.expression (operator :: arguments)) Bindings.empty (fuel + 2)
        live caller =
      (space.atoms.flatMap (equationRhs (.expression (operator :: arguments)))).map
        fun rhs => (rhs, Bindings.empty) := by
  rw [invoke]
  simp only [InvocationMode.errorPassthrough, Bool.false_eq_true, if_false, notExecutable,
    notInstruction, InvocationMode.expected,
    rawQueryResults_ground groundValue groundEquations Atom.undefinedType enough live,
    List.isEmpty_map, List.flatMap_map]
  have nonempty : (space.atoms.flatMap
      (equationRhs (.expression (operator :: arguments)))).isEmpty = false := by
    cases found : space.atoms.flatMap (equationRhs (.expression (operator :: arguments))) with
    | nil => exact absurd found matched
    | cons _ _ => rfl
  simp only [nonempty, Bool.false_eq_true, if_false]
  rw [List.map_eq_flatMap]
  apply List.flatMap_congr
  intro rhs member
  rw [invocationResult_plain (plain rhs member)]
  simp

/-- Ordinary invocation of `(eval atom)` runs the instruction: it invokes the
materialized atom raw and returns its replies through the ordinary call return. -/
theorem invoke_eval {space : Space} {dispatch : GroundedDispatch} {atom : Atom}
    (notExecutable : dispatch.isExecutable (.symbol "eval") = false)
    (expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom)
    (caller : Option Atom) :
    invoke space dispatch (.ordinary expected) (.expression [.symbol "eval", atom]) bindings
        (fuel + 4) live caller =
      (invoke space dispatch .raw (bindings.applyFull atom (fuel + 1)) bindings (fuel + 1)
          (expected :: live) caller).flatMap fun reply =>
        ordinaryCallReturn (.expression [.symbol "eval", atom]) reply.1 reply.2
          (fun value bindings => evalAtom space dispatch value expected bindings (fuel + 3)
            live) := by
  rw [invoke]
  have instruction : minimalInstruction (.expression [.symbol "eval", atom]) = true := rfl
  have notError : isErrorAtom (.expression [.symbol "eval", atom]) = false := rfl
  simp only [InvocationMode.errorPassthrough, notError, Bool.false_eq_true, if_false,
    notExecutable, instruction, if_true, InvocationMode.pendingScope]
  rw [minimalRun]
  simp only [instruction, if_true]
  rw [minimalStep]
  split
  · rename_i same
    simp at same
  · rfl

/-! ## Theorem A: a completed value delivers itself -/

/-- From some fuel on, a completed value evaluates under every accepted expected
type to itself, once, with the bindings it was asked under. The bound is
uniform in the expected type, the bindings and the retained atoms. -/
theorem evalAtom_completed_accepted {space : Space} {dispatch : GroundedDispatch}
    {value range : Atom} (completed : Completed space dispatch value range) :
    ∃ N, ∀ (k : Nat) (expected : Atom) (bindings : Bindings) (live : List Atom),
      accepts expected range = true →
        evalAtom space dispatch value expected bindings (N + k) live = [(value, bindings)] := by
  refine Completed.rec
    (motive_1 := fun value range _ => ∃ N, ∀ (k : Nat) (expected : Atom) (bindings : Bindings)
      (live : List Atom), accepts expected range = true →
        evalAtom space dispatch value expected bindings (N + k) live = [(value, bindings)])
    (motive_2 := fun params args _ => (∀ param ∈ params, atomVariables param = []) →
      List.Forall₂ (ArgumentChecked space) params args ∧
        ∃ N, ∀ (k : Nat) (bindings : Bindings) (live : List Atom),
          interpretArgs space dispatch args params bindings (N + k) live =
            [(argumentPacket args, bindings)])
    ?typed ?nil ?held ?leaf ?value completed
  case typed =>
    intro head params args range declared ground notEmpty notExecutable notInstruction
      noEquation _ ih
    obtain ⟨paramsGround, _⟩ := arrowType_ground ground
    obtain ⟨checked, bound, deliver⟩ := ih paramsGround
    refine ⟨matchFuel (arrowType params range) + bound + 4,
      fun k expected bindings live returns => ?_⟩
    rw [show matchFuel (arrowType params range) + bound + 4 + k =
      matchFuel (arrowType params range) + bound + k + 4 by omega]
    refine evalAtom_completed_step declared ground notEmpty notExecutable notInstruction
      noEquation checked returns bindings (by omega) (fun live => ?_) live
    rw [show matchFuel (arrowType params range) + bound + k + 1 =
      bound + (matchFuel (arrowType params range) + k + 1) by omega]
    exact deliver _ bindings live
  case nil =>
    intro _
    refine ⟨List.Forall₂.nil, 1, fun k bindings live => ?_⟩
    rw [show 1 + k = k + 1 by omega]
    exact interpretArgs_nil_self bindings k live
  case held =>
    intro arg params args checked _ ih paramsGround
    obtain ⟨restChecked, bound, deliver⟩ := ih fun other member =>
      paramsGround other (by simp [member])
    refine ⟨List.Forall₂.cons checked restChecked, bound + 2, fun k bindings live => ?_⟩
    rw [show bound + 2 + k = bound + 1 + k + 1 by omega]
    refine interpretArgs_cons_self (fun live => ?_) (fun live => ?_) live
    · rw [show bound + 1 + k = bound + k + 1 by omega]
      exact evalAtom_held arg bindings _ live
    · rw [show bound + 1 + k = bound + (1 + k) by omega]
      exact deliver _ bindings live
  case leaf =>
    intro param arg params args leaf checked _ ih paramsGround
    have paramGround := paramsGround param (by simp)
    obtain ⟨restChecked, bound, deliver⟩ := ih fun other member =>
      paramsGround other (by simp [member])
    refine ⟨List.Forall₂.cons checked restChecked, bound + matchFuel param + 2,
      fun k bindings live => ?_⟩
    rw [show bound + matchFuel param + 2 + k = bound + matchFuel param + 1 + k + 1 by omega]
    refine interpretArgs_cons_self (fun live => ?_) (fun live => ?_) live
    · rw [show bound + matchFuel param + 1 + k = bound + matchFuel param + k + 1 by omega]
      exact evalAtom_leaf leaf paramGround checked bindings (by omega) live
    · rw [show bound + matchFuel param + 1 + k = bound + (matchFuel param + 1 + k) by omega]
      exact deliver _ bindings live
  case value =>
    intro param arg range params args _ fits checked _ ihValue ihRest paramsGround
    obtain ⟨restChecked, bound, deliver⟩ := ihRest fun other member =>
      paramsGround other (by simp [member])
    obtain ⟨valueBound, selfValue⟩ := ihValue
    have accepted : accepts param range = true := by
      rcases fits with rfl | rfl
      · exact accepts_undefined _
      · exact accepts_self _
    refine ⟨List.Forall₂.cons checked restChecked, bound + valueBound + 1,
      fun k bindings live => ?_⟩
    rw [show bound + valueBound + 1 + k = bound + valueBound + k + 1 by omega]
    refine interpretArgs_cons_self (fun live => ?_) (fun live => ?_) live
    · rw [show bound + valueBound + k = valueBound + (bound + k) by omega]
      exact selfValue _ param bindings live accepted
    · rw [show bound + valueBound + k = bound + (valueBound + k) by omega]
      exact deliver _ bindings live

/-- **Theorem A.** A completed value, interpreted under no expected type
(`%Undefined%`) or under its range, evaluates to exactly `[(value, bindings)]`
from some fuel on: one answer, the value itself, the incoming bindings. -/
theorem evalAtom_completed {space : Space} {dispatch : GroundedDispatch} {value range : Atom}
    (completed : Completed space dispatch value range) :
    ∃ N, ∀ (k : Nat) (expected : Atom) (bindings : Bindings) (live : List Atom),
      (expected = Atom.undefinedType ∨ expected = range) →
        evalAtom space dispatch value expected bindings (N + k) live = [(value, bindings)] := by
  obtain ⟨N, deliver⟩ := evalAtom_completed_accepted completed
  refine ⟨N, fun k expected bindings live accepted => deliver k expected bindings live ?_⟩
  rcases accepted with rfl | rfl
  · exact accepts_undefined _
  · exact accepts_self _

/-! ## Inversion -/

theorem arrowType_inj {params params' : List Atom} {range range' : Atom}
    (same : arrowType params range = arrowType params' range') :
    params = params' ∧ range = range' := by
  simp only [arrowType, Atom.expression.injEq, List.cons.injEq, true_and] at same
  obtain ⟨paramsSame, rangeSame⟩ := List.append_inj' same rfl
  exact ⟨paramsSame, by simpa using rangeSame⟩

/-- Every argument of a completed value passes its parameter check once. -/
theorem CompletedArguments.checked_head {space : Space} {dispatch : GroundedDispatch}
    {param arg : Atom} {params args : List Atom}
    (arguments : CompletedArguments space dispatch (param :: params) (arg :: args)) :
    ArgumentChecked space param arg := by
  cases arguments with
  | held checked _ => exact checked
  | leaf _ checked _ => exact checked
  | value _ _ checked _ => exact checked

/-- How an argument of a completed value is its own value. -/
theorem CompletedArguments.head_cases {space : Space} {dispatch : GroundedDispatch}
    {param arg : Atom} {params args : List Atom}
    (arguments : CompletedArguments space dispatch (param :: params) (arg :: args)) :
    param = Atom.atomType ∨ isLeaf arg = true ∨
      ∃ range, Completed space dispatch arg range ∧
        (param = Atom.undefinedType ∨ param = range) := by
  cases arguments with
  | held _ _ => exact Or.inl rfl
  | leaf leaf _ _ => exact Or.inr (Or.inl leaf)
  | value completed fits _ _ => exact Or.inr (Or.inr ⟨_, completed, fits⟩)

/-! ## Controls -/

namespace Controls

/-- `(: atom type)` -/
abbrev declaration (atom type : Atom) : Atom := .expression [.symbol ":", atom, type]
/-- `(= lhs rhs)` -/
abbrev equation (lhs rhs : Atom) : Atom := .expression [.symbol "=", lhs, rhs]

abbrev nat : Atom := .symbol "Nat"
abbrev bool : Atom := .symbol "Bool"
abbrev zero : Atom := .symbol "Z"
abbrev succ (atom : Atom) : Atom := .expression [.symbol "S", atom]

/-- `Z : Nat` and `S : (-> Nat Nat)`; no equations. -/
def natSpace : Space :=
  Space.ofList [declaration zero nat, declaration (.symbol "S") (arrowType [nat] nat)]

theorem natSpace_ground : GroundEquations natSpace := by
  intro lhs rhs member
  simp [natSpace, Space.ofList, arrowType] at member

theorem natSpace_succ : getAtomTypes natSpace (.symbol "S") = [arrowType [nat] nat] := rfl

theorem natSpace_zero : ArgumentChecked natSpace nat zero := ⟨by decide, by decide⟩

/-- Positive control: `(S Z)` is completed with range `Nat`. -/
theorem succ_zero_completed : Completed natSpace GroundedDispatch.none (succ zero) nat :=
  .typed natSpace_succ rfl (by decide) rfl rfl
    (noEquationMatch_ground rfl natSpace_ground rfl)
    (.leaf rfl natSpace_zero .nil)

/-- Positive control: a completed value is an argument of a completed value. -/
theorem succ_succ_zero_completed :
    Completed natSpace GroundedDispatch.none (succ (succ zero)) nat :=
  .typed natSpace_succ rfl (by decide) rfl rfl
    (noEquationMatch_ground rfl natSpace_ground rfl)
    (.value succ_zero_completed (Or.inr rfl) ⟨by decide, by decide⟩ .nil)

example : ∃ N, ∀ (k : Nat) (expected : Atom) (bindings : Bindings) (live : List Atom),
    (expected = Atom.undefinedType ∨ expected = nat) →
      evalAtom natSpace GroundedDispatch.none (succ (succ zero)) expected bindings (N + k) live =
        [(succ (succ zero), bindings)] :=
  evalAtom_completed succ_succ_zero_completed

/-- Executable positive control at one fuel. -/
example : evalAtom natSpace GroundedDispatch.none (succ (succ zero)) Atom.undefinedType
    Bindings.empty 16 = [(succ (succ zero), Bindings.empty)] := by decide

/-- `Box : (-> Atom Boxed)` holds an unevaluated call that an equation would rewrite. -/
def boxSpace : Space :=
  Space.ofList [declaration (.symbol "Box") (arrowType [Atom.atomType] (.symbol "Boxed")),
    equation (.expression [.symbol "foo"]) (.symbol "bar")]

theorem boxSpace_ground : GroundEquations boxSpace := by
  intro lhs rhs member
  simp [boxSpace, Space.ofList, arrowType] at member
  obtain ⟨rfl, rfl⟩ := member
  exact ⟨rfl, rfl⟩

/-- Positive control: an `Atom` parameter holds a reducible argument. -/
theorem box_completed :
    Completed boxSpace GroundedDispatch.none
      (.expression [.symbol "Box", .expression [.symbol "foo"]]) (.symbol "Boxed") :=
  .typed rfl rfl (by decide) rfl rfl
    (noEquationMatch_ground rfl boxSpace_ground rfl)
    (.held ⟨by decide, by decide⟩ .nil)

/-- The held argument itself is not its own value. -/
example : evalAtom boxSpace GroundedDispatch.none (.expression [.symbol "foo"])
    Atom.undefinedType Bindings.empty 20 = [(.symbol "bar", Bindings.empty)] := by decide

example : evalAtom boxSpace GroundedDispatch.none
    (.expression [.symbol "Box", .expression [.symbol "foo"]]) Atom.undefinedType
    Bindings.empty 20 =
      [(.expression [.symbol "Box", .expression [.symbol "foo"]], Bindings.empty)] := by decide

theorem matchFuel_nat : matchFuel nat = 1 := rfl
theorem matchFuel_natArrow : matchFuel (arrowType [nat] nat) = 5 := by decide
theorem matchFuel_succ_zero : matchFuel (succ zero) = 4 := by decide

theorem natSpace_zero_leaf {dispatch : GroundedDispatch} {bindings : Bindings} {fuel : Nat}
    (enough : 3 ≤ fuel) (live : List Atom) :
    interpretArgs natSpace dispatch [zero] [nat] bindings fuel live =
      [(argumentPacket [zero], bindings)] :=
  interpretArgs_leaves (.cons ⟨rfl, natSpace_zero, rfl⟩ .nil) bindings
    (fun param member => by simp at member; subst member; simpa [matchFuel] using enough)
    (by simp; omega) live

/-! ### Theorem C: an equation added to the program reopens the value -/

/-- `natSpace` with the equation `(= (S Z) Z)`. -/
def rewrittenSpace : Space := natSpace.add (equation (succ zero) zero)

theorem rewrittenSpace_ground : GroundEquations rewrittenSpace := by
  intro lhs rhs member
  simp [rewrittenSpace, natSpace, Space.add, Space.ofList, arrowType] at member
  obtain ⟨rfl, rfl⟩ := member
  exact ⟨rfl, rfl⟩

theorem rewrittenSpace_zero_leaf {bindings : Bindings} {fuel : Nat} (enough : 3 ≤ fuel)
    (live : List Atom) :
    interpretArgs rewrittenSpace GroundedDispatch.none [zero] [nat] bindings fuel live =
      [(argumentPacket [zero], bindings)] :=
  interpretArgs_leaves (.cons ⟨rfl, ⟨by decide, by decide⟩, rfl⟩ .nil) bindings
    (fun param member => by simp at member; subst member; simpa [matchFuel] using enough)
    (by simp; omega) live

/-- **Theorem C.** `(S Z)` is completed in `natSpace`; after one equation whose
left side is `(S Z)` it is not completed, and it evaluates to `Z` at every
sufficiently large fuel. A certificate is a fact about one program. -/
theorem completed_reopens_after_equation :
    Completed natSpace GroundedDispatch.none (succ zero) nat ∧
      (∀ range, ¬Completed rewrittenSpace GroundedDispatch.none (succ zero) range) ∧
      ∃ N, ∀ (k : Nat) (live : List Atom),
        evalAtom rewrittenSpace GroundedDispatch.none (succ zero) Atom.undefinedType
          Bindings.empty (N + k) live = [(zero, Bindings.empty)] := by
  refine ⟨succ_zero_completed, fun range completed => ?_, 9, fun k live => ?_⟩
  · cases completed with
    | typed _ _ _ _ _ noEquation _ => exact absurd (noEquation [] 10) (by decide)
  · rw [show 9 + k = 5 + k + 4 by omega]
    refine evalAtom_rewritten rfl rfl (by decide) rfl rfl rfl rfl rewrittenSpace_ground
      (by decide) (fun rhs member body => ?_) (.cons ⟨by decide, by decide⟩ .nil)
      (accepts_undefined _) rfl (by rw [matchFuel_natArrow]; omega)
      (by rw [matchFuel_succ_zero]; omega)
      (fun live => rewrittenSpace_zero_leaf (by omega) live) live ?_ ?_
    · have rhs_eq : rhs = zero := by
        have : rewrittenSpace.atoms.flatMap (equationRhs (succ zero)) = [zero] := by decide
        rw [this] at member
        simpa using member
      subst rhs_eq
      simp
    · have rhs : rewrittenSpace.atoms.flatMap (equationRhs (succ zero)) = [zero] := by decide
      rw [rhs]
      have leaf := evalAtom_leaf (space := rewrittenSpace) (dispatch := GroundedDispatch.none)
        (param := nat) (arg := zero) rfl rfl ⟨by decide, by decide⟩ Bindings.empty
        (fuel := 5 + k) (by rw [matchFuel_nat]; omega) live
      simp [ordinaryCallReturn, callReturnType, Atom.notReducible, isEmptyOrError,
        isEmptyAtom, isErrorAtom, Atom.empty, Atom.expressionType, leaf]
    · intro result member
      simp at member
      subst member
      rfl

/-! ### Theorem C′: a changed or added declaration reopens the value -/

/-- `Z` is declared `Bool` instead of `Nat`. -/
def retypedSpace : Space :=
  Space.ofList [declaration zero bool, declaration (.symbol "S") (arrowType [nat] nat)]

/-- `S` is declared twice. -/
def redeclaredSpace : Space := natSpace.add (declaration (.symbol "S") (arrowType [nat] nat))

theorem redeclaredSpace_ground : GroundEquations redeclaredSpace := by
  intro lhs rhs member
  simp [redeclaredSpace, natSpace, Space.add, Space.ofList, arrowType] at member

/-- **Theorem C′.** Changing the declaration of the argument turns the value
into a `BadArgType` error; declaring the head a second time delivers the value
twice. Neither program completes `(S Z)`. -/
theorem completed_reopens_after_declaration :
    (∀ range, ¬Completed retypedSpace GroundedDispatch.none (succ zero) range) ∧
      (∃ N, ∀ (k : Nat) (bindings : Bindings) (live : List Atom),
        evalAtom retypedSpace GroundedDispatch.none (succ zero) Atom.undefinedType bindings
          (N + k) live = [(mkError (succ zero) (.badArgType 1 nat bool), bindings)]) ∧
      (∀ range, ¬Completed redeclaredSpace GroundedDispatch.none (succ zero) range) ∧
      ∃ N, ∀ (k : Nat) (bindings : Bindings) (live : List Atom),
        evalAtom redeclaredSpace GroundedDispatch.none (succ zero) Atom.undefinedType bindings
          (N + k) live = [(succ zero, bindings), (succ zero, bindings)] := by
  refine ⟨fun range completed => ?_, ⟨3, fun k bindings live => ?_⟩,
    fun range completed => ?_, ⟨9, fun k bindings live => ?_⟩⟩
  · cases completed with
    | typed declared _ _ _ _ _ arguments =>
        have types : getAtomTypes retypedSpace (.symbol "S") = [arrowType [nat] nat] := rfl
        rw [types, List.cons.injEq] at declared
        obtain ⟨rfl, -⟩ := arrowType_inj declared.1.symm
        exact absurd arguments.checked_head.once (by decide)
  · rw [show 3 + k = k + 2 + 1 by omega]
    refine evalAtom_of_interpretExpression_errors ⟨_, _, rfl⟩ rfl rfl
      (interpretExpression_rejected (type := arrowType [nat] nat) rfl
        (isFunctionType_arrowType _ _)
        (checkIfFunctionTypeIsApplicable_argumentRejected (type := bool) rfl rfl rfl rfl rfl
          bindings k)) ?_
    intro result member
    simp at member
    subst member
    rfl
  · cases completed with
    | typed declared _ _ _ _ _ _ =>
        have types : getAtomTypes redeclaredSpace (.symbol "S") =
            [arrowType [nat] nat, arrowType [nat] nat] := rfl
        rw [types] at declared
        simp at declared
  · rw [show 9 + k = 5 + k + 3 + 1 by omega]
    have refused := invoke_completed (space := redeclaredSpace)
      (dispatch := GroundedDispatch.none) (operator := .symbol "S") (arguments := [zero]) rfl rfl
      (noEquationMatch_ground rfl redeclaredSpace_ground rfl) rfl (callReturnType nat) bindings
      (5 + k + 1) live none
    have interpretation := interpretExpression_typed (copies := 1)
      (expected := Atom.undefinedType) (live := live) rfl rfl (by decide)
      (.cons ⟨by decide, by decide⟩ .nil) (accepts_undefined _) bindings
      (by rw [matchFuel_natArrow]; omega)
      (fun live => interpretArgs_leaves (.cons ⟨rfl, ⟨by decide, by decide⟩, rfl⟩ .nil) bindings
        (fun param member => by simp at member; subst member; rw [matchFuel_nat]; simp; omega)
        (by simp) live) refused
    refine evalAtom_of_interpretExpression ⟨_, _, rfl⟩ rfl rfl interpretation ?_
    intro result member
    simp at member
    subst member
    rfl

/-! ### Theorem D: equations that refuse still count -/

/-- Two equations `(= (S Z) NotReducible)`. -/
def refusedSpace : Space :=
  (natSpace.add (equation (succ zero) Atom.notReducible)).add
    (equation (succ zero) Atom.notReducible)

theorem refusedSpace_ground : GroundEquations refusedSpace := by
  intro lhs rhs member
  simp [refusedSpace, natSpace, Space.add, Space.ofList, arrowType] at member
  obtain ⟨rfl, rfl⟩ := member
  exact ⟨rfl, rfl⟩

/-- **Theorem D.** Each matching equation whose body is `NotReducible` returns
the call itself: two such equations deliver `(S Z)` twice. A certificate that
answers once must therefore require that no equation matched at all. -/
theorem notReducible_value_multiplies :
    (∀ range, ¬Completed refusedSpace GroundedDispatch.none (succ zero) range) ∧
      ∃ N, ∀ (k : Nat) (live : List Atom),
        evalAtom refusedSpace GroundedDispatch.none (succ zero) Atom.undefinedType
          Bindings.empty (N + k) live =
            [(succ zero, Bindings.empty), (succ zero, Bindings.empty)] := by
  have rhs : refusedSpace.atoms.flatMap (equationRhs (succ zero)) =
      [Atom.notReducible, Atom.notReducible] := by decide
  refine ⟨fun range completed => ?_, 9, fun k live => ?_⟩
  · cases completed with
    | typed _ _ _ _ _ noEquation _ => exact absurd (noEquation [] 10) (by decide)
  · rw [show 9 + k = 5 + k + 4 by omega]
    refine evalAtom_rewritten rfl rfl (by decide) rfl rfl rfl rfl refusedSpace_ground
      (by rw [rhs]; simp) (fun reply member body => ?_) (.cons ⟨by decide, by decide⟩ .nil)
      (accepts_undefined _) rfl (by rw [matchFuel_natArrow]; omega)
      (by rw [matchFuel_succ_zero]; omega)
      (fun live => interpretArgs_leaves (.cons ⟨rfl, ⟨by decide, by decide⟩, rfl⟩ .nil)
        Bindings.empty
        (fun param member => by simp at member; subst member; rw [matchFuel_nat]; simp; omega)
        (by simp) live) live ?_ ?_
    · rw [rhs] at member
      simp at member
      subst member
      simp [Atom.notReducible]
    · rw [rhs]
      simp
    · intro result member
      simp at member
      subst member
      rfl

/-! ### Theorem E: a produced value need not be its own value -/

abbrev wrapCall : Atom := .expression [.symbol "wrap"]
abbrev fooCall : Atom := .expression [.symbol "foo"]
abbrev thing : Atom := .symbol "Thing"
abbrev bar : Atom := .symbol "bar"

/-- `wrap : (-> Atom)` returns the unevaluated call `(foo)`, which reduces. -/
def wrapSpace : Space :=
  Space.ofList [declaration (.symbol "wrap") (arrowType [] Atom.atomType),
    equation wrapCall fooCall,
    declaration (.symbol "foo") (arrowType [] thing),
    equation fooCall bar]

theorem wrapSpace_ground : GroundEquations wrapSpace := by
  intro lhs rhs member
  simp [wrapSpace, Space.ofList, arrowType] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- **Theorem E.** `(wrap)` evaluates to `(foo)` at every sufficiently large
fuel, and `(foo)` evaluates to `bar`: the produced value is not its own value.
Producer results therefore receive no certificate. -/
theorem completedProvenance_not_fixpoint :
    ∃ N, ∀ (k : Nat) (live : List Atom),
      evalAtom wrapSpace GroundedDispatch.none wrapCall Atom.undefinedType Bindings.empty
          (N + k) live = [(fooCall, Bindings.empty)] ∧
        evalAtom wrapSpace GroundedDispatch.none fooCall Atom.undefinedType Bindings.empty
          (N + k) live = [(bar, Bindings.empty)] := by
  have wrapRhs : wrapSpace.atoms.flatMap (equationRhs wrapCall) = [fooCall] := by decide
  have fooRhs : wrapSpace.atoms.flatMap (equationRhs fooCall) = [bar] := by decide
  have wrapFuel : matchFuel (arrowType [] Atom.atomType) = 4 := by decide
  have fooFuel : matchFuel (arrowType [] thing) = 4 := by decide
  have wrapCallFuel : matchFuel wrapCall = 3 := by decide
  have fooCallFuel : matchFuel fooCall = 3 := by decide
  refine ⟨8, fun k live => ⟨?_, ?_⟩⟩
  · rw [show 8 + k = 4 + k + 4 by omega]
    refine evalAtom_rewritten (params := []) (range := Atom.atomType) rfl rfl (by decide) rfl rfl
      rfl rfl wrapSpace_ground (by rw [wrapRhs]; simp) (fun reply member body => ?_) .nil
      (accepts_undefined _) rfl (by rw [wrapFuel]; omega) (by rw [wrapCallFuel]; omega)
      (fun live => interpretArgs_nil_self Bindings.empty _ live) live ?_ ?_
    · rw [wrapRhs] at member
      simp at member
      subst member
      simp
    · rw [wrapRhs]
      have held := evalAtom_held (space := wrapSpace) (dispatch := GroundedDispatch.none) fooCall
        Bindings.empty (4 + k) live
      have returned : callReturnType Atom.atomType = Atom.atomType := by decide
      rw [returned]
      simp [ordinaryCallReturn, Atom.notReducible, isEmptyOrError, isEmptyAtom, isErrorAtom,
        Atom.empty, held]
    · intro result member
      simp at member
      subst member
      rfl
  · rw [show 8 + k = 4 + k + 4 by omega]
    refine evalAtom_rewritten (params := []) (range := thing) rfl rfl (by decide) rfl rfl
      rfl rfl wrapSpace_ground (by rw [fooRhs]; simp) (fun reply member body => ?_) .nil
      (accepts_undefined _) rfl (by rw [fooFuel]; omega) (by rw [fooCallFuel]; omega)
      (fun live => interpretArgs_nil_self Bindings.empty _ live) live ?_ ?_
    · rw [fooRhs] at member
      simp at member
      subst member
      simp
    · rw [fooRhs]
      have leaf := evalAtom_leaf (space := wrapSpace) (dispatch := GroundedDispatch.none)
        (param := thing) (arg := bar) rfl rfl ⟨by decide, by decide⟩ Bindings.empty
        (fuel := 3 + k + 1) (by simp [matchFuel]) live
      rw [show 4 + k + 1 = 3 + k + 1 + 1 by omega]
      simp [ordinaryCallReturn, callReturnType, Atom.notReducible, isEmptyOrError,
        isEmptyAtom, isErrorAtom, Atom.empty, Atom.expressionType, leaf]
    · intro result member
      simp at member
      subst member
      rfl

/-! ### Theorem F: finite fuel changes the answer -/

/-- **Theorem F.** The completed value `(S Z)` evaluates to itself only from
fuel 9 on. Below that the evaluator answers nothing, or reports type errors that
truncated type matching produced: `BadArgType` for `Z : Nat` against `Nat` at
fuel 3, and `BadType` of the head's arrow against itself at fuels 4 to 8. -/
theorem completed_fuel_sensitive :
    Completed natSpace GroundedDispatch.none (succ zero) nat ∧
      evalAtom natSpace GroundedDispatch.none (succ zero) Atom.undefinedType Bindings.empty 2 =
        [] ∧
      evalAtom natSpace GroundedDispatch.none (succ zero) Atom.undefinedType Bindings.empty 3 =
        [(mkError (succ zero) (.badArgType 1 nat nat), Bindings.empty)] ∧
      (∀ fuel, 4 ≤ fuel → fuel ≤ 8 →
        evalAtom natSpace GroundedDispatch.none (succ zero) Atom.undefinedType Bindings.empty
          fuel = [(mkError (.symbol "S") (.badType (arrowType [nat] nat) (arrowType [nat] nat)),
            Bindings.empty)]) ∧
      evalAtom natSpace GroundedDispatch.none (succ zero) Atom.undefinedType Bindings.empty 9 =
        [(succ zero, Bindings.empty)] := by
  refine ⟨succ_zero_completed, by decide, by decide, fun fuel low high => ?_, by decide⟩
  interval_cases fuel <;> decide

/-! ### Theorem H: the expected type is part of the question -/

/-- **Theorem H.** Under its range `Nat` the completed value `(S Z)` delivers
itself; under the unrelated expected type `Bool` it is a `BadType` error at
every sufficiently large fuel. A consultation must check the expected type. -/
theorem evalAtom_completedMono_counterexample :
    (∃ N, ∀ (k : Nat) (bindings : Bindings) (live : List Atom),
      evalAtom natSpace GroundedDispatch.none (succ zero) nat bindings (N + k) live =
        [(succ zero, bindings)]) ∧
      ∃ N, ∀ (k : Nat) (bindings : Bindings) (live : List Atom),
        evalAtom natSpace GroundedDispatch.none (succ zero) bool bindings (N + k) live =
          [(mkError (succ zero) (.badType bool nat), bindings)] := by
  refine ⟨?_, 8, fun k bindings live => ?_⟩
  · obtain ⟨N, deliver⟩ := evalAtom_completed succ_zero_completed
    exact ⟨N, fun k bindings live => deliver k nat bindings live (Or.inr rfl)⟩
  · rw [show 8 + k = 5 + k + 1 + 1 + 1 by omega]
    refine evalAtom_of_interpretExpression_errors ⟨_, _, rfl⟩ rfl rfl
      (interpretExpression_rejected (type := arrowType [nat] nat) rfl
        (isFunctionType_arrowType _ _)
        (checkIfFunctionTypeIsApplicable_returnRejected rfl (.cons ⟨nat, rfl, rfl⟩ .nil) rfl rfl
          bindings (by rw [matchFuel_natArrow]; omega))) ?_
    intro result member
    simp at member
    subst member
    rfl

/-! ### Theorem G: an observation of an open value does not transfer -/

abbrev number : Atom := .symbol "Number"
abbrev point : Atom := .symbol "Point"
abbrev one : Atom := .symbol "one"
abbrev pointAt (atom : Atom) : Atom := .expression [.symbol "Pt", atom]
abbrev openPoint : Atom := pointAt (.var "x")
abbrev boundTo (value : Int) : Bindings := Bindings.empty.assign "x" (.grounded (.int value))

/-- `Pt : (-> Number Point)` and `(= (Pt 1) one)`. -/
def pointSpace : Space :=
  Space.ofList [declaration (.symbol "Pt") (arrowType [number] point),
    equation (pointAt (.grounded (.int 1))) one]

theorem pointSpace_query (avoid : List String) (n : Nat) :
    queryEquationsAvoiding avoid pointSpace openPoint (n + 6) = [(one, boundTo 1)] := by
  have matched : matchAtoms openPoint (pointAt (.grounded (.int 1))) (n + 6) = [boundTo 1] := by
    have stable := matchCovered_stable 6 n (.atoms openPoint (pointAt (.grounded (.int 1))))
      (by decide +kernel)
    simp only [evalMatch] at stable
    rw [Nat.add_comm, stable]
    decide +kernel
  have loopFree : (boundTo 1).hasLoop = false := by decide +kernel
  unfold queryEquationsAvoiding
  simp only [pointSpace, Space.ofList, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, freshenEquationAvoiding,
    renameAtom_of_atomVariables_eq_nil _ (pointAt (.grounded (.int 1))) rfl,
    renameAtom_of_atomVariables_eq_nil _ one rfl, matched]
  simp [mergeBindings_empty, loopFree]

theorem pointSpace_refused (expected : Atom) (n : Nat) (live : List Atom) :
    rawQueryResults pointSpace openPoint expected (boundTo 2) (n + 6) live = [] := by
  have conflict : mergeBindings (boundTo 1)
      (Spec.Type.Presentation.BindingTheory.aliasConstraints (boundTo 2)) (n + 6) = [] := by
    have aliased : Spec.Type.Presentation.BindingTheory.aliasConstraints (boundTo 2) =
        boundTo 2 := by decide +kernel
    have stable := matchCovered_stable 6 n (.merge (boundTo 1) (boundTo 2)) (by decide +kernel)
    simp only [evalMatch] at stable
    rw [aliased, Nat.add_comm, stable]
    decide +kernel
  unfold rawQueryResults
  rw [pointSpace_query]
  simp [conflict]

theorem pointSpace_rewritten (expected : Atom) (n : Nat) (live : List Atom) :
    rawQueryResults pointSpace openPoint expected Bindings.empty (n + 6) live =
      [(one, boundTo 1)] := by
  have aliased : Spec.Type.Presentation.BindingTheory.aliasConstraints Bindings.empty =
      Bindings.empty := rfl
  have merged : mergeBindings (boundTo 1) Bindings.empty (n + 6) = [boundTo 1] :=
    mergeBindings_empty _ _
  have loopFree : (boundTo 1).hasLoop = false := by decide +kernel
  unfold rawQueryResults
  rw [pointSpace_query]
  simp [aliased, merged, loopFree, Bindings.applyFull]

/-- **Theorem G.** The open value `(Pt $x)` is answered unchanged under
`{$x ↦ 2}`, where the merge with the equation `(= (Pt 1) one)` fails, but under
the empty record it is rewritten to `one` with `{$x ↦ 1}`, at every sufficiently
large fuel. An observation made under one record is no certificate for another;
certificates are issued for ground values only. -/
theorem completed_ground_only :
    atomVariables openPoint ≠ [] ∧
      ∃ N, ∀ (k : Nat) (live : List Atom),
        evalAtom pointSpace GroundedDispatch.none openPoint Atom.undefinedType (boundTo 2)
            (N + k) live = [(openPoint, boundTo 2)] ∧
          evalAtom pointSpace GroundedDispatch.none openPoint Atom.undefinedType Bindings.empty
            (N + k) live = [(one, boundTo 1)] := by
  have arrowFuel : matchFuel (arrowType [number] point) = 5 := by decide
  have checked : List.Forall₂ (ArgumentChecked pointSpace) [number] [.var "x"] :=
    .cons ⟨by decide, by decide⟩ .nil
  have arguments : ∀ (bindings : Bindings) (fuel : Nat), 3 ≤ fuel → ∀ live,
      interpretArgs pointSpace GroundedDispatch.none [.var "x"] [number] bindings fuel live =
        [(argumentPacket [.var "x"], bindings)] := fun bindings fuel enough live =>
    interpretArgs_leaves (.cons ⟨rfl, ⟨by decide, by decide⟩, rfl⟩ .nil) bindings
      (fun param member => by simp at member; subst member; simp [matchFuel]; omega)
      (by simp; omega) live
  refine ⟨by decide, 9, fun k live => ⟨?_, ?_⟩⟩
  · rw [show 9 + k = 5 + k + 3 + 1 by omega]
    have refused := invoke_refused (space := pointSpace) (dispatch := GroundedDispatch.none)
      (operator := .symbol "Pt") (arguments := [.var "x"]) rfl rfl rfl
      (expected := callReturnType point) (fuel := k + 6) (live := live)
      (pointSpace_refused _ k live) none
    rw [show k + 6 + 1 = 5 + k + 2 by omega] at refused
    have interpretation := interpretExpression_typed (copies := 0)
      (expected := Atom.undefinedType) rfl rfl (by decide) checked (accepts_undefined _)
      (boundTo 2) (fuel := 5 + k) (by rw [arrowFuel]; omega)
      (arguments (boundTo 2) _ (by omega)) refused
    rw [show (List.replicate (0 + 1) [(openPoint, boundTo 2)]).flatten =
      [(openPoint, boundTo 2)] by simp] at interpretation
    refine evalAtom_of_interpretExpression ⟨_, _, rfl⟩ rfl rfl interpretation ?_
    intro result member
    simp at member
    subst member
    rfl
  · rw [show 9 + k = 5 + k + 3 + 1 by omega]
    have leaf := evalAtom_leaf (space := pointSpace) (dispatch := GroundedDispatch.none)
      (param := point) (arg := one) rfl rfl ⟨by decide, by decide⟩ (boundTo 1)
      (fuel := 5 + k) (by simp only [matchFuel]; omega) live
    have rewritten := pointSpace_rewritten (callReturnType point) k live
    rw [show k + 6 = 5 + k + 1 by omega] at rewritten
    have queried := invoke_queried (space := pointSpace) (dispatch := GroundedDispatch.none)
      (operator := .symbol "Pt") (arguments := [.var "x"]) rfl rfl rfl
      (expected := callReturnType point) (bindings := Bindings.empty) (fuel := 5 + k)
      (live := live) rewritten (by simp)
      (by intro reply member body; simp at member; subst member; simp) none
    have returnType : callReturnType point = point := by decide
    rw [returnType] at queried
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at queried
    simp only [ordinaryCallReturn, leaf] at queried
    have interpretation := interpretExpression_typed (copies := 0) (head := "Pt")
      (params := [number]) (args := [.var "x"]) (range := point)
      (expected := Atom.undefinedType) rfl rfl (by decide) checked (accepts_undefined _)
      Bindings.empty (fuel := 5 + k) (by rw [arrowFuel]; omega)
      (arguments Bindings.empty _ (by omega)) (results := [(one, boundTo 1)])
      (by rw [returnType]; simpa [Atom.notReducible, isEmptyOrError, isEmptyAtom, isErrorAtom,
        Atom.empty] using queried)
    rw [show (List.replicate (0 + 1) [(one, boundTo 1)]).flatten = [(one, boundTo 1)] by simp]
      at interpretation
    refine evalAtom_of_interpretExpression ⟨_, _, rfl⟩ rfl rfl interpretation ?_
    intro result member
    simp at member
    subst member
    rfl

/-! ### Negative controls for the argument check -/

/-- `Z` is declared `Nat` twice. -/
def twiceZeroSpace : Space :=
  Space.ofList [declaration zero nat, declaration zero nat,
    declaration (.symbol "S") (arrowType [nat] nat)]

theorem twiceZeroSpace_ground : GroundEquations twiceZeroSpace := by
  intro lhs rhs member
  simp [twiceZeroSpace, Space.ofList, arrowType] at member

/-- Negative control for `ArgumentChecked.once`: a leaf with two accepted types
passes its parameter check twice, and the call delivers itself twice at every
sufficiently large fuel. -/
theorem argumentChecked_once_required :
    ¬ArgumentChecked twiceZeroSpace nat zero ∧
      ∃ N, ∀ (k : Nat) (live : List Atom),
        evalAtom twiceZeroSpace GroundedDispatch.none (succ zero) Atom.undefinedType
          Bindings.empty (N + k) live =
            [(succ zero, Bindings.empty), (succ zero, Bindings.empty)] := by
  refine ⟨fun checked => absurd checked.once (by decide), 9, fun k live => ?_⟩
  have applicable : checkIfFunctionTypeIsApplicable (succ zero) (arrowType [nat] nat)
      Atom.undefinedType twiceZeroSpace Bindings.empty (5 + k + 2) =
        .inr (List.replicate (1 + 1) Bindings.empty) := by
    have stable := functionTypeCovered_stable (succ zero) (arrowType [nat] nat)
      Atom.undefinedType twiceZeroSpace Bindings.empty 2 (5 + k)
      (lookup := rawTypeLookup twiceZeroSpace) (by decide +kernel)
    rw [show 5 + k + 2 = 2 + (5 + k) by omega, stable]
    decide +kernel
  have arguments : ∀ live, interpretArgs twiceZeroSpace GroundedDispatch.none [zero] [nat]
      Bindings.empty (5 + k + 1) live = [(argumentPacket [zero], Bindings.empty)] := by
    intro live
    rw [show 5 + k + 1 = 4 + k + 1 + 1 by omega]
    refine interpretArgs_cons_self (fun live => ?_) (fun live => interpretArgs_nil_self _ _ live)
      live
    exact evalAtom_leaf_of rfl rfl (by decide) (by decide) Bindings.empty (fuel := 4 + k)
      (by rw [matchFuel_nat]; omega) live
  have invoked := invoke_completed (space := twiceZeroSpace) (dispatch := GroundedDispatch.none)
    (operator := .symbol "S") (arguments := [zero]) rfl rfl
    (noEquationMatch_ground rfl twiceZeroSpace_ground rfl) rfl (callReturnType nat)
    Bindings.empty (5 + k + 1) live none
  have interpretation := interpretExpression_replicated (copies := 1)
    (expected := Atom.undefinedType) rfl rfl (by decide) applicable
    (by rw [matchFuel_natArrow]; omega) arguments invoked
  rw [show 9 + k = 5 + k + 3 + 1 by omega]
  refine evalAtom_of_interpretExpression ⟨_, _, rfl⟩ rfl rfl interpretation ?_
  intro result member
  simp at member
  subst member
  rfl

abbrev box (atom : Atom) : Atom := .expression [.symbol "Box", atom]
abbrev boundT : Bindings := Bindings.empty.assign "t" nat

/-- `Z : (Box $t)` and `S : (-> (Box Nat) Nat)`. -/
def openTypeSpace : Space :=
  Space.ofList [declaration zero (box (.var "t")),
    declaration (.symbol "S") (arrowType [box nat] nat)]

theorem openTypeSpace_ground : GroundEquations openTypeSpace := by
  intro lhs rhs member
  simp [openTypeSpace, Space.ofList, arrowType] at member

/-- Negative control for `ArgumentChecked.rejectedGround`: the type `(Box $t)`
is not accepted syntactically by `(Box Nat)`, yet it matches and binds `$t`, so
the ground value `(S Z)` evaluates to itself with the bindings extended by
`{$t ↦ Nat}` at every sufficiently large fuel. -/
theorem argumentChecked_ground_required :
    ¬ArgumentChecked openTypeSpace (box nat) zero ∧
      ∃ N, ∀ (k : Nat) (live : List Atom),
        evalAtom openTypeSpace GroundedDispatch.none (succ zero) Atom.undefinedType
          Bindings.empty (N + k) live = [(succ zero, boundT)] := by
  refine ⟨fun checked => absurd (checked.rejectedGround (box (.var "t")) (by decide)
    (by decide)) (by decide), 11, fun k live => ?_⟩
  have arrowFuel : matchFuel (arrowType [box nat] nat) = 7 := by decide
  have applicable : checkIfFunctionTypeIsApplicable (succ zero) (arrowType [box nat] nat)
      Atom.undefinedType openTypeSpace Bindings.empty (7 + k + 2) =
        .inr (List.replicate (0 + 1) boundT) := by
    have stable := functionTypeCovered_stable (succ zero) (arrowType [box nat] nat)
      Atom.undefinedType openTypeSpace Bindings.empty 6 (3 + k)
      (lookup := rawTypeLookup openTypeSpace) (by decide +kernel)
    rw [show 7 + k + 2 = 6 + (3 + k) by omega, stable]
    decide +kernel
  have cast : typeCast zero (box nat) openTypeSpace boundT (6 + k) = [(zero, boundT)] := by
    have stable := typeCastCovered_stable zero (box nat) openTypeSpace boundT 5 (1 + k)
      (lookup := rawTypeLookup openTypeSpace) (by decide +kernel)
    rw [show 6 + k = 5 + (1 + k) by omega, stable]
    decide +kernel
  have arguments : ∀ live, interpretArgs openTypeSpace GroundedDispatch.none [zero] [box nat]
      boundT (7 + k + 1) live = [(argumentPacket [zero], boundT)] := by
    intro live
    rw [show 7 + k + 1 = 6 + k + 1 + 1 by omega]
    refine interpretArgs_cons_self (fun live => ?_) (fun live => interpretArgs_nil_self _ _ live)
      live
    rw [evalAtom_symbol (by decide) (by decide) (by decide) boundT (6 + k) live]
    exact cast
  have invoked := invoke_completed (space := openTypeSpace) (dispatch := GroundedDispatch.none)
    (operator := .symbol "S") (arguments := [zero]) rfl rfl
    (noEquationMatch_ground rfl openTypeSpace_ground rfl) rfl (callReturnType nat)
    boundT (7 + k + 1) live none
  have interpretation := interpretExpression_replicated (copies := 0)
    (expected := Atom.undefinedType) rfl rfl (by decide) applicable
    (by rw [arrowFuel]; omega) arguments invoked
  rw [show 11 + k = 7 + k + 3 + 1 by omega]
  refine evalAtom_of_interpretExpression ⟨_, _, rfl⟩ rfl rfl interpretation ?_
  intro result member
  simp at member
  subst member
  rfl

/-! ### Negative controls for the head and the arguments -/

abbrev query : Atom := .expression [.symbol "Q"]

/-- `natSpace` with `Q : (-> Bool)`. -/
def mismatchSpace : Space :=
  Space.ofList [declaration zero nat, declaration (.symbol "S") (arrowType [nat] nat),
    declaration (.symbol "Q") (arrowType [] bool)]

theorem mismatchSpace_ground : GroundEquations mismatchSpace := by
  intro lhs rhs member
  simp [mismatchSpace, Space.ofList, arrowType] at member

theorem query_completed : Completed mismatchSpace GroundedDispatch.none query bool :=
  .typed rfl rfl (by decide) rfl rfl (noEquationMatch_ground rfl mismatchSpace_ground rfl) .nil

/-- `(Q)` under `Nat` is a `BadType` error. -/
theorem query_under_nat {bindings : Bindings} {fuel : Nat} (enough : 4 ≤ fuel)
    (live : List Atom) :
    evalAtom mismatchSpace GroundedDispatch.none query nat bindings (fuel + 3) live =
      [(mkError query (.badType nat bool), bindings)] := by
  refine evalAtom_of_interpretExpression_errors ⟨_, _, rfl⟩ rfl rfl
    (interpretExpression_rejected (type := arrowType [] bool) rfl
      (isFunctionType_arrowType _ _)
      (checkIfFunctionTypeIsApplicable_returnRejected rfl .nil rfl rfl bindings
        (by rw [show matchFuel (arrowType [] bool) = 4 by decide]; omega))) ?_
  intro result member
  simp at member
  subst member
  rfl

/-- Negative control for `fits`: `(Q)` is completed with range `Bool`, but under
the parameter `Nat` of `S` it is a type error, which becomes the value of
`(S (Q))` at every sufficiently large fuel. -/
theorem value_fits_required :
    Completed mismatchSpace GroundedDispatch.none query bool ∧
      ¬(nat = Atom.undefinedType ∨ nat = bool) ∧
      ∃ N, ∀ (k : Nat) (bindings : Bindings) (live : List Atom),
        evalAtom mismatchSpace GroundedDispatch.none (succ query) Atom.undefinedType bindings
          (N + k) live = [(mkError query (.badType nat bool), bindings)] := by
  refine ⟨query_completed, by decide, 11, fun k bindings live => ?_⟩
  have failure : ∀ live, interpretArgs mismatchSpace GroundedDispatch.none [query] [nat]
      bindings (7 + k + 1) live = [(mkError query (.badType nat bool), bindings)] := by
    intro live
    refine interpretArgs_cons_failed (fun live => ?_) (by decide) (by decide) live
    rw [show 7 + k = 4 + k + 3 by omega]
    exact query_under_nat (by omega) live
  have interpreted := interpretFunction_arguments (space := mismatchSpace)
    (dispatch := GroundedDispatch.none) (head := "S") (others := []) rfl rfl (by decide) bindings
    (fuel := 7 + k) (by rw [matchFuel_natArrow]; omega) failure
  have applicable : checkIfFunctionTypeIsApplicable (succ query) (arrowType [nat] nat)
      Atom.undefinedType mismatchSpace bindings (7 + k + 2) = .inr [bindings] :=
    checkIfFunctionTypeIsApplicable_completed rfl (.cons ⟨by decide, by decide⟩ .nil)
      (accepts_undefined _) bindings (by rw [matchFuel_natArrow]; omega)
  have interpretation := interpretExpression_single (live := live) rfl applicable
    (fun live => by rw [interpreted live])
    (invoke_passthrough rfl _ _ _ _ none)
  rw [show 11 + k = 7 + k + 3 + 1 by omega]
  refine evalAtom_of_interpretExpression_errors ⟨_, _, rfl⟩ rfl rfl interpretation ?_
  intro result member
  simp at member
  subst member
  rfl

/-- `Empty : (-> Nat Nat)`. -/
def emptyHeadSpace : Space :=
  Space.ofList [declaration zero nat, declaration Atom.empty (arrowType [nat] nat)]

theorem emptyHeadSpace_ground : GroundEquations emptyHeadSpace := by
  intro lhs rhs member
  simp [emptyHeadSpace, Space.ofList, arrowType, Atom.empty] at member

/-- Negative control for `notEmpty`: with the head `Empty` declared as a ground
arrow, `(Empty Z)` evaluates to `Empty` at every sufficiently large fuel. -/
theorem emptyHead_required :
    (∀ range, ¬Completed emptyHeadSpace GroundedDispatch.none
      (.expression [Atom.empty, zero]) range) ∧
      ∃ N, ∀ (k : Nat) (bindings : Bindings) (live : List Atom),
        evalAtom emptyHeadSpace GroundedDispatch.none (.expression [Atom.empty, zero])
          Atom.undefinedType bindings (N + k) live = [(Atom.empty, bindings)] := by
  refine ⟨fun range completed => ?_, 9, fun k bindings live => ?_⟩
  · cases completed with
    | typed _ _ notEmpty _ _ _ _ => exact notEmpty rfl
  · have applicable : checkIfFunctionTypeIsApplicable (.expression [Atom.empty, zero])
        (arrowType [nat] nat) Atom.undefinedType emptyHeadSpace bindings (5 + k + 2) =
          .inr [bindings] :=
      checkIfFunctionTypeIsApplicable_completed (head := "Empty") rfl
        (.cons ⟨by decide, by decide⟩ .nil) (accepts_undefined _) bindings
        (by rw [matchFuel_natArrow]; omega)
    have refused : rawQueryResults emptyHeadSpace Atom.empty (callReturnType nat) bindings
        (5 + k + 1) live = [] := by
      unfold rawQueryResults
      rw [noEquationMatch_ground rfl emptyHeadSpace_ground rfl]
      rfl
    have interpretation := interpretExpression_single (dispatch := GroundedDispatch.none)
      (head := "Empty") (live := live) rfl
      applicable (fun live => interpretFunction_emptyHead bindings (5 + k) live)
      (invoke_symbol_refused refused none)
    rw [show 9 + k = 5 + k + 3 + 1 by omega]
    refine evalAtom_of_interpretExpression ⟨_, _, rfl⟩ rfl rfl interpretation ?_
    intro result member
    simp at member
    subst member
    rfl

/-- A dispatch that runs `S`, answering `one`. -/
def runsSucc : GroundedDispatch where
  isExecutable atom := atom == .symbol "S"
  execute _ _ := .ok [(one, Bindings.empty)]

/-- Negative control for `notExecutable`: when the dispatch runs the head, the
value `(S Z)` evaluates to the host's answer `one` at every sufficiently large
fuel. -/
theorem notExecutable_required :
    (∀ range, ¬Completed natSpace runsSucc (succ zero) range) ∧
      ∃ N, ∀ (k : Nat) (live : List Atom),
        evalAtom natSpace runsSucc (succ zero) Atom.undefinedType Bindings.empty (N + k) live =
          [(one, Bindings.empty)] := by
  refine ⟨fun range completed => ?_, 9, fun k live => ?_⟩
  · cases completed with
    | typed _ _ _ notExecutable _ _ _ => exact absurd notExecutable (by decide)
  · have leaf := evalAtom_leaf (space := natSpace) (dispatch := runsSucc) (param := nat)
      (arg := one) rfl rfl ⟨by decide, by decide⟩ Bindings.empty (fuel := 5 + k)
      (by rw [matchFuel_nat]; omega) live
    have invoked := invoke_executable (space := natSpace) (dispatch := runsSucc)
      (operator := .symbol "S") (arguments := [zero]) (replies := [(one, Bindings.empty)])
      (by decide) rfl rfl (callReturnType nat) (fuel := 5 + k) live none
      (merged := [(one, Bindings.empty)]) (by simp [mergeBindings_empty, Bindings.applyFull])
      (by simp) (by intro reply member body; simp at member; subst member; simp)
    have returnType : callReturnType nat = nat := by decide
    rw [returnType] at invoked
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ordinaryCallReturn,
      leaf] at invoked
    have interpretation := interpretExpression_typed (copies := 0) (head := "S")
      (params := [nat]) (args := [zero]) (range := nat) (expected := Atom.undefinedType)
      (live := live) (results := [(one, Bindings.empty)]) rfl rfl (by decide)
      (.cons natSpace_zero .nil) (accepts_undefined _) Bindings.empty (fuel := 5 + k)
      (by rw [matchFuel_natArrow]; omega)
      (fun live => natSpace_zero_leaf (by omega) live)
      (by rw [returnType]; simpa [Atom.notReducible, isEmptyOrError, isEmptyAtom, isErrorAtom,
        Atom.empty] using invoked)
    rw [show (List.replicate (0 + 1) [(one, Bindings.empty)]).flatten = [(one, Bindings.empty)] by
      simp] at interpretation
    rw [show 9 + k = 5 + k + 3 + 1 by omega]
    refine evalAtom_of_interpretExpression ⟨_, _, rfl⟩ rfl rfl interpretation ?_
    intro result member
    simp at member
    subst member
    rfl

/-- `natSpace` with `foo : (-> Nat)` and `(= (foo) Z)`. -/
def fooZeroSpace : Space :=
  Space.ofList [declaration zero nat, declaration (.symbol "S") (arrowType [nat] nat),
    declaration (.symbol "foo") (arrowType [] nat), equation fooCall zero]

theorem fooZeroSpace_ground : GroundEquations fooZeroSpace := by
  intro lhs rhs member
  simp [fooZeroSpace, Space.ofList, arrowType] at member
  obtain ⟨rfl, rfl⟩ := member
  exact ⟨rfl, rfl⟩

/-- `(foo)` under `Nat` evaluates to `Z`. -/
theorem foo_under_nat {fuel : Nat} (enough : 4 ≤ fuel) (live : List Atom) :
    evalAtom fooZeroSpace GroundedDispatch.none fooCall nat Bindings.empty (fuel + 4) live =
      [(zero, Bindings.empty)] := by
  have rhs : fooZeroSpace.atoms.flatMap (equationRhs fooCall) = [zero] := by decide
  have arrowFuel : matchFuel (arrowType [] nat) = 4 := by decide
  have callFuel : matchFuel fooCall = 3 := by decide
  refine evalAtom_rewritten (params := []) (range := nat) rfl rfl (by decide) rfl rfl rfl rfl
    fooZeroSpace_ground (by rw [rhs]; simp) (fun reply member body => ?_) .nil (accepts_self _)
    rfl (by rw [arrowFuel]; omega) (by rw [callFuel]; omega)
    (fun live => interpretArgs_nil_self Bindings.empty _ live) live ?_ ?_
  · rw [rhs] at member
    simp at member
    subst member
    simp
  · rw [rhs]
    have leaf := evalAtom_leaf (space := fooZeroSpace) (dispatch := GroundedDispatch.none)
      (param := nat) (arg := zero) rfl rfl ⟨by decide, by decide⟩ Bindings.empty
      (fuel := fuel) (by rw [matchFuel_nat]; omega) live
    have returnType : callReturnType nat = nat := by decide
    simp [ordinaryCallReturn, returnType, Atom.notReducible, isEmptyOrError, isEmptyAtom,
      isErrorAtom, Atom.empty, leaf]
  · intro result member
    simp at member
    subst member
    rfl

/-- Negative control for the argument conditions: the argument `(foo)` is not a
leaf, not held, and not completed, and `(S (foo))` evaluates to `(S Z)` at every
sufficiently large fuel. -/
theorem argument_value_required :
    (∀ range, ¬Completed fooZeroSpace GroundedDispatch.none (succ fooCall) range) ∧
      ∃ N, ∀ (k : Nat) (live : List Atom),
        evalAtom fooZeroSpace GroundedDispatch.none (succ fooCall) Atom.undefinedType
          Bindings.empty (N + k) live = [(succ zero, Bindings.empty)] := by
  refine ⟨fun range completed => ?_, 13, fun k live => ?_⟩
  · cases completed with
    | typed declared _ _ _ _ _ arguments =>
        have types : getAtomTypes fooZeroSpace (.symbol "S") = [arrowType [nat] nat] := rfl
        rw [types, List.cons.injEq] at declared
        obtain ⟨rfl, -⟩ := arrowType_inj declared.1.symm
        rcases arguments.head_cases with held | leaf | ⟨inner, completedArgument, -⟩
        · exact absurd held (by decide)
        · exact absurd leaf (by decide)
        · cases completedArgument with
          | typed _ _ _ _ _ noEquation _ => exact absurd (noEquation [] 10) (by decide)
  · have arguments : ∀ live, interpretArgs fooZeroSpace GroundedDispatch.none [fooCall] [nat]
        Bindings.empty (9 + k + 1) live = [(argumentPacket [zero], Bindings.empty)] := by
      intro live
      rw [show 9 + k + 1 = 8 + k + 1 + 1 by omega]
      refine interpretArgs_cons_value (reply := zero) (fun live => ?_) (by decide)
        (fun live => interpretArgs_nil_self Bindings.empty _ live) live
      rw [show 8 + k + 1 = 5 + k + 4 by omega]
      exact foo_under_nat (by omega) live
    have interpreted := interpretFunction_arguments (space := fooZeroSpace)
      (dispatch := GroundedDispatch.none) (head := "S") (others := []) rfl rfl (by decide)
      Bindings.empty (fuel := 9 + k) (by rw [matchFuel_natArrow]; omega) arguments
    have applicable : checkIfFunctionTypeIsApplicable (succ fooCall) (arrowType [nat] nat)
        Atom.undefinedType fooZeroSpace Bindings.empty (9 + k + 2) = .inr [Bindings.empty] :=
      checkIfFunctionTypeIsApplicable_completed rfl (.cons ⟨by decide, by decide⟩ .nil)
        (accepts_undefined _) Bindings.empty (by rw [matchFuel_natArrow]; omega)
    have invoked := invoke_completed (space := fooZeroSpace) (dispatch := GroundedDispatch.none)
      (operator := .symbol "S") (arguments := [zero]) rfl rfl
      (noEquationMatch_ground rfl fooZeroSpace_ground (by decide)) rfl (callReturnType nat)
      Bindings.empty (9 + k + 1) live none
    have interpretation := interpretExpression_single (live := live) rfl applicable
      (fun live => by rw [interpreted live]; simp) invoked
    rw [show 13 + k = 9 + k + 3 + 1 by omega]
    refine evalAtom_of_interpretExpression ⟨_, _, rfl⟩ rfl rfl interpretation ?_
    intro result member
    simp at member
    subst member
    rfl

abbrev typeVar : Atom := .var "a"
abbrev boundA : Bindings := Bindings.empty.assign "a" nat
abbrev boundAliased : Bindings :=
  { assignments := [("a", nat)], equalities := [("a", "a"), ("a", "a")] }

/-- `S : (-> $a $a)`. -/
def polySpace : Space :=
  Space.ofList [declaration zero nat, declaration (.symbol "S") (arrowType [typeVar] typeVar)]

theorem polySpace_ground : GroundEquations polySpace := by
  intro lhs rhs member
  simp [polySpace, Space.ofList, arrowType] at member

/-- Negative control for `ground`: with the open arrow `(-> $a $a)` the type
checks bind `$a`, and the ground value `(S Z)` evaluates to itself with the
bindings extended at every sufficiently large fuel. -/
theorem arrow_ground_required :
    atomVariables (arrowType [typeVar] typeVar) ≠ [] ∧
      ∃ N, ∀ (k : Nat) (live : List Atom),
        evalAtom polySpace GroundedDispatch.none (succ zero) Atom.undefinedType Bindings.empty
          (N + k) live = [(succ zero, boundAliased)] := by
  refine ⟨by decide, 10, fun k live => ?_⟩
  have applicable : checkIfFunctionTypeIsApplicable (succ zero) (arrowType [typeVar] typeVar)
      Atom.undefinedType polySpace Bindings.empty (6 + k + 2) = .inr [boundA] := by
    have stable := functionTypeCovered_stable (succ zero) (arrowType [typeVar] typeVar)
      Atom.undefinedType polySpace Bindings.empty 3 (5 + k)
      (lookup := rawTypeLookup polySpace) (by decide +kernel)
    rw [show 6 + k + 2 = 3 + (5 + k) by omega, stable]
    decide +kernel
  have headEval : ∀ fuel, 7 ≤ fuel → ∀ live, evalAtom polySpace GroundedDispatch.none
      (.symbol "S") (arrowType [typeVar] typeVar) boundA fuel live =
        [(.symbol "S", boundAliased)] := by
    intro fuel enough live
    obtain ⟨g, rfl⟩ : ∃ g, fuel = 6 + g + 1 := ⟨fuel - 7, by omega⟩
    rw [evalAtom_symbol (by decide) (by decide) (by decide) boundA (6 + g) live]
    have stable := typeCastCovered_stable (.symbol "S") (arrowType [typeVar] typeVar) polySpace
      boundA 6 g (lookup := rawTypeLookup polySpace) (by decide +kernel)
    rw [stable]
    decide +kernel
  have argumentEval : ∀ fuel, 3 ≤ fuel → ∀ live, evalAtom polySpace GroundedDispatch.none zero
      typeVar boundAliased fuel live = [(zero, boundAliased)] := by
    intro fuel enough live
    obtain ⟨g, rfl⟩ : ∃ g, fuel = 2 + g + 1 := ⟨fuel - 3, by omega⟩
    rw [evalAtom_symbol (by decide) (by decide) (by decide) boundAliased (2 + g) live]
    have stable := typeCastCovered_stable zero typeVar polySpace boundAliased 2 g
      (lookup := rawTypeLookup polySpace) (by decide +kernel)
    rw [stable]
    decide +kernel
  have arguments : ∀ fuel, 4 ≤ fuel → ∀ live, interpretArgs polySpace GroundedDispatch.none
      [zero] [typeVar] boundAliased fuel live = [(argumentPacket [zero], boundAliased)] := by
    intro fuel enough live
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 + 1 := ⟨fuel - 2, by omega⟩
    rw [interpretArgs_cons_general (argumentEval (g + 1) (by omega))
      (fun live => interpretArgs_nil_self boundAliased g live) live]
    simp
  have interpreted : ∀ live, interpretFunction polySpace GroundedDispatch.none (succ zero)
      (arrowType [typeVar] typeVar) boundA (6 + k + 2) live = [(succ zero, boundAliased)] := by
    intro live
    rw [interpretFunction_general (fuel := 6 + k + 1) (headEval _ (by omega)) (by decide)
      (getFunctionArgTypes_arrowType _ _) (arguments _ (by omega)) live]
    simp
  have invoked := invoke_completed (space := polySpace) (dispatch := GroundedDispatch.none)
    (operator := .symbol "S") (arguments := [zero]) rfl rfl
    (noEquationMatch_ground rfl polySpace_ground rfl) rfl (callReturnType typeVar) boundAliased
    (6 + k + 1) live none
  have interpretation := interpretExpression_single (dispatch := GroundedDispatch.none)
    (head := "S") (params := [typeVar]) (args := [zero]) (range := typeVar)
    (expected := Atom.undefinedType) (live := live) rfl applicable interpreted invoked
  rw [show 10 + k = 6 + k + 3 + 1 by omega]
  refine evalAtom_of_interpretExpression ⟨_, _, rfl⟩ rfl rfl interpretation ?_
  intro result member
  simp at member
  subst member
  rfl

/-- `eval : (-> Atom Nat)`, beside `foo : (-> Nat)` and `(= (foo) Z)`. -/
def evalSpace : Space :=
  Space.ofList [declaration zero nat, declaration (.symbol "eval") (arrowType [Atom.atomType] nat),
    declaration (.symbol "foo") (arrowType [] nat), equation fooCall zero]

theorem evalSpace_ground : GroundEquations evalSpace := by
  intro lhs rhs member
  simp [evalSpace, Space.ofList, arrowType] at member
  obtain ⟨rfl, rfl⟩ := member
  exact ⟨rfl, rfl⟩

/-- Negative control for `notInstruction`: a typed `eval` is a minimal
instruction, and `(eval (foo))` runs it, evaluating to `Z` at every
sufficiently large fuel. -/
theorem notInstruction_required :
    (∀ range, ¬Completed evalSpace GroundedDispatch.none
      (.expression [.symbol "eval", fooCall]) range) ∧
      ∃ N, ∀ (k : Nat) (live : List Atom),
        evalAtom evalSpace GroundedDispatch.none (.expression [.symbol "eval", fooCall])
          Atom.undefinedType Bindings.empty (N + k) live = [(zero, Bindings.empty)] := by
  refine ⟨fun range completed => ?_, 9, fun k live => ?_⟩
  · cases completed with
    | typed _ _ _ _ notInstruction _ _ => exact absurd notInstruction (by decide)
  · have arrowFuel : matchFuel (arrowType [Atom.atomType] nat) = 5 := by decide
    have applicable : checkIfFunctionTypeIsApplicable (.expression [.symbol "eval", fooCall])
        (arrowType [Atom.atomType] nat) Atom.undefinedType evalSpace Bindings.empty (5 + k + 2) =
          .inr [Bindings.empty] :=
      checkIfFunctionTypeIsApplicable_completed rfl (.cons ⟨by decide, by decide⟩ .nil)
        (accepts_undefined _) Bindings.empty (by rw [arrowFuel]; omega)
    have held : ∀ live, interpretArgs evalSpace GroundedDispatch.none [fooCall] [Atom.atomType]
        Bindings.empty (5 + k + 1) live = [(argumentPacket [fooCall], Bindings.empty)] := by
      intro live
      rw [show 5 + k + 1 = 4 + k + 1 + 1 by omega]
      exact interpretArgs_cons_self (fun live => evalAtom_held fooCall Bindings.empty _ live)
        (fun live => interpretArgs_nil_self Bindings.empty _ live) live
    have interpreted := interpretFunction_arguments (space := evalSpace)
      (dispatch := GroundedDispatch.none) (head := "eval") (others := []) rfl rfl (by decide)
      Bindings.empty (fuel := 5 + k) (by rw [arrowFuel]; omega) held
    have rhs : evalSpace.atoms.flatMap (equationRhs fooCall) = [zero] := by decide
    have raw : invoke evalSpace GroundedDispatch.none .raw fooCall Bindings.empty (2 + k + 2)
        (nat :: live) none = [(zero, Bindings.empty)] := by
      rw [invoke_raw_equations rfl rfl rfl evalSpace_ground (by rw [rhs]; simp)
        (fun reply member body => by rw [rhs] at member; simp at member; subst member; simp)
        (by rw [show matchFuel fooCall = 3 by decide]; omega) (nat :: live) none, rhs]
      rfl
    have leaf := evalAtom_leaf (space := evalSpace) (dispatch := GroundedDispatch.none)
      (param := nat) (arg := zero) rfl rfl ⟨by decide, by decide⟩ Bindings.empty
      (fuel := 5 + k) (by rw [matchFuel_nat]; omega) live
    have returnType : callReturnType nat = nat := by decide
    have invoked : invoke evalSpace GroundedDispatch.none (.ordinary (callReturnType nat))
        (.expression [.symbol "eval", fooCall]) Bindings.empty (5 + k + 2) live =
          [(zero, Bindings.empty)] := by
      rw [returnType, show 5 + k + 2 = 3 + k + 4 by omega, invoke_eval rfl nat Bindings.empty
        (3 + k) live none, applyFull_ground _ _ _ rfl, show 3 + k + 1 = 2 + k + 2 by omega, raw,
        show 3 + k + 3 = 5 + k + 1 by omega]
      simp [ordinaryCallReturn, Atom.notReducible, isEmptyOrError, isEmptyAtom, isErrorAtom,
        Atom.empty, leaf]
    have interpretation := interpretExpression_single (live := live) rfl applicable
      (fun live => by rw [interpreted live]; simp) invoked
    rw [show 9 + k = 5 + k + 3 + 1 by omega]
    refine evalAtom_of_interpretExpression ⟨_, _, rfl⟩ rfl rfl interpretation ?_
    intro result member
    simp at member
    subst member
    rfl

/-! ### Controls for the auxiliary notions -/

example : accepts nat nat = true := rfl
example : accepts Atom.undefinedType bool = true := rfl
example : accepts nat Atom.atomType = true := rfl
example : accepts nat bool = false := rfl
example : accepts (box nat) (box (.var "t")) = false := rfl

example : isLeaf zero = true := rfl
example : isLeaf (.var "x") = true := rfl
example : isLeaf (.grounded (.int 1)) = true := rfl
example : isLeaf (succ zero) = false := rfl

example : matchFuel nat = 1 := rfl
example : matchFuel (succ zero) = 4 := by decide

example : ArgumentChecked natSpace nat zero := natSpace_zero
example : ArgumentChecked natSpace nat (succ zero) := ⟨by decide, by decide⟩
example : ¬ArgumentChecked retypedSpace nat zero := fun checked => absurd checked.once (by decide)
example : ¬ArgumentChecked twiceZeroSpace nat zero :=
  fun checked => absurd checked.once (by decide)

example : GroundEquations rewrittenSpace := rewrittenSpace_ground
example : ¬GroundEquations (Space.ofList [equation (succ (.var "n")) zero]) := fun ground => by
  have := (ground (succ (.var "n")) zero (by simp [Space.ofList])).1
  simp [atomVariables, atomListVariables] at this

example : NoEquationMatch natSpace (succ zero) := noEquationMatch_ground rfl natSpace_ground rfl
example : ¬NoEquationMatch rewrittenSpace (succ zero) := fun none => absurd (none [] 10) (by decide)

example : callReturnType nat = nat := by decide
example : callReturnType Atom.expressionType = Atom.undefinedType := by decide

end Controls

/-! ## Shared values: one certificate per distinct node -/

namespace Sharing

open Controls


/-- `Z : Nat`, `S : (-> Nat Nat)` and `P : (-> Nat Nat Nat)`; no equations. -/
def pairSpace : Space :=
  Space.ofList [declaration zero nat, declaration (.symbol "S") (arrowType [nat] nat),
    declaration (.symbol "P") (arrowType [nat, nat] nat)]

/-- The shared spine `(S Z)`, `(P v v)`, `(P (P v v) (P v v))`, …: each level
names the previous value twice. -/
def spine : Nat → Atom
  | 0 => succ zero
  | n + 1 => .expression [.symbol "P", spine n, spine n]

theorem pairSpace_no_equations (lhs rhs : Atom) :
    Atom.expression [.symbol "=", lhs, rhs] ∉ pairSpace.atoms := by
  simp [pairSpace, Space.ofList, arrowType]

theorem pairSpace_expression_types {atoms : List Atom} (nonempty : atoms ≠ []) :
    getAtomTypes pairSpace (.expression atoms) = [Atom.undefinedType] := by
  cases atoms with
  | nil => exact absurd rfl nonempty
  | cons _ _ => simp [getAtomTypes, getAnnotatedTypes, pairSpace, Space.ofList, arrowType]

theorem spine_expression (n : Nat) : ∃ head rest, spine n = .expression (head :: rest) := by
  cases n with
  | zero => exact ⟨_, _, rfl⟩
  | succ n => exact ⟨_, _, rfl⟩

theorem spine_checked (n : Nat) : ArgumentChecked pairSpace nat (spine n) := by
  obtain ⟨head, rest, same⟩ := spine_expression n
  rw [same]
  exact ⟨by rw [pairSpace_expression_types (by simp)]; rfl,
    by rw [pairSpace_expression_types (by simp)]; intro type member; simp at member; subst member
       simp [accepts]⟩

/-- Every level of the spine is a completed value, at every depth. -/
theorem spine_completed : ∀ n, Completed pairSpace GroundedDispatch.none (spine n) nat
  | 0 => .typed rfl rfl (by decide) rfl rfl
      (noEquationMatch_of_no_equations _ pairSpace_no_equations)
      (.leaf rfl ⟨by decide, by decide⟩ .nil)
  | n + 1 => .typed rfl rfl (by decide) rfl rfl
      (noEquationMatch_of_no_equations _ pairSpace_no_equations)
      (.value (spine_completed n) (Or.inr rfl) (spine_checked n)
        (.value (spine_completed n) (Or.inr rfl) (spine_checked n) .nil))

mutual
/-- Expression occurrences of an atom tree. -/
def expressionNodes : Atom → Nat
  | .expression atoms => expressionNodesList atoms + 1
  | _ => 0
/-- Expression occurrences of a list of atom trees. -/
def expressionNodesList : List Atom → Nat
  | [] => 0
  | atom :: atoms => expressionNodes atom + expressionNodesList atoms
end

theorem expressionNodes_spine (n : Nat) :
    expressionNodes (spine n) = Machines.DemandSummary.eager Machines.SharedSpineCost.graph
      Machines.SharedSpineCost.treeSize n := by
  induction n with
  | zero =>
      rw [Machines.SharedSpineCost.eager_zero]
      simp [spine, expressionNodes, expressionNodesList]
  | succ n ih =>
      rw [Machines.SharedSpineCost.eager_succ, ← ih]
      simp [spine, expressionNodes, expressionNodesList]
      omega

/-- The certificate a node of the shared spine receives from its children:
the leaf node `(S Z)` has the range `Nat`, and `(P v v)` has it when both
arguments carry the range `Nat` of their parameters. -/
def spineCertificate (_ : Unit) : List (Option Atom) → Option Atom
  | [] => some nat
  | [left, right] => if left = some nat ∧ right = some nat then some nat else none
  | _ => none

theorem spineCertificate_eager (n : Nat) :
    Machines.DemandSummary.eager Machines.SharedSpineCost.graph spineCertificate n = some nat := by
  induction n with
  | zero =>
      rw [Machines.DemandSummary.eager]
      rfl
  | succ n ih =>
      rw [Machines.DemandSummary.eager]
      show spineCertificate ()
        [Machines.DemandSummary.eager Machines.SharedSpineCost.graph spineCertificate n,
          Machines.DemandSummary.eager Machines.SharedSpineCost.graph spineCertificate n] =
        some nat
      rw [ih]
      rfl

/-- **Certificates over a shared value (stretch).** Every node of the shared
spine of depth `n` is a completed value whose certificate is its range, so each
certified answer is its evaluation by `evalAtom_completed`. Memoized
certification over the shared graph answers the root after at most `n + 1`
node certifications, each a distinct node, while the value it describes has
`2 ^ (n + 1) - 1` expression occurrences. -/
theorem certificates_linear_on_shared_spine (n : Nat) :
    (∀ i, Machines.DemandSummary.eager Machines.SharedSpineCost.graph spineCertificate i =
        some nat ∧ Completed pairSpace GroundedDispatch.none (spine i) nat) ∧
      (Machines.DemandSummary.demand Machines.SharedSpineCost.graph spineCertificate n
        (fun _ => none)).value = some nat ∧
      (Machines.DemandSummary.demand Machines.SharedSpineCost.graph spineCertificate n
        (fun _ => none)).computed.length ≤ n + 1 ∧
      (Machines.DemandSummary.demand Machines.SharedSpineCost.graph spineCertificate n
        (fun _ => none)).computed.Nodup ∧
      expressionNodes (spine n) + 1 = 2 ^ (n + 1) := by
  have valid := Machines.DemandSummary.demand_valid Machines.SharedSpineCost.graph
    spineCertificate n (fun _ => none)
    (Machines.DemandSummary.empty_sound Machines.SharedSpineCost.graph spineCertificate)
  refine ⟨fun i => ⟨spineCertificate_eager i, spine_completed i⟩, ?_, ?_, valid.nodup, ?_⟩
  · rw [valid.value_eq, spineCertificate_eager]
  · have bound := Machines.DemandSummary.demand_combinations_le_uncached_reachable
      Machines.SharedSpineCost.graph spineCertificate n (fun _ => none)
      (Machines.DemandSummary.empty_sound Machines.SharedSpineCost.graph spineCertificate)
    simpa [Machines.SharedSpineCost.reachable_exact] using bound
  · rw [expressionNodes_spine]
    exact Machines.SharedSpineCost.unfolded_size n

/-- Executable instance: depth 8 certifies its nine distinct nodes once each,
for a value of 511 expression occurrences. -/
example : (Machines.DemandSummary.demand Machines.SharedSpineCost.graph spineCertificate 8
    (fun _ => none)).computed = List.range 9 ∧ expressionNodes (spine 8) = 511 := by
  decide +kernel

end Sharing

end Mettapedia.Languages.MeTTa.HE.CompletedDelivery
