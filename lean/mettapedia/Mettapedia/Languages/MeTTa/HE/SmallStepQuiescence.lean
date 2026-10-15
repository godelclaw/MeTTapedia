import Mettapedia.Languages.MeTTa.HE.SmallStep
import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa

/-!
# Theorem Q: Quiescent Atoms Self-Evaluate Officially

Companion to the master absorption theorem (see
`docs/plans/2026-06-10_correspondence_master_theorem_design.txt` in the
CeTTa repository): on a characterized domain, coarse-quiescent atoms
evaluate to themselves under the official declarative semantics.

The domain (`SelfEvalQuiescent`) is deliberately the honest fragment:

* untyped (`%Undefined%`-typed) heads only, so the tuple path applies and
  no type errors arise (design-note trap T1: function-typed stuck heads can
  officially evaluate to `BadType` errors — *excluded*, not hand-waved);
* no matching equations and non-executable heads (trap T2: no-match sugar
  shapes officially evaluate to Empty — excluded by shape);
* the existing expression fragment retains its conservative requirement of
  at least two elements and a non-expression last element. Tuple evaluation
  preserves singleton wrappers and nested expression elements; these shape
  restrictions do not characterize the maximal self-evaluating fragment.

Payoff: `minimalStep_absorbs_chain_subst` — the substitution half of
`HES_Chain`'s correspondence with the official `MinimalStep.chain`
instruction, on the characterized domain.  (The source-progress half needs
the master theorem M; we state only what we prove.)
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- `matchTypes` with `%Undefined%` on the left succeeds at any fuel (the
short-circuit branch is fuel-independent). -/
theorem matchTypes_undefined_left_fuel (t : Atom) (b : Bindings) (fuel : Nat) :
    matchTypes Atom.undefinedType t b fuel = [b] := by
  simp [matchTypes]

/-- An atom whose only type is `%Undefined%` type-casts to itself (with the
incoming bindings) under any expected type, at any fuel. -/
theorem typeCast_self_of_undefined {space : Space} {a : Atom}
    (h : getAtomTypes space a = [Atom.undefinedType])
    (t : Atom) (b : Bindings) (fuel : Nat) :
    typeCast a t space b fuel = [(a, b)] := by
  unfold typeCast
  rw [h]
  simp [typeCast.typeCastLoop, matchTypes]

/-- An expression headed by anything other than the bare `"Error"` symbol
is not Error-shaped. -/
theorem isErrorAtom_expr_false {y : Atom} (zs : List Atom)
    (hy : y ≠ Atom.symbol "Error") :
    isErrorAtom (.expression (y :: zs)) = false := by
  cases y with
  | symbol s =>
      by_cases hs : s = "Error"
      · exact absurd (by rw [hs]) hy
      · simp [isErrorAtom, hs]
  | var v => rfl
  | grounded g => rfl
  | expression es => rfl

/-- Expressions are never the `Empty` symbol. -/
theorem isEmptyAtom_expr_false (l : List Atom) :
    isEmptyAtom (.expression l) = false := by
  simp [isEmptyAtom, Atom.empty]

theorem isEmptyOrError_expr_false {y : Atom} (zs : List Atom)
    (hy : y ≠ Atom.symbol "Error") :
    isEmptyOrError (.expression (y :: zs)) = false := by
  simp [isEmptyOrError, isEmptyAtom_expr_false, isErrorAtom_expr_false zs hy]

/-- **Q's domain**: officially-self-evaluating quiescent atoms. -/
inductive SelfEvalQuiescent (space : Space) (d : GroundedDispatch)
    (fuel : Nat) : Atom → Prop where
  | symbol {s : String}
      (h_not_err : isEmptyOrError (Atom.symbol s) = false)
      (h_untyped : getAtomTypes space (Atom.symbol s) = [Atom.undefinedType]) :
      SelfEvalQuiescent space d fuel (.symbol s)
  | grounded {g : GroundedValue}
      (h_untyped : getAtomTypes space (Atom.grounded g) = [Atom.undefinedType]) :
      SelfEvalQuiescent space d fuel (.grounded g)
  | expr {op e2 : Atom} {rest : List Atom}
      (h_not_err : isEmptyOrError (Atom.expression (op :: e2 :: rest)) = false)
      (h_not_exec : HeadNotExecutable d (.expression (op :: e2 :: rest)))
      (h_no_eqs : ∀ f, queryEquations space (.expression (op :: e2 :: rest)) f = [])
      (h_head_untyped : getAtomTypes space op = [Atom.undefinedType])
      (h_last_flat : ∀ es', (op :: e2 :: rest).getLast? = some (Atom.expression es') → False)
      (h_no_error_sym : ∀ e ∈ op :: e2 :: rest, e ≠ Atom.symbol "Error")
      (h_elems : ∀ e ∈ op :: e2 :: rest, SelfEvalQuiescent space d fuel e) :
      SelfEvalQuiescent space d fuel (.expression (op :: e2 :: rest))

/-- Domain atoms are never Empty/Error. -/
theorem SelfEvalQuiescent.not_empty_or_error {space : Space}
    {d : GroundedDispatch} {fuel : Nat} {a : Atom}
    (h : SelfEvalQuiescent space d fuel a) : isEmptyOrError a = false := by
  cases h with
  | symbol h_not_err _ => exact h_not_err
  | grounded _ => rfl
  | expr h_not_err _ _ _ _ _ _ => exact h_not_err

/-- Tail-tuple self-evaluation: a list of self-evaluating, non-Empty/Error
elements, with at least two entries and a non-expression last element,
tuple-evaluates to itself. The pair case uses a wrapped singleton tail,
so reconstruction preserves a nested last element as well. -/
theorem tuple_self {space : Space} {d : GroundedDispatch} :
    ∀ (x y : Atom) (zs : List Atom) (b : Bindings),
      (∀ e ∈ x :: y :: zs, ∀ b' : Bindings,
        EvalAtom space d e Atom.undefinedType b' (e, b')) →
      (∀ e ∈ x :: y :: zs, isEmptyOrError e = false) →
      (∀ es', (x :: y :: zs).getLast? = some (Atom.expression es') → False) →
      (∀ e ∈ x :: y :: zs, e ≠ Atom.symbol "Error") →
      InterpretTuple space d (.expression (x :: y :: zs)) b
        (.expression (x :: y :: zs), b)
  | x, y, [], b, h_eval, h_ok, _h_last, h_nes => by
      have h_y : InterpretTuple space d (.expression [y]) b
          (.expression [y], b) :=
        InterpretTuple.singleton y b (y, b)
          (h_eval y (by simp) b) (h_ok y (by simp))
      exact InterpretTuple.success x [y] b (x, b) (.expression [y], b)
        (by simp) (h_eval x (by simp) b) (h_ok x (by simp)) h_y
        (isEmptyOrError_expr_false [] (h_nes y (by simp)))
  | x, y, z :: zs, b, h_eval, h_ok, h_last, h_nes => by
      have h_tl : InterpretTuple space d (.expression (y :: z :: zs)) b
          (.expression (y :: z :: zs), b) :=
        tuple_self y z zs b
          (fun e he b' => h_eval e (List.mem_cons_of_mem x he) b')
          (fun e he => h_ok e (List.mem_cons_of_mem x he))
          (fun es' h' => h_last es' (by simpa using h'))
          (fun e he => h_nes e (List.mem_cons_of_mem x he))
      have h_comb := InterpretTuple.success x (y :: z :: zs) b
        (x, b) (.expression (y :: z :: zs), b)
        (by simp)
        (h_eval x (by simp) b)
        (h_ok x (by simp))
        h_tl
        (isEmptyOrError_expr_false (z :: zs) (h_nes y (by simp)))
      simpa using h_comb

/-- **Theorem Q** (quiescent self-evaluation): on the characterized domain,
atoms officially evaluate to themselves with unchanged bindings, under
`%Undefined%` expected type. -/
theorem selfEval_of_quiescent {space : Space} {d : GroundedDispatch}
    {fuel : Nat} :
    (a : Atom) → SelfEvalQuiescent space d fuel a → (b : Bindings) →
      EvalAtom space d a Atom.undefinedType b (a, b)
  | a, h, b => by
    cases h with
    | @symbol s h_not_err h_untyped =>
        refine EvalAtom.type_cast _ _ _ _ fuel h_not_err ?_ (Or.inl rfl) ?_
        · simp [getMetaType, Atom.undefinedType, Atom.atomType,
            Atom.symbolType, Atom.variableType]
        · rw [typeCast_self_of_undefined h_untyped]
          exact List.mem_singleton.mpr rfl
    | @grounded g h_untyped =>
        refine EvalAtom.type_cast _ _ _ _ fuel rfl ?_ (Or.inr (Or.inl rfl)) ?_
        · simp [getMetaType, Atom.undefinedType, Atom.atomType,
            Atom.groundedType, Atom.variableType]
        · rw [typeCast_self_of_undefined h_untyped]
          exact List.mem_singleton.mpr rfl
    | @expr op e2 rest h_not_err h_not_exec h_no_eqs h_head_untyped h_last h_nes h_elems =>
        have h_elem_eval : ∀ e ∈ op :: e2 :: rest, ∀ b' : Bindings,
            EvalAtom space d e Atom.undefinedType b' (e, b') := by
          intro e he b'
          exact selfEval_of_quiescent e (h_elems e he) b'
        have h_elem_ok : ∀ e ∈ op :: e2 :: rest, isEmptyOrError e = false :=
          fun e he => (h_elems e he).not_empty_or_error
        have h_tuple : InterpretTuple space d (.expression (op :: e2 :: rest)) b
            (.expression (op :: e2 :: rest), b) :=
          tuple_self op e2 rest b h_elem_eval h_elem_ok h_last h_nes
        have h_not_err_atom : isErrorAtom (Atom.expression (op :: e2 :: rest)) = false := by
          simp only [isEmptyOrError, Bool.or_eq_false_iff] at h_not_err
          exact h_not_err.2
        refine EvalAtom.interpret_success _ _ _ _ h_not_err ?_ rfl ?_ ?_ ?_
        · simp [getMetaType, Atom.undefinedType, Atom.atomType,
            Atom.variableType, Atom.expressionType]
        · intro h_unit
          simp [Atom.unit] at h_unit
        · refine InterpretExpression.tuple_path _ _ _
            (.expression (op :: e2 :: rest), b)
            (.expression (op :: e2 :: rest), b)
            ⟨Atom.undefinedType, by simp [h_head_untyped], Or.inr rfl⟩
            h_tuple ?_ (by simp [Atom.unit])
          exact MettaCall.no_match _ _ _ fuel h_not_err_atom
            (by
              revert h_not_exec
              unfold HeadNotExecutable
              exact fun h => h)
            (h_no_eqs fuel)
        · exact h_not_err_atom
  termination_by a _ _ => sizeOf a
  decreasing_by
    have h1 : sizeOf e < sizeOf (op :: e2 :: rest) := List.sizeOf_lt_of_mem he
    have h2 : sizeOf (Atom.expression (op :: e2 :: rest)) =
        1 + sizeOf (op :: e2 :: rest) := by
      simp [Atom.expression.sizeOf_spec]
    omega

/-- Tail-tuple uniqueness: with all elements in Q's domain (and the shape
conditions), self-evaluation is the ONLY tuple evaluation.  Element
uniqueness is a hypothesis (supplied by `selfEval_unique`'s recursion). -/
theorem tuple_unique_of {space : Space} {d : GroundedDispatch}
    {fuel : Nat} :
    ∀ (x y : Atom) (zs : List Atom) {b : Bindings} {r : ResultPair},
      (∀ e ∈ x :: y :: zs, SelfEvalQuiescent space d fuel e) →
      (∀ e ∈ x :: y :: zs, ∀ {b' : Bindings} {r' : ResultPair},
        EvalAtom space d e Atom.undefinedType b' r' → r' = (e, b')) →
      (∀ es', (x :: y :: zs).getLast? = some (Atom.expression es') → False) →
      (∀ e ∈ x :: y :: zs, e ≠ Atom.symbol "Error") →
      InterpretTuple space d (.expression (x :: y :: zs)) b r →
      r = (.expression (x :: y :: zs), b)
  | x, y, zs, b, r, h_elems, h_uniq, h_last, h_nes, h => by
    cases h with
    | @head_error _ _ _ _ h_ne h_ev h_isErr =>
        have hr := h_uniq x (by simp) h_ev
        have h_ok := (h_elems x (by simp)).not_empty_or_error
        rw [hr] at h_isErr
        simp [h_isErr] at h_ok
    | @tail_error _ _ _ hr _ h_ne h_ev h_hok h_tail h_terr =>
        have hx := h_uniq x (by simp) h_ev
        subst hx
        cases zs with
        | nil =>
            cases h_tail with
            | @singleton _ _ _ h_ev_y _ =>
                have hy := h_uniq y (by simp) h_ev_y
                rw [hy] at h_terr
                have h_ok := isEmptyOrError_expr_false [] (h_nes y (by simp))
                simp [h_terr] at h_ok
            | @singleton_error _ _ _ h_ev_y h_error =>
                have hy := h_uniq y (by simp) h_ev_y
                rw [hy] at h_error
                have h_ok := (h_elems y (by simp)).not_empty_or_error
                simp [h_error] at h_ok
            | @head_error _ _ _ _ h_ne' _ _ => exact absurd rfl h_ne'
            | @tail_error _ _ _ _ _ h_ne' _ _ _ _ => exact absurd rfl h_ne'
            | @success _ _ _ _ _ h_ne' _ _ _ _ => exact absurd rfl h_ne'
        | cons z zs' =>
            have h_tl := tuple_unique_of y z zs'
              (fun e he => h_elems e (List.mem_cons_of_mem x he))
              (fun e he => h_uniq e (List.mem_cons_of_mem x he))
              (fun es' h' => h_last es' (by simpa using h'))
              (fun e he => h_nes e (List.mem_cons_of_mem x he))
              h_tail
            rw [h_tl] at h_terr
            have h_ok := isEmptyOrError_expr_false (z :: zs')
              (h_nes y (by simp))
            simp [h_terr] at h_ok
    | @success _ _ _ hr tr h_ne h_ev h_hok h_tl h_tok =>
        have hx := h_uniq x (by simp) h_ev
        subst hx
        cases zs with
        | nil =>
            cases h_tl with
            | @singleton _ _ _ h_ev_y _ =>
                have hy := h_uniq y (by simp) h_ev_y
                subst hy
                rfl
            | @singleton_error _ _ _ h_ev_y h_error =>
                have hy := h_uniq y (by simp) h_ev_y
                rw [hy] at h_error
                have h_ok := (h_elems y (by simp)).not_empty_or_error
                simp [h_error] at h_ok
            | @head_error _ _ _ _ h_ne' _ _ => exact absurd rfl h_ne'
            | @tail_error _ _ _ _ _ h_ne' _ _ _ _ => exact absurd rfl h_ne'
            | @success _ _ _ _ _ h_ne' _ _ _ _ => exact absurd rfl h_ne'
        | cons z zs' =>
            have h_tl' := tuple_unique_of y z zs'
              (fun e he => h_elems e (List.mem_cons_of_mem x he))
              (fun e he => h_uniq e (List.mem_cons_of_mem x he))
              (fun es' h' => h_last es' (by simpa using h'))
              (fun e he => h_nes e (List.mem_cons_of_mem x he))
              h_tl
            subst h_tl'
            rfl

/-- `MettaCall` inertness on the untyped-inert shape: with a non-executable
head, no matching equations at any fuel, and a non-Error shape, the call
returns the atom unchanged — `no_match` and `error_passthrough` are the
only constructors that survive, and both return `(atom, b)`. -/
theorem mettaCall_untyped_inert {space : Space} {d : GroundedDispatch}
    {es : List Atom} {t : Atom} {b : Bindings} {r : ResultPair}
    (h_not_exec : HeadNotExecutable d (.expression es))
    (h_no_eqs : ∀ f, queryEquations space (.expression es) f = [])
    (h : MettaCall space d (.expression es) t b r) :
    r = (.expression es, b) := by
  unfold HeadNotExecutable at h_not_exec
  cases h with
  | error_passthrough _ _ _ _ => rfl
  | unify_success_raw => simp_all
  | unify_no_match_raw => simp_all
  | unify_bad_arity => simp_all
  | switch_minimal_result => simp_all
  | switch_minimal_bad_shape => simp_all
  | no_match _ _ _ _ _ _ _ => rfl
  | grounded_ok => simp_all
  | grounded_runtime_error => simp_all
  | grounded_no_reduce => simp_all
  | grounded_incorrect_arg => simp_all
  | grounded_empty_results => simp_all
  | equation_match => simp_all
  | empty_results => simp_all

/-- **Theorem S0 (Q-uniqueness)**: on Q's domain, self-evaluation is the
ONLY official evaluation — every `EvalAtom` derivation at `%Undefined%`
returns the atom itself with unchanged bindings.  This pins arbitrary
successor derivations in the master-absorption transport (design note S0). -/
theorem selfEval_unique {space : Space} {d : GroundedDispatch}
    {fuel : Nat} :
    (a : Atom) → SelfEvalQuiescent space d fuel a →
    ∀ {b : Bindings} {r : ResultPair},
      EvalAtom space d a Atom.undefinedType b r → r = (a, b)
  | a, h_dom, b, r, h => by
    cases h with
    | empty_or_error _ _ _ _ => rfl
    | type_pass _ _ _ _ _ => rfl
    | @type_cast _ _ _ _ fuel' h_ne h_np h_branch h_result =>
        cases h_dom with
        | symbol h_not_err h_untyped =>
            rw [typeCast_self_of_undefined h_untyped] at h_result
            exact List.mem_singleton.mp h_result
        | grounded h_untyped =>
            rw [typeCast_self_of_undefined h_untyped] at h_result
            exact List.mem_singleton.mp h_result
        | expr _ _ _ _ _ _ _ =>
            rcases h_branch with h' | h' | h'
            · simp [getMetaType, Atom.symbolType, Atom.expressionType] at h'
            · simp [getMetaType, Atom.groundedType, Atom.expressionType] at h'
            · simp [Atom.unit] at h'
    | interpret_success _ _ _ _ _ _ h_expr h_not_unit h_interp h_not_error =>
        cases h_dom with
        | symbol h_not_err h_untyped =>
            simp [getMetaType, Atom.symbolType, Atom.expressionType] at h_expr
        | grounded h_untyped =>
            simp [getMetaType, Atom.groundedType, Atom.expressionType] at h_expr
        | @expr op e2 rest h_not_err h_not_exec h_no_eqs h_head_untyped h_last h_nes h_elems =>
            cases h_interp with
            | function_path =>
                simp_all [isFunctionType, Atom.undefinedType]
            | op_type_error =>
                simp_all [isFunctionType, Atom.undefinedType]
            | @tuple_path _ _ _ tupleResult _ h_has h_tuple h_mc _ =>
                have h_tr : tupleResult = (.expression (op :: e2 :: rest), b) :=
                  tuple_unique_of op e2 rest h_elems
                    (fun e he => selfEval_unique e (h_elems e he))
                    h_last h_nes h_tuple
                rw [h_tr] at h_mc
                exact mettaCall_untyped_inert h_not_exec h_no_eqs h_mc
    | interpret_error _ _ _ _ _ _ h_expr h_not_unit h_interp h_is_error =>
        cases h_dom with
        | symbol h_not_err h_untyped =>
            simp [getMetaType, Atom.symbolType, Atom.expressionType] at h_expr
        | grounded h_untyped =>
            simp [getMetaType, Atom.groundedType, Atom.expressionType] at h_expr
        | @expr op e2 rest h_not_err h_not_exec h_no_eqs h_head_untyped h_last h_nes h_elems =>
            cases h_interp with
            | function_path =>
                simp_all [isFunctionType, Atom.undefinedType]
            | op_type_error =>
                simp_all [isFunctionType, Atom.undefinedType]
            | @tuple_path _ _ _ tupleResult _ h_has h_tuple h_mc _ =>
                have h_tr : tupleResult = (.expression (op :: e2 :: rest), b) :=
                  tuple_unique_of op e2 rest h_elems
                    (fun e he => selfEval_unique e (h_elems e he))
                    h_last h_nes h_tuple
                rw [h_tr] at h_mc
                exact mettaCall_untyped_inert h_not_exec h_no_eqs h_mc
  termination_by a _ => sizeOf a
  decreasing_by
  all_goals
    have h1 : sizeOf e < sizeOf (op :: e2 :: rest) := List.sizeOf_lt_of_mem he
    have h2 : sizeOf (Atom.expression (op :: e2 :: rest)) =
        1 + sizeOf (op :: e2 :: rest) := by
      simp [Atom.expression.sizeOf_spec]
    have h3 : a = Atom.expression (op :: e2 :: rest) := ‹_›
    rw [h3]
    omega

/-- A completed list of quiescent elements with no literal `Error` symbol
retains all occurrences, including singleton and nested tuple wrappers. -/
theorem tuple_self_of_quiescent_elements {space : Space} {d : GroundedDispatch}
    {fuel : Nat} (values : List Atom) (b : Bindings)
    (h_elems : ∀ e ∈ values, SelfEvalQuiescent space d fuel e)
    (h_no_error : Atom.symbol "Error" ∉ values) :
    InterpretTuple space d (.expression values) b (.expression values, b) := by
  induction values with
  | nil => exact .nil b
  | cons head tail ih =>
      have h_head := h_elems head (by simp)
      have h_tail : ∀ e ∈ tail, SelfEvalQuiescent space d fuel e :=
        fun e he => h_elems e (List.mem_cons_of_mem head he)
      have h_tail_no_error : Atom.symbol "Error" ∉ tail :=
        fun he => h_no_error (List.mem_cons_of_mem head he)
      cases tail with
      | nil =>
          exact .singleton head b (head, b)
            (selfEval_of_quiescent head h_head b) h_head.not_empty_or_error
      | cons second rest =>
          have h_second_ne : second ≠ Atom.symbol "Error" := by
            intro he
            exact h_tail_no_error (by simp [he])
          exact .success head (second :: rest) b (head, b)
            (.expression (second :: rest), b) (by simp)
            (selfEval_of_quiescent head h_head b) h_head.not_empty_or_error
            (ih h_tail h_tail_no_error)
            (isEmptyOrError_expr_false rest h_second_ne)

/-- The completed tuple above is the only result licensed by the source
rules. Bindings and every retained occurrence are fixed by element uniqueness. -/
theorem tuple_unique_of_quiescent_elements {space : Space} {d : GroundedDispatch}
    {fuel : Nat} (values : List Atom)
    (h_elems : ∀ e ∈ values, SelfEvalQuiescent space d fuel e)
    (h_no_error : Atom.symbol "Error" ∉ values)
    {b : Bindings} {r : ResultPair}
    (h : InterpretTuple space d (.expression values) b r) :
    r = (.expression values, b) := by
  induction values generalizing b r with
  | nil => cases h; rfl
  | cons head tail ih =>
      have h_head := h_elems head (by simp)
      have h_tail : ∀ e ∈ tail, SelfEvalQuiescent space d fuel e :=
        fun e he => h_elems e (List.mem_cons_of_mem head he)
      have h_tail_no_error : Atom.symbol "Error" ∉ tail :=
        fun he => h_no_error (List.mem_cons_of_mem head he)
      have h_tail_ok : isEmptyOrError (.expression tail) = false := by
        cases tail with
        | nil => rfl
        | cons second rest =>
            apply isEmptyOrError_expr_false
            intro he
            exact h_tail_no_error (by simp [he])
      cases h with
      | singleton _ _ _ h_eval _ =>
          have he := selfEval_unique head h_head h_eval
          subst he
          rfl
      | singleton_error _ _ _ h_eval h_error =>
          have he := selfEval_unique head h_head h_eval
          rw [he] at h_error
          simp [h_head.not_empty_or_error] at h_error
      | head_error _ _ _ _ _ h_eval h_error =>
          have he := selfEval_unique head h_head h_eval
          rw [he] at h_error
          simp [h_head.not_empty_or_error] at h_error
      | tail_error _ _ _ _ _ _ h_eval _ h_eval_tail h_error =>
          have he := selfEval_unique head h_head h_eval
          subst he
          have ht := ih h_tail h_tail_no_error h_eval_tail
          rw [ht] at h_error
          simp [h_tail_ok] at h_error
      | success _ _ _ _ _ _ h_eval _ h_eval_tail _ =>
          have he := selfEval_unique head h_head h_eval
          subst he
          have ht := ih h_tail h_tail_no_error h_eval_tail
          subst ht
          rfl

/-- Once all elements have source-level self-evaluation evidence, completion
selects the suffix beginning at the rightmost literal `Error` symbol. A
constructed Error-shaped suffix propagates before earlier heads are prepended. -/
theorem tuple_rightmost_error_of_quiescent_elements
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    (front tail : List Atom) (b : Bindings)
    (h_elems : ∀ e ∈ front ++ Atom.symbol "Error" :: tail,
      SelfEvalQuiescent space d fuel e)
    (h_last : Atom.symbol "Error" ∉ tail) :
    InterpretTuple space d (.expression (front ++ Atom.symbol "Error" :: tail)) b
      (.expression (Atom.symbol "Error" :: tail), b) := by
  induction front with
  | nil =>
      have h_error := h_elems (Atom.symbol "Error") (by simp)
      cases tail with
      | nil =>
          exact .singleton (Atom.symbol "Error") b (Atom.symbol "Error", b)
            (selfEval_of_quiescent _ h_error b) h_error.not_empty_or_error
      | cons head rest =>
          have h_head_ne : head ≠ Atom.symbol "Error" := by
            intro he
            exact h_last (by simp [he])
          exact .success (Atom.symbol "Error") (head :: rest) b
            (Atom.symbol "Error", b) (.expression (head :: rest), b) (by simp)
            (selfEval_of_quiescent _ h_error b) h_error.not_empty_or_error
            (tuple_self_of_quiescent_elements (head :: rest) b
              (fun e he => h_elems e (List.mem_cons_of_mem _ he)) h_last)
            (isEmptyOrError_expr_false rest h_head_ne)
  | cons head rest ih =>
      have h_head := h_elems head (by simp)
      exact .tail_error head (rest ++ Atom.symbol "Error" :: tail) b
        (head, b) (.expression (Atom.symbol "Error" :: tail), b) (by simp)
        (selfEval_of_quiescent head h_head b) h_head.not_empty_or_error
        (ih (fun e he => h_elems e (List.mem_cons_of_mem head he))) rfl

/-- Rightmost-Error completion fixes the result and endpoint independently
of which tuple derivation was chosen. Earlier Error symbols cannot replace it. -/
theorem tuple_rightmost_error_unique_of_quiescent_elements
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    (front tail : List Atom)
    (h_elems : ∀ e ∈ front ++ Atom.symbol "Error" :: tail,
      SelfEvalQuiescent space d fuel e)
    (h_last : Atom.symbol "Error" ∉ tail)
    {b : Bindings} {r : ResultPair}
    (h : InterpretTuple space d (.expression (front ++ Atom.symbol "Error" :: tail)) b r) :
    r = (.expression (Atom.symbol "Error" :: tail), b) := by
  induction front generalizing b r with
  | nil =>
      have h_error := h_elems (Atom.symbol "Error") (by simp)
      have h_tail : ∀ e ∈ tail, SelfEvalQuiescent space d fuel e :=
        fun e he => h_elems e (List.mem_cons_of_mem _ he)
      have h_tail_ok : isEmptyOrError (.expression tail) = false := by
        cases tail with
        | nil => rfl
        | cons head rest =>
            apply isEmptyOrError_expr_false
            intro he
            exact h_last (by simp [he])
      cases h with
      | singleton _ _ _ h_eval _ =>
          have he := selfEval_unique _ h_error h_eval
          subst he
          rfl
      | singleton_error _ _ _ h_eval h_is_error =>
          have he := selfEval_unique _ h_error h_eval
          rw [he] at h_is_error
          simp [h_error.not_empty_or_error] at h_is_error
      | head_error _ _ _ _ _ h_eval h_is_error =>
          have he := selfEval_unique _ h_error h_eval
          rw [he] at h_is_error
          simp [h_error.not_empty_or_error] at h_is_error
      | tail_error _ _ _ _ _ _ h_eval _ h_eval_tail h_is_error =>
          have he := selfEval_unique _ h_error h_eval
          subst he
          have ht := tuple_unique_of_quiescent_elements tail h_tail h_last h_eval_tail
          rw [ht] at h_is_error
          simp [h_tail_ok] at h_is_error
      | success _ _ _ _ _ _ h_eval _ h_eval_tail _ =>
          have he := selfEval_unique _ h_error h_eval
          subst he
          have ht := tuple_unique_of_quiescent_elements tail h_tail h_last h_eval_tail
          subst ht
          rfl
  | cons head rest ih =>
      have h_head := h_elems head (by simp)
      have h_rest : ∀ e ∈ rest ++ Atom.symbol "Error" :: tail,
          SelfEvalQuiescent space d fuel e :=
        fun e he => h_elems e (List.mem_cons_of_mem head he)
      change InterpretTuple space d
        (.expression (head :: (rest ++ Atom.symbol "Error" :: tail))) b r at h
      generalize h_remaining : rest ++ Atom.symbol "Error" :: tail = remaining at h
      have h_remaining_ne : remaining ≠ [] := by
        rw [← h_remaining]
        simp
      have h_remaining_unique : ∀ {b' : Bindings} {r' : ResultPair},
          InterpretTuple space d (.expression remaining) b' r' →
            r' = (.expression (Atom.symbol "Error" :: tail), b') := by
        intro b' r' h'
        rw [← h_remaining] at h'
        exact ih h_rest h'
      clear h_remaining
      cases h with
      | singleton _ _ _ _ _ => exact False.elim (h_remaining_ne rfl)
      | singleton_error _ _ _ _ _ => exact False.elim (h_remaining_ne rfl)
      | head_error _ _ _ _ _ h_eval h_is_error =>
          have he := selfEval_unique head h_head h_eval
          rw [he] at h_is_error
          simp [h_head.not_empty_or_error] at h_is_error
      | tail_error _ _ _ _ _ _ h_eval _ h_eval_tail _ =>
          have he := selfEval_unique head h_head h_eval
          subst he
          exact h_remaining_unique h_eval_tail
      | success _ _ _ _ _ _ h_eval _ h_eval_tail h_tail_ok =>
          have he := selfEval_unique head h_head h_eval
          subst he
          have ht := h_remaining_unique h_eval_tail
          rw [ht] at h_tail_ok
          simp [isEmptyOrError, isEmptyAtom, isErrorAtom] at h_tail_ok

/-- Exhaustive completion/readback characterization. The rightmost occurrence
is obtained from finite list membership; no evaluation or search oracle is assumed. -/
theorem tuple_completion_iff_of_quiescent_elements
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    (values : List Atom)
    (h_elems : ∀ e ∈ values, SelfEvalQuiescent space d fuel e)
    (b : Bindings) (r : ResultPair) :
    InterpretTuple space d (.expression values) b r ↔
      (Atom.symbol "Error" ∉ values ∧ r = (.expression values, b)) ∨
      ∃ front tail, values = front ++ Atom.symbol "Error" :: tail ∧
        Atom.symbol "Error" ∉ tail ∧ r = (.expression (Atom.symbol "Error" :: tail), b) := by
  have lastError : Atom.symbol "Error" ∈ values →
      ∃ front tail, values = front ++ Atom.symbol "Error" :: tail ∧
        Atom.symbol "Error" ∉ tail := by
    clear h_elems
    induction values with
    | nil => simp
    | cons head rest ih =>
        intro member
        by_cases in_rest : Atom.symbol "Error" ∈ rest
        · obtain ⟨front, tail, eq, last⟩ := ih in_rest
          exact ⟨head :: front, tail, by rw [eq]; rfl, last⟩
        · have head_error : head = Atom.symbol "Error" := by
            rcases List.mem_cons.mp member with equal | member
            · exact equal.symm
            · exact (in_rest member).elim
          subst head
          exact ⟨[], rest, rfl, in_rest⟩
  constructor
  · intro interpreted
    by_cases member : Atom.symbol "Error" ∈ values
    · obtain ⟨front, tail, eq, last⟩ := lastError member
      right
      refine ⟨front, tail, eq, last, ?_⟩
      subst values
      exact tuple_rightmost_error_unique_of_quiescent_elements front tail h_elems last interpreted
    · exact Or.inl ⟨member, tuple_unique_of_quiescent_elements values h_elems member interpreted⟩
  · rintro (⟨no_error, rfl⟩ | ⟨front, tail, rfl, last, rfl⟩)
    · exact tuple_self_of_quiescent_elements values b h_elems no_error
    · exact tuple_rightmost_error_of_quiescent_elements front tail b h_elems last

/-- **Absorption, chain substitution half.**  On Q's domain, the coarse
`HES_Chain` substitution step coincides exactly with the official
`MinimalStep.chain` instruction's result: the official instruction
evaluates the source (to itself, by Q) and substitutes it into the
template with `applyDefault` — precisely the coarse successor. -/
theorem minimalStep_absorbs_chain_subst
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {a : Atom} {v : String} {t : Atom}
    (h_seq : SelfEvalQuiescent space d fuel a)
    (h_not_empty : a ≠ Atom.empty) :
    MinimalStep d space (.expression [.symbol "chain", a, .var v, t])
      Bindings.empty space
      ((Bindings.empty.assign v a).applyDefault t,
        Bindings.empty.assign v a) :=
  MinimalStep.chain space a v t Bindings.empty (a, Bindings.empty)
    (selfEval_of_quiescent a h_seq Bindings.empty)
    h_not_empty

end Mettapedia.Languages.MeTTa.HE
