import Mettapedia.Languages.MeTTa.HE.SmallStep
import Mettapedia.Languages.MeTTa.HE.BindingComposition
import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa

/-!
# Coarse Root Steps and Ordinary Call Returns

The root rules of `HESmallStep` expose raw grounded or equation replies.
Their correspondence with the maintained declarative model is staged:

> a root step from `a` to raw reply `b`, followed by the ordinary call-return
> judgment with saved invocation `a`, yields `MettaCall a`.

The return stage restores `a` on `NotReducible`, retains stopped results,
and evaluates other replies. Evaluating the bare successor alone is therefore
insufficient. A source-level contraction may erase this stage only with a
nonprotocol license, as in `SmallStepMaster.FragStep`.

Covered here are the two ordinary root rules and the separate minimal `eval`
instruction. This does not assert whole-language contextual contraction;
minimal control, ordinary returns and typed evaluation retain their distinct
boundaries.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- At fuel zero the equation query is empty: `simpleMatch` refuses to match
without fuel, so no equation can fire.  (Hence fuel-zero coarse equation
steps are impossible, and the absorption theorem needs no fuel premise.) -/
theorem queryEquations_zero (space : Space) (a : Atom) :
    queryEquations space a 0 = [] := by
  simp [queryEquations]

/-- The scoped equation query is also empty at fuel zero. -/
theorem queryEquationsAvoiding_zero (avoid : List String) (space : Space) (a : Atom) :
    queryEquationsAvoiding avoid space a 0 = [] := by
  simp [queryEquationsAvoiding]

/-- A raw grounded root reply composes with its ordinary return stage.
The saved original is the actual invocation, and `bs` is retained through
protocol restoration as well as ordinary evaluation. -/
theorem mettaCall_absorbs_grounded_dispatch
    {space : Space} {d : GroundedDispatch}
    {op : Atom} {args : List Atom} {rs : ResultSet} {r : Atom} {bs : Bindings}
    {type_ : Atom} {finalResult : ResultPair} (fuel : Nat)
    (h_not_special : ¬ SpecialFormHead (.expression (op :: args)))
    (h_exec : d.isExecutable op = true)
    (h_run : d.execute op args = .ok rs)
    (h_mem : (r, bs) ∈ rs)
    (h_not_err : isErrorAtom (.expression (op :: args)) = false)
    (h_return : OrdinaryCallReturnRel space d (.expression (op :: args))
      r type_ bs finalResult live) :
    MettaCall space d (live := live) (.expression (op :: args)) type_ Bindings.empty
      finalResult :=
  MettaCall.grounded_ok (.expression (op :: args)) type_ Bindings.empty
    op args rs (r, bs) bs finalResult (fuel + 1)
    rfl h_exec
    (by
      intro h_unify
      apply h_not_special
      simp [SpecialFormHead, h_unify])
    (by
      intro h_switch
      apply h_not_special
      simp [SpecialFormHead, h_switch])
    h_not_err h_run h_mem
    (by rw [mergeBindings_empty_right]; exact List.mem_singleton.mpr rfl)
    h_return

/-- **Absorption, equation match.**  A coarse `HES_EquationMatch` step from
`(es…)` to `qb.applyFull rhs fuel` composes with its ordinary return
judgment under `qb` into a `MettaCall` of the original expression under
empty incoming bindings.  This is the Lean soundness theorem behind
`HES_EquationMatch`'s `rule-sound` claim.

The coarse rule's premises are exactly the official ones: the query
membership and the head-not-executable priority come from
`MettaCall.equation_match` itself, and the coarse rule's `h_no_loop` side
condition discharges the official `hasLoop` requirement (with empty incoming
bindings, the merged bindings are the query bindings).

The official rule admits only hygienic rule instances: the instance must come
from the equation query renamed apart from every variable of the source. -/
theorem mettaCall_absorbs_equation_match
    {space : Space} {d : GroundedDispatch}
    {es : List Atom} {rhs : Atom} {qb : Bindings}
    {type_ : Atom} {finalResult : ResultPair} {fuel : Nat}
    (h_not_grounded : HeadNotExecutable d (.expression es))
    {avoid : List String}
    (h_cover : CoversEvaluation avoid live (.expression es) type_ Bindings.empty)
    (h_query : (rhs, qb) ∈ queryEquationsAvoiding avoid space (.expression es) fuel)
    (h_no_loop : qb.hasLoop = false)
    (h_not_err : isErrorAtom (.expression es) = false)
    (h_return : OrdinaryCallReturnRel space d (.expression es)
      (qb.applyFull rhs fuel) type_ qb finalResult live) :
    MettaCall space d (live := live) (.expression es) type_ Bindings.empty finalResult := by
  cases fuel with
  | zero =>
      rw [queryEquationsAvoiding_zero] at h_query
      cases h_query
  | succ n =>
      exact MettaCall.equation_match (.expression es) type_ Bindings.empty
        rhs qb qb finalResult (n + 1)
        h_not_err
        (by
          revert h_not_grounded
          unfold HeadNotExecutable
          cases es with
          | nil => intro h; exact h
          | cons op rest => intro h; exact h)
        h_cover h_query
        (by rw [mergeBindings_empty_right]; exact List.mem_singleton.mpr rfl)
        h_no_loop
        h_return

/-- Packaging both root rules: any root coarse step (grounded dispatch or
equation match, as produced by `HESmallStep`'s first two constructors)
composes with the saved-call return judgment into a `MettaCall` of the
source. The return stage uses the step's witness bindings, including when
restoring the invocation after a raw `NotReducible` reply.

The coarse equation rule protects the expected type in its retained scope.
Its actual query therefore supplies the freshness premise; no separate
assumption about the existence of a hygienic replacement is needed. -/
theorem mettaCall_absorbs_root_step
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {a b type_ : Atom} (h : HESmallStep space d fuel a b (type_ :: live))
    (h_not_err : isErrorAtom a = false)
    (h_not_special : ¬ SpecialFormHead a)
    (h_root : ∀ {pre x x' post}, a = Atom.expression (pre ++ x :: post) →
      b = Atom.expression (pre ++ x' :: post) → False) :
    ∃ bnd, ∀ {finalResult : ResultPair},
      OrdinaryCallReturnRel space d a b type_ bnd finalResult live →
      MettaCall space d (live := live) a type_ Bindings.empty finalResult := by
  cases h with
  | @grounded_dispatch scope op args rs r bs _ h_exec h_run h_mem =>
      exact ⟨bs, fun h_return =>
        mettaCall_absorbs_grounded_dispatch fuel h_not_special h_exec h_run h_mem
          h_not_err h_return⟩
  | @equation_match scope es rhs qb _ h_not_grounded h_query h_no_loop =>
      have h_cover : CoversEvaluation
          (equationScope (type_ :: live) (.expression es) Atom.undefinedType Bindings.empty)
          live (.expression es) type_ Bindings.empty := by
        intro name member
        simp only [equationScope, atomListVariables, List.mem_append] at member ⊢
        tauto
      exact ⟨qb, fun h_return =>
        mettaCall_absorbs_equation_match h_not_grounded h_cover h_query h_no_loop
          h_not_err h_return⟩
  | eval_step h_shape =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | chain_source h_shape _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | chain_subst h_shape _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | function_source h_shape _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | function_return h_shape _ _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | function_no_return h_shape _ _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | letStar_empty h_shape =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | letStar_unroll h_shape =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | let_source h_shape _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | let_subst h_shape _ _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | case_scrutinee h_shape _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | case_match h_shape _ _ _ _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | switch_scrutinee h_shape _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | switch_match h_shape _ _ _ _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | switch_minimal_match h_shape _ _ _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | @leftmost_congruence scope pre x x' post _ _ _ _ _ =>
      exact absurd rfl (fun h' => h_root h' rfl)

/-- **Absorption, eval.**  The coarse `HES_Eval` rule steps `(eval E)` to
`E`; the official `MinimalStep.eval` instruction evaluates `(eval E)` by
evaluating `E`.  So any official evaluation of the coarse successor IS an
official result of the instruction — the rule's content is exactly the
official constructor.  This is the Lean soundness theorem behind
`HES_Eval`'s `rule-sound` claim. -/
theorem minimalStep_absorbs_eval
    {space : Space} {d : GroundedDispatch}
    {e : Atom} {ib : Bindings} {r : ResultPair}
    (h_eval : EvalAtom space d e Atom.undefinedType ib r) :
    MinimalStep d space (.expression [.symbol "eval", e]) ib space r :=
  MinimalStep.eval space e ib r h_eval

end Mettapedia.Languages.MeTTa.HE
