import Mettapedia.Logic.HostingStyles.AtomsReduce.Hosting

/-!
# Two programs as equations in a space of the candidate

A program is a list of equations stored in a space, and a query is an atom
that is run in that space.  An expression `(f a b)` is read as the
application of `f` to `a` and then to `b`: expression formation of the
candidate is application of an atom to an atom, so `(f a b)` and `((f a) b)`
are one atom.  A symbol is a constant.

For a list of equations without binder whose right sides are bound, the
transitions of the run of a query are the runs of its steps by the equations
and by beta, at every position (`program_rewrites`, `exists_reduces_of_reaches`),
and a query that the equations cannot rewrite gives a run that has no
transition (`program_normal`).

## Unary addition

    (= (add Z $y) $y)
    (= (add (S $x) $y) (S (add $x $y)))

* The run of `(add m n)` reaches the run of the numeral `m + n`, for all
  numerals (`addition_reaches`), which has no transition
  (`addition_result_normal`), and every run without transition that it
  reaches is that one (`addition_normalForms`): the two equations are
  orthogonal (`addition_orthogonal`).
* For the query `(add (S (S Z)) (S Z))` the reduction has three steps
  (`addition_three_steps`).  The second and the third are beneath `S`: the
  evaluator answers nothing for `(S (add (S Z) (S Z)))` at the root
  (`addition_second_root_silent`), so the step is that of a congruence
  beneath the run.

## Two equations for one left side

    (= (choose $x $y) $x)
    (= (choose $x $y) $y)

* The run of `(choose heads tails)` has a transition to the run of `heads` and
  one to the run of `tails` (`choice_left`, `choice_right`), which are apart
  (`choice_apart`) and have no transition (`choice_results_normal`); and
  every run without transition that it reaches is one of the two
  (`choice_normalForms`).

## The four equations together: a reduct that is not a normal form

The run of `(choose (add Z Z) (add (S Z) Z))` reaches the run of
`(S (add Z Z))`, by the second equation of choice and one step of addition
(`mixed_reaches_partial`).  That run is not a normal form: it has a
transition to the run of `(S Z)`, by a step of addition beneath `S`
(`mixed_partial_steps`), which has none (`mixed_final_normal`).  The run of
the query also reaches the run of `Z`, which has none (`mixed_reaches_zero`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.LanguageDef.LFTyping (subst0)
open Mettapedia.GSLT.Dedukti
  (Theory RootStep Reduces inst patternVars usesOnly chooseLeft chooseRight chooseName
    normal_of_normalTest normalTest mayContract mayContract_of_rootStep orthogonalCheck
    orthogonal_of_check normal_form_unique_of_orthogonal inst_app inst_con inst_var)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

/-! ## Programs -/

/-- **The theory of a program**: its equations as rules, no definition. -/
abbrev programTheory (rules : List Dedukti.RewriteRule) : Theory := Theory.ofSig [] rules

/-- The cover of the theory of a program, for the test of normal terms. -/
def programCover (rules : List Dedukti.RewriteRule) : (programTheory rules).Cover :=
  Theory.coverOfRules [] rules fun _ => rfl

/-- **Equations that a space of the candidate runs**: without binder, their
right sides mentioning only variables of their left sides. -/
def RunnableEquations (rules : List Dedukti.RewriteRule) : Prop :=
  (∀ rule ∈ rules, Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true) ∧
    ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true

/-- **The transitions of the run of a query** are the runs of its steps in
the theory of the program. -/
theorem program_termStep_iff {rules : List Dedukti.RewriteRule} (runnable : RunnableEquations rules)
    {source : LF.Term} {target : Contexts.Term atomsReduce closedAtom} :
    atomsReduceTheory.rewrites (runTermIn rules source) target ↔
      ∃ next, Dedukti.Step (programTheory rules) source next ∧
        (atomsReduceTheory.equations closedAtom).r target (runTermIn rules next) :=
  termStep_runTermIn_iff runnable.1 runnable.2 (theory := programTheory rules) (fun _ => Iff.rfl)
    fun _ => rfl

/-- **A step of the program is a transition of the candidate.** -/
theorem program_rewrites {rules : List Dedukti.RewriteRule} (runnable : RunnableEquations rules)
    {source next : LF.Term} (step : Dedukti.Step (programTheory rules) source next) :
    atomsReduceTheory.rewrites (runTermIn rules source) (runTermIn rules next) :=
  (program_termStep_iff runnable).mpr ⟨next, step, Relation.EqvGen.refl _⟩

/-- A reduction of the program is a reduction of the candidate. -/
theorem program_reaches {rules : List Dedukti.RewriteRule} (runnable : RunnableEquations rules)
    {source next : LF.Term} (reduces : Reduces (programTheory rules) source next) :
    atomsReduceTheory.Reaches (runTermIn rules source) (runTermIn rules next) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (program_rewrites runnable step)

/-- **A query that the program cannot rewrite gives a run without
transition.** -/
theorem program_normal {rules : List Dedukti.RewriteRule} (runnable : RunnableEquations rules)
    {term : LF.Term} (normal : IsNormal (Dedukti.Step (programTheory rules)) term)
    (target : Contexts.Term atomsReduce closedAtom) :
    ¬ atomsReduceTheory.rewrites (runTermIn rules term) target := by
  intro step
  obtain ⟨next, sourceStep, -⟩ := (program_termStep_iff runnable).mp step
  exact normal next sourceStep

/-- **What the run of a query reaches is the run of what the query reduces
to**, up to the static equivalence. -/
theorem exists_reduces_of_reaches {rules : List Dedukti.RewriteRule}
    (runnable : RunnableEquations rules) {source : LF.Term}
    {target : Contexts.Term atomsReduce closedAtom}
    (reaches : atomsReduceTheory.Reaches (runTermIn rules source) target) :
    ∃ next, Reduces (programTheory rules) source next ∧
      (atomsReduceTheory.equations closedAtom).r target (runTermIn rules next) := by
  induction reaches with
  | refl => exact ⟨source, .refl, (atomsReduceTheory.equations closedAtom).iseqv.refl _⟩
  | tail _ step ih =>
      obtain ⟨middle, reduces, related⟩ := ih
      obtain ⟨moved, movedStep, movedRelated⟩ :=
        atomsReduceTheory.rewrites_resp_left related step
      obtain ⟨next, sourceStep, nextRelated⟩ := (program_termStep_iff runnable).mp movedStep
      exact ⟨next, reduces.tail sourceStep,
        (atomsReduceTheory.equations closedAtom).iseqv.trans movedRelated nextRelated⟩

/-- **A run without transition that the run of a query reaches is the run of
a normal form of the query.** -/
theorem exists_normal_of_reaches {rules : List Dedukti.RewriteRule}
    (runnable : RunnableEquations rules) {source : LF.Term}
    {target : Contexts.Term atomsReduce closedAtom}
    (reaches : atomsReduceTheory.Reaches (runTermIn rules source) target)
    (normal : ∀ next, ¬ atomsReduceTheory.rewrites target next) :
    ∃ result, Reduces (programTheory rules) source result ∧
      IsNormal (Dedukti.Step (programTheory rules)) result ∧
        (atomsReduceTheory.equations closedAtom).r target (runTermIn rules result) := by
  obtain ⟨result, reduces, related⟩ := exists_reduces_of_reaches runnable reaches
  refine ⟨result, reduces, fun next step => ?_, related⟩
  obtain ⟨moved, movedStep, -⟩ := atomsReduceTheory.rewrites_resp_left
    ((atomsReduceTheory.equations closedAtom).iseqv.symm related)
    (program_rewrites runnable step)
  exact normal moved movedStep

/-- What a contraction at the root of a query is: beta, or an instance of an
equation. -/
theorem rootStep_program_inv {rules : List Dedukti.RewriteRule} {source target : LF.Term}
    (root : RootStep (programTheory rules) source target) :
    (∃ domain body argument, source = .app (.lam domain body) argument ∧
      target = subst0 argument body) ∨
      ∃ rule ∈ rules, ∃ assignment : Nat → LF.Term,
        source = inst assignment rule.lhs ∧ target = inst assignment rule.rhs := by
  cases root with
  | beta domain body argument => exact .inl ⟨domain, body, argument, rfl, rfl⟩
  | delta defined => cases defined
  | @rule rule assignment member => exact .inr ⟨rule, member, assignment, rfl, rfl⟩

/-! ## Unary addition -/

/-- `Z`. -/
def zero : LF.Term := .con "Z"

/-- `(S n)`. -/
def succ (term : LF.Term) : LF.Term := .app (.con "S") term

/-- `(add m n)`. -/
def plus (first second : LF.Term) : LF.Term := .app (.app (.con "add") first) second

/-- The numeral of a number: `Z`, `(S Z)`, `(S (S Z))`, … -/
def unary : Nat → LF.Term
  | 0 => zero
  | count + 1 => succ (unary count)

/-- `(= (add Z $y) $y)`. -/
def addZero : Dedukti.RewriteRule := ⟨plus zero (.var 0), .var 0⟩

/-- `(= (add (S $x) $y) (S (add $x $y)))`. -/
def addSucc : Dedukti.RewriteRule :=
  ⟨plus (succ (.var 0)) (.var 1), succ (plus (.var 0) (.var 1))⟩

/-- **The program of unary addition.** -/
def additionRules : List Dedukti.RewriteRule := [addZero, addSucc]

/-- **Positive**: the two equations of addition are runnable. -/
theorem addition_runnable : RunnableEquations additionRules := by
  constructor <;> decide

/-- **Negative**: the equation `c = x`, whose right side mentions a variable
that its left side does not bind. -/
theorem freeRule_not_runnable :
    ¬ RunnableEquations [Mettapedia.GSLT.Dedukti.ConfluenceExamples.freeRule] := by
  intro runnable
  have bound := runnable.2 _ (List.mem_singleton.mpr rfl)
  revert bound
  decide

theorem plus_zero_step (term : LF.Term) :
    Dedukti.Step (programTheory additionRules) (plus zero term) term :=
  step_of_rule (rule := addZero) (List.mem_cons_self ..) (fun _ => term)
    (by simp [addZero, plus, zero]) (by simp [addZero])

theorem plus_succ_step (first second : LF.Term) :
    Dedukti.Step (programTheory additionRules) (plus (succ first) second)
      (succ (plus first second)) :=
  step_of_rule (rule := addSucc) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (fun index => if index = 0 then first else second)
    (by simp [addSucc, plus, succ]) (by simp [addSucc, plus, succ])

/-- **Addition computes the sum**, in `m + 1` steps of which `m` are beneath
`S`. -/
theorem addition_reduces (first second : Nat) :
    Reduces (programTheory additionRules) (plus (unary first) (unary second))
      (unary (first + second)) := by
  induction first with
  | zero =>
      rw [Nat.zero_add]
      exact .single (plus_zero_step _)
  | succ first ih =>
      rw [Nat.succ_add]
      exact Relation.ReflTransGen.head (plus_succ_step _ _)
        (ih.plug (.appArgument (.con "S") .hole))

/-- No equation of addition and no beta contracts `(S n)` at the root. -/
theorem mayContract_succ (term : LF.Term) :
    mayContract (fun _ => true) additionRules (.app (.con "S") term) = false := by
  simp [mayContract, Dedukti.isBetaRedex, Dedukti.mayUnfold, Dedukti.firstOrderMatch,
    additionRules, addZero, addSucc, plus, zero, succ]

theorem normalTest_unary (count : Nat) :
    normalTest (fun _ => true) additionRules (unary count) = true := by
  induction count with
  | zero => decide
  | succ count ih =>
      have head : mayContract (fun _ => true) additionRules (.con "S") = false := by decide
      show normalTest (fun _ => true) additionRules (.app (.con "S") (unary count)) = true
      simp only [normalTest, mayContract_succ, head, ih, Bool.not_false, Bool.and_true]

/-- A numeral has no step. -/
theorem unary_normal (count : Nat) :
    IsNormal (Dedukti.Step (programTheory additionRules)) (unary count) :=
  normal_of_normalTest (programCover additionRules) _ (normalTest_unary count)

/-- **The two equations of addition are orthogonal**: reduction by them and
by beta is confluent. -/
theorem addition_orthogonal : (programTheory additionRules).Orthogonal :=
  orthogonal_of_check additionRules (fun _ member => member) (fun _ => rfl) (by decide)

/-- **The run of `(add m n)` reaches the run of the numeral of `m + n`.** -/
theorem addition_reaches (first second : Nat) :
    atomsReduceTheory.Reaches (runTermIn additionRules (plus (unary first) (unary second)))
      (runTermIn additionRules (unary (first + second))) :=
  program_reaches addition_runnable (addition_reduces first second)

/-- **The run of a numeral has no transition.** -/
theorem addition_result_normal (count : Nat) (target : Contexts.Term atomsReduce closedAtom) :
    ¬ atomsReduceTheory.rewrites (runTermIn additionRules (unary count)) target :=
  program_normal addition_runnable (unary_normal count) target

/-- **The run of the numeral of the sum is the only run without transition
that the run of `(add m n)` reaches.** -/
theorem addition_normalForms (first second : Nat)
    {target : Contexts.Term atomsReduce closedAtom}
    (reaches : atomsReduceTheory.Reaches
      (runTermIn additionRules (plus (unary first) (unary second))) target)
    (normal : ∀ next, ¬ atomsReduceTheory.rewrites target next) :
    (atomsReduceTheory.equations closedAtom).r target
      (runTermIn additionRules (unary (first + second))) := by
  obtain ⟨result, reduces, resultNormal, related⟩ :=
    exists_normal_of_reaches addition_runnable reaches normal
  have same : result = unary (first + second) :=
    normal_form_unique_of_orthogonal addition_orthogonal reduces resultNormal
      (addition_reduces first second) (unary_normal _)
  rw [same] at related
  exact related

/-- The query `(add (S (S Z)) (S Z))`. -/
def additionQuery : LF.Term := plus (unary 2) (unary 1)

/-- **The three steps of the query**: at the root, beneath `S`, and beneath
`S` twice. -/
theorem addition_three_steps :
    atomsReduceTheory.Steps 3 (runTermIn additionRules additionQuery)
      (runTermIn additionRules (unary 3)) :=
  .succ (program_rewrites addition_runnable (plus_succ_step (unary 1) (unary 1)))
    (.succ (program_rewrites addition_runnable
        ((plus_succ_step zero (unary 1)).plug (.appArgument (.con "S") .hole)))
      (.succ (program_rewrites addition_runnable
          ((plus_zero_step (unary 1)).plug
            (.appArgument (.con "S") (.appArgument (.con "S") .hole))))
        (.zero _)))

/-- **The second step is not at the root**: no equation and no beta contracts
`(S (add (S Z) (S Z)))` at the root. -/
theorem addition_second_not_root (target : LF.Term) :
    ¬ RootStep (programTheory additionRules) (succ (plus (unary 1) (unary 1))) target := by
  intro root
  have contracts := mayContract_of_rootStep (programCover additionRules) root
  revert contracts
  decide

/-- So the evaluator answers nothing for it at the root: its step is the step
of a part, found by a congruence beneath the run. -/
theorem addition_second_root_silent :
    matchResults (ruleSpace additionRules) (atomAt 0 (succ (plus (unary 1) (unary 1)))) = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr fun answer found => ?_
  obtain ⟨rule, member, assignment, same, -⟩ :=
    (mem_matchResults_ruleSpace_iff addition_runnable.1 addition_runnable.2).mp found
  exact addition_second_not_root (inst assignment rule.rhs)
    (same ▸ RootStep.rule assignment member)

/-! ## Two equations for one left side -/

/-- **The program of choice**: `(= (choose $x $y) $x)` and
`(= (choose $x $y) $y)`. -/
def choiceRules : List Dedukti.RewriteRule := [chooseLeft, chooseRight]

theorem choice_runnable : RunnableEquations choiceRules := by
  constructor <;> decide

/-- `heads`. -/
def heads : LF.Term := .con "heads"

/-- `tails`. -/
def tails : LF.Term := .con "tails"

/-- The query `(choose heads tails)`. -/
def choiceQuery : LF.Term := Dedukti.choose heads tails

theorem choose_left_step (first second : LF.Term) :
    Dedukti.Step (programTheory choiceRules) (Dedukti.choose first second) first :=
  step_of_rule (rule := chooseLeft) (List.mem_cons_self ..)
    (fun index => if index = 0 then second else first)
    (by simp [chooseLeft, Dedukti.choose]) (by simp [chooseLeft])

theorem choose_right_step (first second : LF.Term) :
    Dedukti.Step (programTheory choiceRules) (Dedukti.choose first second) second :=
  step_of_rule (rule := chooseRight) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (fun index => if index = 0 then second else first)
    (by simp [chooseRight, Dedukti.choose]) (by simp [chooseRight])

/-- **The run of the query has a transition to the run of `heads`.** -/
theorem choice_left :
    atomsReduceTheory.rewrites (runTermIn choiceRules choiceQuery) (runTermIn choiceRules heads) :=
  program_rewrites choice_runnable (choose_left_step heads tails)

/-- **And one to the run of `tails`.** -/
theorem choice_right :
    atomsReduceTheory.rewrites (runTermIn choiceRules choiceQuery) (runTermIn choiceRules tails) :=
  program_rewrites choice_runnable (choose_right_step heads tails)

/-- **The two results are apart.** -/
theorem choice_apart :
    ¬ (atomsReduceTheory.equations closedAtom).r (runTermIn choiceRules heads)
      (runTermIn choiceRules tails) := by
  intro related
  have same := eq_runTermIn_of_related related
  exact absurd (runTermIn_injective same).2 (by decide)

/-- **Neither result has a transition.** -/
theorem choice_results_normal (target : Contexts.Term atomsReduce closedAtom) :
    ¬ atomsReduceTheory.rewrites (runTermIn choiceRules heads) target ∧
      ¬ atomsReduceTheory.rewrites (runTermIn choiceRules tails) target :=
  ⟨program_normal choice_runnable
      (normal_of_normalTest (programCover choiceRules) _ (by decide)) target,
    program_normal choice_runnable
      (normal_of_normalTest (programCover choiceRules) _ (by decide)) target⟩

/-- Every step of the query is one of the two. -/
theorem choice_step_inv {target : LF.Term}
    (step : Dedukti.Step (programTheory choiceRules) choiceQuery target) :
    target = heads ∨ target = tails := by
  rcases step.app_inv with root | ⟨function, inner, -⟩ | ⟨argument, inner, -⟩
  · rcases rootStep_program_inv root with ⟨domain, body, argument, shape, -⟩ |
      ⟨rule, member, assignment, shape, rfl⟩
    · simp at shape
    · simp only [choiceRules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simp only [Dedukti.choose, chooseLeft, inst_app, inst_con, inst_var,
          LF.Term.app.injEq, true_and] at shape ⊢
        exact .inl shape.1.symm
      · simp only [Dedukti.choose, chooseRight, inst_app, inst_con, inst_var,
          LF.Term.app.injEq, true_and] at shape ⊢
        exact .inr shape.2.symm
  · exact absurd inner (normal_of_normalTest (programCover choiceRules) _ (by decide) _)
  · exact absurd inner (normal_of_normalTest (programCover choiceRules) _ (by decide) _)

/-- **The set of normal forms**: every run without transition that the run of
the query reaches is the run of `heads` or the run of `tails`. -/
theorem choice_normalForms {target : Contexts.Term atomsReduce closedAtom}
    (reaches : atomsReduceTheory.Reaches (runTermIn choiceRules choiceQuery) target)
    (normal : ∀ next, ¬ atomsReduceTheory.rewrites target next) :
    (atomsReduceTheory.equations closedAtom).r target (runTermIn choiceRules heads) ∨
      (atomsReduceTheory.equations closedAtom).r target (runTermIn choiceRules tails) := by
  obtain ⟨result, reduces, resultNormal, related⟩ :=
    exists_normal_of_reaches choice_runnable reaches normal
  rcases Relation.ReflTransGen.cases_head reduces with same | ⟨middle, first, rest⟩
  · subst same
    exact absurd (choose_left_step heads tails) (resultNormal heads)
  · rcases choice_step_inv first with rfl | rfl
    · have fixed := (normal_of_normalTest (programCover choiceRules) heads
        (by decide)).reflTransGen_eq rest
      exact .inl (fixed ▸ related)
    · have fixed := (normal_of_normalTest (programCover choiceRules) tails
        (by decide)).reflTransGen_eq rest
      exact .inr (fixed ▸ related)

/-! ## Both programs in one space, and a query that an eager reading finishes -/

/-- The four equations together. -/
def mixedRules : List Dedukti.RewriteRule := additionRules ++ choiceRules

theorem mixed_runnable : RunnableEquations mixedRules := by
  constructor <;> decide

/-- The query `(choose (add Z Z) (add (S Z) Z))`. -/
def mixedQuery : LF.Term := Dedukti.choose (plus zero zero) (plus (unary 1) zero)

/-- **The run of the query reaches the run of `(S (add Z Z))`**: the second
equation of choice, then the second equation of addition. -/
theorem mixed_reaches_partial :
    atomsReduceTheory.Reaches (runTermIn mixedRules mixedQuery)
      (runTermIn mixedRules (succ (plus zero zero))) := by
  have chosen : Dedukti.Step (programTheory mixedRules) mixedQuery (plus (unary 1) zero) :=
    step_of_rule (rule := chooseRight) (show chooseRight ∈ mixedRules by decide)
      (fun index => if index = 0 then plus (unary 1) zero else plus zero zero)
      (by simp [chooseRight, Dedukti.choose, mixedQuery]) (by simp [chooseRight])
  have unfolded : Dedukti.Step (programTheory mixedRules) (plus (unary 1) zero)
      (succ (plus zero zero)) :=
    step_of_rule (rule := addSucc) (show addSucc ∈ mixedRules by decide) (fun _ => zero)
      (by simp [addSucc, plus, succ, unary]) (by simp [addSucc, plus, succ])
  exact (Relation.ReflTransGen.single (program_rewrites mixed_runnable chosen)).tail
    (program_rewrites mixed_runnable unfolded)

/-- **That run is not a normal form of the candidate**: it has a transition
to the run of `(S Z)`, by the first equation of addition beneath `S`. -/
theorem mixed_partial_steps :
    atomsReduceTheory.rewrites (runTermIn mixedRules (succ (plus zero zero)))
      (runTermIn mixedRules (unary 1)) := by
  have inner : Dedukti.Step (programTheory mixedRules) (plus zero zero) zero :=
    step_of_rule (rule := addZero) (show addZero ∈ mixedRules by decide) (fun _ => zero)
      (by simp [addZero, plus, zero]) (by simp [addZero])
  exact program_rewrites mixed_runnable (inner.plug (.appArgument (.con "S") .hole))

/-- **The run of `(S Z)` has no transition.** -/
theorem mixed_final_normal (target : Contexts.Term atomsReduce closedAtom) :
    ¬ atomsReduceTheory.rewrites (runTermIn mixedRules (unary 1)) target :=
  program_normal mixed_runnable (normal_of_normalTest (programCover mixedRules) _ (by decide))
    target

/-- **The run of the query also reaches the run of `Z`**, which has no
transition. -/
theorem mixed_reaches_zero :
    atomsReduceTheory.Reaches (runTermIn mixedRules mixedQuery) (runTermIn mixedRules zero) ∧
      ∀ target, ¬ atomsReduceTheory.rewrites (runTermIn mixedRules zero) target := by
  have chosen : Dedukti.Step (programTheory mixedRules) mixedQuery (plus zero zero) :=
    step_of_rule (rule := chooseLeft) (show chooseLeft ∈ mixedRules by decide)
      (fun index => if index = 0 then plus (unary 1) zero else plus zero zero)
      (by simp [chooseLeft, Dedukti.choose, mixedQuery]) (by simp [chooseLeft])
  have added : Dedukti.Step (programTheory mixedRules) (plus zero zero) zero :=
    step_of_rule (rule := addZero) (show addZero ∈ mixedRules by decide) (fun _ => zero)
      (by simp [addZero, plus, zero]) (by simp [addZero])
  exact ⟨(Relation.ReflTransGen.single (program_rewrites mixed_runnable chosen)).tail
      (program_rewrites mixed_runnable added),
    program_normal mixed_runnable (normal_of_normalTest (programCover mixedRules) _ (by decide))⟩

#print axioms program_termStep_iff
#print axioms program_reaches
#print axioms program_normal
#print axioms exists_reduces_of_reaches
#print axioms exists_normal_of_reaches
#print axioms addition_runnable
#print axioms addition_reduces
#print axioms unary_normal
#print axioms addition_orthogonal
#print axioms addition_reaches
#print axioms addition_result_normal
#print axioms addition_normalForms
#print axioms addition_three_steps
#print axioms addition_second_not_root
#print axioms addition_second_root_silent
#print axioms choice_left
#print axioms choice_right
#print axioms choice_apart
#print axioms choice_results_normal
#print axioms choice_step_inv
#print axioms choice_normalForms
#print axioms mixed_reaches_partial
#print axioms mixed_partial_steps
#print axioms mixed_final_normal
#print axioms mixed_reaches_zero
#print axioms freeRule_not_runnable

end Mettapedia.Logic.HostingStyles.AtomsReduce
