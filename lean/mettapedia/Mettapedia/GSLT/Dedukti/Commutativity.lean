import Mettapedia.GSLT.Dedukti.OrthogonalCheck
import Mettapedia.Logic.Relation.NormalFormDecision

/-!
# Commutativity is decided by no rewrite rules

The λΠ-calculus modulo rewriting decides conversion by reducing both sides to
normal form.  This module proves that no theory of the calculus decides a
commutative operator that way, whatever its rules, their orientation, or
their number.

Write `f x y` for `op f (var 0) (var 1)`, with `f` a closed term.

* **Exchanging two variables** (`swapAt`, `swap`) is a composite of lifting
  and substitution (`subst_lift_eq_swapAt`), so every step of every theory
  with closed definitions is carried to a step (`Step.swap`); it is an
  involution (`swapAt_swapAt`).  A term fixed by the exchange has no free
  occurrence of the exchanged variables (`occurs_eq_false_of_swapAt_eq`), so
  substituting for one of them gives the same result whatever is substituted
  (`subst_eq_of_occurs_eq_false`).
* **The obstruction** (`not_decidedOn_of_commutative`): let a theory with
  closed definitions convert `f x y` with `f y x` and keep `f u x` apart from
  `f v x` for two distinct variables `u`, `v`.  Then no set of terms that
  contains `f x y` and `f y x` has its conversion decided by normal forms.  If
  the theory is confluent, `f x y` has no normal form at all
  (`no_normalForm_of_commutative`).  The proof is the symmetry obstruction of
  `Mettapedia.Logic.Relation.NormalFormDecision`: the exchange preserves the
  class of `f x y`, and a member fixed by the exchange would not depend on `x`,
  which would identify `f u x` with `f v x`.
* **The hypotheses are met** (`Witness`): the theory with the single rule
  `add x y ↪ add y x` passes the orthogonality test (`commTheory_check`), so
  it is confluent; it converts `add x y` with `add y x` and keeps `add u x`
  apart from `add v x`.  So it satisfies every syntactic condition of the
  orthogonal algebraic fragment (headed algebraic left side, left-linear,
  right side determined by the left, no overlap), and the conversion of
  `add x y` is still not decided by normal forms (`commTheory_no_normalForm`).
  Orthogonality gives confluence; it gives no normal forms.

Commutativity of addition on numerals is a different matter: a closed sum of
numerals has a normal form under the recursion rules (`PeanoFiber`).  The
obstruction is about variables, which every rule instance may permute.  This
is why rewriting modulo commutativity (and associativity) is a separate
mechanism (Peterson and Stickel 1981; Jouannaud and Kirchner 1986), and why
translations that need `max` on universe levels to commute either use it or
represent the level variables by closed codes (`LeanMinusLevelNormalization`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.Commutativity

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig lift subst lookupBody sigT)
open Mettapedia.Logic.Relation (Confluent IsNormal IsNormalFormOf DecidedOn)

/-! ## Exchanging two variables -/

/-- Exchange the variables `c` and `c + 1`; under a binder, the next two. -/
def swapAt (c : Nat) : Term → Term
  | .var k => .var (if k = c then c + 1 else if k = c + 1 then c else k)
  | .srt sort => .srt sort
  | .con name => .con name
  | .pi domain body => .pi (swapAt c domain) (swapAt (c + 1) body)
  | .lam domain body => .lam (swapAt c domain) (swapAt (c + 1) body)
  | .app function argument => .app (swapAt c function) (swapAt c argument)

/-- Exchange the two outermost free variables. -/
abbrev swap (term : Term) : Term := swapAt 0 term

/-- The exchange is lifting followed by substitution. -/
theorem subst_lift_eq_swapAt (term : Term) :
    ∀ c : Nat, subst (c + 2) (.var c) (lift 1 c term) = swapAt c term := by
  induction term with
  | var k =>
      intro c
      by_cases below : k < c
      · have notTarget : k ≠ c + 2 := by omega
        have notAbove : ¬ c + 2 < k := by omega
        have notFirst : k ≠ c := by omega
        have notSecond : k ≠ c + 1 := by omega
        simp [lift, subst, swapAt, below, notTarget, notAbove, notFirst, notSecond]
      · by_cases first : k = c
        · subst first
          simp [lift, subst, swapAt]
        · by_cases second : k = c + 1
          · subst second
            simp [lift, subst, swapAt]
          · have above : c + 2 < k + 1 := by omega
            simp [lift, subst, swapAt, below, first, second, above]
  | srt sort => intro c; rfl
  | con name => intro c; rfl
  | pi domain body ihDomain ihBody =>
      intro c
      have shifted : c + 2 + 1 = c + 1 + 2 := by omega
      simp only [lift, subst, swapAt, Nat.not_lt_zero, ↓reduceIte]
      rw [shifted, ihDomain c, ihBody (c + 1)]
  | lam domain body ihDomain ihBody =>
      intro c
      have shifted : c + 2 + 1 = c + 1 + 2 := by omega
      simp only [lift, subst, swapAt, Nat.not_lt_zero, ↓reduceIte]
      rw [shifted, ihDomain c, ihBody (c + 1)]
  | app function argument ihFunction ihArgument =>
      intro c
      simp only [lift, subst, swapAt]
      rw [ihFunction c, ihArgument c]

theorem swap_eq (term : Term) : swap term = subst 2 (.var 0) (lift 1 0 term) :=
  (subst_lift_eq_swapAt term 0).symm

/-- **The exchange is an involution.** -/
theorem swapAt_swapAt (term : Term) : ∀ c : Nat, swapAt c (swapAt c term) = term := by
  induction term with
  | var k =>
      intro c
      by_cases first : k = c
      · subst first
        simp [swapAt]
      · by_cases second : k = c + 1
        · subst second
          simp [swapAt]
        · simp [swapAt, first, second]
  | srt sort => intro c; rfl
  | con name => intro c; rfl
  | pi domain body ihDomain ihBody => intro c; simp only [swapAt, ihDomain, ihBody]
  | lam domain body ihDomain ihBody => intro c; simp only [swapAt, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro c; simp only [swapAt, ihFunction, ihArgument]

theorem swap_swap (term : Term) : swap (swap term) = term := swapAt_swapAt term 0

/-- A closed term is unchanged by the exchange. -/
theorem swap_of_closed {term : Term} (closed : Closed term) : swap term = term := by
  rw [swap_eq, closed.lift, closed.subst]

variable {theory : Theory}

/-- **Every step of a theory with closed definitions is carried to a step by
the exchange.** -/
theorem Step.swap (closedBodies : theory.ClosedBodies) {source target : Term}
    (step : Step theory source target) : Step theory (swap source) (swap target) := by
  rw [swap_eq, swap_eq]
  exact (step.lift closedBodies 1 0).subst closedBodies 2 (.var 0)

theorem Conv.swap (closedBodies : theory.ClosedBodies) {source target : Term}
    (converted : Conv theory source target) : Conv theory (swap source) (swap target) :=
  Mettapedia.Logic.Relation.EqvGen.map_of_steps (fun _ _ step => Step.swap closedBodies step)
    converted

/-! ## Free occurrences -/

/-- The variable `k` occurs free in a term; under a binder, the variable
`k + 1`. -/
def occurs (k : Nat) : Term → Bool
  | .var index => index == k
  | .srt _ => false
  | .con _ => false
  | .pi domain body => occurs k domain || occurs (k + 1) body
  | .lam domain body => occurs k domain || occurs (k + 1) body
  | .app function argument => occurs k function || occurs k argument

/-- **A term fixed by the exchange of `c` and `c + 1` has no free `c`.** -/
theorem occurs_eq_false_of_swapAt_eq (term : Term) :
    ∀ c : Nat, swapAt c term = term → occurs c term = false := by
  induction term with
  | var k =>
      intro c fixed
      by_cases first : k = c
      · subst first
        simp [swapAt] at fixed
      · simp [occurs, first]
  | srt sort => intro c _; rfl
  | con name => intro c _; rfl
  | pi domain body ihDomain ihBody =>
      intro c fixed
      simp only [swapAt, Term.pi.injEq] at fixed
      simp [occurs, ihDomain c fixed.1, ihBody (c + 1) fixed.2]
  | lam domain body ihDomain ihBody =>
      intro c fixed
      simp only [swapAt, Term.lam.injEq] at fixed
      simp [occurs, ihDomain c fixed.1, ihBody (c + 1) fixed.2]
  | app function argument ihFunction ihArgument =>
      intro c fixed
      simp only [swapAt, Term.app.injEq] at fixed
      simp [occurs, ihFunction c fixed.1, ihArgument c fixed.2]

/-- **Substituting for a variable that does not occur gives the same result
whatever is substituted.** -/
theorem subst_eq_of_occurs_eq_false (term : Term) :
    ∀ (c : Nat) (first second : Term), occurs c term = false →
      subst c first term = subst c second term := by
  induction term with
  | var k =>
      intro c first second absent
      have distinct : k ≠ c := by simpa [occurs] using absent
      simp [subst, distinct]
  | srt sort => intro c first second _; rfl
  | con name => intro c first second _; rfl
  | pi domain body ihDomain ihBody =>
      intro c first second absent
      simp only [occurs, Bool.or_eq_false_iff] at absent
      simp only [subst]
      rw [ihDomain c first second absent.1, ihBody (c + 1) _ _ absent.2]
  | lam domain body ihDomain ihBody =>
      intro c first second absent
      simp only [occurs, Bool.or_eq_false_iff] at absent
      simp only [subst]
      rw [ihDomain c first second absent.1, ihBody (c + 1) _ _ absent.2]
  | app function argument ihFunction ihArgument =>
      intro c first second absent
      simp only [occurs, Bool.or_eq_false_iff] at absent
      simp only [subst]
      rw [ihFunction c first second absent.1, ihArgument c first second absent.2]

/-! ## The obstruction -/

/-- A binary operator applied to two arguments. -/
def op (operator left right : Term) : Term := .app (.app operator left) right

theorem swap_op {operator : Term} (closed : Closed operator) :
    swap (op operator (.var 0) (.var 1)) = op operator (.var 1) (.var 0) := by
  have fixed : swapAt 0 operator = operator := swap_of_closed closed
  simp [op, swapAt, fixed]

theorem subst_op {operator : Term} (closed : Closed operator) (replacement : Term) :
    subst 0 replacement (op operator (.var 0) (.var 1)) = op operator replacement (.var 0) := by
  have fixed : subst 0 replacement operator = operator := closed.subst 0 replacement
  simp [op, subst, fixed]

/-- No term convertible with `f x y` is fixed by the exchange, when the theory
keeps `f u x` apart from `f v x`. -/
theorem not_swap_fixed (closedBodies : theory.ClosedBodies) {operator : Term}
    (closed : Closed operator)
    (separates : ¬ Conv theory (op operator (.var 1) (.var 0)) (op operator (.var 2) (.var 0)))
    {other : Term} (converted : Conv theory (op operator (.var 0) (.var 1)) other) :
    swap other ≠ other := by
  intro fixed
  have absent : occurs 0 other = false := occurs_eq_false_of_swapAt_eq other 0 fixed
  have atOne := converted.subst closedBodies 0 (.var 1)
  have atTwo := converted.subst closedBodies 0 (.var 2)
  rw [subst_op closed] at atOne atTwo
  rw [subst_eq_of_occurs_eq_false other 0 (.var 2) (.var 1) absent] at atTwo
  exact separates (.trans _ _ _ atOne (.symm _ _ atTwo))

/-- **No set of terms containing `f x y` and `f y x` has its conversion
decided by normal forms**, in any theory with closed definitions that
converts `f x y` with `f y x` and keeps `f u x` apart from `f v x`. -/
theorem not_decidedOn_of_commutative (closedBodies : theory.ClosedBodies) {operator : Term}
    (closed : Closed operator)
    (commutes : Conv theory (op operator (.var 0) (.var 1)) (op operator (.var 1) (.var 0)))
    (separates : ¬ Conv theory (op operator (.var 1) (.var 0)) (op operator (.var 2) (.var 0)))
    {S : Set Term} (member : op operator (.var 0) (.var 1) ∈ S)
    (swapped : op operator (.var 1) (.var 0) ∈ S) : ¬ DecidedOn (Step theory) S := by
  refine Mettapedia.Logic.Relation.not_decidedOn_of_symmetric_class (π := swap) (σ := swap)
    swap_swap (fun _ _ step => Step.swap closedBodies step)
    (fun _ _ step => Step.swap closedBodies step) member (by rwa [swap_op closed]) ?_
    (fun _ converted => not_swap_fixed closedBodies closed separates converted)
  rw [swap_op closed]
  exact .symm _ _ commutes

/-- **In a confluent theory, `f x y` has no normal form**, under the same
hypotheses. -/
theorem no_normalForm_of_commutative (closedBodies : theory.ClosedBodies)
    (confluent : Confluent (Step theory)) {operator : Term} (closed : Closed operator)
    (commutes : Conv theory (op operator (.var 0) (.var 1)) (op operator (.var 1) (.var 0)))
    (separates : ¬ Conv theory (op operator (.var 1) (.var 0)) (op operator (.var 2) (.var 0))) :
    ∀ normal, ¬ IsNormalFormOf (Step theory) (op operator (.var 0) (.var 1)) normal := by
  refine Mettapedia.Logic.Relation.no_normalForm_of_symmetric_class (π := swap) (σ := swap)
    confluent swap_swap (fun _ _ step => Step.swap closedBodies step)
    (fun _ _ step => Step.swap closedBodies step) ?_
    (fun _ converted => not_swap_fixed closedBodies closed separates converted)
  rw [swap_op closed]
  exact .symm _ _ commutes

/-! ## The hypotheses are met: the commutation rule -/

namespace Witness

/-- `add`. -/
def add : Term := .con "add"

/-- `add x y ↪ add y x`. -/
def commRule : RewriteRule := ⟨op add (.var 0) (.var 1), op add (.var 1) (.var 0)⟩

/-- The theory with the commutation rule and no definition. -/
def commTheory : Theory := Theory.ofSig [] [commRule]

theorem add_closed : Closed add := .con

theorem commTheory_closedBodies : commTheory.ClosedBodies := by
  intro name term defined
  simp [commTheory, Theory.ofSig, lookupBody] at defined

/-- **The commutation rule passes the orthogonality test.** -/
theorem commTheory_check : orthogonalCheck [commRule] = true := by decide

theorem commTheory_orthogonal : commTheory.Orthogonal :=
  orthogonal_of_check [commRule] (fun _ member => member)
    (fun name => by simp [commTheory, Theory.ofSig, lookupBody]) commTheory_check

theorem commTheory_confluent : Confluent (Step commTheory) :=
  confluent_of_orthogonal commTheory_orthogonal

theorem commTheory_commutes :
    Conv commTheory (op add (.var 0) (.var 1)) (op add (.var 1) (.var 0)) := by
  have step := Conv.rule (theory := commTheory) (rule := commRule) (List.mem_singleton.mpr rfl)
    (fun index => .var index)
  simpa [commRule, op, add] using step

private theorem headed : commTheory.Headed :=
  commTheory_orthogonal.leftAlgebraic.headed

/-- A root step of the commutation theory is beta or the commutation. -/
theorem rootStep_cases {source target : Term} (root : RootStep commTheory source target) :
    (∃ domain body argument, source = .app (.lam domain body) argument) ∨
      ∃ assignment : Nat → Term, source = op add (assignment 0) (assignment 1) ∧
        target = op add (assignment 1) (assignment 0) := by
  cases root with
  | beta domain body argument => exact Or.inl ⟨domain, body, argument, rfl⟩
  | delta defined => simp [commTheory, Theory.ofSig, lookupBody] at defined
  | rule assignment member =>
      have isComm : _ = commRule := List.mem_singleton.mp member
      subst isComm
      exact Or.inr ⟨assignment, by simp [commRule, op, add], by simp [commRule, op, add]⟩

/-- The steps of `add u v`, for variables `u`, `v`: the commutation only. -/
theorem step_op_vars {first second : Nat} {target : Term}
    (step : Step commTheory (op add (.var first) (.var second)) target) :
    target = op add (.var second) (.var first) := by
  rcases step.app_inv with root | ⟨function', inner, rfl⟩ | ⟨argument', inner, rfl⟩
  · rcases rootStep_cases root with ⟨domain, body, argument, same⟩ | ⟨assignment, same, rfl⟩
    · simp [add] at same
    · simp only [op, add, Term.app.injEq] at same ⊢
      obtain ⟨⟨_, firstEq⟩, secondEq⟩ := same
      rw [← firstEq, ← secondEq]
      trivial
  · exfalso
    rcases inner.app_inv with root | ⟨function'', inner', rfl⟩ | ⟨argument'', inner', rfl⟩
    · rcases rootStep_cases root with ⟨domain, body, argument, same⟩ | ⟨assignment, same, _⟩
      · simp [add] at same
      · simp [op, add] at same
    · rcases RootStep.con_inv inner'.con_inv with defined | ⟨rule, assignment, member, shape, _⟩
      · simp [commTheory, Theory.ofSig, lookupBody] at defined
      · have isComm : rule = commRule := List.mem_singleton.mp member
        subst isComm
        simp [commRule, op] at shape
    · exact var_normal headed first _ inner'
  · exact (var_normal headed second _ inner).elim

/-- The reducts of `add u v`: itself and its commutation. -/
theorem reduces_op_vars {first second : Nat} {target : Term}
    (reduces : Reduces commTheory (op add (.var first) (.var second)) target) :
    target = op add (.var first) (.var second) ∨ target = op add (.var second) (.var first) := by
  induction reduces with
  | refl => exact Or.inl rfl
  | tail _ step ih =>
      rcases ih with rfl | rfl
      · exact Or.inr (step_op_vars step)
      · exact Or.inl (step_op_vars step)

/-- **The commutation rule keeps `add u x` apart from `add v x`.** -/
theorem commTheory_separates :
    ¬ Conv commTheory (op add (.var 1) (.var 0)) (op add (.var 2) (.var 0)) := by
  intro converted
  obtain ⟨common, fromLeft, fromRight⟩ := (conv_iff_joinable commTheory_confluent).mp converted
  rcases reduces_op_vars fromLeft with rfl | rfl <;>
    rcases reduces_op_vars fromRight with same | same <;>
      simp [op, add] at same

/-- **The commutation rule is orthogonal, and `add x y` has no normal form.** -/
theorem commTheory_no_normalForm :
    ∀ normal, ¬ IsNormalFormOf (Step commTheory) (op add (.var 0) (.var 1)) normal :=
  no_normalForm_of_commutative commTheory_closedBodies commTheory_confluent add_closed
    commTheory_commutes commTheory_separates

/-- **No set containing `add x y` and `add y x` is decided by normal forms**
under the commutation rule. -/
theorem commTheory_not_decidedOn :
    ¬ DecidedOn (Step commTheory) {op add (.var 0) (.var 1), op add (.var 1) (.var 0)} :=
  not_decidedOn_of_commutative commTheory_closedBodies add_closed commTheory_commutes
    commTheory_separates (Or.inl rfl) (Or.inr rfl)

end Witness

#print axioms subst_lift_eq_swapAt
#print axioms swapAt_swapAt
#print axioms Step.swap
#print axioms occurs_eq_false_of_swapAt_eq
#print axioms subst_eq_of_occurs_eq_false
#print axioms not_decidedOn_of_commutative
#print axioms no_normalForm_of_commutative
#print axioms Witness.commTheory_check
#print axioms Witness.commTheory_separates
#print axioms Witness.commTheory_no_normalForm
#print axioms Witness.commTheory_not_decidedOn

end Mettapedia.GSLT.Dedukti.Commutativity
