import Mettapedia.GSLT.Dedukti.Commutativity

/-!
# Addition by recursion: inside the fiber on numerals, commutativity outside it

The theory with the two recursion rules of addition,

* `plus x zero ↪ x`,
* `plus x (succ y) ↪ succ (plus x y)`,

passes the orthogonality test (`peano_check`), so its reduction is confluent.

* **Inside the fiber.**  Every closed arithmetic expression (built from
  `zero`, `succ` and `plus`) reduces to a numeral (`IsArith.reduces_numeral`),
  and numerals are normal (`numeral_normal`).  So conversion on closed
  arithmetic expressions is decided by normal forms (`peano_decidedOn`): the
  checker of the λΠ-calculus modulo decides `2 + 3 ≡ 5` by reducing both sides
  (`two_plus_three`), and two closed expressions are convertible exactly when
  their numerals are equal (`conv_iff_numeral_eq`).
* **Commutativity is not a conversion here.**  With variables, `plus x y` and
  `plus y x` are distinct normal terms (`plus_vars_normal`), so they are not
  convertible (`plus_comm_not_conv`).  Commutativity of addition is a
  propositional theorem, proved by induction, and a proof that uses it at the
  type level transports along it.  Adding it as a rule takes the theory out of
  the fiber: by `Commutativity.not_decidedOn_of_commutative`, any theory that
  converts `plus x y` with `plus y x` and keeps `plus u x` apart from
  `plus v x` decides no set containing `plus x y` and `plus y x` by normal
  forms, whatever its other rules.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.PeanoFiber

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lookupBody)
open Mettapedia.Logic.Relation (Confluent IsNormal IsNormalFormOf DecidedOn WeaklyNormalizingOn
  decidedOn_of_confluent)

def zero : Term := .con "zero"

def succ (term : Term) : Term := .app (.con "succ") term

def plus (left right : Term) : Term := .app (.app (.con "plus") left) right

/-- `plus x zero ↪ x`. -/
def plusZero : RewriteRule := ⟨plus (.var 0) zero, .var 0⟩

/-- `plus x (succ y) ↪ succ (plus x y)`. -/
def plusSucc : RewriteRule := ⟨plus (.var 0) (succ (.var 1)), succ (plus (.var 0) (.var 1))⟩

def peanoRules : List RewriteRule := [plusZero, plusSucc]

/-- The theory of addition by recursion, with no definition. -/
def peanoTheory : Theory := Theory.ofSig [] peanoRules

/-- **The recursion rules pass the orthogonality test.** -/
theorem peano_check : orthogonalCheck peanoRules = true := by decide

theorem peano_orthogonal : peanoTheory.Orthogonal :=
  orthogonal_of_check peanoRules (fun _ member => member)
    (fun name => by simp [peanoTheory, Theory.ofSig, lookupBody]) peano_check

theorem peano_confluent : Confluent (Step peanoTheory) :=
  confluent_of_orthogonal peano_orthogonal

theorem peano_closedBodies : peanoTheory.ClosedBodies :=
  peano_orthogonal.closedBodies

private theorem headed : peanoTheory.Headed :=
  peano_orthogonal.leftAlgebraic.headed

/-! ## Root steps -/

/-- A root step of the theory is beta or an instance of one of the two rules. -/
theorem rootStep_cases {source target : Term} (root : RootStep peanoTheory source target) :
    (∃ domain body argument, source = .app (.lam domain body) argument) ∨
      (∃ left, source = plus left zero ∧ target = left) ∨
      ∃ left right, source = plus left (succ right) ∧ target = succ (plus left right) := by
  cases root with
  | beta domain body argument => exact Or.inl ⟨domain, body, argument, rfl⟩
  | delta defined => simp [peanoTheory, Theory.ofSig, lookupBody] at defined
  | rule assignment member =>
      simp only [peanoTheory, Theory.ofSig, peanoRules, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact Or.inr (Or.inl ⟨assignment 0, by simp [plusZero, plus, zero],
          by simp [plusZero]⟩)
      · exact Or.inr (Or.inr ⟨assignment 0, assignment 1, by simp [plusSucc, plus, succ],
          by simp [plusSucc, plus, succ]⟩)

/-- A constant has no step. -/
theorem con_normal (name : String) : IsNormal (Step peanoTheory) (.con name) := by
  intro target step
  rcases RootStep.con_inv step.con_inv with defined | ⟨rule, assignment, member, shape, _⟩
  · simp [peanoTheory, Theory.ofSig, lookupBody] at defined
  · simp only [peanoTheory, Theory.ofSig, peanoRules, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl <;> simp [plusZero, plusSucc, plus] at shape

/-- `succ t` steps only inside `t`. -/
theorem step_succ {term target : Term} (step : Step peanoTheory (succ term) target) :
    ∃ term', Step peanoTheory term term' ∧ target = succ term' := by
  rcases step.app_inv with root | ⟨function', inner, rfl⟩ | ⟨argument', inner, rfl⟩
  · rcases rootStep_cases root with ⟨_, _, _, same⟩ | ⟨_, same, _⟩ | ⟨_, _, same, _⟩ <;>
      simp [succ, plus] at same
  · exact (con_normal "succ" _ inner).elim
  · exact ⟨argument', inner, rfl⟩

/-! ## Numerals and closed arithmetic expressions -/

def numeral : Nat → Term
  | 0 => zero
  | n + 1 => succ (numeral n)

/-- **Numerals are normal.** -/
theorem numeral_normal (n : Nat) : IsNormal (Step peanoTheory) (numeral n) := by
  induction n with
  | zero => exact con_normal "zero"
  | succ n ih =>
      intro target step
      obtain ⟨_, inner, _⟩ := step_succ step
      exact ih _ inner

/-- **A sum of numerals reduces to the numeral of the sum.** -/
theorem reduces_plus_numerals (a : Nat) :
    ∀ b : Nat, Reduces peanoTheory (plus (numeral a) (numeral b)) (numeral (a + b)) := by
  intro b
  induction b with
  | zero =>
      have root := RootStep.rule (theory := peanoTheory) (rule := plusZero) (fun _ => numeral a)
        (by simp [peanoTheory, Theory.ofSig, peanoRules])
      have step : Step peanoTheory (plus (numeral a) zero) (numeral a) := by
        simpa [plusZero, plus, zero] using Step.root root
      exact Relation.ReflTransGen.single step
  | succ b ih =>
      have root := RootStep.rule (theory := peanoTheory) (rule := plusSucc)
        (fun index => if index = 0 then numeral a else numeral b)
        (by simp [peanoTheory, Theory.ofSig, peanoRules])
      have step : Step peanoTheory (plus (numeral a) (succ (numeral b)))
          (succ (plus (numeral a) (numeral b))) := by
        simpa [plusSucc, plus, succ] using Step.root root
      have inner : Reduces peanoTheory (succ (plus (numeral a) (numeral b)))
          (succ (numeral (a + b))) := ih.plug (.appArgument (.con "succ") .hole)
      exact (Relation.ReflTransGen.single step).trans inner

/-- Closed arithmetic expressions. -/
inductive IsArith : Term → Prop where
  | zero : IsArith zero
  | succ {term : Term} : IsArith term → IsArith (succ term)
  | plus {left right : Term} : IsArith left → IsArith right → IsArith (plus left right)

/-- **Every closed arithmetic expression reduces to a numeral.** -/
theorem IsArith.reduces_numeral {term : Term} (arith : IsArith term) :
    ∃ n, Reduces peanoTheory term (numeral n) := by
  induction arith with
  | zero => exact ⟨0, .refl⟩
  | succ _ ih =>
      obtain ⟨n, reduces⟩ := ih
      exact ⟨n + 1, reduces.plug (.appArgument (.con "succ") .hole)⟩
  | plus _ _ ihLeft ihRight =>
      obtain ⟨a, left⟩ := ihLeft
      obtain ⟨b, right⟩ := ihRight
      exact ⟨a + b, (Reduces.app (Reduces.app .refl left) right).trans
        (reduces_plus_numerals a b)⟩

theorem peano_weaklyNormalizing : WeaklyNormalizingOn (Step peanoTheory) {term | IsArith term} := by
  intro _ arith
  obtain ⟨n, reduces⟩ := IsArith.reduces_numeral arith
  exact ⟨numeral n, reduces, numeral_normal n⟩

/-- **Conversion of closed arithmetic expressions is decided by normal
forms.** -/
theorem peano_decidedOn : DecidedOn (Step peanoTheory) {term | IsArith term} :=
  decidedOn_of_confluent peano_confluent peano_weaklyNormalizing

/-- Closed arithmetic expressions step only to closed arithmetic expressions. -/
theorem isArith_step {term : Term} (arith : IsArith term) :
    ∀ {target : Term}, Step peanoTheory term target → IsArith target := by
  induction arith with
  | zero => intro target step; exact (con_normal "zero" _ step).elim
  | succ _ ih =>
      intro target step
      obtain ⟨_, inner, rfl⟩ := step_succ step
      exact .succ (ih inner)
  | @plus left right leftArith rightArith ihLeft ihRight =>
      intro target step
      rcases step.app_inv with root | ⟨function', inner, rfl⟩ | ⟨argument', inner, rfl⟩
      · rcases rootStep_cases root with ⟨_, _, _, same⟩ | ⟨left', same, rfl⟩ |
            ⟨left', right', same, rfl⟩
        · simp at same
        · simp only [plus, Term.app.injEq, true_and] at same
          rw [← same.1]
          exact leftArith
        · simp only [plus, Term.app.injEq, true_and] at same
          obtain ⟨rfl, rfl⟩ := same
          cases rightArith with
          | succ inner => exact .succ (.plus leftArith inner)
      · rcases inner.app_inv with root | ⟨_, inner', _⟩ | ⟨argument'', inner', rfl⟩
        · rcases rootStep_cases root with ⟨_, _, _, same⟩ | ⟨_, same, _⟩ | ⟨_, _, same, _⟩ <;>
            simp [plus] at same
        · exact (con_normal "plus" _ inner').elim
        · exact .plus (ihLeft inner') rightArith
      · exact .plus leftArith (ihRight inner)

theorem peano_stepClosed :
    Mettapedia.Logic.Relation.StepClosed (Step peanoTheory) {term | IsArith term} :=
  fun _ _ arith step => isArith_step arith step

/-- Closed arithmetic expressions have the Church–Rosser property, read off
the decision by normal forms. -/
theorem peano_churchRosser :
    Mettapedia.Logic.Relation.ChurchRosserOn (Step peanoTheory) {term | IsArith term} :=
  ((Mettapedia.Logic.Relation.decidedOn_iff_churchRosser peano_stepClosed).mp peano_decidedOn).2

/-- Closed arithmetic expressions have unique normal forms. -/
theorem peano_uniqueNormalForms :
    Mettapedia.Logic.Relation.UniqueNormalFormsOn (Step peanoTheory) {term | IsArith term} :=
  (Mettapedia.Logic.Relation.decidedOn_iff_uniqueNormalForms.mp peano_decidedOn).2

theorem numeral_injective : Function.Injective numeral := by
  intro a b same
  induction a generalizing b with
  | zero => cases b with
    | zero => rfl
    | succ b => simp [numeral, zero, succ] at same
  | succ a ih => cases b with
    | zero => simp [numeral, zero, succ] at same
    | succ b =>
        simp only [numeral, succ, Term.app.injEq, true_and] at same
        exact congrArg (· + 1) (ih same)

/-- **Two closed arithmetic expressions are convertible exactly when they
reduce to the same numeral.** -/
theorem conv_iff_numeral_eq {left right : Term} {a b : Nat}
    (leftReduces : Reduces peanoTheory left (numeral a))
    (rightReduces : Reduces peanoTheory right (numeral b)) :
    Conv peanoTheory left right ↔ a = b :=
  (Mettapedia.Logic.Relation.conv_iff_normalForm_eq_of_confluent peano_confluent
    ⟨leftReduces, numeral_normal a⟩ ⟨rightReduces, numeral_normal b⟩).trans
    numeral_injective.eq_iff

/-- `2 + 3 ≡ 5`, by reduction. -/
theorem two_plus_three : Conv peanoTheory (plus (numeral 2) (numeral 3)) (numeral 5) :=
  (reduces_plus_numerals 2 3).conv

/-- `2 + 3` is not convertible with `4`. -/
theorem two_plus_three_ne_four : ¬ Conv peanoTheory (plus (numeral 2) (numeral 3)) (numeral 4) :=
  fun converted => by
    have := (conv_iff_numeral_eq (reduces_plus_numerals 2 3) .refl).mp converted
    omega

/-! ## Commutativity is not a conversion -/

/-- `plus u v`, for variables `u` and `v`, is normal. -/
theorem plus_vars_normal (first second : Nat) :
    IsNormal (Step peanoTheory) (plus (.var first) (.var second)) := by
  intro target step
  rcases step.app_inv with root | ⟨function', inner, rfl⟩ | ⟨argument', inner, rfl⟩
  · rcases rootStep_cases root with ⟨_, _, _, same⟩ | ⟨_, same, _⟩ | ⟨_, _, same, _⟩ <;>
      simp [plus, zero, succ] at same
  · rcases inner.app_inv with root | ⟨function'', inner', rfl⟩ | ⟨argument'', inner', rfl⟩
    · rcases rootStep_cases root with ⟨_, _, _, same⟩ | ⟨_, same, _⟩ | ⟨_, _, same, _⟩ <;>
        simp [plus] at same
    · exact con_normal "plus" _ inner'
    · exact var_normal headed first _ inner'
  · exact var_normal headed second _ inner

/-- **Commutativity of addition is not a conversion of the recursion rules.** -/
theorem plus_comm_not_conv :
    ¬ Conv peanoTheory (plus (.var 0) (.var 1)) (plus (.var 1) (.var 0)) :=
  not_conv_of_normal peano_confluent (plus_vars_normal 0 1) (plus_vars_normal 1 0)
    (by simp [plus])

#print axioms peano_check
#print axioms numeral_normal
#print axioms reduces_plus_numerals
#print axioms peano_decidedOn
#print axioms peano_stepClosed
#print axioms peano_churchRosser
#print axioms conv_iff_numeral_eq
#print axioms two_plus_three
#print axioms two_plus_three_ne_four
#print axioms plus_comm_not_conv

end Mettapedia.GSLT.Dedukti.PeanoFiber
