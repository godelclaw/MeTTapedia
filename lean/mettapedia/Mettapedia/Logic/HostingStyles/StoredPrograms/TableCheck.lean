import Mettapedia.Logic.HostingStyles.StoredPrograms.Firing

/-!
# A test for stored tables

The existing test for orthogonal rule lists (`Dedukti.orthogonalCheck`)
compares every part of every left side with every left side.  For a table of
a hundred rules or more that is too much work for the kernel.  A stored table
has a shape that makes most of it unnecessary: every rule rewrites a call,
and below the head of a call a left side is a pattern of data.

`storedTableCheck rules` tests

* of each rule: that it rewrites a call (`rewritesCall`), that its left side
  is an algebraic pattern in which no variable occurs twice, that its right
  side has no binder and uses only variables of the left side, and that **no
  part of the argument of the call opens a redex** (`quiet`);
* of each two rules: that their left sides clash (`apartRules`).

A list that passes is a **stored table** (`StoredTable`): it has an orthogonal
theory (`StoredTable.orthogonal`), is a table that a space of the candidate
runs (`StoredTable.runnable`), and has rules that rewrite calls
(`StoredTable.rewriteCalls`).  Two stored tables whose rules rewrite calls of
different roots, a root being a kind and a head (`rootOf`), are a stored table
one after the other (`StoredTable.append`, `cross_of_roots`).  The parts of a left side need no
comparison: a quiet algebraic part is the left side of no call, whatever is
put for its variables (`quiet_ne_call`).

The test is narrower than the existing one in one respect: a rule that occurs
twice in the list fails it.

Positive: the table of unary addition.  Negative: the table of the two
equations of one left side (`storedTableCheck_examples`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dedukti
  (Theory RewriteRule Step Reduces inst binderFree usesOnly algebraic subpatterns clashes
    ne_inst_of_clashes instantiate_congr_of_usesOnly)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)

/-- **A quiet pattern**: variables, constants and applications, no part of
which is a redex kind applied to two terms. -/
def quiet : LF.Term → Bool
  | .var _ => true
  | .con _ => true
  | .app function argument => !opensRedex function && quiet function && quiet argument
  | _ => false

theorem quiet_app {function argument : LF.Term} :
    quiet (.app function argument) = true ↔
      opensRedex function = false ∧ quiet function = true ∧ quiet argument = true := by
  simp [quiet, and_assoc]

/-- The parts of a quiet pattern are quiet. -/
theorem quiet_of_mem_subpatterns : ∀ {whole part : LF.Term}, part ∈ subpatterns whole →
    quiet whole = true → quiet part = true := by
  intro whole
  induction whole with
  | app function argument ihFunction ihArgument =>
      intro part member isQuiet
      obtain ⟨-, functionQuiet, argumentQuiet⟩ := quiet_app.mp isQuiet
      simp only [subpatterns, List.mem_cons, List.mem_append] at member
      rcases member with rfl | rfl | inFunction | inArgument
      · exact functionQuiet
      · exact argumentQuiet
      · exact ihFunction inFunction functionQuiet
      · exact ihArgument inArgument argumentQuiet
  | var index => intro part member; simp [subpatterns] at member
  | con name => intro part member; simp [subpatterns] at member
  | srt sort => intro part member; simp [subpatterns] at member
  | pi domain body _ _ => intro part member; simp [subpatterns] at member
  | lam domain body _ _ => intro part member; simp [subpatterns] at member

/-- **A quiet headed pattern is the left side of no call**, whatever is put
for its variables: no instance of it is a redex kind applied to two terms. -/
theorem quiet_ne_call {part : LF.Term} (isQuiet : quiet part = true)
    (headed : algebraic true part = true) (assignment : Nat → LF.Term) {kind : String}
    (isKind : redexKinds.contains kind = true) (head argument : LF.Term) :
    inst assignment part ≠ .app (.app (.con kind) head) argument := by
  intro same
  cases part with
  | con name => simp at same
  | var index => simp [algebraic] at headed
  | srt sort => simp [algebraic] at headed
  | pi domain body => simp [algebraic] at headed
  | lam domain body => simp [algebraic] at headed
  | app function inner =>
      obtain ⟨closed, -, -⟩ := quiet_app.mp isQuiet
      obtain ⟨functionHeaded, -⟩ := Dedukti.algebraic_app.mp headed
      rw [Dedukti.inst_app] at same
      have functions := (LF.Term.app.inj same).1
      cases function with
      | con name => simp at functions
      | var index => simp [algebraic] at functionHeaded
      | srt sort => simp [algebraic] at functionHeaded
      | pi domain body => simp [algebraic] at functionHeaded
      | lam domain body => simp [algebraic] at functionHeaded
      | app opener first =>
          obtain ⟨openerHeaded, -⟩ := Dedukti.algebraic_app.mp functionHeaded
          rw [Dedukti.inst_app] at functions
          have openers := (LF.Term.app.inj functions).1
          cases opener with
          | con name =>
              rw [Dedukti.inst_con] at openers
              obtain rfl := LF.Term.con.inj openers
              simp only [opensRedex] at closed
              rw [isKind] at closed
              cases closed
          | var index => simp [algebraic] at openerHeaded
          | srt sort => simp [algebraic] at openerHeaded
          | pi domain body => simp [algebraic] at openerHeaded
          | lam domain body => simp [algebraic] at openerHeaded
          | app deeper second => simp at openers

/-- The argument of a call. -/
def callArgument : LF.Term → LF.Term
  | .app _ argument => argument
  | term => term

/-- **The test of one rule of a stored table.** -/
def storedRuleCheck (rule : RewriteRule) : Bool :=
  rewritesCall rule && algebraic true rule.lhs && decide (Dedukti.patternVars rule.lhs).Nodup &&
    usesOnly (Dedukti.patternVars rule.lhs) 0 rule.rhs && binderFree rule.rhs &&
    quiet (callArgument rule.lhs)

/-- **Whether the left sides of the rules of a list clash, two by two.** -/
def apartRules : List RewriteRule → Bool
  | [] => true
  | first :: rest => rest.all (fun other => clashes first.lhs other.lhs) && apartRules rest

/-- **The test for stored tables.** -/
def storedTableCheck (rules : List RewriteRule) : Bool :=
  rules.all storedRuleCheck && apartRules rules

theorem storedRuleCheck_spec {rule : RewriteRule} (checked : storedRuleCheck rule = true) :
    rewritesCall rule = true ∧ algebraic true rule.lhs = true ∧
      (Dedukti.patternVars rule.lhs).Nodup ∧
      usesOnly (Dedukti.patternVars rule.lhs) 0 rule.rhs = true ∧ binderFree rule.rhs = true ∧
      quiet (callArgument rule.lhs) = true := by
  simpa [storedRuleCheck, and_assoc] using checked

/-- An algebraic pattern has no binder. -/
theorem binderFree_of_algebraic : ∀ {term : LF.Term} {headed : Bool},
    algebraic headed term = true → binderFree term = true := by
  intro term
  induction term with
  | app function argument ihFunction ihArgument =>
      intro headed isAlgebraic
      obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := Dedukti.algebraic_app.mp isAlgebraic
      simp [binderFree, ihFunction functionAlgebraic, ihArgument argumentAlgebraic]
  | var index => intro _ _; rfl
  | con name => intro _ _; rfl
  | srt sort => intro _ _; rfl
  | pi domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | lam domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic

theorem apartRules_pairwise : ∀ {rules : List RewriteRule}, apartRules rules = true →
    rules.Pairwise fun first second => clashes first.lhs second.lhs = true
  | [], _ => List.Pairwise.nil
  | first :: rest, checked => by
      simp only [apartRules, Bool.and_eq_true, List.all_eq_true] at checked
      exact List.Pairwise.cons checked.1 (apartRules_pairwise checked.2)

/-! ## Stored tables -/

/-- **A stored table**: every rule passes the test of one rule, and the left
sides of two rules clash. -/
structure StoredTable (rules : List RewriteRule) : Prop where
  /-- Every rule passes the test of one rule. -/
  each : ∀ rule ∈ rules, storedRuleCheck rule = true
  /-- The left side of a rule clashes with that of every later rule. -/
  apart : rules.Pairwise fun first second => clashes first.lhs second.lhs = true

/-- A list that passes the test is a stored table. -/
theorem storedTable_of_check {rules : List RewriteRule} (checked : storedTableCheck rules = true) :
    StoredTable rules := by
  simp only [storedTableCheck, Bool.and_eq_true, List.all_eq_true] at checked
  exact ⟨checked.1, apartRules_pairwise checked.2⟩

/-- **Two stored tables, one after the other**, when every left side of the
first clashes with every left side of the second. -/
theorem StoredTable.append {first second : List RewriteRule} (left : StoredTable first)
    (right : StoredTable second)
    (cross : ∀ rule ∈ first, ∀ other ∈ second, clashes rule.lhs other.lhs = true) :
    StoredTable (first ++ second) where
  each := by
    intro rule member
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact left.each rule inFirst
    · exact right.each rule inSecond
  apart := List.pairwise_append.mpr ⟨left.apart, right.apart, cross⟩

/-- Two rules of a stored table have no common instance of their left
sides. -/
theorem pairwise_distinct : ∀ {rules : List RewriteRule},
    (rules.Pairwise fun first second => clashes first.lhs second.lhs = true) →
    ∀ first ∈ rules, ∀ second ∈ rules, first ≠ second →
      ∀ left right : Nat → LF.Term, inst left first.lhs ≠ inst right second.lhs
  | [], _, _, member, _, _, _ => by cases member
  | head :: rest, apartness, first, firstMember, second, secondMember, different => by
      obtain ⟨headApart, restApart⟩ := List.pairwise_cons.mp apartness
      rcases List.mem_cons.mp firstMember with rfl | firstLater
      · rcases List.mem_cons.mp secondMember with rfl | secondLater
        · exact absurd rfl different
        · exact fun left right => ne_inst_of_clashes (headApart second secondLater) left right
      · rcases List.mem_cons.mp secondMember with rfl | secondLater
        · exact fun left right same =>
            ne_inst_of_clashes (headApart first firstLater) right left same.symm
        · exact pairwise_distinct restApart first firstLater second secondLater different

/-- **A stored table is a table that a space of the candidate runs.** -/
theorem StoredTable.runnable {rules : List RewriteRule} (stored : StoredTable rules) :
    RunnableEquations rules := by
  constructor
  · intro rule member
    obtain ⟨-, leftAlgebraic, -, -, rightFree, -⟩ := storedRuleCheck_spec (stored.each rule member)
    exact ⟨binderFree_of_algebraic leftAlgebraic, rightFree⟩
  · intro rule member
    exact (storedRuleCheck_spec (stored.each rule member)).2.2.2.1

/-- **Every rule of a stored table rewrites a call.** -/
theorem StoredTable.rewriteCalls {rules : List RewriteRule} (stored : StoredTable rules) :
    ∀ rule ∈ rules, rewritesCall rule = true :=
  fun rule member => (storedRuleCheck_spec (stored.each rule member)).1

/-- **A stored table has an orthogonal theory.** -/
theorem StoredTable.orthogonal {rules : List RewriteRule} (stored : StoredTable rules) :
    (programTheory rules).Orthogonal := by
  have each := stored.each
  have distinct := pairwise_distinct stored.apart
  refine
    { closedBodies := fun name term defined => by cases defined
      leftAlgebraic := fun rule member => (storedRuleCheck_spec (each rule member)).2.1
      leftLinear := fun rule member => (storedRuleCheck_spec (each rule member)).2.2.1
      rightDetermined := fun rule member first second agree =>
        instantiate_congr_of_usesOnly agree rule.rhs 0
          (storedRuleCheck_spec (each rule member)).2.2.2.1
      leftUndefined := fun _ _ name _ => rfl
      rootUnique := fun first second firstMember secondMember left right same => by
        by_contra different
        exact distinct first firstMember second secondMember different left right same
      nonOverlapping := fun rule member part partMember partAlgebraic =>
        { undefined := fun name _ => rfl
          unmatched := fun other first second otherMember => ?_ } }
  obtain ⟨rooted, -, -, -, -, argumentQuiet⟩ := storedRuleCheck_spec (each rule member)
  obtain ⟨kind, head, argument, shape, -⟩ := rewritesCall_shape rooted
  obtain ⟨otherKind, otherHead, otherArgument, otherShape, isKind⟩ :=
    rewritesCall_shape (storedRuleCheck_spec (each other otherMember)).1
  rw [otherShape, Dedukti.inst_app, Dedukti.inst_app, Dedukti.inst_con]
  rw [shape] at partMember argumentQuiet
  simp only [callArgument] at argumentQuiet
  simp only [subpatterns, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at partMember
  rcases partMember with rfl | rfl | (rfl | rfl) | inArgument
  · simp
  · exact quiet_ne_call argumentQuiet partAlgebraic first isKind _ _
  · simp
  · simp
  · exact quiet_ne_call (quiet_of_mem_subpatterns inArgument argumentQuiet) partAlgebraic first
      isKind _ _

/-- **A list that passes the test is a table that a space of the candidate
runs.** -/
theorem runnable_of_storedTableCheck {rules : List RewriteRule}
    (checked : storedTableCheck rules = true) : RunnableEquations rules :=
  (storedTable_of_check checked).runnable

/-- **Every rule of a list that passes the test rewrites a call.** -/
theorem rewriteCalls_of_storedTableCheck {rules : List RewriteRule}
    (checked : storedTableCheck rules = true) : ∀ rule ∈ rules, rewritesCall rule = true :=
  (storedTable_of_check checked).rewriteCalls

/-- **A list that passes the test has an orthogonal theory.** -/
theorem orthogonal_of_storedTableCheck {rules : List RewriteRule}
    (checked : storedTableCheck rules = true) : (programTheory rules).Orthogonal :=
  (storedTable_of_check checked).orthogonal

/-! ## The call that a rule rewrites -/

/-- **The root of a rule**: the kind and the head of the call that it
rewrites. -/
def rootOf (rule : RewriteRule) : String × String :=
  match rule.lhs with
  | .app (.app (.con kind) (.con head)) _ => (kind, head)
  | _ => ("", "")

/-- **Two rules that rewrite calls of two roots have clashing left sides.** -/
theorem clashes_of_rootOf_ne {first second : RewriteRule} (firstRooted : rewritesCall first = true)
    (secondRooted : rewritesCall second = true) (different : rootOf first ≠ rootOf second) :
    clashes first.lhs second.lhs = true := by
  obtain ⟨kind, head, argument, shape, -⟩ := rewritesCall_shape firstRooted
  obtain ⟨otherKind, otherHead, otherArgument, otherShape, -⟩ := rewritesCall_shape secondRooted
  simp only [rootOf, shape, otherShape, ne_eq, Prod.mk.injEq, not_and] at different
  rw [shape, otherShape]
  by_cases sameKind : kind = otherKind
  · simp [clashes, sameKind, different sameKind]
  · simp [clashes, sameKind]

/-- Every rule of a stored table is apart from every rule of another, when no
root of the first is a root of the second. -/
theorem cross_of_roots {first second : List RewriteRule} (left : StoredTable first)
    (right : StoredTable second)
    (disjoint : ∀ rule ∈ first, ∀ other ∈ second, rootOf rule ≠ rootOf other) :
    ∀ rule ∈ first, ∀ other ∈ second, clashes rule.lhs other.lhs = true :=
  fun rule member other otherMember =>
    clashes_of_rootOf_ne (left.rewriteCalls rule member) (right.rewriteCalls other otherMember)
      (disjoint rule member other otherMember)

/-- **Positive and negative**: the table of unary addition passes the test;
the table of two equations for one left side does not. -/
theorem storedTableCheck_examples :
    storedTableCheck (programRules constantSpelling additionProgram []) = true ∧
      storedTableCheck (programRules constantSpelling firstOrSecond []) = false := by
  decide

#print axioms quiet_ne_call
#print axioms runnable_of_storedTableCheck
#print axioms rewriteCalls_of_storedTableCheck
#print axioms orthogonal_of_storedTableCheck
#print axioms StoredTable.append
#print axioms StoredTable.orthogonal
#print axioms clashes_of_rootOf_ne
#print axioms storedTableCheck_examples

end Mettapedia.Logic.HostingStyles.StoredPrograms
