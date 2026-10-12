import Mettapedia.Logic.HostingStyles.NameEquality.DataEquality
import Mettapedia.Logic.HostingStyles.StoredPrograms.Sequential

/-!
# The first match by rules, for every spelling of names

The engine takes the first equation of a head whose left side matches.  A
table puts that order into rules: the call of an ordered head becomes the
trial of its first equation, a trial asks whether the arguments match the
left side of its equation, and on `False` the next equation is tried.  The
question is answered by the comparison of data in the mode `open`.

This module states those rules for an arbitrary spelling (`orderedRulesIn`),
as the comparison of data is stated for one (`structuralRules`).  The rules
are those of the existing table when the spelling is in letters.

**A theory that holds these rules for the ordered heads and the rule of each
equation of the other heads, and that holds the rules of the comparison of
data and compares written names, dispatches the program**
(`dispatches_of_tables_in`): the equations of an ordered head are tried in
their order, one question at a time (`chain_reduces_in`).

With names as constants the question is answered over the family of the
equality of names; the left side of an equation, stored as a datum for the
question, then has its names as constants.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host Env LeftLinear patternVarsList matchTerm matchTerms CallsWithin)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces inst)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## The rules of an ordered head -/

/-- **The question whether arguments match the left side of an equation**:
the comparison, in the mode `open`, of the left side as a datum with the list
of the arguments. -/
abbrev matchTestIn (N : Spelling) (equation : Equation) (arguments : LF.Term) : LF.Term :=
  same (modeTerm true) (datum N (.list equation.params)) (tag "list" arguments)

/-- **The trial of the equation at a position**, with the answer to its
question and the arguments. -/
abbrev triedIn (N : Spelling) (head : String) (position : Nat) (answer arguments : LF.Term) :
    LF.Term :=
  libTerm "select" [N.write head, unary position, answer, arguments]

/-- The equation at a position, about to fire on the arguments. -/
abbrev firedIn (N : Spelling) (head : String) (position : Nat) (arguments : LF.Term) : LF.Term :=
  libTerm "fire" [N.write head, unary position, arguments]

namespace OrderedIn

/-- The call of the head becomes the trial of its first equation. -/
def entry (N : Spelling) (head : String) (first : Equation) : RewriteRule :=
  ⟨.app (.app (.con "call") (.con head)) (.var 0),
    triedIn N head 0 (matchTestIn N first (.var 0)) (.var 0)⟩

/-- On `True` the equation at the position fires. -/
def accept (N : Spelling) (head : String) (position : Nat) : RewriteRule :=
  ⟨triedIn N head position (truth N true) (.var 0), firedIn N head position (.var 0)⟩

/-- On `False` the next equation is tried. -/
def reject (N : Spelling) (head : String) (position : Nat) (next : Equation) : RewriteRule :=
  ⟨triedIn N head position (truth N false) (.var 0),
    triedIn N head (position + 1) (matchTestIn N next (.var 0)) (.var 0)⟩

/-- The equation at the position: its left side on the arguments rewrites to
its right side. -/
def fire (N : Spelling) (called : String → Bool) (head : String) (position : Nat)
    (equation : Equation) : RewriteRule :=
  ⟨firedIn N head position (cells (patterns N (slots equation) equation.params)),
    body N called (slots equation) equation.body⟩

end OrderedIn

/-- **The rules that try a list of equations of a head in order**, from a
position. -/
def chainRulesIn (N : Spelling) (called : String → Bool) (head : String) :
    Nat → List Equation → List RewriteRule
  | _, [] => []
  | position, [equation] =>
      [OrderedIn.accept N head position, OrderedIn.fire N called head position equation]
  | position, equation :: next :: rest =>
      OrderedIn.accept N head position :: OrderedIn.fire N called head position equation ::
        OrderedIn.reject N head position next ::
          chainRulesIn N called head (position + 1) (next :: rest)

/-- **The rules of a head whose equations are tried in order.** -/
def orderedRulesIn (N : Spelling) (called : String → Bool) (program : Program) (head : String) :
    List RewriteRule :=
  match equationsOf program head with
  | [] => []
  | first :: rest => OrderedIn.entry N head first :: chainRulesIn N called head 0 (first :: rest)

/-- **Positive**: at the spelling in letters these are the rules of the
existing table.  **Negative**: a head without equation has no rule. -/
theorem orderedRulesIn_examples (called : String → Bool) (program : Program) (head : String) :
    orderedRulesIn letterSpelling called program head = orderedRules called program head ∧
      orderedRulesIn constantSpelling called [] head = [] := by
  refine ⟨?_, rfl⟩
  have chains : ∀ (equations : List Equation) (position : Nat),
      chainRulesIn letterSpelling called head position equations =
        chainRules called head position equations := by
    intro equations
    induction equations with
    | nil => intro position; rfl
    | cons equation rest ih =>
        intro position
        cases rest with
        | nil => rfl
        | cons next others =>
            simp only [chainRulesIn, chainRules, ih (position + 1)]
            rfl
  unfold orderedRulesIn orderedRules
  cases equationsOf program head with
  | nil => rfl
  | cons first rest =>
      simp only [chains]
      rfl

/-! ## The equations are tried in their order -/

/-- The question about an equation is answered: `True` when the engine matches
its left side against the arguments, `False` otherwise. -/
theorem matchTest_reduces_in (N : Spelling) {theory : Theory} (compare : HoldsStructural N theory)
    (equation : Equation) (values : List EngineTerm) :
    Reduces theory (matchTestIn N equation (cells (data N values)))
      (truth N (matchTerms equation.params values).isSome) := by
  have computed := same_reduces_over N compare true (.list equation.params) (.list values)
  have agreed : agree true (.list equation.params) (.list values) =
      (matchTerms equation.params values).isSome := by
    rw [agree_open]
    simp [matchTerm]
  rw [agreed] at computed
  exact computed

/-- **The equations of a head are tried in their order**: the trial of the
first of a list of equations, at a position, reduces to the instance of the
right side of the first equation of the list that the engine's search
selects. -/
theorem chain_reduces_in (N : Spelling) {theory : Theory} (compare : HoldsStructural N theory)
    (called : String → Bool) (head : String) (values : List EngineTerm) :
    ∀ (rest : List Equation) (first : Equation) (position : Nat),
      Holds theory (chainRulesIn N called head position (first :: rest)) →
      (∀ equation ∈ first :: rest, equation.head = head) →
      ∀ {selected : Equation} {bindings : Env}, (slots selected).Nodup →
        (first :: rest).findSome? (searchOf head values) = some (selected, bindings) →
          Reduces theory
            (triedIn N head position (matchTestIn N first (cells (data N values)))
              (cells (data N values)))
            (inst (assignment N (slots selected) bindings)
              (body N called (slots selected) selected.body)) := by
  intro rest
  induction rest with
  | nil =>
      intro first position holds heads selected bindings linear found
      have answered := matchTest_reduces_in N compare first values
      cases matched : matchTerms first.params values with
      | none =>
          rw [List.findSome?_cons, searchOf_of_unmatched matched] at found
          cases found
      | some firstBindings =>
          rw [List.findSome?_cons,
            searchOf_of_matched (heads first (List.mem_cons_self ..)) matched] at found
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
          rw [matched] at answered
          have accepted : Reduces theory
              (triedIn N head position (truth N true) (cells (data N values)))
              (firedIn N head position (cells (data N values))) :=
            fires (rule := OrderedIn.accept N head position) (holds _ (by simp [chainRulesIn]))
              [cells (data N values)] (by side [OrderedIn.accept])
              (by side [OrderedIn.accept])
          have left : inst (assignment N (slots first) firstBindings)
              (OrderedIn.fire N called head position first).lhs =
                firedIn N head position (cells (data N values)) := by
            simp only [OrderedIn.fire, inst_libTerm, List.map_cons, List.map_nil, inst_write,
              inst_unary, inst_cells]
            rw [inst_patterns N (slots first) firstBindings _ _ _ matched
              (matched_bindings matched linear)]
          exact ((reduces_libTerm "select" (.cons .refl (.cons .refl (.cons answered
            (.cons .refl .nil))))).trans accepted).trans
            (.single (step_of_rule (holds _ (by simp [chainRulesIn])) _ left rfl))
  | cons next rest ih =>
      intro first position holds heads selected bindings linear found
      have answered := matchTest_reduces_in N compare first values
      cases matched : matchTerms first.params values with
      | none =>
          rw [List.findSome?_cons, searchOf_of_unmatched matched] at found
          rw [matched] at answered
          have rejected : Reduces theory
              (triedIn N head position (truth N false) (cells (data N values)))
              (triedIn N head (position + 1) (matchTestIn N next (cells (data N values)))
                (cells (data N values))) :=
            fires (rule := OrderedIn.reject N head position next)
              (holds _ (by simp [chainRulesIn]))
              [cells (data N values)] (by side [OrderedIn.reject])
              (by side [OrderedIn.reject, modeTerm])
          have later := ih next (position + 1)
            (fun rule member => holds rule (by
              simp only [chainRulesIn, List.mem_cons]
              exact .inr (.inr (.inr member))))
            (fun equation member => heads equation (List.mem_cons_of_mem _ member)) linear found
          exact ((reduces_libTerm "select" (.cons .refl (.cons .refl (.cons answered
            (.cons .refl .nil))))).trans rejected).trans later
      | some firstBindings =>
          rw [List.findSome?_cons,
            searchOf_of_matched (heads first (List.mem_cons_self ..)) matched] at found
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
          rw [matched] at answered
          have accepted : Reduces theory
              (triedIn N head position (truth N true) (cells (data N values)))
              (firedIn N head position (cells (data N values))) :=
            fires (rule := OrderedIn.accept N head position) (holds _ (by simp [chainRulesIn]))
              [cells (data N values)] (by side [OrderedIn.accept])
              (by side [OrderedIn.accept])
          have left : inst (assignment N (slots first) firstBindings)
              (OrderedIn.fire N called head position first).lhs =
                firedIn N head position (cells (data N values)) := by
            simp only [OrderedIn.fire, inst_libTerm, List.map_cons, List.map_nil, inst_write,
              inst_unary, inst_cells]
            rw [inst_patterns N (slots first) firstBindings _ _ _ matched
              (matched_bindings matched linear)]
          exact ((reduces_libTerm "select" (.cons .refl (.cons .refl (.cons answered
            (.cons .refl .nil))))).trans accepted).trans
            (.single (step_of_rule (holds _ (by simp [chainRulesIn])) _ left rfl))

/-! ## A theory that holds the rules dispatches the program -/

/-- **A theory that holds the rule of each equation of the unordered heads,
and the ordered rules of the others, dispatches the program**, for every
spelling.  The ordered rules may be read off a larger program `source` in
which the ordered heads have the same equations, and the right sides may be
read with another test of what is called that agrees on the right sides of the
program. -/
theorem dispatches_of_tables_in (N : Spelling) {theory : Theory} {program : Program}
    {primitives : List String} (called : String → Bool)
    (agrees : ∀ equation ∈ program,
      body N (isCalled program primitives) (slots equation) equation.body =
        body N called (slots equation) equation.body)
    (leftLinear : LeftLinear program) (ordered : List String) (source : Program)
    (sameSelect : ∀ head ∈ ordered, ∀ values,
      program.select head values = source.select head values)
    (direct : ∀ equation ∈ program, equation.head ∉ ordered →
      theory.rule (ruleOf N called equation))
    (chains : ∀ head ∈ ordered, Holds theory (orderedRulesIn N called source head))
    (compare : HoldsStructural N theory) : Dispatches N theory program primitives := by
  intro head values equation bindings selected
  obtain ⟨member, sameHead, matched⟩ := select_spec selected
  rw [agrees equation member]
  by_cases inOrdered : head ∈ ordered
  · have searched := (sameSelect head inOrdered values).symm.trans selected
    rw [select_eq_equationsOf] at searched
    have holds := chains head inOrdered
    unfold orderedRulesIn at holds
    cases listed : equationsOf source head with
    | nil =>
        rw [listed] at searched
        cases searched
    | cons first rest =>
        rw [listed] at searched holds
        have heads : ∀ candidate ∈ first :: rest, candidate.head = head := by
          intro candidate inList
          have inFilter : candidate ∈ equationsOf source head := listed ▸ inList
          simpa using (List.mem_filter.mp inFilter).2
        have entered : Reduces theory (callTerm head (data N values))
            (triedIn N head 0 (matchTestIn N first (cells (data N values)))
              (cells (data N values))) :=
          fires (rule := OrderedIn.entry N head first) (holds _ (List.mem_cons_self ..))
            [cells (data N values)] (by side [OrderedIn.entry])
            (by side [OrderedIn.entry, modeTerm])
        exact entered.trans (chain_reduces_in N compare called head values rest first 0
          (fun rule inChain => holds rule (List.mem_cons_of_mem _ inChain)) heads
          (leftLinear equation member) searched)
  · have left : inst (assignment N (slots equation) bindings) (ruleOf N called equation).lhs =
        callTerm head (data N values) := by
      simp only [ruleOf, inst_callTerm, sameHead]
      rw [inst_patterns N (slots equation) bindings _ _ _ matched
        (matched_bindings matched (leftLinear equation member))]
    exact .single (step_of_rule (direct equation member (sameHead ▸ inOrdered)) _ left rfl)

#print axioms orderedRulesIn_examples
#print axioms matchTest_reduces_in
#print axioms chain_reduces_in
#print axioms dispatches_of_tables_in

end Mettapedia.Logic.HostingStyles.NameEquality
