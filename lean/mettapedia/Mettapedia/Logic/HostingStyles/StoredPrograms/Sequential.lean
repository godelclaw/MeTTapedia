import Mettapedia.Logic.HostingStyles.StoredPrograms.Comparison
import Mettapedia.Logic.HostingStyles.StoredPrograms.SeparatedTables
import Mettapedia.Logic.HostingStyles.StoredPrograms.Restriction

/-!
# The first match, by rules

The engine takes the first equation of a head whose left side matches.  The
rule of each equation alone does not say which is first, and the table of two
overlapping equations reaches the values of both (`firstMatch_witness`).

Here the order is put into rules, for the heads that need it.  For a head
whose equations are tried in order (`orderedRules`):

* the call of the head on its arguments becomes the trial of the first
  equation (`Ordered.entry`);
* a trial holds the head, the position of the equation, the arguments, and
  the question whether the arguments match the left side of that equation,
  which the comparison rules answer in the mode `open` (`matchTest`);
* on `True` the equation fires (`Ordered.accept`, `Ordered.fire`); on `False`
  the next equation is tried (`Ordered.reject`); after the last there is no
  rule, as the engine fails when no equation matches.

A left side is stored twice: as the pattern of the rule that fires, and as a
datum for the question.  The rules of one head have left sides that clash by
construction: two trials differ in their position or in their answer.

**A theory that holds these rules for the ordered heads, and the rule of each
equation of the other heads, dispatches the program**
(`dispatches_of_tables`): the call that selects an equation reduces to the
instance of its right side.  The equations of an ordered head are tried in
their order, one question at a time (`chain_reduces`).

Names are written in letters, because the question compares names.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host Env LeftLinear patternVarsList matchTerm matchTerms CallsWithin)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces inst)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)

/-! ## The rules of an ordered head -/

/-- **The equations of a head**, in the order of the program. -/
def equationsOf (program : Program) (head : String) : List Equation :=
  program.filter fun equation => equation.head = head

/-- **The question whether arguments match the left side of an equation**:
the comparison, in the mode `open`, of the left side as a datum with the list
of the arguments. -/
abbrev matchTest (equation : Equation) (arguments : LF.Term) : LF.Term :=
  same (modeTerm true) (datum letterSpelling (.list equation.params)) (tag "list" arguments)

/-- **The trial of the equation at a position**, with the answer to its
question and the arguments. -/
abbrev tried (head : String) (position : Nat) (answer arguments : LF.Term) : LF.Term :=
  libTerm "select" [letterSpelling.write head, unary position, answer, arguments]

/-- The equation at a position, about to fire on the arguments. -/
abbrev fired (head : String) (position : Nat) (arguments : LF.Term) : LF.Term :=
  libTerm "fire" [letterSpelling.write head, unary position, arguments]

namespace Ordered

/-- The call of the head becomes the trial of its first equation. -/
def entry (head : String) (first : Equation) : RewriteRule :=
  ⟨.app (.app (.con "call") (.con head)) (.var 0), tried head 0 (matchTest first (.var 0)) (.var 0)⟩

/-- On `True` the equation at the position fires. -/
def accept (head : String) (position : Nat) : RewriteRule :=
  ⟨tried head position yes (.var 0), fired head position (.var 0)⟩

/-- On `False` the next equation is tried. -/
def reject (head : String) (position : Nat) (next : Equation) : RewriteRule :=
  ⟨tried head position no (.var 0), tried head (position + 1) (matchTest next (.var 0)) (.var 0)⟩

/-- The equation at the position: its left side on the arguments rewrites to
its right side. -/
def fire (called : String → Bool) (head : String) (position : Nat) (equation : Equation) :
    RewriteRule :=
  ⟨fired head position (cells (patterns letterSpelling (slots equation) equation.params)),
    body letterSpelling called (slots equation) equation.body⟩

end Ordered

/-- **The rules that try a list of equations of a head in order**, from a
position. -/
def chainRules (called : String → Bool) (head : String) : Nat → List Equation → List RewriteRule
  | _, [] => []
  | position, [equation] =>
      [Ordered.accept head position, Ordered.fire called head position equation]
  | position, equation :: next :: rest =>
      Ordered.accept head position :: Ordered.fire called head position equation ::
        Ordered.reject head position next :: chainRules called head (position + 1) (next :: rest)

/-- **The rules of a head whose equations are tried in order.** -/
def orderedRules (called : String → Bool) (program : Program) (head : String) :
    List RewriteRule :=
  match equationsOf program head with
  | [] => []
  | first :: rest => Ordered.entry head first :: chainRules called head 0 (first :: rest)

/-! ## The equations are tried in their order -/

/-- The bindings of a match of patterns with distinct variables: each is at a
slot, and the match binds it to its value. -/
theorem matched_bindings {items values : List EngineTerm} {bindings : Env}
    (matched : matchTerms items values = some bindings) (distinct : (patternVarsList items).Nodup) :
    ∀ binding ∈ bindings, binding.1 ∈ patternVarsList items ∧
      bindings.lookup binding.1 = some binding.2 := by
  have keys := matchTerms_keys _ _ _ matched
  intro binding found
  exact ⟨by rw [← keys]; exact List.mem_map_of_mem found, lookup_of_mem (keys ▸ distinct) found⟩

/-- The question about an equation is answered: `True` when the engine
matches its left side against the arguments, `False` otherwise. -/
theorem matchTest_reduces {theory : Theory} (compare : HoldsComparison theory) (equation : Equation)
    (values : List EngineTerm) :
    Reduces theory (matchTest equation (cells (data letterSpelling values)))
      (truth letterSpelling (matchTerms equation.params values).isSome) := by
  have computed := same_reduces compare true (.list equation.params) (.list values)
  have agreed : agree true (.list equation.params) (.list values) =
      (matchTerms equation.params values).isSome := by
    rw [agree_open]
    simp [matchTerm]
  rw [agreed] at computed
  exact computed

/-- What the engine's search answers for one equation. -/
abbrev searchOf (head : String) (values : List EngineTerm) (equation : Equation) :
    Option (Equation × Env) :=
  if equation.head = head ∧ equation.params.length = values.length then
    (matchTerms equation.params values).map fun bindings => (equation, bindings)
  else none

theorem searchOf_of_matched {head : String} {values : List EngineTerm} {equation : Equation}
    {bindings : Env} (sameHead : equation.head = head)
    (matched : matchTerms equation.params values = some bindings) :
    searchOf head values equation = some (equation, bindings) := by
  simp [searchOf, sameHead, DeterministicEquations.matchTerms_length matched, matched]

theorem searchOf_of_unmatched {head : String} {values : List EngineTerm} {equation : Equation}
    (unmatched : matchTerms equation.params values = none) :
    searchOf head values equation = none := by
  simp [searchOf, unmatched]

/-- **The equations of a head are tried in their order**: the trial of the
first of a list of equations, at a position, reduces to the instance of the
right side of the first equation of the list that the engine's search
selects. -/
theorem chain_reduces {theory : Theory} (compare : HoldsComparison theory) (called : String → Bool)
    (head : String) (values : List EngineTerm) :
    ∀ (rest : List Equation) (first : Equation) (position : Nat),
      Holds theory (chainRules called head position (first :: rest)) →
      (∀ equation ∈ first :: rest, equation.head = head) →
      ∀ {selected : Equation} {bindings : Env}, (slots selected).Nodup →
        (first :: rest).findSome? (searchOf head values) = some (selected, bindings) →
          Reduces theory
            (tried head position (matchTest first (cells (data letterSpelling values)))
              (cells (data letterSpelling values)))
            (inst (assignment letterSpelling (slots selected) bindings)
              (body letterSpelling called (slots selected) selected.body)) := by
  intro rest
  induction rest with
  | nil =>
      intro first position holds heads selected bindings linear found
      have answered := matchTest_reduces compare first values
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
              (tried head position yes (cells (data letterSpelling values)))
              (fired head position (cells (data letterSpelling values))) :=
            fires (rule := Ordered.accept head position) (holds _ (by simp [chainRules]))
              [cells (data letterSpelling values)] (by side [Ordered.accept])
              (by side [Ordered.accept])
          have left : inst (assignment letterSpelling (slots first) firstBindings)
              (Ordered.fire called head position first).lhs =
                fired head position (cells (data letterSpelling values)) := by
            simp only [Ordered.fire, inst_libTerm, List.map_cons, List.map_nil, inst_write,
              inst_unary, inst_cells]
            rw [inst_patterns letterSpelling (slots first) firstBindings _ _ _ matched
              (matched_bindings matched linear)]
          exact ((reduces_libTerm "select" (.cons .refl (.cons .refl (.cons answered
            (.cons .refl .nil))))).trans accepted).trans
            (.single (step_of_rule (holds _ (by simp [chainRules])) _ left rfl))
  | cons next rest ih =>
      intro first position holds heads selected bindings linear found
      have answered := matchTest_reduces compare first values
      cases matched : matchTerms first.params values with
      | none =>
          rw [List.findSome?_cons, searchOf_of_unmatched matched] at found
          rw [matched] at answered
          have rejected : Reduces theory
              (tried head position no (cells (data letterSpelling values)))
              (tried head (position + 1) (matchTest next (cells (data letterSpelling values)))
                (cells (data letterSpelling values))) :=
            fires (rule := Ordered.reject head position next) (holds _ (by simp [chainRules]))
              [cells (data letterSpelling values)] (by side [Ordered.reject])
              (by side [Ordered.reject, modeTerm])
          have later := ih next (position + 1)
            (fun rule member => holds rule (by
              simp only [chainRules, List.mem_cons]
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
              (tried head position yes (cells (data letterSpelling values)))
              (fired head position (cells (data letterSpelling values))) :=
            fires (rule := Ordered.accept head position) (holds _ (by simp [chainRules]))
              [cells (data letterSpelling values)] (by side [Ordered.accept])
              (by side [Ordered.accept])
          have left : inst (assignment letterSpelling (slots first) firstBindings)
              (Ordered.fire called head position first).lhs =
                fired head position (cells (data letterSpelling values)) := by
            simp only [Ordered.fire, inst_libTerm, List.map_cons, List.map_nil, inst_write,
              inst_unary, inst_cells]
            rw [inst_patterns letterSpelling (slots first) firstBindings _ _ _ matched
              (matched_bindings matched linear)]
          exact ((reduces_libTerm "select" (.cons .refl (.cons .refl (.cons answered
            (.cons .refl .nil))))).trans accepted).trans
            (.single (step_of_rule (holds _ (by simp [chainRules])) _ left rfl))

/-- The engine's search in a program is its search among the equations of the
head. -/
theorem select_eq_equationsOf (program : Program) (head : String) (values : List EngineTerm) :
    program.select head values = (equationsOf program head).findSome? (searchOf head values) := by
  unfold Program.select equationsOf
  refine (findSome?_filter_of_none _ _ (fun equation dropped => ?_) program).symm
  have other : equation.head ≠ head := by simpa using dropped
  simp [other]

/-! ## A theory that holds the rules dispatches the program -/

mutual

/-- A right side is read alike under two tests of what is called that agree
on the heads it mentions. -/
theorem body_congr (N : Spelling) {called other : String → Bool} {heads : List String}
    (agrees : ∀ head ∈ heads, called head = other head) (names : List String) :
    ∀ term : EngineTerm, CallsWithin heads term →
      body N called names term = body N other names term
  | .var _, _ => rfl
  | .sym _, _ => rfl
  | .lit _, _ => rfl
  | .list items, confined => by
      simp only [body]
      rw [bodies_congr N agrees names items fun item member => confined.list_child member]
  | .expr items, confined => by
      simp only [body]
      rw [bodies_congr N agrees names items fun item member => confined.expr_child member]
      cases items with
      | nil => rfl
      | cons first rest =>
          cases first with
          | sym head =>
              have same : called head = other head := agrees head confined.head
              simp [expression, same]
          | var _ => rfl
          | lit _ => rfl
          | expr _ => rfl
          | list _ => rfl

theorem bodies_congr (N : Spelling) {called other : String → Bool} {heads : List String}
    (agrees : ∀ head ∈ heads, called head = other head) (names : List String) :
    ∀ items : List EngineTerm, (∀ item ∈ items, CallsWithin heads item) →
      bodies N called names items = bodies N other names items
  | [], _ => rfl
  | first :: rest, confined => by
      simp only [bodies]
      rw [body_congr N agrees names first (confined first (List.mem_cons_self ..)),
        bodies_congr N agrees names rest fun item member =>
          confined item (List.mem_cons_of_mem _ member)]

end

/-- **A theory that holds the rule of each equation of the unordered heads,
and the ordered rules of the others, dispatches the program.**  The ordered
rules may be read off a larger program `source` in which the ordered heads
have the same equations, and the right sides may be read with another test of
what is called that agrees on the right sides of the program. -/
theorem dispatches_of_tables {theory : Theory} {program : Program} {primitives : List String}
    (called : String → Bool)
    (agrees : ∀ equation ∈ program,
      body letterSpelling (isCalled program primitives) (slots equation) equation.body =
        body letterSpelling called (slots equation) equation.body)
    (leftLinear : LeftLinear program) (ordered : List String) (source : Program)
    (sameSelect : ∀ head ∈ ordered, ∀ values, program.select head values = source.select head values)
    (direct : ∀ equation ∈ program, equation.head ∉ ordered →
      theory.rule (ruleOf letterSpelling called equation))
    (chains : ∀ head ∈ ordered, Holds theory (orderedRules called source head))
    (compare : HoldsComparison theory) : Dispatches letterSpelling theory program primitives := by
  intro head values equation bindings selected
  obtain ⟨member, sameHead, matched⟩ := select_spec selected
  rw [agrees equation member]
  by_cases inOrdered : head ∈ ordered
  · have searched := (sameSelect head inOrdered values).symm.trans selected
    rw [select_eq_equationsOf] at searched
    have holds := chains head inOrdered
    unfold orderedRules at holds
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
        have entered : Reduces theory (callTerm head (data letterSpelling values))
            (tried head 0 (matchTest first (cells (data letterSpelling values)))
              (cells (data letterSpelling values))) :=
          fires (rule := Ordered.entry head first) (holds _ (List.mem_cons_self ..))
            [cells (data letterSpelling values)] (by side [Ordered.entry])
            (by side [Ordered.entry, modeTerm])
        exact entered.trans (chain_reduces compare called head values rest first 0
          (fun rule inChain => holds rule (List.mem_cons_of_mem _ inChain)) heads
          (leftLinear equation member) searched)
  · have left : inst (assignment letterSpelling (slots equation) bindings)
        (ruleOf letterSpelling called equation).lhs =
          callTerm head (data letterSpelling values) := by
      simp only [ruleOf, inst_callTerm, sameHead]
      rw [inst_patterns letterSpelling (slots equation) bindings _ _ _ matched
        (matched_bindings matched (leftLinear equation member))]
    exact .single (step_of_rule (direct equation member (sameHead ▸ inOrdered)) _ left rfl)

#print axioms matchTest_reduces
#print axioms chain_reduces
#print axioms select_eq_equationsOf
#print axioms body_congr
#print axioms dispatches_of_tables

end Mettapedia.Logic.HostingStyles.StoredPrograms
