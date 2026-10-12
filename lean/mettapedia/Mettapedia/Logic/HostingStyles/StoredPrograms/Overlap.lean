import Mettapedia.Logic.HostingStyles.StoredPrograms.SharedHost

/-!
# What is read off a program: its primitives, its special forms, its overlaps

Three functions compute, on the text of a program, what separates it from a
table.

* `calledPrimitives program handled`: the heads that a right side calls, that
  the program does not define, and that the host handles.
* `specialForms program`: the special forms of the evaluator, `let` on three
  arguments and `metta-nullary` on one, that right sides use.
* `overlappingPairs program`: the pairs of equations of one head whose left
  sides are not apart.

Two patterns are **apart** when they differ at a position where neither is a
variable (`apart`).  Then no value matches both (`not_both_of_apart`).  A
program without overlapping pair is **separated** (`Separated`,
`separated_of_no_overlappingPairs`): the equations of one head have left
sides that are pairwise apart.  For a separated program **the order of the
equations does not matter**: every equation of the head whose left side
matches the arguments is the one that the engine selects
(`Separated.select_of_matches`).

Positive: unary addition is separated.  Negative: the two equations of
`firstOrSecond` overlap (`firstOrSecond_overlaps`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host Env Special matchTerm matchTerms)

/-! ## Primitives and special forms -/

/-- **The primitives of a host that a program calls**: the heads that a right
side calls, that the program does not define, and that the host handles. -/
def calledPrimitives (program : Program) (handled : List String) : List String :=
  (program.calledHeads.filter fun head => !program.defines head && handled.contains head).eraseDups

mutual

/-- The special forms of the evaluator in a term: `let` on three arguments
and `metta-nullary` on one. -/
def specialFormsOf : EngineTerm → List String
  | .expr items => specialHead items ++ specialFormsOfList items
  | .list items => specialFormsOfList items
  | _ => []

def specialFormsOfList : List EngineTerm → List String
  | [] => []
  | first :: rest => specialFormsOf first ++ specialFormsOfList rest

/-- The special form at the head of an expression, if it is one. -/
def specialHead : List EngineTerm → List String
  | .sym head :: arguments => if Special head arguments then [head] else []
  | _ => []

end

/-- **The special forms that the right sides of a program use.** -/
def specialForms (program : Program) : List String :=
  (program.flatMap fun equation => specialFormsOf equation.body).eraseDups

/-! ## Patterns that are apart -/

mutual

/-- **Two patterns are apart**: they differ at a position where neither is a
variable. -/
def apart : EngineTerm → EngineTerm → Bool
  | .var _, _ => false
  | .sym first, .sym second => first != second
  | .sym _, .var _ => false
  | .sym _, _ => true
  | .lit first, .lit second => first != second
  | .lit _, .var _ => false
  | .lit _, _ => true
  | .expr first, .expr second => apartList first second
  | .expr _, .var _ => false
  | .expr _, _ => true
  | .list first, .list second => apartList first second
  | .list _, .var _ => false
  | .list _, _ => true

/-- Two lists of patterns are apart: they have two lengths, or two patterns at
one position are apart. -/
def apartList : List EngineTerm → List EngineTerm → Bool
  | [], [] => false
  | first :: rest, second :: others => apart first second || apartList rest others
  | [], _ :: _ => true
  | _ :: _, [] => true

end

mutual

/-- **No value matches two patterns that are apart.** -/
theorem not_both_of_apart : ∀ (first second value : EngineTerm) (left right : Env),
    apart first second = true → matchTerm first value = some left →
      matchTerm second value = some right → False
  | .var _, _, _, _, _, distinct, _, _ => by simp [apart] at distinct
  | .sym name, second, _, _, _, distinct, firstMatched, secondMatched => by
      obtain ⟨rfl, -⟩ := DeterministicEquations.matchTerm_sym firstMatched
      cases second with
      | var _ => simp [apart] at distinct
      | sym other =>
          obtain ⟨same, -⟩ := DeterministicEquations.matchTerm_sym secondMatched
          simp only [apart, bne_iff_ne, ne_eq] at distinct
          exact distinct (DeterministicEquations.Term.sym.inj same)
      | lit _ => cases (DeterministicEquations.matchTerm_lit secondMatched).1
      | expr _ =>
          obtain ⟨_, impossible, -⟩ := DeterministicEquations.matchTerm_expr secondMatched
          cases impossible
      | list _ =>
          obtain ⟨_, impossible, -⟩ := DeterministicEquations.matchTerm_list secondMatched
          cases impossible
  | .lit spelling, second, _, _, _, distinct, firstMatched, secondMatched => by
      obtain ⟨rfl, -⟩ := DeterministicEquations.matchTerm_lit firstMatched
      cases second with
      | var _ => simp [apart] at distinct
      | lit other =>
          obtain ⟨same, -⟩ := DeterministicEquations.matchTerm_lit secondMatched
          simp only [apart, bne_iff_ne, ne_eq] at distinct
          exact distinct (DeterministicEquations.Term.lit.inj same)
      | sym _ => cases (DeterministicEquations.matchTerm_sym secondMatched).1
      | expr _ =>
          obtain ⟨_, impossible, -⟩ := DeterministicEquations.matchTerm_expr secondMatched
          cases impossible
      | list _ =>
          obtain ⟨_, impossible, -⟩ := DeterministicEquations.matchTerm_list secondMatched
          cases impossible
  | .expr items, second, _, _, _, distinct, firstMatched, secondMatched => by
      obtain ⟨values, rfl, inner⟩ := DeterministicEquations.matchTerm_expr firstMatched
      cases second with
      | var _ => simp [apart] at distinct
      | expr others =>
          obtain ⟨same, shape, otherInner⟩ := DeterministicEquations.matchTerm_expr secondMatched
          cases shape
          exact not_both_of_apartList items others values _ _ (by simpa [apart] using distinct)
            inner otherInner
      | sym _ => cases (DeterministicEquations.matchTerm_sym secondMatched).1
      | lit _ => cases (DeterministicEquations.matchTerm_lit secondMatched).1
      | list _ =>
          obtain ⟨_, impossible, -⟩ := DeterministicEquations.matchTerm_list secondMatched
          cases impossible
  | .list items, second, _, _, _, distinct, firstMatched, secondMatched => by
      obtain ⟨values, rfl, inner⟩ := DeterministicEquations.matchTerm_list firstMatched
      cases second with
      | var _ => simp [apart] at distinct
      | list others =>
          obtain ⟨same, shape, otherInner⟩ := DeterministicEquations.matchTerm_list secondMatched
          cases shape
          exact not_both_of_apartList items others values _ _ (by simpa [apart] using distinct)
            inner otherInner
      | sym _ => cases (DeterministicEquations.matchTerm_sym secondMatched).1
      | lit _ => cases (DeterministicEquations.matchTerm_lit secondMatched).1
      | expr _ =>
          obtain ⟨_, impossible, -⟩ := DeterministicEquations.matchTerm_expr secondMatched
          cases impossible

theorem not_both_of_apartList : ∀ (first second values : List EngineTerm) (left right : Env),
    apartList first second = true → matchTerms first values = some left →
      matchTerms second values = some right → False
  | [], [], _, _, _, distinct, _, _ => by simp [apartList] at distinct
  | [], _ :: _, _, _, _, _, firstMatched, secondMatched => by
      obtain ⟨rfl, -⟩ := DeterministicEquations.matchTerms_nil firstMatched
      obtain ⟨_, _, _, _, impossible, -⟩ := DeterministicEquations.matchTerms_cons secondMatched
      cases impossible
  | _ :: _, [], _, _, _, _, firstMatched, secondMatched => by
      obtain ⟨rfl, -⟩ := DeterministicEquations.matchTerms_nil secondMatched
      obtain ⟨_, _, _, _, impossible, -⟩ := DeterministicEquations.matchTerms_cons firstMatched
      cases impossible
  | first :: rest, second :: others, _, _, _, distinct, firstMatched, secondMatched => by
      obtain ⟨value, tail, _, _, rfl, headMatched, tailMatched, -⟩ :=
        DeterministicEquations.matchTerms_cons firstMatched
      obtain ⟨_, _, _, _, shape, otherHead, otherTail, -⟩ :=
        DeterministicEquations.matchTerms_cons secondMatched
      cases shape
      simp only [apartList, Bool.or_eq_true] at distinct
      rcases distinct with inHead | inTail
      · exact not_both_of_apart first second value _ _ inHead headMatched otherHead
      · exact not_both_of_apartList rest others tail _ _ inTail tailMatched otherTail

end

/-! ## Separated programs -/

/-- **The pairs of equations of one head whose left sides are not apart**, by
their names. -/
def overlappingPairs : Program → List (String × String)
  | [] => []
  | first :: rest =>
      (rest.filterMap fun second =>
        if first.head = second.head ∧ apartList first.params second.params = false then
          some (first.name, second.name)
        else none) ++ overlappingPairs rest

/-- **A separated program**: the left sides of two equations of one head are
apart. -/
def Separated (program : Program) : Prop :=
  program.Pairwise fun first second =>
    first.head = second.head → apartList first.params second.params = true

theorem separated_of_no_overlappingPairs : ∀ {program : Program},
    overlappingPairs program = [] → Separated program
  | [], _ => List.Pairwise.nil
  | first :: rest, empty => by
      simp only [overlappingPairs, List.append_eq_nil_iff, List.filterMap_eq_nil_iff] at empty
      refine List.Pairwise.cons (fun second member sameHead => ?_)
        (separated_of_no_overlappingPairs empty.2)
      have absent := empty.1 second member
      by_cases isApart : apartList first.params second.params = true
      · exact isApart
      · simp [sameHead, isApart] at absent

/-- **For a separated program the order of the equations does not matter**:
an equation of the head whose left side matches the arguments is the one that
the engine selects. -/
theorem Separated.select_of_matches : ∀ {program : Program}, Separated program →
    ∀ {equation : Equation} {head : String} {arguments : List EngineTerm} {bindings : Env},
      equation ∈ program → equation.head = head →
      matchTerms equation.params arguments = some bindings →
        program.select head arguments = some (equation, bindings)
  | [], _, _, _, _, _, member, _, _ => by cases member
  | first :: rest, separated, equation, head, arguments, bindings, member, sameHead, matched => by
      obtain ⟨firstApart, restSeparated⟩ := List.pairwise_cons.mp separated
      have sameLength := DeterministicEquations.matchTerms_length matched
      rcases List.mem_cons.mp member with rfl | later
      · simp [Program.select, sameHead, sameLength, matched]
      · have inRest := Separated.select_of_matches restSeparated later sameHead matched
        have skipped : (if first.head = head ∧ first.params.length = arguments.length then
            (matchTerms first.params arguments).map fun found => (first, found) else none) = none := by
          split
          · next condition =>
            cases firstMatched : matchTerms first.params arguments with
            | none => rfl
            | some other =>
                exact (not_both_of_apartList _ _ _ _ _
                  (firstApart equation later (condition.1.trans sameHead.symm)) firstMatched
                  matched).elim
          · rfl
        simp only [Program.select, List.findSome?_cons, skipped]
        exact inRest

/-- **Positive**: unary addition is separated. -/
theorem additionProgram_separated : Separated additionProgram :=
  separated_of_no_overlappingPairs (by decide)

/-- **Negative**: the two equations of `firstOrSecond` overlap, and the
program is not separated. -/
theorem firstOrSecond_overlaps :
    overlappingPairs firstOrSecond = [("first", "second")] ∧ ¬ Separated firstOrSecond := by
  refine ⟨by decide, fun separated => ?_⟩
  have selected := separated.select_of_matches (equation := ⟨"second", "pick", [.var "x"], .sym "B"⟩)
    (head := "pick") (arguments := [.sym "c"]) (bindings := [("x", .sym "c")])
    (by simp [firstOrSecond]) rfl rfl
  have actual : firstOrSecond.select "pick" [.sym "c"] =
      some (⟨"first", "pick", [.var "x"], .sym "A"⟩, [("x", .sym "c")]) := rfl
  rw [actual] at selected
  simp at selected

/-- **Positive and negative**: unary addition calls no primitive and has no
special form; the program with a `let` has one. -/
theorem specialForms_examples :
    specialForms additionProgram = [] ∧ calledPrimitives additionProgram computationalHandled = [] ∧
      specialForms withLet = ["let"] := by
  decide

#print axioms not_both_of_apart
#print axioms separated_of_no_overlappingPairs
#print axioms Separated.select_of_matches
#print axioms additionProgram_separated
#print axioms firstOrSecond_overlaps
#print axioms specialForms_examples

end Mettapedia.Logic.HostingStyles.StoredPrograms
