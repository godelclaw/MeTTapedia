import Mettapedia.Languages.HOLLight.MeTTa.TypeVariables

/-!
# Actual native-list conversion and type-parameter sorting

The authored checker converts its tagged parameter list to a native list,
calls the closed string-list sorting primitive, and converts the result back.
The primitive preserves occurrences; distinctness comes from the variable
collector, not from sorting. A primitive call does not assert bounded work.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.NameSorting

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval (clauses clauses_use_only_the_named_equations read_cases_encoded)
open Effects (State)

namespace NativeList

private def equation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:native-list"))[0]'(by decide)
private def consBody : Atom := .expression [.symbol "cons-atom", .var "first",
  .expression [.symbol "hol-light:native-list", .var "rest"]]
private def cases : SpaceSemantics.Cases :=
  [(.symbol "HOL:Nil", .expression []),
   (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], consBody),
   (.var "malformed", .expression [])]
private def environment (items : List Atom) : Subst := [("items", Premises.keys items)]
private def consEnvironment (first : Atom) (rest : List Atom) : Subst :=
  [("rest", Premises.keys rest), ("first", first)] ++ environment (first :: rest)
private theorem shape : equation.body = .expression [.symbol "case", .var "items",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (items : List Atom) :
    clauses program "hol-light:native-list" [Premises.keys items] = [.evaluate (environment items) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:native-list") = [equation] := rfl
  rw [unique]
  have formals : equation.arguments = [.var "items"] := by decide
  simp [List.filterMap, formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (items : List Atom) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment items) state equation.body state (.expression items) := by
  induction items with
  | nil =>
      rw [shape]
      apply BoundCalls.CorePath.case_returns program (environment []) (environment []) state state state
        (.var "items") (.symbol "HOL:Nil") (.expression []) _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "items"
      · simp [cases, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact .step rfl (Eval.step_transition rfl)
          (BoundCalls.CorePath.data_arguments_values_return program (environment []) state [] 0)
  | cons first rest ih =>
      rw [shape]
      apply BoundCalls.CorePath.case_returns program (environment (first :: rest)) (consEnvironment first rest)
        state state state (.var "items") (Premises.keys (first :: rest)) consBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "items"
      · simp [cases, consEnvironment, environment, Premises.keys, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        apply BoundCalls.CorePath.native_binary_call_returns program (consEnvironment first rest)
          state state state state "cons-atom" (.var "first") (.expression [.symbol "hol-light:native-list", .var "rest"])
          first (.expression rest) (.expression (first :: rest)) (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
        · simpa [consEnvironment, applySubst, Subst.lookup] using
            BoundCalls.CorePath.variable_returns program (consEnvironment first rest) state "first"
        · apply BoundCalls.CorePath.authored_variable_call_returns program (consEnvironment first rest)
            (environment rest) state state "hol-light:native-list" ["rest"] equation.body _
            (by decide) (by decide) (by decide) _ ih (by decide)
          simpa [consEnvironment, applySubst, Subst.lookup] using clause rest
        · exact StdLib.native_cons state first rest

theorem authored_certificate (bindings : Subst) (state : State) (items : List Atom)
    (expression : Atom) (returned : BoundCalls.CorePath.PureReturns program bindings state expression state (Premises.keys items)) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:native-list", expression]) state (.expression items) :=
  BoundCalls.CorePath.authored_unary_call_returns program bindings (environment items) state state state
    "hol-light:native-list" expression (Premises.keys items) equation.body (.expression items)
    (by decide) (by decide) (by decide) (by decide) returned (clause items) (body_returns items state) (by decide)

end NativeList

namespace TaggedList

private def equation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:tagged-list"))[0]'(by decide)
private def consBody : Atom := .expression [.symbol "HOL:Cons", .var "first",
  .expression [.symbol "hol-light:tagged-list", .var "rest"]]
private def cases : SpaceSemantics.Cases :=
  [(.expression [], .symbol "HOL:Nil"),
   (.expression [.symbol "cons", .var "first", .var "rest"], consBody),
   (.var "malformed", .symbol "None")]
private def environment (items : List Atom) : Subst := [("items", .expression items)]
private def consEnvironment (first : Atom) (rest : List Atom) : Subst :=
  [("rest", .expression rest), ("first", first)] ++ environment (first :: rest)
private theorem shape : equation.body = .expression [.symbol "case", .var "items",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (items : List Atom) :
    clauses program "hol-light:tagged-list" [.expression items] = [.evaluate (environment items) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:tagged-list") = [equation] := rfl
  rw [unique]
  have formals : equation.arguments = [.var "items"] := by decide
  simp [List.filterMap, formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (items : List Atom) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment items) state equation.body state (Premises.keys items) := by
  induction items with
  | nil =>
      rw [shape]
      apply BoundCalls.CorePath.case_returns program (environment []) (environment []) state state state
        (.var "items") (.expression []) (.symbol "HOL:Nil") _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "items"
      · simp [cases, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues]
      · exact BoundCalls.CorePath.symbol_returns program _ state "HOL:Nil"
  | cons first rest ih =>
      rw [shape]
      apply BoundCalls.CorePath.case_returns program (environment (first :: rest)) (consEnvironment first rest)
        state state state (.var "items") (.expression (first :: rest)) consBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "items"
      · simp [cases, consEnvironment, environment, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        apply BoundCalls.CorePath.binary_constructor_returns program (consEnvironment first rest) state state state
          "HOL:Cons" (.var "first") (.expression [.symbol "hol-light:tagged-list", .var "rest"])
          first (Premises.keys rest) (by decide) (by decide)
        · simpa [consEnvironment, applySubst, Subst.lookup] using
            BoundCalls.CorePath.variable_returns program (consEnvironment first rest) state "first"
        · apply BoundCalls.CorePath.authored_variable_call_returns program (consEnvironment first rest)
            (environment rest) state state "hol-light:tagged-list" ["rest"] equation.body _
            (by decide) (by decide) (by decide) _ ih (by decide)
          simpa [consEnvironment, applySubst, Subst.lookup] using clause rest

theorem authored_certificate (bindings : Subst) (state : State) (items : List Atom)
    (expression : Atom) (returned : BoundCalls.CorePath.PureReturns program bindings state expression state (.expression items)) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:tagged-list", expression]) state (Premises.keys items) :=
  BoundCalls.CorePath.authored_unary_call_returns program bindings (environment items) state state state
    "hol-light:tagged-list" expression (.expression items) equation.body (Premises.keys items)
    (by decide) (by decide) (by decide) (by decide) returned (clause items) (body_returns items state) (by decide)

end TaggedList

def sorted (items : List String) : List String := items.mergeSort (· ≤ ·)

theorem sorted_permutation (items : List String) : (sorted items).Perm items := List.mergeSort_perm _ _

theorem sorted_nodup (items : List String) (distinct : items.Nodup) : (sorted items).Nodup :=
  (sorted_permutation items).nodup_iff.mpr distinct

theorem sorted_support (items : List String) : (sorted items).toFinset = items.toFinset := by
  ext name
  simp only [List.mem_toFinset, (sorted_permutation items).mem_iff]

private def sortingEquation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:sorted-names"))[0]'(by decide)
private def sortingEnvironment (items : List String) : Subst := [("items", Premises.keys (StdLib.stringAtoms items))]
private theorem sorting_clause (items : List String) :
    clauses program "hol-light:sorted-names" [Premises.keys (StdLib.stringAtoms items)] =
      [.evaluate (sortingEnvironment items) sortingEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:sorted-names") = [sortingEquation] := rfl
  rw [unique]
  have formals : sortingEquation.arguments = [.var "items"] := by decide
  simp [List.filterMap, formals, sortingEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

theorem authored_sorted_certificate (bindings : Subst) (state : State) (items : List String)
    (expression : Atom)
    (returned : BoundCalls.CorePath.PureReturns program bindings state expression state (Premises.keys (StdLib.stringAtoms items))) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:sorted-names", expression]) state (Premises.keys (StdLib.stringAtoms (sorted items))) := by
  apply BoundCalls.CorePath.authored_unary_call_returns program bindings (sortingEnvironment items) state state state
    "hol-light:sorted-names" expression (Premises.keys (StdLib.stringAtoms items)) sortingEquation.body _
    (by decide) (by decide) (by decide) (by decide) returned (sorting_clause items) _ (by decide)
  have shape : sortingEquation.body = .expression [.symbol "hol-light:tagged-list",
      .expression [.symbol "sort-atom", .expression [.symbol "hol-light:native-list", .var "items"]]] := by decide
  rw [shape]
  apply TaggedList.authored_certificate
  apply BoundCalls.CorePath.native_unary_call_returns program (sortingEnvironment items) state state state "sort-atom"
    _ (.expression (StdLib.stringAtoms items)) _ (by decide) (by decide) (by decide) _ _ (by decide)
  · apply NativeList.authored_certificate
    exact BoundCalls.CorePath.variable_returns program (sortingEnvironment items) state "items"
  · exact StdLib.string_list_sort state items

theorem duplicates_retained : (sorted ["B", "A", "A"]).count "A" = 2 := by
  rw [(sorted_permutation ["B", "A", "A"]).count_eq]
  rfl

theorem empty_sorted : sorted [] = [] := by simp [sorted]

end Mettapedia.Languages.HOLLight.MeTTa.NameSorting
