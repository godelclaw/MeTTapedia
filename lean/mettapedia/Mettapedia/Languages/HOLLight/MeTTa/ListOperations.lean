import Mettapedia.Languages.HOLLight.MeTTa.Lookup

/-!
# Finite data lists executed by the authored HOL library

The proofs concern the actual retained MeTTa equations. Validity, length,
membership, insertion, union, removal, subset and append agree with existing
finite-list operations. Their exact order and multiplicity are retained.
These laws supply the data boundary used by declaration and hypothesis checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.ListOperations

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)

namespace Validity

private def equation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:list-valid"))[0]'(by decide)

private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def environment (items : List Atom) : Subst := [("items", Premises.keys items)]
private def consEnvironment (first : Atom) (rest : List Atom) : Subst :=
  [("rest", Premises.keys rest), ("first", first)] ++ environment (first :: rest)

private theorem unique :
    program.equations.filter (fun row => row.head == "hol-light:list-valid") = [equation] := by rfl
private theorem formals : equation.arguments = [.var "items"] := by decide
private theorem body_shape : equation.body = .expression [.symbol "case", .var "items",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.symbol "HOL:Nil", boolean true),
     (.expression [.symbol "HOL:Cons", .var "first", .var "rest"],
       .expression [.symbol "hol-light:list-valid", .var "rest"]),
     (.var "malformed", boolean false)] := by decide

private theorem clause (items : List Atom) :
    clauses program "hol-light:list-valid" [Premises.keys items] =
      [.evaluate (environment items) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (items : List Atom) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment items) state equation.body state (boolean true) := by
  induction items with
  | nil =>
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment []) (environment []) state state state
        (.var "items") (.symbol "HOL:Nil") (boolean true) _ _ cases (read_cases_encoded cases)
      · simpa [environment, Premises.keys, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program (environment []) state "items"
      · simp [cases_shape, environment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact BoundCalls.CorePath.grounded_returns program _ state _
  | cons first rest ih =>
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment (first :: rest)) (consEnvironment first rest) state state state
        (.var "items") (Premises.keys (first :: rest))
        (.expression [.symbol "hol-light:list-valid", .var "rest"]) _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "items"
      · simp [cases_shape, environment, consEnvironment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · apply BoundCalls.CorePath.authored_variable_call_returns program (consEnvironment first rest) (environment rest)
          state state "hol-light:list-valid" ["rest"] equation.body _
          (by decide) (by decide) (by decide) _ ih (by decide)
        simpa [consEnvironment, environment, applySubst, Subst.lookup] using clause rest

theorem authored_list_valid_certificate (bindings : Subst) (state : State) (items : List Atom)
    (itemsKey : String) (captured : applySubst bindings (.var itemsKey) = Premises.keys items) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:list-valid", .var itemsKey]) state
      (boolean true) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment items) state state
    "hol-light:list-valid" [itemsKey] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns items state) (by decide)
  simpa only [List.map_cons, List.map_nil, captured] using clause items


theorem authored_list_valid_return (bindings : Subst) (state : State) (items : List Atom)
    (itemsKey : String) (captured : applySubst bindings (.var itemsKey) = Premises.keys items) :
    PureReturns program bindings state (.expression [.symbol "hol-light:list-valid", .var itemsKey]) state
      (boolean true) :=
  (authored_list_valid_certificate bindings state items itemsKey captured).original

theorem authored_list_valid_bound_return (bindings : Subst) (state : State) (items : List Atom)
    (itemsKey : String) (captured : applySubst bindings (.var itemsKey) = Premises.keys items) :
    BoundCalls.PureReturns program bindings state (.expression [.symbol "hol-light:list-valid", .var itemsKey]) state
      (boolean true) :=
  (authored_list_valid_certificate bindings state items itemsKey captured).extended

end Validity

namespace Length

private def equation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:length"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def consBody : Atom := .expression [.symbol "+", .grounded (.int 1),
  .expression [.symbol "hol-light:length", .var "rest"]]
private def environment (items : List Atom) : Subst := [("items", Premises.keys items)]
private def consEnvironment (first : Atom) (rest : List Atom) : Subst :=
  [("rest", Premises.keys rest), ("first", first)] ++ environment (first :: rest)

private theorem unique :
    program.equations.filter (fun row => row.head == "hol-light:length") = [equation] := by rfl
private theorem formals : equation.arguments = [.var "items"] := by decide
private theorem body_shape : equation.body = .expression [.symbol "case", .var "items",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.symbol "HOL:Nil", .grounded (.int 0)),
     (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], consBody),
     (.var "malformed", .grounded (.int (-1)))] := by decide

private theorem clause (items : List Atom) :
    clauses program "hol-light:length" [Premises.keys items] =
      [.evaluate (environment items) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (items : List Atom) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment items) state equation.body state (.grounded (.int items.length)) := by
  induction items with
  | nil =>
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment []) (environment []) state state state
        (.var "items") (.symbol "HOL:Nil") (.grounded (.int 0)) _ _ cases (read_cases_encoded cases)
      · simpa [environment, Premises.keys, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program (environment []) state "items"
      · simp [cases_shape, environment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact BoundCalls.CorePath.grounded_returns program _ state _
  | cons first rest ih =>
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment (first :: rest)) (consEnvironment first rest) state state state
        (.var "items") (Premises.keys (first :: rest)) consBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "items"
      · simp [cases_shape, environment, consEnvironment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        apply BoundCalls.CorePath.native_binary_call_returns program (consEnvironment first rest) state state state state "+"
          (.grounded (.int 1)) (.expression [.symbol "hol-light:length", .var "rest"])
          (.grounded (.int 1)) (.grounded (.int rest.length)) (.grounded (.int (first :: rest).length))
          (by decide) (by decide) (by decide) (by decide) (BoundCalls.CorePath.grounded_returns program _ state _) _ _ (by decide)
        · apply BoundCalls.CorePath.authored_variable_call_returns program (consEnvironment first rest) (environment rest)
            state state "hol-light:length" ["rest"] equation.body _
            (by decide) (by decide) (by decide) _ ih (by decide)
          simpa [consEnvironment, environment, applySubst, Subst.lookup] using clause rest
        · simp [StdLib.integer_addition, Int.add_comm]

theorem authored_length_certificate (bindings : Subst) (state : State) (items : List Atom)
    (itemsKey : String) (captured : applySubst bindings (.var itemsKey) = Premises.keys items) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:length", .var itemsKey]) state
      (.grounded (.int items.length)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment items) state state
    "hol-light:length" [itemsKey] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns items state) (by decide)
  simpa only [List.map_cons, List.map_nil, captured] using clause items


theorem authored_length_return (bindings : Subst) (state : State) (items : List Atom)
    (itemsKey : String) (captured : applySubst bindings (.var itemsKey) = Premises.keys items) :
    PureReturns program bindings state (.expression [.symbol "hol-light:length", .var itemsKey]) state
      (.grounded (.int items.length)) :=
  (authored_length_certificate bindings state items itemsKey captured).original

theorem authored_length_bound_return (bindings : Subst) (state : State) (items : List Atom)
    (itemsKey : String) (captured : applySubst bindings (.var itemsKey) = Premises.keys items) :
    BoundCalls.PureReturns program bindings state (.expression [.symbol "hol-light:length", .var itemsKey]) state
      (.grounded (.int items.length)) :=
  (authored_length_certificate bindings state items itemsKey captured).extended

end Length

namespace Membership

private def equation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:member"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def consBody : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .var "item", .var "first"], boolean true,
  .expression [.symbol "hol-light:member", .var "item", .var "rest"]]
private def environment (item : Atom) (items : List Atom) : Subst :=
  [("items", Premises.keys items), ("item", item)]
private def consEnvironment (item first : Atom) (rest : List Atom) : Subst :=
  [("rest", Premises.keys rest), ("first", first)] ++ environment item (first :: rest)

private theorem unique :
    program.equations.filter (fun row => row.head == "hol-light:member") = [equation] := by rfl
private theorem formals : equation.arguments = [.var "item", .var "items"] := by decide
private theorem body_shape : equation.body = .expression [.symbol "case", .var "items",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.symbol "HOL:Nil", boolean false),
     (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], consBody),
     (.var "malformed", boolean false)] := by decide

private theorem clause (item : Atom) (items : List Atom) :
    clauses program "hol-light:member" [item, Premises.keys items] =
      [.evaluate (environment item items) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (item : Atom) (items : List Atom) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment item items) state equation.body state (boolean (decide (item ∈ items))) := by
  induction items with
  | nil =>
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment item []) (environment item []) state state state
        (.var "items") (.symbol "HOL:Nil") (boolean false) _ _ cases (read_cases_encoded cases)
      · simpa [environment, Premises.keys, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program (environment item []) state "items"
      · simp [cases_shape, environment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact BoundCalls.CorePath.grounded_returns program _ state _
  | cons first rest ih =>
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment item (first :: rest)) (consEnvironment item first rest) state state state
        (.var "items") (Premises.keys (first :: rest)) consBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "items"
      · simp [cases_shape, environment, consEnvironment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        apply BoundCalls.CorePath.if_returns program (consEnvironment item first rest) state state state _
          (boolean (decide (item = first))) _ _ _
        · apply BoundCalls.CorePath.native_variable_call_returns program (consEnvironment item first rest) state state "=="
            ["item", "first"] _ (by decide) (by decide) _ (by decide)
          simp [StdLib.structural_equality, consEnvironment, environment, applySubst, Subst.lookup, beq_eq_decide]
        · by_cases same : item = first
          · simp only [same, decide_true, boolean, BEq.rfl, ↓reduceIte]
            simpa using BoundCalls.CorePath.grounded_returns program (consEnvironment first first rest) state (.bool true)
          · simp only [same, decide_false, boolean]
            apply BoundCalls.CorePath.authored_variable_call_returns program (consEnvironment item first rest) (environment item rest)
              state state "hol-light:member" ["item", "rest"] equation.body _
              (by decide) (by decide) (by decide) _ _ (by decide)
            · simpa [consEnvironment, environment, applySubst, Subst.lookup] using clause item rest
            · simpa [same, boolean] using ih

theorem authored_member_certificate (bindings : Subst) (state : State) (item : Atom) (items : List Atom)
    (itemKey itemsKey : String) (capturedItem : applySubst bindings (.var itemKey) = item)
    (capturedItems : applySubst bindings (.var itemsKey) = Premises.keys items) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:member", .var itemKey, .var itemsKey]) state (boolean (decide (item ∈ items))) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment item items) state state
    "hol-light:member" [itemKey, itemsKey] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns item items state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedItem, capturedItems] using clause item items

theorem authored_member_return (bindings : Subst) (state : State) (item : Atom) (items : List Atom)
    (itemKey itemsKey : String) (capturedItem : applySubst bindings (.var itemKey) = item)
    (capturedItems : applySubst bindings (.var itemsKey) = Premises.keys items) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:member", .var itemKey, .var itemsKey]) state (boolean (decide (item ∈ items))) :=
  (authored_member_certificate bindings state item items itemKey itemsKey capturedItem capturedItems).original

/-- Computed lists use the same first-order membership operation and exact
observation as captured lists. Both argument occurrences are evaluated. -/
theorem authored_member_computed_certificate (bindings : Subst) (state : State)
    (item : Atom) (items : List Atom) (itemExpression itemsExpression : Atom)
    (itemReturned : BoundCalls.CorePath.PureReturns program bindings state itemExpression state item)
    (itemsReturned : BoundCalls.CorePath.PureReturns program bindings state itemsExpression state (Premises.keys items)) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:member", itemExpression, itemsExpression]) state
      (boolean (decide (item ∈ items))) :=
  BoundCalls.CorePath.authored_binary_call_returns program bindings (environment item items) state state state state
    "hol-light:member" itemExpression itemsExpression item (Premises.keys items) equation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide)
    itemReturned itemsReturned (clause item items) (body_returns item items state) (by decide)

theorem authored_member_computed_return (bindings : Subst) (state : State)
    (item : Atom) (items : List Atom) (itemExpression itemsExpression : Atom)
    (itemReturned : PureReturns program bindings state itemExpression state item)
    (itemsReturned : PureReturns program bindings state itemsExpression state (Premises.keys items)) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:member", itemExpression, itemsExpression]) state
      (boolean (decide (item ∈ items))) :=
  authored_binary_call_returns program bindings (environment item items) state state state state
    "hol-light:member" itemExpression itemsExpression item (Premises.keys items) equation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide)
    itemReturned itemsReturned (clause item items) (body_returns item items state).original (by decide)

end Membership

namespace Insertion

private def equation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:insert"))[0]'(by decide)
private def environment (item : Atom) (items : List Atom) : Subst :=
  [("items", Premises.keys items), ("item", item)]
private theorem unique :
    program.equations.filter (fun row => row.head == "hol-light:insert") = [equation] := by rfl
private theorem formals : equation.arguments = [.var "item", .var "items"] := by decide
private theorem body_shape : equation.body = .expression [.symbol "if",
    .expression [.symbol "hol-light:member", .var "item", .var "items"], .var "items",
    .expression [.symbol "HOL:Cons", .var "item", .var "items"]] := by decide

private theorem clause (item : Atom) (items : List Atom) :
    clauses program "hol-light:insert" [item, Premises.keys items] =
      [.evaluate (environment item items) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (item : Atom) (items : List Atom) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment item items) state equation.body state
      (Premises.keys (if item ∈ items then items else item :: items)) := by
  rw [body_shape]
  apply BoundCalls.CorePath.if_returns program (environment item items) state state state _
    (boolean (decide (item ∈ items))) _ _ _
  · exact Membership.authored_member_certificate (environment item items) state item items "item" "items"
      (by simp [environment, applySubst, Subst.lookup])
      (by simp [environment, applySubst, Subst.lookup])
  · by_cases member : item ∈ items
    · simp only [member, decide_true, boolean, BEq.rfl, ↓reduceIte]
      exact BoundCalls.CorePath.variable_returns program _ state "items"
    · simp only [member, decide_false, boolean]
      simpa [Premises.keys, environment, applySubst, Subst.lookup] using
        BoundCalls.CorePath.constructor_variables_return program (environment item items) state "HOL:Cons"
          ["item", "items"] (by decide) (by decide)

theorem authored_insert_certificate (bindings : Subst) (state : State) (item : Atom) (items : List Atom)
    (itemKey itemsKey : String) (capturedItem : applySubst bindings (.var itemKey) = item)
    (capturedItems : applySubst bindings (.var itemsKey) = Premises.keys items) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:insert", .var itemKey, .var itemsKey]) state
      (Premises.keys (if item ∈ items then items else item :: items)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment item items) state state
    "hol-light:insert" [itemKey, itemsKey] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns item items state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedItem, capturedItems] using clause item items

theorem authored_insert_return (bindings : Subst) (state : State) (item : Atom) (items : List Atom)
    (itemKey itemsKey : String) (capturedItem : applySubst bindings (.var itemKey) = item)
    (capturedItems : applySubst bindings (.var itemsKey) = Premises.keys items) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:insert", .var itemKey, .var itemsKey]) state
      (Premises.keys (if item ∈ items then items else item :: items)) :=
  (authored_insert_certificate bindings state item items itemKey itemsKey capturedItem capturedItems).original

/-- Insertion evaluates both computed occurrences before comparing their
results. This supports the authored hypothesis-image traversals without
replacing their execution by a host list operation. -/
theorem authored_insert_computed_certificate (bindings : Subst) (state : State)
    (item : Atom) (items : List Atom) (itemExpression itemsExpression : Atom)
    (itemReturned : BoundCalls.CorePath.PureReturns program bindings state itemExpression state item)
    (itemsReturned : BoundCalls.CorePath.PureReturns program bindings state itemsExpression state (Premises.keys items)) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:insert", itemExpression, itemsExpression]) state
      (Premises.keys (if item ∈ items then items else item :: items)) :=
  BoundCalls.CorePath.authored_binary_call_returns program bindings (environment item items)
    state state state state "hol-light:insert" itemExpression itemsExpression item (Premises.keys items)
    equation.body _ (by decide) (by decide) (by decide) (by decide) (by decide)
    itemReturned itemsReturned (clause item items) (body_returns item items state) (by decide)

theorem authored_insert_computed_return (bindings : Subst) (state : State)
    (item : Atom) (items : List Atom) (itemExpression itemsExpression : Atom)
    (itemReturned : PureReturns program bindings state itemExpression state item)
    (itemsReturned : PureReturns program bindings state itemsExpression state (Premises.keys items)) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:insert", itemExpression, itemsExpression]) state
      (Premises.keys (if item ∈ items then items else item :: items)) :=
  authored_binary_call_returns program bindings (environment item items)
    state state state state "hol-light:insert" itemExpression itemsExpression item (Premises.keys items)
    equation.body _ (by decide) (by decide) (by decide) (by decide) (by decide)
    itemReturned itemsReturned (clause item items) (body_returns item items state).original (by decide)

end Insertion

namespace Union

private def equation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:union"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def consBody : Atom := .expression [.symbol "hol-light:union", .var "rest",
  .expression [.symbol "hol-light:insert", .var "first", .var "right"]]
private def environment (left right : List Atom) : Subst :=
  [("right", Premises.keys right), ("left", Premises.keys left)]
private def consEnvironment (first : Atom) (rest right : List Atom) : Subst :=
  [("rest", Premises.keys rest), ("first", first)] ++ environment (first :: rest) right

private theorem unique :
    program.equations.filter (fun row => row.head == "hol-light:union") = [equation] := by rfl
private theorem formals : equation.arguments = [.var "left", .var "right"] := by decide
private theorem body_shape : equation.body = .expression [.symbol "case", .var "left",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.symbol "HOL:Nil", .var "right"),
     (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], consBody),
     (.var "malformed", .symbol "None")] := by decide

private theorem clause (left right : List Atom) :
    clauses program "hol-light:union" [Premises.keys left, Premises.keys right] =
      [.evaluate (environment left right) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (left right : List Atom) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment left right) state equation.body state
      (Premises.keys (left.foldl (fun items item => if item ∈ items then items else item :: items) right)) := by
  induction left generalizing right with
  | nil =>
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment [] right) (environment [] right) state state state
        (.var "left") (.symbol "HOL:Nil") (.var "right") _ _ cases (read_cases_encoded cases)
      · simpa [environment, Premises.keys, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program (environment [] right) state "left"
      · simp [cases_shape, environment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact BoundCalls.CorePath.variable_returns program _ state "right"
  | cons first rest ih =>
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment (first :: rest) right) (consEnvironment first rest right) state state state
        (.var "left") (Premises.keys (first :: rest)) consBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "left"
      · simp [cases_shape, environment, consEnvironment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        simp only [List.foldl_cons]
        let next := if first ∈ right then right else first :: right
        apply BoundCalls.CorePath.authored_binary_call_returns program (consEnvironment first rest right) (environment rest next)
          state state state state "hol-light:union" (.var "rest")
          (.expression [.symbol "hol-light:insert", .var "first", .var "right"])
          (Premises.keys rest) (Premises.keys next) equation.body _
          (by decide) (by decide) (by decide) (by decide) (by decide) _ _ _ (ih next) (by decide)
        · simpa [consEnvironment, applySubst, Subst.lookup] using
            BoundCalls.CorePath.variable_returns program (consEnvironment first rest right) state "rest"
        · exact Insertion.authored_insert_certificate (consEnvironment first rest right) state first right "first" "right"
            (by simp [consEnvironment, applySubst, Subst.lookup])
            (by simp [consEnvironment, environment, applySubst, Subst.lookup])
        · exact clause rest next

theorem authored_union_certificate (bindings : Subst) (state : State) (left right : List Atom)
    (leftKey rightKey : String) (capturedLeft : applySubst bindings (.var leftKey) = Premises.keys left)
    (capturedRight : applySubst bindings (.var rightKey) = Premises.keys right) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:union", .var leftKey, .var rightKey]) state
      (Premises.keys (left.foldl (fun items item => if item ∈ items then items else item :: items) right)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment left right) state state
    "hol-light:union" [leftKey, rightKey] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns left right state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedLeft, capturedRight] using clause left right

theorem authored_union_return (bindings : Subst) (state : State) (left right : List Atom)
    (leftKey rightKey : String) (capturedLeft : applySubst bindings (.var leftKey) = Premises.keys left)
    (capturedRight : applySubst bindings (.var rightKey) = Premises.keys right) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:union", .var leftKey, .var rightKey]) state
      (Premises.keys (left.foldl (fun items item => if item ∈ items then items else item :: items) right)) :=
  (authored_union_certificate bindings state left right leftKey rightKey capturedLeft capturedRight).original

/-- Computed list arguments retain the source union's exact order. -/
theorem authored_union_computed_certificate (bindings : Subst) (state : State)
    (left right : List Atom) (leftExpression rightExpression : Atom)
    (leftReturned : BoundCalls.CorePath.PureReturns program bindings state leftExpression state (Premises.keys left))
    (rightReturned : BoundCalls.CorePath.PureReturns program bindings state rightExpression state (Premises.keys right)) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:union", leftExpression, rightExpression]) state
      (Premises.keys (left.foldl (fun items item => if item ∈ items then items else item :: items) right)) :=
  BoundCalls.CorePath.authored_binary_call_returns program bindings (environment left right) state state state state
    "hol-light:union" leftExpression rightExpression (Premises.keys left) (Premises.keys right) equation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide)
    leftReturned rightReturned (clause left right) (body_returns left right state) (by decide)

theorem authored_union_computed_return (bindings : Subst) (state : State)
    (left right : List Atom) (leftExpression rightExpression : Atom)
    (leftReturned : PureReturns program bindings state leftExpression state (Premises.keys left))
    (rightReturned : PureReturns program bindings state rightExpression state (Premises.keys right)) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:union", leftExpression, rightExpression]) state
      (Premises.keys (left.foldl (fun items item => if item ∈ items then items else item :: items) right)) :=
  authored_binary_call_returns program bindings (environment left right) state state state state
    "hol-light:union" leftExpression rightExpression (Premises.keys left) (Premises.keys right) equation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide)
    leftReturned rightReturned (clause left right) (body_returns left right state).original (by decide)

/-- Logical support is the union even though insertion retains a specific
list order. This theorem does not discard any proof receipt or execution path. -/
theorem union_support (item : Atom) (left right : List Atom) :
    item ∈ left.foldl (fun items first => if first ∈ items then items else first :: items) right ↔
      item ∈ left ∨ item ∈ right := by
  induction left generalizing right with
  | nil => simp
  | cons first rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      by_cases member : first ∈ right
      · simp only [member, ↓reduceIte, List.mem_cons]
        by_cases same : item = first
        · subst first
          simp [member]
        · simp [same]
      · simp [member]
        tauto

end Union

namespace Removal

private def equation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:remove"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def choice : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .var "item", .var "first"], .var "tail",
  .expression [.symbol "HOL:Cons", .var "first", .var "tail"]]
private def consBody : Atom := .expression [.symbol "let", .var "tail",
  .expression [.symbol "hol-light:remove", .var "item", .var "rest"], choice]
private def environment (item : Atom) (items : List Atom) : Subst :=
  [("items", Premises.keys items), ("item", item)]
private def consEnvironment (item first : Atom) (rest : List Atom) : Subst :=
  [("rest", Premises.keys rest), ("first", first)] ++ environment item (first :: rest)

private theorem unique :
    program.equations.filter (fun row => row.head == "hol-light:remove") = [equation] := by rfl
private theorem formals : equation.arguments = [.var "item", .var "items"] := by decide
private theorem body_shape : equation.body = .expression [.symbol "case", .var "items",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.symbol "HOL:Nil", .symbol "HOL:Nil"),
     (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], consBody),
     (.var "malformed", .symbol "None")] := by decide

private theorem clause (item : Atom) (items : List Atom) :
    clauses program "hol-light:remove" [item, Premises.keys items] =
      [.evaluate (environment item items) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (item : Atom) (items : List Atom) (state : State) :
    PureReturns program (environment item items) state equation.body state
      (Premises.keys (items.filter (fun entry => entry != item))) := by
  induction items with
  | nil =>
      rw [body_shape]
      apply case_returns program (environment item []) (environment item []) state state state
        (.var "items") (.symbol "HOL:Nil") (.symbol "HOL:Nil") _ _ cases (read_cases_encoded cases)
      · simpa [environment, Premises.keys, applySubst, Subst.lookup] using
          variable_returns program (environment item []) state "items"
      · simp [cases_shape, environment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program _ state "HOL:Nil"
  | cons first rest ih =>
      rw [body_shape]
      apply case_returns program (environment item (first :: rest)) (consEnvironment item first rest) state state state
        (.var "items") (Premises.keys (first :: rest)) consBody _ _ cases (read_cases_encoded cases)
      · exact variable_returns program _ state "items"
      · simp [cases_shape, environment, consEnvironment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        let withTail := ("tail", Premises.keys (rest.filter (fun entry => entry != item))) ::
          consEnvironment item first rest
        apply let_returns program (consEnvironment item first rest) withTail state state state (.var "tail")
          (.expression [.symbol "hol-light:remove", .var "item", .var "rest"]) choice
          (Premises.keys (rest.filter (fun entry => entry != item))) _ _ _ _
        · apply authored_variable_call_returns program (consEnvironment item first rest) (environment item rest)
            state state "hol-light:remove" ["item", "rest"] equation.body _
            (by decide) (by decide) (by decide) _ ih (by decide)
          simpa [consEnvironment, environment, applySubst, Subst.lookup] using clause item rest
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, withTail,
            consEnvironment, environment, matchAtom, Subst.lookup]
        · unfold choice
          apply if_returns program withTail state state state _ (boolean (decide (item = first))) _ _ _
          · apply native_variable_call_returns program withTail state state "==" ["item", "first"] _
              (by decide) (by decide) _ (by decide)
            simp [StdLib.structural_equality, withTail, consEnvironment, environment, applySubst, Subst.lookup, beq_eq_decide]
          · by_cases same : item = first
            · simp only [same, decide_true, boolean, BEq.rfl, ↓reduceIte]
              simpa [same, withTail, applySubst, Subst.lookup] using variable_returns program withTail state "tail"
            · simp only [same, decide_false, boolean]
              simpa [List.filter_cons, same, Ne.symm same, Premises.keys, withTail,
                consEnvironment, applySubst, Subst.lookup] using
                constructor_variables_return program withTail state "HOL:Cons"
                  ["first", "tail"] (by decide) (by decide)

theorem authored_remove_return (bindings : Subst) (state : State) (item : Atom) (items : List Atom)
    (itemKey itemsKey : String) (capturedItem : applySubst bindings (.var itemKey) = item)
    (capturedItems : applySubst bindings (.var itemsKey) = Premises.keys items) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:remove", .var itemKey, .var itemsKey]) state
      (Premises.keys (items.filter (fun entry => entry != item))) := by
  apply authored_variable_call_returns program bindings (environment item items) state state
    "hol-light:remove" [itemKey, itemsKey] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns item items state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedItem, capturedItems] using clause item items

/-- Discharge removes every matching hypothesis occurrence, retaining exactly
the remaining logical support. -/
theorem removal_support (removed item : Atom) (items : List Atom) :
    item ∈ items.filter (fun entry => entry != removed) ↔ item ∈ items ∧ item ≠ removed := by
  simp

end Removal

namespace Subset

private def equation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:subset"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def consBody : Atom := .expression [.symbol "if",
  .expression [.symbol "hol-light:member", .var "first", .var "right"],
  .expression [.symbol "hol-light:subset", .var "rest", .var "right"], boolean false]
private def environment (left right : List Atom) : Subst :=
  [("right", Premises.keys right), ("left", Premises.keys left)]
private def consEnvironment (first : Atom) (rest right : List Atom) : Subst :=
  [("rest", Premises.keys rest), ("first", first)] ++ environment (first :: rest) right

private theorem unique :
    program.equations.filter (fun row => row.head == "hol-light:subset") = [equation] := by rfl
private theorem formals : equation.arguments = [.var "left", .var "right"] := by decide
private theorem body_shape : equation.body = .expression [.symbol "case", .var "left",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.symbol "HOL:Nil", boolean true),
     (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], consBody),
     (.var "malformed", boolean false)] := by decide

private theorem clause (left right : List Atom) :
    clauses program "hol-light:subset" [Premises.keys left, Premises.keys right] =
      [.evaluate (environment left right) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (left right : List Atom) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment left right) state equation.body state (boolean (decide (left ⊆ right))) := by
  induction left with
  | nil =>
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment [] right) (environment [] right) state state state
        (.var "left") (.symbol "HOL:Nil") (boolean true) _ _ cases (read_cases_encoded cases)
      · simpa [environment, Premises.keys, applySubst, Subst.lookup] using
          BoundCalls.CorePath.variable_returns program (environment [] right) state "left"
      · simp [cases_shape, environment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact BoundCalls.CorePath.grounded_returns program _ state _
  | cons first rest ih =>
      rw [body_shape]
      apply BoundCalls.CorePath.case_returns program (environment (first :: rest) right) (consEnvironment first rest right) state state state
        (.var "left") (Premises.keys (first :: rest)) consBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "left"
      · simp [cases_shape, environment, consEnvironment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        apply BoundCalls.CorePath.if_returns program (consEnvironment first rest right) state state state _
          (boolean (decide (first ∈ right))) _ _ _
        · exact Membership.authored_member_certificate (consEnvironment first rest right) state first right "first" "right"
            (by simp [consEnvironment, applySubst, Subst.lookup])
            (by simp [consEnvironment, environment, applySubst, Subst.lookup])
        · by_cases member : first ∈ right
          · simp only [member, decide_true, boolean, BEq.rfl, ↓reduceIte]
            apply BoundCalls.CorePath.authored_variable_call_returns program (consEnvironment first rest right) (environment rest right)
              state state "hol-light:subset" ["rest", "right"] equation.body _
              (by decide) (by decide) (by decide) _ _ (by decide)
            · simpa [consEnvironment, environment, applySubst, Subst.lookup] using clause rest right
            · simpa [List.cons_subset, member, boolean] using ih
          · simp only [member, decide_false, boolean]
            simpa [List.cons_subset, member] using
              BoundCalls.CorePath.grounded_returns program (consEnvironment first rest right) state (.bool false)

theorem authored_subset_certificate (bindings : Subst) (state : State) (left right : List Atom)
    (leftKey rightKey : String) (capturedLeft : applySubst bindings (.var leftKey) = Premises.keys left)
    (capturedRight : applySubst bindings (.var rightKey) = Premises.keys right) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:subset", .var leftKey, .var rightKey]) state (boolean (decide (left ⊆ right))) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment left right) state state
    "hol-light:subset" [leftKey, rightKey] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns left right state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedLeft, capturedRight] using clause left right

theorem authored_subset_return (bindings : Subst) (state : State) (left right : List Atom)
    (leftKey rightKey : String) (capturedLeft : applySubst bindings (.var leftKey) = Premises.keys left)
    (capturedRight : applySubst bindings (.var rightKey) = Premises.keys right) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:subset", .var leftKey, .var rightKey]) state (boolean (decide (left ⊆ right))) :=
  (authored_subset_certificate bindings state left right leftKey rightKey capturedLeft capturedRight).original

/-- Both collectors execute before the actual inclusion helper. The returned
Boolean reflects their logical support without changing their source paths. -/
theorem authored_subset_computed_certificate (bindings : Subst) (state : State)
    (left right : List Atom) (leftExpression rightExpression : Atom)
    (leftReturned : BoundCalls.CorePath.PureReturns program bindings state leftExpression state (Premises.keys left))
    (rightReturned : BoundCalls.CorePath.PureReturns program bindings state rightExpression state (Premises.keys right)) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:subset", leftExpression, rightExpression]) state
      (boolean (decide (left ⊆ right))) :=
  BoundCalls.CorePath.authored_binary_call_returns program bindings (environment left right) state state state state
    "hol-light:subset" leftExpression rightExpression (Premises.keys left) (Premises.keys right) equation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide)
    leftReturned rightReturned (clause left right) (body_returns left right state) (by decide)

end Subset

namespace Append

private def equation : SpaceSemantics.Equation :=
  (dataSource.program.equations.filter (fun row => row.head == "hol-light:append"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def consBody : Atom := .expression [.symbol "HOL:Cons", .var "first",
  .expression [.symbol "hol-light:append", .var "rest", .var "right"]]
private def environment (left right : List Atom) : Subst :=
  [("right", Premises.keys right), ("left", Premises.keys left)]
private def consEnvironment (first : Atom) (rest right : List Atom) : Subst :=
  [("rest", Premises.keys rest), ("first", first)] ++ environment (first :: rest) right

private theorem unique :
    program.equations.filter (fun row => row.head == "hol-light:append") = [equation] := by rfl
private theorem formals : equation.arguments = [.var "left", .var "right"] := by decide
private theorem body_shape : equation.body = .expression [.symbol "case", .var "left",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases =
    [(.symbol "HOL:Nil", .var "right"),
     (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], consBody),
     (.var "malformed", .symbol "None")] := by decide

private theorem clause (left right : List Atom) :
    clauses program "hol-light:append" [Premises.keys left, Premises.keys right] =
      [.evaluate (environment left right) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (left right : List Atom) (state : State) :
    PureReturns program (environment left right) state equation.body state (Premises.keys (left ++ right)) := by
  induction left with
  | nil =>
      rw [body_shape]
      apply case_returns program (environment [] right) (environment [] right) state state state
        (.var "left") (.symbol "HOL:Nil") (.var "right") _ _ cases (read_cases_encoded cases)
      · simpa [environment, Premises.keys, applySubst, Subst.lookup] using
          variable_returns program (environment [] right) state "left"
      · simp [cases_shape, environment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact variable_returns program _ state "right"
  | cons first rest ih =>
      rw [body_shape]
      apply case_returns program (environment (first :: rest) right) (consEnvironment first rest right) state state state
        (.var "left") (Premises.keys (first :: rest)) consBody _ _ cases (read_cases_encoded cases)
      · exact variable_returns program _ state "left"
      · simp [cases_shape, environment, consEnvironment, Premises.keys,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        simp only [List.cons_append, Premises.keys]
        apply binary_constructor_returns program (consEnvironment first rest right) state state state "HOL:Cons"
          (.var "first") (.expression [.symbol "hol-light:append", .var "rest", .var "right"])
          first (Premises.keys (rest ++ right)) (by decide) (by decide)
        · simpa [consEnvironment, applySubst, Subst.lookup] using
            variable_returns program (consEnvironment first rest right) state "first"
        · apply authored_variable_call_returns program (consEnvironment first rest right) (environment rest right)
            state state "hol-light:append" ["rest", "right"] equation.body _
            (by decide) (by decide) (by decide) _ ih (by decide)
          simpa [consEnvironment, environment, applySubst, Subst.lookup] using clause rest right

theorem authored_append_return (bindings : Subst) (state : State) (left right : List Atom)
    (leftKey rightKey : String) (capturedLeft : applySubst bindings (.var leftKey) = Premises.keys left)
    (capturedRight : applySubst bindings (.var rightKey) = Premises.keys right) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:append", .var leftKey, .var rightKey]) state (Premises.keys (left ++ right)) := by
  apply authored_variable_call_returns program bindings (environment left right) state state
    "hol-light:append" [leftKey, rightKey] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns left right state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedLeft, capturedRight] using clause left right

end Append

end Mettapedia.Languages.HOLLight.MeTTa.ListOperations
