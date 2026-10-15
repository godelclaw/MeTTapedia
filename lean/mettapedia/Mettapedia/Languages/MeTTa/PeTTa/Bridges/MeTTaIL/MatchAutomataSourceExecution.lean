import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataProgram
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtom
import Mettapedia.GSLT.LanguageDef.TopDownMatchDerivatives
import Mettapedia.GSLT.LanguageDef.CettaWireEquality

/-!
# Executing the retained matching source in the PeTTa judgment

Named equation lookup ties each proof to the quoted program, independent of
physical equation offsets. Pure source execution laws compose recursive
calls, source cases and data construction. The store is arbitrary and remains
unchanged; captured wire data is never treated as code.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataSourceExecution

open Mettapedia.GSLT.LanguageDef.CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst applySubst_nil matchAtom)
open Effects (State)
open Eval MatchAutomataProgram

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name

abbrev listValue (values : List Term) : Atom := CettaWireAtom.encode (encodeList id values)

private def appendEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:append")[0]'(by decide +kernel)

private theorem append_unique : equations "gslt:automata:append" = [appendEquation] := by rfl

private def appendCons : Atom :=
  a "let" [v "tail", a "gslt:automata:append" [v "xs", v "right"], a "LCons" [v "x", v "tail"]]

private def appendCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", v "right"), (a "LCons" [v "x", v "xs"], appendCons)]

private theorem append_shape : appendEquation.body =
    a "case" [v "left", .expression (appendCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem append_formals : appendEquation.arguments = [v "left", v "right"] := by decide +kernel

private def appendEnv (left right : List Term) : Subst :=
  [("right", listValue right), ("left", listValue left)]

private theorem append_clause (left right : List Term) :
    clauses program "gslt:automata:append" [listValue left, listValue right] =
      [.evaluate (appendEnv left right) appendEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:append").filterMap _ = _
  rw [append_unique]
  simp [append_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, appendEnv]

private theorem append_call (bindings : Subst) (state : State) (left right : List Term)
    (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) = [listValue left, listValue right])
    (length : arguments.length = 2)
    (body : PureReturns program (appendEnv left right) state appendEquation.body state
      (listValue (left ++ right))) :
    PureReturns program bindings state (a "gslt:automata:append" arguments) state
      (listValue (left ++ right)) := by
  apply PureData.raw_authored_call_return program bindings (appendEnv left right) state state
    "gslt:automata:append" arguments appendEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ body
  · intro index bounded
    rw [length] at bounded
    have small : index = 0 ∨ index = 1 := by omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact append_clause left right

private theorem cons_template : PureData.Template program (a "LCons" [v "x", v "tail"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

theorem append_body_returns (state : State) (left right : List Term) :
    PureReturns program (appendEnv left right) state appendEquation.body state
      (listValue (left ++ right)) := by
  induction left with
  | nil =>
      rw [append_shape]
      apply case_returns program (appendEnv [] right) (appendEnv [] right) state state state
        (v "left") (listValue []) (v "right") (listValue right) _ appendCases
        (read_cases_encoded _) _ _ _
      · simpa [appendEnv, applySubst, Subst.lookup] using
          variable_returns program (appendEnv [] right) state "left"
      · simp [appendCases, listValue, encodeList, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [appendEnv, applySubst, Subst.lookup] using
          variable_returns program (appendEnv [] right) state "right"
  | cons first rest ih =>
      let bindings := appendEnv (first :: rest) right
      let selected := ("xs", listValue rest) :: ("x", CettaWireAtom.encode first) :: bindings
      rw [append_shape]
      apply case_returns program bindings selected state state state
        (v "left") (listValue (first :: rest)) appendCons (listValue ((first :: rest) ++ right))
        _ appendCases (read_cases_encoded _) _ _ _
      · simpa [bindings, appendEnv, applySubst, Subst.lookup] using
          variable_returns program bindings state "left"
      · simp [appendCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, appendEnv]
      · let bound := ("tail", listValue (rest ++ right)) :: selected
        apply let_returns program selected bound state state state (v "tail")
          (a "gslt:automata:append" [v "xs", v "right"])
          (a "LCons" [v "x", v "tail"]) (listValue (rest ++ right)) _
        · apply append_call selected state rest right _ _ rfl ih
          simp [selected, bindings, appendEnv, applySubst, Subst.lookup]
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, appendEnv, bound]
        · simpa [applySubst, applySubst.applySubstList, Subst.lookup, bound, selected,
            bindings, appendEnv, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
            using PureData.template_return program bound state _ cons_template

/-- Arbitrarily long encoded lists execute through the actual source. -/
theorem append_returns (state : State) (left right : List Term) :
    PureReturns program [] state (a "gslt:automata:append" [listValue left, listValue right]) state
      (listValue (left ++ right)) :=
  append_call [] state left right _ (by simp) rfl (append_body_returns state left right)

/-- List composition also executes when its operands are captured in a caller.
The operands remain data throughout the authored raw-argument call. -/
theorem append_captured_returns (caller : Subst) (state : State) (left right : List Term)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [listValue left, listValue right]) :
    PureReturns program caller state (a "gslt:automata:append" [one, two]) state
      (listValue (left ++ right)) :=
  append_call caller state left right [one, two] captured rfl (append_body_returns state left right)

#print axioms append_returns
#print axioms append_captured_returns

private def lengthEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:length")[0]'(by decide +kernel)

private def number (value : Nat) : Atom := CettaWireAtom.encode (.natural value)

private def lengthCons : Atom := a "+" [number 1, a "gslt:automata:length" [v "rest"]]
private def lengthCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", number 0), (a "LCons" [v "x", v "rest"], lengthCons)]

private theorem length_shape : lengthEquation.body =
    a "case" [v "xs", .expression (lengthCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def lengthEnv (values : List Term) : Subst := [("xs", listValue values)]

private theorem length_clause (values : List Term) :
    clauses program "gslt:automata:length" [listValue values] =
      [.evaluate (lengthEnv values) lengthEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:length").filterMap _ = _
  rw [show equations "gslt:automata:length" = [lengthEquation] from rfl]
  have formals : lengthEquation.arguments = [v "xs"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, lengthEnv]

private theorem length_call (bindings : Subst) (state : State) (values : List Term) (argument : Atom)
    (captured : applySubst bindings argument = listValue values)
    (body : PureReturns program (lengthEnv values) state lengthEquation.body state (number values.length)) :
    PureReturns program bindings state (a "gslt:automata:length" [argument]) state (number values.length) := by
  apply PureData.raw_authored_call_return program bindings (lengthEnv values) state state
    "gslt:automata:length" [argument] lengthEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ body
  · intro index bounded
    have zero : index = 0 := by simp only [List.length_singleton] at bounded; omega
    subst index
    decide +kernel
  · simpa [captured] using length_clause values

theorem length_body_returns (state : State) (values : List Term) :
    PureReturns program (lengthEnv values) state lengthEquation.body state (number values.length) := by
  induction values with
  | nil =>
      rw [length_shape]
      apply case_returns program (lengthEnv []) (lengthEnv []) state state state (v "xs")
        (listValue []) (number 0) (number 0) _ lengthCases (read_cases_encoded _) _ _ _
      · simpa [lengthEnv, applySubst, Subst.lookup] using variable_returns program (lengthEnv []) state "xs"
      · simp [lengthCases, listValue, encodeList, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program (lengthEnv []) state (.int 0)
  | cons first rest ih =>
      let bindings := lengthEnv (first :: rest)
      let selected := ("rest", listValue rest) :: ("x", CettaWireAtom.encode first) :: bindings
      rw [length_shape]
      apply case_returns program bindings selected state state state (v "xs")
        (listValue (first :: rest)) lengthCons (number (rest.length + 1))
        _ lengthCases (read_cases_encoded _) _ _ _
      · simpa [bindings, lengthEnv, applySubst, Subst.lookup] using variable_returns program bindings state "xs"
      · simp [lengthCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, lengthEnv]
      · apply native_binary_call_returns program selected state state state state "+"
          (number 1) (a "gslt:automata:length" [v "rest"])
          (number 1) (number rest.length) (number (rest.length + 1))
          (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
        · exact grounded_returns program selected state (.int 1)
        · apply length_call selected state rest (v "rest") _ ih
          simp [selected, applySubst, Subst.lookup]
        · simpa only [number, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one, Int.add_comm]
            using StdLib.integer_addition state 1 (rest.length : Int)

theorem length_returns (state : State) (values : List Term) :
    PureReturns program [] state (a "gslt:automata:length" [listValue values]) state (number values.length) :=
  length_call [] state values _ (by simp) (length_body_returns state values)

/-- Length calls compose inside arbitrary lexical environments. Captured
list elements remain opaque values. -/
theorem length_captured_returns (bindings : Subst) (state : State) (values : List Term)
    (argument : Atom) (captured : applySubst bindings argument = listValue values) :
    PureReturns program bindings state (a "gslt:automata:length" [argument]) state
      (CettaWireAtom.encode (.natural values.length)) :=
  length_call bindings state values argument captured (length_body_returns state values)

private def memberEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:member")[0]'(by decide +kernel)

private def memberCons : Atom :=
  a "if" [a "==" [v "x", v "y"], Effects.boolean true, a "gslt:automata:member" [v "x", v "rest"]]
private def memberCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean false), (a "LCons" [v "y", v "rest"], memberCons)]

private theorem member_shape : memberEquation.body =
    a "case" [v "xs", .expression (memberCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def memberEnv (value : Term) (values : List Term) : Subst :=
  [("xs", listValue values), ("x", CettaWireAtom.encode value)]

private theorem member_clause (value : Term) (values : List Term) :
    clauses program "gslt:automata:member" [CettaWireAtom.encode value, listValue values] =
      [.evaluate (memberEnv value values) memberEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:member").filterMap _ = _
  rw [show equations "gslt:automata:member" = [memberEquation] from rfl]
  have formals : memberEquation.arguments = [v "x", v "xs"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, memberEnv]

private theorem member_call (bindings : Subst) (state : State) (value : Term) (values : List Term)
    (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) = [CettaWireAtom.encode value, listValue values])
    (length : arguments.length = 2)
    (body : PureReturns program (memberEnv value values) state memberEquation.body state
      (Effects.boolean (decide (value ∈ values)))) :
    PureReturns program bindings state (a "gslt:automata:member" arguments) state
      (Effects.boolean (decide (value ∈ values))) := by
  apply PureData.raw_authored_call_return program bindings (memberEnv value values) state state
    "gslt:automata:member" arguments memberEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ body
  · intro index bounded
    rw [length] at bounded
    have small : index = 0 ∨ index = 1 := by omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact member_clause value values

theorem member_body_returns (state : State) (value : Term) (values : List Term) :
    PureReturns program (memberEnv value values) state memberEquation.body state
      (Effects.boolean (decide (value ∈ values))) := by
  induction values with
  | nil =>
      rw [member_shape]
      apply case_returns program (memberEnv value []) (memberEnv value []) state state state
        (v "xs") (listValue []) (Effects.boolean false) (Effects.boolean false)
        _ memberCases (read_cases_encoded _) _ _ _
      · simpa [memberEnv, applySubst, Subst.lookup] using
          variable_returns program (memberEnv value []) state "xs"
      · simp [memberCases, listValue, encodeList, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program (memberEnv value []) state (.bool false)
  | cons first rest ih =>
      let bindings := memberEnv value (first :: rest)
      let selected := ("rest", listValue rest) :: ("y", CettaWireAtom.encode first) :: bindings
      rw [member_shape]
      apply case_returns program bindings selected state state state (v "xs")
        (listValue (first :: rest)) memberCons (Effects.boolean (decide (value ∈ first :: rest)))
        _ memberCases (read_cases_encoded _) _ _ _
      · simpa [bindings, memberEnv, applySubst, Subst.lookup] using variable_returns program bindings state "xs"
      · simp [memberCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, memberEnv]
      · have tested : PureReturns program selected state (a "==" [v "x", v "y"]) state
            (Effects.boolean (decide (value = first))) := by
          have comparison : (CettaWireAtom.encode value == CettaWireAtom.encode first) =
              decide (value = first) := by
            apply Bool.eq_iff_iff.mpr
            simp [CettaWireAtom.encode_eq_encode]
          apply native_variable_call_returns program selected state state "==" ["x", "y"] _
            (by decide) (by decide) _ (by decide)
          simp [selected, bindings, memberEnv, applySubst, Subst.lookup,
            StdLib.structural_equality, comparison]
        apply if_returns program selected state state state _ _ _ _ _ tested
        by_cases same : value = first
        · simpa [Effects.boolean, same, List.mem_cons] using
            grounded_returns program selected state (.bool true)
        · have recursive := member_call selected state value rest [v "x", v "rest"]
            (by simp [selected, bindings, memberEnv, applySubst, Subst.lookup]) rfl ih
          simpa [Effects.boolean, same, List.mem_cons] using recursive

/-- Equality-based membership refuses unequal repeated payloads, regardless
of their internal expression shape. -/
theorem member_returns (state : State) (value : Term) (values : List Term) :
    PureReturns program [] state (a "gslt:automata:member" [CettaWireAtom.encode value, listValue values]) state
      (Effects.boolean (decide (value ∈ values))) :=
  member_call [] state value values _ (by simp) rfl (member_body_returns state value values)

#print axioms length_returns
#print axioms member_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataSourceExecution
