import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseEnvironmentExecution
import Mettapedia.Languages.MeTTa.PeTTa.StdLibCalls

/-!
# The lexicographic rho canonicalizer through PeTTa execution

The authored library `gslt_rho_lex_canonical.metta` computes, on wire patterns, the
lexicographic canonical form `LexCanonical.lexCanon` of closed rho processes. Its own
text is its whole runtime. The theorems below run that text in the PeTTa evaluator.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RhoLexCanonicalExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_rho_lex_canonical.metta"
    sha256 "ea89006ed07ec4d269a28232582a2637896cfec2e5437f4eb5aa257269bf6b13"

def runtime : Program := source.program

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev terms (values : List Term) : Atom := encoded (encodeList id values)

private inductive Helper where
  | nameSer | append | length | ser | serList | le | insert | sort | nonZero | contents | collapse
  | quote | canonical | canonicalList

private def Helper.head : Helper → String
  | .nameSer => "rho:lex:name-ser"
  | .append => "rho:lex:append"
  | .length => "rho:lex:length"
  | .ser => "rho:lex:ser"
  | .serList => "rho:lex:ser-list"
  | .le => "rho:lex:le"
  | .insert => "rho:lex:insert"
  | .sort => "rho:lex:sort"
  | .nonZero => "rho:lex:non-zero"
  | .contents => "rho:lex:contents"
  | .collapse => "rho:lex:collapse"
  | .quote => "rho:lex:quote"
  | .canonical => "rho:lex:canonical"
  | .canonicalList => "rho:lex:canonical-list"

private def Helper.names : Helper → List String
  | .nameSer => ["name"]
  | .append => ["left", "right"]
  | .length => ["items"]
  | .ser => ["pattern"]
  | .serList => ["patterns"]
  | .le => ["left", "right"]
  | .insert => ["pattern", "sorted"]
  | .sort => ["patterns"]
  | .nonZero => ["patterns"]
  | .contents => ["patterns"]
  | .collapse => ["patterns"]
  | .quote => ["pattern"]
  | .canonical => ["pattern"]
  | .canonicalList => ["patterns"]

private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (source.program.equations.filter (fun equation => equation.head == helper.head))[0]'(by
    cases helper <;> decide +kernel)

private def bindings (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses runtime helper.head values = [.evaluate (bindings helper values) (equation helper).body] :=
  PureData.named_equation_clause runtime helper.head (equation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> rfl) (by cases helper <;> decide) length

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw runtime helper.head index = true := by
  have checked : (List.range helper.names.length).all
      (fun index => argumentIsRaw runtime helper.head index) = true := by
    cases helper <;> decide +kernel
  exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime (bindings helper values) state (equation helper).body state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return runtime caller (bindings helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
  · cases helper <;> decide +kernel
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime [] state (a helper.head values) state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns runtime [] caller state state helper.head values arguments answer
  · cases helper <;> decide +kernel
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · cases helper <;> decide
  · have unchanged : applySubst [] = id := by
      funext value
      exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm
  · exact returned

private theorem branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns runtime caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns runtime selected state body state answer) :
    PureReturns runtime caller state
      (a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns runtime caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

private theorem named_let_returns (caller : Subst) (state : State)
    (name : String) (expression value body answer : Atom)
    (fresh : caller.lookup name = none)
    (computed : PureReturns runtime caller state expression state value)
    (continued : PureReturns runtime ((name, value) :: caller) state body state answer) :
    PureReturns runtime caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns runtime caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed
  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]
  · exact continued

private theorem template_constructor (head : String) (arguments : List Atom)
    (constructor : head ∈ ["LCons", "PApp", "PLam", "PCollection", "Var", "UnknownRhoConstructor"])
    (children : ∀ child ∈ arguments, PureData.Template runtime child) :
    PureData.Template runtime (a head arguments) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at constructor
  rcases constructor with (rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals exact PureData.Template.constructor _ _ (by decide +kernel) (by decide) children

local macro "rho_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply template_constructor _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

/-! ## Lists -/

private def appendCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", v "right"),
   (a "LCons" [v "first", v "rest"],
    a "let" [v "tail", a "rho:lex:append" [v "rest", v "right"], a "LCons" [v "first", v "tail"]])]

private theorem append_shape : (equation .append).body =
    a "case" [v "left", .expression (appendCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- List concatenation keeps every element in order. -/
theorem append_returns (state : State) (left right : List Term) :
    PureReturns runtime [] state (a "rho:lex:append" [terms left, terms right]) state (terms (left ++ right)) := by
  induction left with
  | nil =>
      let caller := bindings .append [terms [], terms right]
      apply helper_call .append [] state _ [terms [], terms right] _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [append_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") appendCases (v "right") _
      · simpa [caller, bindings, Helper.names, terms, encodeList, CettaWireAtom.encode, applySubst,
          Subst.lookup] using variable_returns runtime caller state "left"
      · simp [caller, bindings, Helper.names, appendCases, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, matchAtom]
      · simpa [caller, bindings, Helper.names, applySubst, Subst.lookup] using
          variable_returns runtime caller state "right"
  | cons first rest ih =>
      let value := terms (first :: rest)
      let caller := bindings .append [value, terms right]
      let selected := [("rest", terms rest), ("first", encoded first)] ++ caller
      let finished := ("tail", terms (rest ++ right)) :: selected
      apply helper_call .append [] state _ [value, terms right] _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
      rw [append_shape]
      apply branch_returns caller selected state _ value appendCases
        (a "let" [v "tail", a "rho:lex:append" [v "rest", v "right"], a "LCons" [v "first", v "tail"]]) _
      · exact variable_returns runtime caller state "left"
      · simp [selected, caller, value, bindings, Helper.names, appendCases, terms,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, encoded]
      · apply named_let_returns selected state "tail" _ (terms (rest ++ right))
        · simp [selected, caller, bindings, Helper.names, Subst.lookup]
        · apply helper_capture .append selected state [v "rest", v "right"] [terms rest, terms right] _ rfl
          · simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
          · exact ih
        · have template : PureData.Template runtime (a "LCons" [v "first", v "tail"]) := by rho_template
          simpa [finished, selected, caller, bindings, Helper.names, terms, encodeList, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return runtime finished state _ template

theorem append_captured_returns (caller : Subst) (state : State) (left right : List Term)
    (leftName rightName : String)
    (captured : [v leftName, v rightName].map (applySubst caller) = [terms left, terms right]) :
    PureReturns runtime caller state (a "rho:lex:append" [v leftName, v rightName]) state (terms (left ++ right)) :=
  helper_capture .append caller state _ _ _ rfl captured (append_returns state left right)

private def lengthCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", number 0),
   (a "LCons" [v "item", v "rest"],
    a "let" [v "tail", a "rho:lex:length" [v "rest"], a "+" [v "tail", number 1]])]

private theorem length_shape : (equation .length).body =
    a "case" [v "items", .expression (lengthCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem add_one_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns runtime caller state (a "+" [v name, number 1]) state (number (value + 1)) := by
  apply native_binary_call_returns runtime caller state state state state "+"
    (v name) (number 1) (number value) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns runtime caller state name
  · exact grounded_returns runtime caller state (.int 1)
  · have casts : ((value + 1 : Nat) : Int) = (value : Int) + 1 := by omega
    simpa only [number, encoded, CettaWireAtom.encode, casts, Int.natCast_one] using
      StdLib.integer_addition state (value : Int) 1

/-- The length of an encoded list. -/
theorem length_returns (state : State) (items : List Term) :
    PureReturns runtime [] state (a "rho:lex:length" [terms items]) state (number items.length) := by
  induction items with
  | nil =>
      let caller := bindings .length [terms []]
      apply helper_call .length [] state _ [terms []] _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [length_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") lengthCases (number 0) _
      · simpa [caller, bindings, Helper.names, terms, encodeList, CettaWireAtom.encode, applySubst,
          Subst.lookup] using variable_returns runtime caller state "items"
      · simp [caller, bindings, Helper.names, lengthCases, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns runtime caller state (.int 0)
  | cons item rest ih =>
      let value := terms (item :: rest)
      let caller := bindings .length [value]
      let selected := [("rest", terms rest), ("item", encoded item)] ++ caller
      apply helper_call .length [] state _ [value] _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
      rw [length_shape]
      apply branch_returns caller selected state _ value lengthCases
        (a "let" [v "tail", a "rho:lex:length" [v "rest"], a "+" [v "tail", number 1]]) _
      · exact variable_returns runtime caller state "items"
      · simp [selected, caller, value, bindings, Helper.names, lengthCases, terms,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, encoded, CettaWireAtom.encode]
      · apply named_let_returns selected state "tail" _ (number rest.length)
        · simp [selected, caller, bindings, Helper.names, Subst.lookup]
        · apply helper_capture .length selected state [v "rest"] [terms rest] _ rfl
          · simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
          · exact ih
        · simpa only [List.length_cons] using
            add_one_returns (("tail", number rest.length) :: selected) state rest.length "tail"
              (by simp [applySubst, Subst.lookup])

theorem length_captured_returns (caller : Subst) (state : State) (items : List Term) (name : String)
    (captured : applySubst caller (v name) = terms items) :
    PureReturns runtime caller state (a "rho:lex:length" [v name]) state (number items.length) :=
  helper_capture .length caller state _ _ _ rfl (by simp [captured]) (length_returns state items)

/-! ## Constructor names -/

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (bagSplice bagContents collapseBag normalizeQuote)

private def nameValue (name : String) : Atom := terms ((serString name).map Term.natural)

private def nameRows : List (String × Atom) := rhoNames.map fun name => (name, nameValue name)

private def nameChain : List (String × Atom) → Atom
  | [] => a "UnknownRhoConstructor" [v "name"]
  | (literal, value) :: rest => a "if" [a "==" [v "name", encoded (.string literal)], value, nameChain rest]

private theorem name_ser_shape : (equation .nameSer).body = nameChain nameRows := by
  decide +kernel

private theorem name_test_returns (caller : Subst) (state : State) (name literal : String)
    (captured : applySubst caller (v "name") = encoded (.string name)) :
    PureReturns runtime caller state (a "==" [v "name", encoded (.string literal)]) state
      (Effects.boolean (decide (name = literal))) := by
  have tested := CettaWireAtom.equality_evaluated_returns runtime caller state (.string name) (.string literal)
    (v "name") (encoded (.string literal)) (by decide +kernel) (by decide +kernel)
    (by simpa only [captured] using variable_returns runtime caller state "name")
    (grounded_returns runtime caller state (.string literal))
  simpa only [Term.string.injEq] using tested

private theorem name_value_template (name : String) : PureData.Template runtime (nameValue name) := by
  unfold nameValue terms encoded
  generalize serString name = codes
  induction codes with
  | nil => exact PureData.Template.symbol _
  | cons code codes ih =>
    simp only [List.map_cons, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
    apply template_constructor _ _ (by decide)
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact PureData.Template.grounded _
    · exact ih

private theorem name_value_closed (caller : Subst) (name : String) :
    applySubst caller (nameValue name) = nameValue name := by
  unfold nameValue terms encoded
  generalize serString name = codes
  induction codes with
  | nil => rfl
  | cons code codes ih =>
    simp only [List.map_cons, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany] at ih ⊢
    simp only [applySubst, applySubst.applySubstList]
    rw [ih]
    simp [CettaWireAtom.encode, applySubst]

private theorem chain_returns (caller : Subst) (state : State) (name : String)
    (captured : applySubst caller (v "name") = encoded (.string name)) :
    ∀ names : List String, name ∈ names →
      PureReturns runtime caller state (nameChain (names.map fun name => (name, nameValue name))) state
        (nameValue name)
  | [], member => absurd member (List.not_mem_nil)
  | literal :: names, member => by
    simp only [List.map_cons, nameChain]
    apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
      runtime caller state _ (decide (name = literal))
    · exact name_test_returns caller state name literal captured
    · by_cases same : name = literal
      · subst same
        simp only [decide_true, ↓reduceIte]
        simpa only [name_value_closed] using
          PureData.template_return runtime caller state _ (name_value_template name)
      · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact chain_returns caller state name captured names
          ((List.mem_cons.mp member).resolve_left same)

/-- The table serializes each rho constructor name as its length and character codes. -/
theorem name_ser_returns (state : State) (name : String) (known : name ∈ rhoNames) :
    PureReturns runtime [] state (a "rho:lex:name-ser" [encoded (.string name)]) state
      (terms ((serString name).map Term.natural)) := by
  apply helper_call .nameSer [] state _ [encoded (.string name)] _ rfl (by
    simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [name_ser_shape]
  exact chain_returns _ state name (by simp [bindings, Helper.names, applySubst, Subst.lookup]) rhoNames known

/-! ## The order -/

private abbrev naturals (values : List Nat) : Atom := terms (values.map Term.natural)

private def leInnerCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean false),
   (a "LCons" [v "y", v "ys"],
    a "if" [a "<" [v "x", v "y"], Effects.boolean true,
      a "if" [a "==" [v "x", v "y"], a "rho:lex:le" [v "xs", v "ys"], Effects.boolean false]])]

private def leCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean true),
   (a "LCons" [v "x", v "xs"],
    a "case" [v "right", .expression (leInnerCases.map fun row => .expression [row.1, row.2])])]

private theorem le_shape : (equation .le).body =
    a "case" [v "left", .expression (leCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem less_returns (caller : Subst) (state : State) (x y : Nat)
    (left : applySubst caller (v "x") = number x) (right : applySubst caller (v "y") = number y) :
    PureReturns runtime caller state (a "<" [v "x", v "y"]) state (Effects.boolean (decide (x < y))) := by
  apply native_binary_call_returns runtime caller state state state state "<"
    (v "x") (v "y") (number x) (number y) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [left] using variable_returns runtime caller state "x"
  · simpa only [right] using variable_returns runtime caller state "y"
  · simpa only [number, encoded, CettaWireAtom.encode, Int.ofNat_lt] using StdLib.less_comparison state (x : Int) y

private theorem equal_returns (caller : Subst) (state : State) (x y : Nat)
    (left : applySubst caller (v "x") = number x) (right : applySubst caller (v "y") = number y) :
    PureReturns runtime caller state (a "==" [v "x", v "y"]) state (Effects.boolean (decide (x = y))) := by
  have tested := CettaWireAtom.equality_evaluated_returns runtime caller state (.natural x) (.natural y)
    (v "x") (v "y") (by decide +kernel) (by decide +kernel)
    (by simpa only [left] using variable_returns runtime caller state "x")
    (by simpa only [right] using variable_returns runtime caller state "y")
  simpa only [Term.natural.injEq] using tested

/-- The comparator is lexicographic order on number lists. -/
theorem le_returns (state : State) (xs ys : List Nat) :
    PureReturns runtime [] state (a "rho:lex:le" [naturals xs, naturals ys]) state
      (Effects.boolean (lexLe xs ys)) := by
  induction xs generalizing ys with
  | nil =>
      let caller := bindings .le [naturals [], naturals ys]
      apply helper_call .le [] state _ [naturals [], naturals ys] _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [le_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") leCases (Effects.boolean true) _
      · simpa [caller, bindings, Helper.names, naturals, terms, encodeList, CettaWireAtom.encode, applySubst,
          Subst.lookup] using variable_returns runtime caller state "left"
      · simp [caller, bindings, Helper.names, leCases, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, matchAtom]
      · simpa [lexLe, Effects.boolean] using grounded_returns runtime caller state (.bool true)
  | cons x xs ih =>
      let caller := bindings .le [naturals (x :: xs), naturals ys]
      let selected := [("xs", naturals xs), ("x", number x)] ++ caller
      apply helper_call .le [] state _ [naturals (x :: xs), naturals ys] _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [le_shape]
      apply branch_returns caller selected state _ (naturals (x :: xs)) leCases
        (a "case" [v "right", .expression (leInnerCases.map fun row => .expression [row.1, row.2])]) _
      · exact variable_returns runtime caller state "left"
      · simp [selected, caller, bindings, Helper.names, leCases, naturals, terms, encodeList,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · cases ys with
        | nil =>
            apply branch_returns selected selected state _ (.symbol "LNil") leInnerCases
              (Effects.boolean false) _
            · simpa [selected, caller, bindings, Helper.names, naturals, terms, encodeList, CettaWireAtom.encode,
                applySubst, Subst.lookup] using variable_returns runtime selected state "right"
            · simp [leInnerCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · simpa [lexLe, Effects.boolean] using grounded_returns runtime selected state (.bool false)
        | cons y ys =>
            let inner := [("ys", naturals ys), ("y", number y)] ++ selected
            apply branch_returns selected inner state _ (naturals (y :: ys)) leInnerCases
              (a "if" [a "<" [v "x", v "y"], Effects.boolean true,
                a "if" [a "==" [v "x", v "y"], a "rho:lex:le" [v "xs", v "ys"], Effects.boolean false]]) _
            · simpa [selected, caller, bindings, Helper.names, applySubst, Subst.lookup] using
                variable_returns runtime selected state "right"
            · simp [inner, selected, caller, bindings, Helper.names, leInnerCases, naturals, terms, encodeList,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
            · apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
                runtime inner state _ (decide (x < y))
              · exact less_returns inner state x y (by simp [inner, selected, applySubst, Subst.lookup])
                  (by simp [inner, applySubst, Subst.lookup])
              · by_cases less : x < y
                · simp only [less, decide_true, ↓reduceIte]
                  simpa [lexLe, less, Effects.boolean] using grounded_returns runtime inner state (.bool true)
                · simp only [less, decide_false, Bool.false_eq_true, ↓reduceIte]
                  apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
                    runtime inner state _ (decide (x = y))
                  · exact equal_returns inner state x y (by simp [inner, selected, applySubst, Subst.lookup])
                      (by simp [inner, applySubst, Subst.lookup])
                  · by_cases same : x = y
                    · subst same
                      simp only [decide_true, ↓reduceIte]
                      have recursive := helper_capture .le inner state [v "xs", v "ys"]
                        [naturals xs, naturals ys] _ rfl
                        (by simp [inner, selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
                        (ih ys)
                      simpa [lexLe, Helper.head] using recursive
                    · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte]
                      have differ : (x == y) = false := beq_false_of_ne same
                      simpa [lexLe, less, differ, Effects.boolean] using
                        grounded_returns runtime inner state (.bool false)

/-! ## The serialization -/

private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
private abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)

private theorem patternsValue_eq (patterns : List Pattern) :
    patternsValue patterns = terms (patterns.map InferenceCettaWire.encodePattern) := by
  simp [patternsValue, terms, InferenceCettaWire.encodePatterns_eq_encodeList]

private abbrev bagName : Atom := encoded (.string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag")

private def pairsAtom (pairs : List (Atom × Atom)) : Atom :=
  .expression (pairs.map fun pair => .expression [pair.1, pair.2])

private def serApplyPairs : List (Atom × Atom) :=
  [(v "head", a "rho:lex:name-ser" [v "name"]),
   (v "count", a "rho:lex:length" [v "arguments"]),
   (v "body", a "rho:lex:ser-list" [v "arguments"]),
   (v "all", a "rho:lex:append" [v "head", a "LCons" [v "count", v "body"]])]

private def serBagPairs : List (Atom × Atom) :=
  [(v "count", a "rho:lex:length" [v "elements"]),
   (v "body", a "rho:lex:ser-list" [v "elements"]),
   (v "all", a "rho:lex:append" [v "body", a "LCons" [number 0, .symbol "LNil"]])]

private def serCases : SpaceSemantics.Cases :=
  [(a "Var" [v "index"], a "LCons" [number 0, a "LCons" [v "index", .symbol "LNil"]]),
   (a "PApp" [v "name", v "arguments"], a "let*" [pairsAtom serApplyPairs, a "LCons" [number 2, v "all"]]),
   (a "PLam" [.symbol "BNone", v "body"],
    a "let" [v "inner", a "rho:lex:ser" [v "body"], a "LCons" [number 3, a "LCons" [number 0, v "inner"]]]),
   (a "PCollection" [bagName, v "elements", .symbol "RNone"],
    a "let*" [pairsAtom serBagPairs, a "LCons" [number 6, a "LCons" [number 1, a "LCons" [v "count", v "all"]]]])]

private theorem ser_shape : (equation .ser).body =
    a "case" [v "pattern", .expression (serCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def serListPairs : List (Atom × Atom) :=
  [(v "head", a "rho:lex:ser" [v "first"]), (v "tail", a "rho:lex:ser-list" [v "rest"])]

private def serListCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [v "first", v "rest"], a "let*" [pairsAtom serListPairs, a "rho:lex:append" [v "head", v "tail"]])]

private theorem ser_list_shape : (equation .serList).body =
    a "case" [v "patterns", .expression (serListCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem bind_fresh {caller final : Subst} {state : State} {name : String} {expression value : Atom}
    {rest : List (Atom × Atom)}
    (fresh : caller.lookup name = none)
    (computed : PureReturns runtime caller state expression state value)
    (continued : PureData.BindingsReturn runtime ((name, value) :: caller) state rest final state) :
    PureData.BindingsReturn runtime caller state ((v name, expression) :: rest) final state :=
  .cons computed (by simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]) continued

private theorem let_star_bindings {caller final : Subst} {state : State} {pairs : List (Atom × Atom)}
    {body answer : Atom}
    (computed : PureData.BindingsReturn runtime caller state pairs final state)
    (returned : PureReturns runtime final state body state answer) :
    PureReturns runtime caller state (a "let*" [pairsAtom pairs, body]) state answer :=
  PureData.let_bindings_return computed state body answer returned

private theorem closed_arguments (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value
    exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

mutual
  /-- The serializer computes `ser` on every rho shape. -/
  theorem ser_returns (state : State) : ∀ {pattern : Pattern}, RhoShaped pattern →
      PureReturns runtime [] state (a "rho:lex:ser" [patternValue pattern]) state (naturals (ser pattern))
    | _, .bvar index => by
        let caller := bindings .ser [patternValue (.bvar index)]
        let selected := ("index", number index) :: caller
        apply helper_call .ser [] state _ [patternValue (.bvar index)] _ rfl (closed_arguments _)
        rw [ser_shape]
        apply branch_returns caller selected state _ (patternValue (.bvar index)) serCases
          (a "LCons" [number 0, a "LCons" [v "index", .symbol "LNil"]]) _
        · exact variable_returns runtime caller state "pattern"
        · simp [serCases, selected, caller, bindings, Helper.names, patternValue, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · have template : PureData.Template runtime (a "LCons" [number 0, a "LCons" [v "index", .symbol "LNil"]]) := by
            rho_template
          simpa [ser, selected, caller, bindings, Helper.names, naturals, terms, encodeList, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return runtime selected state _ template
    | _, .apply (constructor := name) (arguments := arguments) known argumentsShaped => by
        let caller := bindings .ser [patternValue (.apply name arguments)]
        let selected := [("arguments", patternsValue arguments), ("name", encoded (.string name))] ++ caller
        let headValue := terms ((serString name).map Term.natural)
        let withHead := ("head", headValue) :: selected
        let withCount := ("count", number arguments.length) :: withHead
        let withBody := ("body", naturals (serList arguments)) :: withCount
        let allValue := terms ((serString name).map Term.natural ++
          Term.natural arguments.length :: (serList arguments).map Term.natural)
        let final := ("all", allValue) :: withBody
        apply helper_call .ser [] state _ [patternValue (.apply name arguments)] _ rfl (closed_arguments _)
        rw [ser_shape]
        apply branch_returns caller selected state _ (patternValue (.apply name arguments)) serCases
          (a "let*" [pairsAtom serApplyPairs, a "LCons" [number 2, v "all"]]) _
        · exact variable_returns runtime caller state "pattern"
        · simp [serCases, selected, caller, bindings, Helper.names, patternValue, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · apply let_star_bindings (final := final)
          · apply bind_fresh (by simp [selected, caller, bindings, Helper.names, Subst.lookup])
              (helper_capture .nameSer selected state [v "name"] [encoded (.string name)] _ rfl
                (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
                (name_ser_returns state name known))
            apply bind_fresh (by simp [selected, caller, bindings, Helper.names, Subst.lookup])
              (by
                have counted := helper_capture .length withHead state [v "arguments"]
                  [terms (arguments.map InferenceCettaWire.encodePattern)] _ rfl
                  (by simp [withHead, selected, caller, bindings, Helper.names, applySubst, Subst.lookup,
                    patternsValue_eq])
                  (length_returns state (arguments.map InferenceCettaWire.encodePattern))
                simpa only [List.length_map, Helper.head] using counted)
            apply bind_fresh (by simp [withCount, withHead, selected, caller, bindings, Helper.names, Subst.lookup])
              (helper_capture .serList withCount state [v "arguments"] [patternsValue arguments] _ rfl
                (by simp [withCount, withHead, selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
                (serList_returns state argumentsShaped))
            apply bind_fresh
              (by simp [withBody, withCount, withHead, selected, caller, bindings, Helper.names, Subst.lookup])
              (helper_capture .append withBody state [v "head", a "LCons" [v "count", v "body"]]
                [terms ((serString name).map Term.natural),
                  terms (Term.natural arguments.length :: (serList arguments).map Term.natural)] _ rfl
                (by simp [withBody, withCount, withHead, headValue, selected, caller, bindings, Helper.names,
                  applySubst, applySubst.applySubstList, Subst.lookup, naturals, terms, encodeList,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany])
                (append_returns state _ _))
            exact .nil _ _
          · have template : PureData.Template runtime (a "LCons" [number 2, v "all"]) := by rho_template
            simpa [ser, final, allValue, naturals, terms, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              applySubst, applySubst.applySubstList, Subst.lookup] using
              PureData.template_return runtime final state _ template
    | _, .lambda (body := body) bodyShaped => by
        let caller := bindings .ser [patternValue (.lambda none body)]
        let selected := ("body", patternValue body) :: caller
        let final := ("inner", naturals (ser body)) :: selected
        apply helper_call .ser [] state _ [patternValue (.lambda none body)] _ rfl (closed_arguments _)
        rw [ser_shape]
        apply branch_returns caller selected state _ (patternValue (.lambda none body)) serCases
          (a "let" [v "inner", a "rho:lex:ser" [v "body"], a "LCons" [number 3, a "LCons" [number 0, v "inner"]]]) _
        · exact variable_returns runtime caller state "pattern"
        · simp [serCases, selected, caller, bindings, Helper.names, patternValue, InferenceCettaWire.encodePattern,
            InferenceCettaWire.encodeBinder, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup]
        · apply named_let_returns selected state "inner" _ (naturals (ser body))
          · simp [selected, caller, bindings, Helper.names, Subst.lookup]
          · exact helper_capture .ser selected state [v "body"] [patternValue body] _ rfl
              (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
              (ser_returns state bodyShaped)
          · have template : PureData.Template runtime
                (a "LCons" [number 3, a "LCons" [number 0, v "inner"]]) := by rho_template
            simpa [ser, serOptString, final, naturals, terms, encodeList, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
              PureData.template_return runtime final state _ template
    | _, .bag (elements := elements) elementsShaped => by
        let caller := bindings .ser [patternValue (.collection .hashBag elements none)]
        let selected := ("elements", patternsValue elements) :: caller
        let withCount := ("count", number elements.length) :: selected
        let withBody := ("body", naturals (serList elements)) :: withCount
        let allValue := terms ((serList elements).map Term.natural ++ [Term.natural 0])
        let final := ("all", allValue) :: withBody
        apply helper_call .ser [] state _ [patternValue (.collection .hashBag elements none)] _ rfl
          (closed_arguments _)
        rw [ser_shape]
        apply branch_returns caller selected state _ (patternValue (.collection .hashBag elements none)) serCases
          (a "let*" [pairsAtom serBagPairs,
            a "LCons" [number 6, a "LCons" [number 1, a "LCons" [v "count", v "all"]]]]) _
        · exact variable_returns runtime caller state "pattern"
        · simp [serCases, selected, caller, bindings, Helper.names, patternValue, InferenceCettaWire.encodePattern,
            InferenceCettaWire.encodeCollectionType, InferenceCettaWire.encodeRest, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · apply let_star_bindings (final := final)
          · apply bind_fresh (by simp [selected, caller, bindings, Helper.names, Subst.lookup])
              (by
                have counted := helper_capture .length selected state [v "elements"]
                  [terms (elements.map InferenceCettaWire.encodePattern)] _ rfl
                  (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup, patternsValue_eq])
                  (length_returns state (elements.map InferenceCettaWire.encodePattern))
                simpa only [List.length_map, Helper.head] using counted)
            apply bind_fresh (by simp [withCount, selected, caller, bindings, Helper.names, Subst.lookup])
              (helper_capture .serList withCount state [v "elements"] [patternsValue elements] _ rfl
                (by simp [withCount, selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
                (serList_returns state elementsShaped))
            apply bind_fresh (by simp [withBody, withCount, selected, caller, bindings, Helper.names, Subst.lookup])
              (helper_capture .append withBody state [v "body", a "LCons" [number 0, .symbol "LNil"]]
                [naturals (serList elements), terms [Term.natural 0]] _ rfl
                (by simp [withBody, withCount, selected, caller, bindings, Helper.names, applySubst,
                  applySubst.applySubstList, Subst.lookup, naturals, terms, encodeList, CettaWireAtom.encode,
                  CettaWireAtom.encodeMany])
                (append_returns state _ _))
            exact .nil _ _
          · have template : PureData.Template runtime
                (a "LCons" [number 6, a "LCons" [number 1, a "LCons" [v "count", v "all"]]]) := by rho_template
            simpa [ser, serOptString, collectionTag, final, withBody, withCount, allValue, naturals, terms,
              encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
              Subst.lookup] using PureData.template_return runtime final state _ template

  theorem serList_returns (state : State) : ∀ {patterns : List Pattern}, RhoShapedList patterns →
      PureReturns runtime [] state (a "rho:lex:ser-list" [patternsValue patterns]) state
        (naturals (serList patterns))
    | _, .nil => by
        let caller := bindings .serList [patternsValue []]
        apply helper_call .serList [] state _ [patternsValue []] _ rfl (closed_arguments _)
        rw [ser_list_shape]
        apply branch_returns caller caller state _ (.symbol "LNil") serListCases (.symbol "LNil") _
        · simpa [caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
            applySubst, Subst.lookup] using variable_returns runtime caller state "patterns"
        · simp [serListCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa [serList, naturals, terms, encodeList, CettaWireAtom.encode] using
            symbol_returns runtime caller state "LNil"
    | _, .cons (pattern := first) (patterns := rest) firstShaped restShaped => by
        let caller := bindings .serList [patternsValue (first :: rest)]
        let selected := [("rest", patternsValue rest), ("first", patternValue first)] ++ caller
        let withHead := ("head", naturals (ser first)) :: selected
        let final := ("tail", naturals (serList rest)) :: withHead
        apply helper_call .serList [] state _ [patternsValue (first :: rest)] _ rfl (closed_arguments _)
        rw [ser_list_shape]
        apply branch_returns caller selected state _ (patternsValue (first :: rest)) serListCases
          (a "let*" [pairsAtom serListPairs, a "rho:lex:append" [v "head", v "tail"]]) _
        · exact variable_returns runtime caller state "patterns"
        · simp [serListCases, selected, caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · apply let_star_bindings (final := final)
          · apply bind_fresh (by simp [selected, caller, bindings, Helper.names, Subst.lookup])
              (helper_capture .ser selected state [v "first"] [patternValue first] _ rfl
                (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
                (ser_returns state firstShaped))
            apply bind_fresh (by simp [withHead, selected, caller, bindings, Helper.names, Subst.lookup])
              (helper_capture .serList withHead state [v "rest"] [patternsValue rest] _ rfl
                (by simp [withHead, selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
                (serList_returns state restShaped))
            exact .nil _ _
          · simpa [serList, naturals, List.map_append] using
              append_captured_returns final state ((ser first).map Term.natural) ((serList rest).map Term.natural)
                "head" "tail" (by simp [final, withHead, applySubst, Subst.lookup])
end

/-! ## Insertion sort -/

private def insertPairs : List (Atom × Atom) :=
  [(v "key", a "rho:lex:ser" [v "pattern"]),
   (v "firstKey", a "rho:lex:ser" [v "first"]),
   (v "before", a "rho:lex:le" [v "key", v "firstKey"])]

private def insertLater : Atom :=
  a "let" [v "tail", a "rho:lex:insert" [v "pattern", v "rest"], a "LCons" [v "first", v "tail"]]

private def insertCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "LCons" [v "pattern", .symbol "LNil"]),
   (a "LCons" [v "first", v "rest"],
    a "let*" [pairsAtom insertPairs,
      a "if" [v "before", a "LCons" [v "pattern", a "LCons" [v "first", v "rest"]], insertLater]])]

private theorem insert_shape : (equation .insert).body =
    a "case" [v "sorted", .expression (insertCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- Insertion places a rho shape before the first component it precedes. -/
theorem insert_returns (state : State) {pattern : Pattern} (shaped : RhoShaped pattern)
    (sorted : List Pattern) (sortedShaped : ∀ member ∈ sorted, RhoShaped member) :
    PureReturns runtime [] state (a "rho:lex:insert" [patternValue pattern, patternsValue sorted]) state
      (patternsValue (sorted.orderedInsert PatternLe pattern)) := by
  induction sorted with
  | nil =>
      let caller := bindings .insert [patternValue pattern, patternsValue []]
      apply helper_call .insert [] state _ [patternValue pattern, patternsValue []] _ rfl (closed_arguments _)
      rw [insert_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") insertCases
        (a "LCons" [v "pattern", .symbol "LNil"]) _
      · simpa [caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns runtime caller state "sorted"
      · simp [insertCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · have template : PureData.Template runtime (a "LCons" [v "pattern", .symbol "LNil"]) := by rho_template
        simpa [caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return runtime caller state _ template
  | cons first rest ih =>
      have firstShaped := sortedShaped first List.mem_cons_self
      have restShaped : ∀ member ∈ rest, RhoShaped member :=
        fun member membership => sortedShaped member (List.mem_cons_of_mem first membership)
      let caller := bindings .insert [patternValue pattern, patternsValue (first :: rest)]
      let selected := [("rest", patternsValue rest), ("first", patternValue first)] ++ caller
      let withKey := ("key", naturals (ser pattern)) :: selected
      let withFirstKey := ("firstKey", naturals (ser first)) :: withKey
      let final := ("before", Effects.boolean (lexLe (ser pattern) (ser first))) :: withFirstKey
      apply helper_call .insert [] state _ [patternValue pattern, patternsValue (first :: rest)] _ rfl
        (closed_arguments _)
      rw [insert_shape]
      apply branch_returns caller selected state _ (patternsValue (first :: rest)) insertCases
        (a "let*" [pairsAtom insertPairs,
          a "if" [v "before", a "LCons" [v "pattern", a "LCons" [v "first", v "rest"]], insertLater]]) _
      · exact variable_returns runtime caller state "sorted"
      · simp [insertCases, selected, caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · apply let_star_bindings (final := final)
        · apply bind_fresh (by simp [selected, caller, bindings, Helper.names, Subst.lookup])
            (helper_capture .ser selected state [v "pattern"] [patternValue pattern] _ rfl
              (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
              (ser_returns state shaped))
          apply bind_fresh (by simp [withKey, selected, caller, bindings, Helper.names, Subst.lookup])
            (helper_capture .ser withKey state [v "first"] [patternValue first] _ rfl
              (by simp [withKey, selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
              (ser_returns state firstShaped))
          apply bind_fresh (by simp [withFirstKey, withKey, selected, caller, bindings, Helper.names, Subst.lookup])
            (helper_capture .le withFirstKey state [v "key", v "firstKey"]
              [naturals (ser pattern), naturals (ser first)] _ rfl
              (by simp [withFirstKey, withKey, selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
              (le_returns state _ _))
          exact .nil _ _
        · apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
            runtime final state _ (lexLe (ser pattern) (ser first))
          · exact variable_returns runtime final state "before"
          · rw [List.orderedInsert_cons]
            cases before : lexLe (ser pattern) (ser first)
            · have unordered : ¬ PatternLe pattern first := by simp [PatternLe, before]
              simp only [unordered, Bool.false_eq_true, ↓reduceIte]
              let finished := ("tail", patternsValue (rest.orderedInsert PatternLe pattern)) :: final
              unfold insertLater
              apply named_let_returns final state "tail" _ (patternsValue (rest.orderedInsert PatternLe pattern))
              · simp [final, withFirstKey, withKey, selected, caller, bindings, Helper.names, Subst.lookup]
              · exact helper_capture .insert final state [v "pattern", v "rest"]
                  [patternValue pattern, patternsValue rest] _ rfl
                  (by simp [final, withFirstKey, withKey, selected, caller, bindings, Helper.names, applySubst,
                    Subst.lookup])
                  (ih restShaped)
              · have template : PureData.Template runtime (a "LCons" [v "first", v "tail"]) := by rho_template
                simpa [finished, final, withFirstKey, withKey, selected, patternsValue,
                  InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
                  applySubst.applySubstList, Subst.lookup] using
                  PureData.template_return runtime finished state _ template
            · have ordered : PatternLe pattern first := before
              simp only [ordered, ↓reduceIte]
              have template : PureData.Template runtime
                  (a "LCons" [v "pattern", a "LCons" [v "first", v "rest"]]) := by rho_template
              simpa [final, withFirstKey, withKey, selected, caller, bindings, Helper.names, patternsValue,
                InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
                applySubst.applySubstList, Subst.lookup] using PureData.template_return runtime final state _ template

private def sortCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [v "first", v "rest"],
    a "let" [v "sorted", a "rho:lex:sort" [v "rest"], a "rho:lex:insert" [v "first", v "sorted"]])]

private theorem sort_shape : (equation .sort).body =
    a "case" [v "patterns", .expression (sortCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- The sort is `sortLex`, insertion sort by the lexicographic order of serializations. -/
theorem sort_returns (state : State) (patterns : List Pattern) (shaped : ∀ member ∈ patterns, RhoShaped member) :
    PureReturns runtime [] state (a "rho:lex:sort" [patternsValue patterns]) state
      (patternsValue (sortLex patterns)) := by
  induction patterns with
  | nil =>
      let caller := bindings .sort [patternsValue []]
      apply helper_call .sort [] state _ [patternsValue []] _ rfl (closed_arguments _)
      rw [sort_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") sortCases (.symbol "LNil") _
      · simpa [caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns runtime caller state "patterns"
      · simp [sortCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [sortLex, patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
          symbol_returns runtime caller state "LNil"
  | cons first rest ih =>
      have firstShaped := shaped first List.mem_cons_self
      have restShaped : ∀ member ∈ rest, RhoShaped member :=
        fun member membership => shaped member (List.mem_cons_of_mem first membership)
      let caller := bindings .sort [patternsValue (first :: rest)]
      let selected := [("rest", patternsValue rest), ("first", patternValue first)] ++ caller
      let final := ("sorted", patternsValue (sortLex rest)) :: selected
      apply helper_call .sort [] state _ [patternsValue (first :: rest)] _ rfl (closed_arguments _)
      rw [sort_shape]
      apply branch_returns caller selected state _ (patternsValue (first :: rest)) sortCases
        (a "let" [v "sorted", a "rho:lex:sort" [v "rest"], a "rho:lex:insert" [v "first", v "sorted"]]) _
      · exact variable_returns runtime caller state "patterns"
      · simp [sortCases, selected, caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · apply named_let_returns selected state "sorted" _ (patternsValue (sortLex rest))
        · simp [selected, caller, bindings, Helper.names, Subst.lookup]
        · exact helper_capture .sort selected state [v "rest"] [patternsValue rest] _ rfl
            (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) (ih restShaped)
        · have sortedShaped : ∀ member ∈ sortLex rest, RhoShaped member :=
            fun member membership => restShaped member ((sortLex_perm rest).mem_iff.mp membership)
          have inserted := helper_capture .insert final state [v "first", v "sorted"]
            [patternValue first, patternsValue (sortLex rest)] _ rfl
            (by simp [final, selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
            (insert_returns state firstShaped (sortLex rest) sortedShaped)
          have unfolded : sortLex (first :: rest) = (sortLex rest).orderedInsert PatternLe first := rfl
          rw [unfolded]
          exact inserted

/-! ## Bag contents -/

private theorem head_mismatch (bindings : Subst) {head other : String} (patterns values : List Atom)
    (differ : head ≠ other) (notCons : head ≠ "cons") :
    SpaceSemantics.matchValue bindings (.expression (.symbol head :: patterns))
      (.expression (.symbol other :: values)) = none := by
  rw [SpaceSemantics.matchValue.eq_3 _ _ _
    (fun _ _ _ _ same _ => notCons (by simp only [List.cons.injEq, Atom.symbol.injEq] at same; exact same.1))
    (fun _ _ same => notCons (by simp only [List.cons.injEq, Atom.symbol.injEq] at same; exact same.1))]
  simp only [SpaceSemantics.matchValue.matchValues]
  rw [SpaceSemantics.matchValue.eq_5 bindings (.symbol head) (.symbol other) (by simp) (by simp) (by simp)
    (by simp)]
  simp [matchAtom, differ]

private theorem zero_row (caller : Subst) (pattern : Pattern) :
    SpaceSemantics.matchValue caller (a "PApp" [encoded (.string "PZero"), .symbol "LNil"]) (patternValue pattern) =
      if pattern = .apply "PZero" [] then some caller else none := by
  cases pattern
  case apply name arguments =>
    by_cases named : name = "PZero"
    · subst named
      cases arguments with
      | nil =>
        simp [patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom]
      | cons first rest =>
        simp [patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom]
    · have differs : "PZero" ≠ name := Ne.symm named
      cases arguments with
      | nil =>
        simp [patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, named, differs]
      | cons first rest =>
        simp [patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, named, differs]
  all_goals simp [patternValue, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    head_mismatch]

private theorem bag_row_fail (caller : Subst) (name : String) {pattern : Pattern} (shaped : RhoShaped pattern)
    (notBag : ∀ elements, pattern ≠ .collection .hashBag elements none) :
    SpaceSemantics.matchValue caller (a "PCollection" [bagName, v name, .symbol "RNone"]) (patternValue pattern) =
      none := by
  cases shaped with
  | bag => exact absurd rfl (notBag _)
  | bvar | apply | lambda =>
    simp [patternValue, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      head_mismatch]

private theorem bagSplice_other {pattern : Pattern} (notBag : ∀ elements, pattern ≠ .collection .hashBag elements none) :
    bagSplice pattern = [pattern] := by
  unfold bagSplice
  split
  · rename_i elements
    exact absurd rfl (notBag elements)
  · rfl

private def nonZeroInner : SpaceSemantics.Cases :=
  [(a "PApp" [encoded (.string "PZero"), .symbol "LNil"], v "tail"),
   (v "other", a "LCons" [v "other", v "tail"])]

private def nonZeroCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [v "first", v "rest"],
    a "let" [v "tail", a "rho:lex:non-zero" [v "rest"],
      a "case" [v "first", .expression (nonZeroInner.map fun row => .expression [row.1, row.2])]])]

private theorem non_zero_shape : (equation .nonZero).body =
    a "case" [v "patterns", .expression (nonZeroCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- Removing the parallel unit. -/
theorem nonZero_returns (state : State) (patterns : List Pattern) :
    PureReturns runtime [] state (a "rho:lex:non-zero" [patternsValue patterns]) state
      (patternsValue (patterns.filter fun pattern => pattern ≠ .apply "PZero" [])) := by
  induction patterns with
  | nil =>
      let caller := bindings .nonZero [patternsValue []]
      apply helper_call .nonZero [] state _ [patternsValue []] _ rfl (closed_arguments _)
      rw [non_zero_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") nonZeroCases (.symbol "LNil") _
      · simpa [caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns runtime caller state "patterns"
      · simp [nonZeroCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
          symbol_returns runtime caller state "LNil"
  | cons first rest ih =>
      let kept := rest.filter fun pattern => pattern ≠ .apply "PZero" []
      let caller := bindings .nonZero [patternsValue (first :: rest)]
      let selected := [("rest", patternsValue rest), ("first", patternValue first)] ++ caller
      let final := ("tail", patternsValue kept) :: selected
      apply helper_call .nonZero [] state _ [patternsValue (first :: rest)] _ rfl (closed_arguments _)
      rw [non_zero_shape]
      apply branch_returns caller selected state _ (patternsValue (first :: rest)) nonZeroCases
        (a "let" [v "tail", a "rho:lex:non-zero" [v "rest"],
          a "case" [v "first", .expression (nonZeroInner.map fun row => .expression [row.1, row.2])]]) _
      · exact variable_returns runtime caller state "patterns"
      · simp [nonZeroCases, selected, caller, bindings, Helper.names, patternsValue,
          InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup]
      · apply named_let_returns selected state "tail" _ (patternsValue kept)
        · simp [selected, caller, bindings, Helper.names, Subst.lookup]
        · exact helper_capture .nonZero selected state [v "rest"] [patternsValue rest] _ rfl
            (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) ih
        · by_cases zero : first = .apply "PZero" []
          · subst zero
            apply branch_returns final final state _ (patternValue (.apply "PZero" [])) nonZeroInner (v "tail") _
            · simpa [final, selected, applySubst, Subst.lookup] using variable_returns runtime final state "first"
            · simp [nonZeroInner, SpaceSemantics.selectCase, zero_row]
            · simpa [kept, final, applySubst, Subst.lookup] using variable_returns runtime final state "tail"
          · let other := ("other", patternValue first) :: final
            apply branch_returns final other state _ (patternValue first) nonZeroInner
              (a "LCons" [v "other", v "tail"]) _
            · simpa [final, selected, applySubst, Subst.lookup] using variable_returns runtime final state "first"
            · simp [nonZeroInner, SpaceSemantics.selectCase, zero_row, zero, other, final, selected, caller,
                bindings, Helper.names, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · have template : PureData.Template runtime (a "LCons" [v "other", v "tail"]) := by rho_template
              simpa [other, final, kept, zero, patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
                CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
                PureData.template_return runtime other state _ template

private def contentsInner : SpaceSemantics.Cases :=
  [(a "PCollection" [bagName, v "inner", .symbol "RNone"],
    a "let" [v "kept", a "rho:lex:non-zero" [v "inner"], a "rho:lex:append" [v "kept", v "tail"]]),
   (a "PApp" [encoded (.string "PZero"), .symbol "LNil"], v "tail"),
   (v "other", a "LCons" [v "other", v "tail"])]

private def contentsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [v "first", v "rest"],
    a "let" [v "tail", a "rho:lex:contents" [v "rest"],
      a "case" [v "first", .expression (contentsInner.map fun row => .expression [row.1, row.2])]])]

private theorem contents_shape : (equation .contents).body =
    a "case" [v "patterns", .expression (contentsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem bagContents_cons (first : Pattern) (rest : List Pattern) :
    bagContents (first :: rest) =
      (bagSplice first).filter (fun pattern => pattern ≠ .apply "PZero" []) ++ bagContents rest := by
  simp only [bagContents, List.flatMap_cons, List.filter_append]

/-- Splicing nested bags and removing the parallel unit is `bagContents`. -/
theorem contents_returns (state : State) (patterns : List Pattern) (shaped : ∀ member ∈ patterns, RhoShaped member) :
    PureReturns runtime [] state (a "rho:lex:contents" [patternsValue patterns]) state
      (patternsValue (bagContents patterns)) := by
  induction patterns with
  | nil =>
      let caller := bindings .contents [patternsValue []]
      apply helper_call .contents [] state _ [patternsValue []] _ rfl (closed_arguments _)
      rw [contents_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") contentsCases (.symbol "LNil") _
      · simpa [caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns runtime caller state "patterns"
      · simp [contentsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [bagContents, patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
          symbol_returns runtime caller state "LNil"
  | cons first rest ih =>
      have firstShaped := shaped first List.mem_cons_self
      have restShaped : ∀ member ∈ rest, RhoShaped member :=
        fun member membership => shaped member (List.mem_cons_of_mem first membership)
      let caller := bindings .contents [patternsValue (first :: rest)]
      let selected := [("rest", patternsValue rest), ("first", patternValue first)] ++ caller
      let final := ("tail", patternsValue (bagContents rest)) :: selected
      apply helper_call .contents [] state _ [patternsValue (first :: rest)] _ rfl (closed_arguments _)
      rw [contents_shape, bagContents_cons]
      apply branch_returns caller selected state _ (patternsValue (first :: rest)) contentsCases
        (a "let" [v "tail", a "rho:lex:contents" [v "rest"],
          a "case" [v "first", .expression (contentsInner.map fun row => .expression [row.1, row.2])]]) _
      · exact variable_returns runtime caller state "patterns"
      · simp [contentsCases, selected, caller, bindings, Helper.names, patternsValue,
          InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup]
      · apply named_let_returns selected state "tail" _ (patternsValue (bagContents rest))
        · simp [selected, caller, bindings, Helper.names, Subst.lookup]
        · exact helper_capture .contents selected state [v "rest"] [patternsValue rest] _ rfl
            (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]) (ih restShaped)
        · by_cases bag : ∃ inner, first = .collection .hashBag inner none
          · obtain ⟨inner, rfl⟩ := bag
            let opened := ("inner", patternsValue inner) :: final
            let kept := inner.filter fun pattern => pattern ≠ .apply "PZero" []
            apply branch_returns final opened state _ (patternValue (.collection .hashBag inner none)) contentsInner
              (a "let" [v "kept", a "rho:lex:non-zero" [v "inner"], a "rho:lex:append" [v "kept", v "tail"]]) _
            · simpa [final, selected, applySubst, Subst.lookup] using variable_returns runtime final state "first"
            · simp [contentsInner, opened, final, selected, caller, bindings, Helper.names, patternValue,
                InferenceCettaWire.encodePattern, InferenceCettaWire.encodeCollectionType,
                InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, Subst.lookup]
            · apply named_let_returns opened state "kept" _ (patternsValue kept)
              · simp [opened, final, selected, caller, bindings, Helper.names, Subst.lookup]
              · exact helper_capture .nonZero opened state [v "inner"] [patternsValue inner] _ rfl
                  (by simp [opened, applySubst, Subst.lookup]) (nonZero_returns state inner)
              · have appended := append_captured_returns (("kept", patternsValue kept) :: opened) state
                  (kept.map InferenceCettaWire.encodePattern) ((bagContents rest).map InferenceCettaWire.encodePattern)
                  "kept" "tail" (by simp [opened, final, applySubst, Subst.lookup, patternsValue_eq])
                simpa [bagSplice, kept, patternsValue_eq, List.map_append] using appended
          · have notBag : ∀ elements, first ≠ .collection .hashBag elements none :=
              fun elements same => bag ⟨elements, same⟩
            rw [bagSplice_other notBag]
            by_cases zero : first = .apply "PZero" []
            · subst zero
              apply branch_returns final final state _ (patternValue (.apply "PZero" [])) contentsInner (v "tail") _
              · simpa [final, selected, applySubst, Subst.lookup] using variable_returns runtime final state "first"
              · simp [contentsInner, SpaceSemantics.selectCase, zero_row, bag_row_fail _ _ firstShaped notBag]
              · simpa [final, applySubst, Subst.lookup] using variable_returns runtime final state "tail"
            · let other := ("other", patternValue first) :: final
              apply branch_returns final other state _ (patternValue first) contentsInner
                (a "LCons" [v "other", v "tail"]) _
              · simpa [final, selected, applySubst, Subst.lookup] using variable_returns runtime final state "first"
              · simp [contentsInner, SpaceSemantics.selectCase, zero_row, zero, bag_row_fail _ _ firstShaped notBag, other,
                  final, selected, caller, bindings, Helper.names, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
              · have template : PureData.Template runtime (a "LCons" [v "other", v "tail"]) := by rho_template
                simpa [other, final, zero, patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
                  CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
                  PureData.template_return runtime other state _ template

/-! ## Collapse and the name equation -/

private def collapseCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "PApp" [encoded (.string "PZero"), .symbol "LNil"]),
   (a "LCons" [v "only", .symbol "LNil"], v "only"),
   (v "many", a "PCollection" [bagName, v "many", .symbol "RNone"])]

private theorem collapse_shape : (equation .collapse).body =
    a "case" [v "patterns", .expression (collapseCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- Empty and singleton bags lose their wrapper. -/
theorem collapse_returns (state : State) (patterns : List Pattern) :
    PureReturns runtime [] state (a "rho:lex:collapse" [patternsValue patterns]) state
      (patternValue (collapseBag patterns)) := by
  match patterns with
  | [] =>
    let caller := bindings .collapse [patternsValue []]
    apply helper_call .collapse [] state _ [patternsValue []] _ rfl (closed_arguments _)
    rw [collapse_shape]
    apply branch_returns caller caller state _ (.symbol "LNil") collapseCases
      (a "PApp" [encoded (.string "PZero"), .symbol "LNil"]) _
    · simpa [caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
        applySubst, Subst.lookup] using variable_returns runtime caller state "patterns"
    · simp [collapseCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · have template : PureData.Template runtime (a "PApp" [encoded (.string "PZero"), .symbol "LNil"]) := by
        rho_template
      simpa [collapseBag, patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList] using
        PureData.template_return runtime caller state _ template
  | [only] =>
    let caller := bindings .collapse [patternsValue [only]]
    let selected := ("only", patternValue only) :: caller
    apply helper_call .collapse [] state _ [patternsValue [only]] _ rfl (closed_arguments _)
    rw [collapse_shape]
    apply branch_returns caller selected state _ (patternsValue [only]) collapseCases (v "only") _
    · exact variable_returns runtime caller state "patterns"
    · simp [collapseCases, selected, caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · simpa [collapseBag, selected, applySubst, Subst.lookup] using variable_returns runtime selected state "only"
  | first :: second :: rest =>
    let caller := bindings .collapse [patternsValue (first :: second :: rest)]
    let selected := ("many", patternsValue (first :: second :: rest)) :: caller
    apply helper_call .collapse [] state _ [patternsValue (first :: second :: rest)] _ rfl (closed_arguments _)
    rw [collapse_shape]
    apply branch_returns caller selected state _ (patternsValue (first :: second :: rest)) collapseCases
      (a "PCollection" [bagName, v "many", .symbol "RNone"]) _
    · exact variable_returns runtime caller state "patterns"
    · simp [collapseCases, selected, caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · have template : PureData.Template runtime (a "PCollection" [bagName, v "many", .symbol "RNone"]) := by
        rho_template
      simpa [collapseBag, selected, patternValue, patternsValue, InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodeCollectionType, InferenceCettaWire.encodeRest, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
        PureData.template_return runtime selected state _ template

private theorem unary_row_fail (caller : Subst) (literal name : String) (pattern : Pattern)
    (notUnary : ∀ argument, pattern ≠ .apply literal [argument]) :
    SpaceSemantics.matchValue caller (a "PApp" [encoded (.string literal), a "LCons" [v name, .symbol "LNil"]])
      (patternValue pattern) = none := by
  cases pattern
  case apply constructor arguments =>
    by_cases named : constructor = literal
    · subst named
      match arguments with
      | [] =>
        simp [patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom]
      | [argument] => exact absurd rfl (notUnary argument)
      | first :: second :: rest =>
        simp [patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom]
    · have differs : literal ≠ constructor := Ne.symm named
      match arguments with
      | [] =>
        simp [patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, differs]
      | [argument] =>
        simp [patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, differs]
      | first :: second :: rest =>
        simp [patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, differs]
  all_goals simp [patternValue, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    head_mismatch]

private def quoteCases : SpaceSemantics.Cases :=
  [(a "PApp" [encoded (.string "PDrop"), a "LCons" [v "name", .symbol "LNil"]], v "name"),
   (v "other", a "PApp" [encoded (.string "NQuote"), a "LCons" [v "other", .symbol "LNil"]])]

private theorem quote_shape : (equation .quote).body =
    a "case" [v "pattern", .expression (quoteCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- The name equation `@(*x) = x`, oriented. -/
theorem quote_returns (state : State) (pattern : Pattern) :
    PureReturns runtime [] state (a "rho:lex:quote" [patternValue pattern]) state
      (patternValue (normalizeQuote pattern)) := by
  let caller := bindings .quote [patternValue pattern]
  apply helper_call .quote [] state _ [patternValue pattern] _ rfl (closed_arguments _)
  rw [quote_shape]
  by_cases dropped : ∃ name, pattern = .apply "PDrop" [name]
  · obtain ⟨name, rfl⟩ := dropped
    let selected := ("name", patternValue name) :: caller
    apply branch_returns caller selected state _ (patternValue (.apply "PDrop" [name])) quoteCases (v "name") _
    · exact variable_returns runtime caller state "pattern"
    · simp [quoteCases, selected, caller, bindings, Helper.names, patternValue, InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        Subst.lookup]
    · simpa [normalizeQuote, selected, applySubst, Subst.lookup] using variable_returns runtime selected state "name"
  · have notUnary : ∀ argument, pattern ≠ .apply "PDrop" [argument] :=
      fun argument same => dropped ⟨argument, same⟩
    have kept : normalizeQuote pattern = .apply "NQuote" [pattern] := by
      unfold normalizeQuote
      split
      · rename_i name
        exact absurd rfl (notUnary name)
      · rfl
    let selected := ("other", patternValue pattern) :: caller
    rw [kept]
    apply branch_returns caller selected state _ (patternValue pattern) quoteCases
      (a "PApp" [encoded (.string "NQuote"), a "LCons" [v "other", .symbol "LNil"]]) _
    · exact variable_returns runtime caller state "pattern"
    · simp [quoteCases, SpaceSemantics.selectCase, unary_row_fail _ _ _ _ notUnary, selected, caller, bindings,
        Helper.names, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · have template : PureData.Template runtime
          (a "PApp" [encoded (.string "NQuote"), a "LCons" [v "other", .symbol "LNil"]]) := by rho_template
      simpa [selected, patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
        PureData.template_return runtime selected state _ template

/-! ## The canonical form -/

private def canonicalBagPairs : List (Atom × Atom) :=
  [(v "inner", a "rho:lex:canonical-list" [v "elements"]),
   (v "contents", a "rho:lex:contents" [v "inner"]),
   (v "sorted", a "rho:lex:sort" [v "contents"])]

private def canonicalCases : SpaceSemantics.Cases :=
  [(a "Var" [v "index"], a "Var" [v "index"]),
   (a "PApp" [encoded (.string "NQuote"), a "LCons" [v "argument", .symbol "LNil"]],
    a "let" [v "inner", a "rho:lex:canonical" [v "argument"], a "rho:lex:quote" [v "inner"]]),
   (a "PApp" [v "name", v "arguments"],
    a "let" [v "inner", a "rho:lex:canonical-list" [v "arguments"], a "PApp" [v "name", v "inner"]]),
   (a "PLam" [v "binder", v "body"],
    a "let" [v "inner", a "rho:lex:canonical" [v "body"], a "PLam" [v "binder", v "inner"]]),
   (a "PCollection" [bagName, v "elements", .symbol "RNone"],
    a "let*" [pairsAtom canonicalBagPairs, a "rho:lex:collapse" [v "sorted"]])]

private theorem canonical_shape : (equation .canonical).body =
    a "case" [v "pattern", .expression (canonicalCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def canonicalListPairs : List (Atom × Atom) :=
  [(v "head", a "rho:lex:canonical" [v "first"]), (v "tail", a "rho:lex:canonical-list" [v "rest"])]

private def canonicalListCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [v "first", v "rest"], a "let*" [pairsAtom canonicalListPairs, a "LCons" [v "head", v "tail"]])]

private theorem canonical_list_shape : (equation .canonicalList).body =
    a "case" [v "patterns", .expression (canonicalListCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem canonical_list_returns (state : State) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns runtime [] state (a "rho:lex:canonical" [patternValue pattern])
      state (patternValue (lexCanon pattern))) :
    PureReturns runtime [] state (a "rho:lex:canonical-list" [patternsValue patterns]) state
      (patternsValue (lexCanonList patterns)) := by
  induction patterns with
  | nil =>
      let caller := bindings .canonicalList [patternsValue []]
      apply helper_call .canonicalList [] state _ [patternsValue []] _ rfl (closed_arguments _)
      rw [canonical_list_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") canonicalListCases (.symbol "LNil") _
      · simpa [caller, bindings, Helper.names, patternsValue, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns runtime caller state "patterns"
      · simp [canonicalListCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [lexCanonList, patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
          symbol_returns runtime caller state "LNil"
  | cons first rest ih =>
      let caller := bindings .canonicalList [patternsValue (first :: rest)]
      let selected := [("rest", patternsValue rest), ("first", patternValue first)] ++ caller
      let withHead := ("head", patternValue (lexCanon first)) :: selected
      let final := ("tail", patternsValue (lexCanonList rest)) :: withHead
      apply helper_call .canonicalList [] state _ [patternsValue (first :: rest)] _ rfl (closed_arguments _)
      rw [canonical_list_shape]
      apply branch_returns caller selected state _ (patternsValue (first :: rest)) canonicalListCases
        (a "let*" [pairsAtom canonicalListPairs, a "LCons" [v "head", v "tail"]]) _
      · exact variable_returns runtime caller state "patterns"
      · simp [canonicalListCases, selected, caller, bindings, Helper.names, patternsValue,
          InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup]
      · apply let_star_bindings (final := final)
        · apply bind_fresh (by simp [selected, caller, bindings, Helper.names, Subst.lookup])
            (helper_capture .canonical selected state [v "first"] [patternValue first] _ rfl
              (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
              (elements first List.mem_cons_self))
          apply bind_fresh (by simp [withHead, selected, caller, bindings, Helper.names, Subst.lookup])
            (helper_capture .canonicalList withHead state [v "rest"] [patternsValue rest] _ rfl
              (by simp [withHead, selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
              (ih fun pattern member => elements pattern (List.mem_cons_of_mem first member)))
          exact .nil _ _
        · have template : PureData.Template runtime (a "LCons" [v "head", v "tail"]) := by rho_template
          simpa [lexCanonList, final, withHead, patternsValue, InferenceCettaWire.encodePatterns,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return runtime final state _ template

/-- **The MeTTa canonicalizer computes `lexCanon`** on every rho shape. -/
theorem canonical_returns (state : State) (pattern : Pattern) (shaped : RhoShaped pattern) :
    PureReturns runtime [] state (a "rho:lex:canonical" [patternValue pattern]) state
      (patternValue (lexCanon pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      let caller := bindings .canonical [patternValue (.bvar index)]
      let selected := ("index", number index) :: caller
      apply helper_call .canonical [] state _ [patternValue (.bvar index)] _ rfl (closed_arguments _)
      rw [canonical_shape]
      apply branch_returns caller selected state _ (patternValue (.bvar index)) canonicalCases (a "Var" [v "index"]) _
      · exact variable_returns runtime caller state "pattern"
      · simp [canonicalCases, selected, caller, bindings, Helper.names, patternValue,
          InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup]
      · have template : PureData.Template runtime (a "Var" [v "index"]) := by rho_template
        simpa [lexCanon, selected, patternValue, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return runtime selected state _ template
  | hfvar name => exact absurd shaped (not_rhoShaped_fvar name)
  | happly name arguments ih =>
      cases shaped with
      | apply known argumentsShaped =>
      have argumentShapes := (rhoShapedList_iff arguments).mp argumentsShaped
      by_cases quote : name = "NQuote" ∧ ∃ argument, arguments = [argument]
      · obtain ⟨rfl, argument, rfl⟩ := quote
        have argumentShaped := argumentShapes argument List.mem_cons_self
        let caller := bindings .canonical [patternValue (.apply "NQuote" [argument])]
        let selected := ("argument", patternValue argument) :: caller
        let final := ("inner", patternValue (lexCanon argument)) :: selected
        apply helper_call .canonical [] state _ [patternValue (.apply "NQuote" [argument])] _ rfl
          (closed_arguments _)
        rw [canonical_shape]
        apply branch_returns caller selected state _ (patternValue (.apply "NQuote" [argument])) canonicalCases
          (a "let" [v "inner", a "rho:lex:canonical" [v "argument"], a "rho:lex:quote" [v "inner"]]) _
        · exact variable_returns runtime caller state "pattern"
        · simp [canonicalCases, selected, caller, bindings, Helper.names, patternValue,
            InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · apply named_let_returns selected state "inner" _ (patternValue (lexCanon argument))
          · simp [selected, caller, bindings, Helper.names, Subst.lookup]
          · exact helper_capture .canonical selected state [v "argument"] [patternValue argument] _ rfl
              (by simp [selected, applySubst, Subst.lookup]) (ih argument List.mem_cons_self argumentShaped)
          · have quoted := helper_capture .quote final state [v "inner"] [patternValue (lexCanon argument)] _ rfl
              (by simp [final, applySubst, Subst.lookup]) (quote_returns state (lexCanon argument))
            have unfolded : lexCanon (.apply "NQuote" [argument]) = normalizeQuote (lexCanon argument) := by
              simp only [lexCanon]
            rw [unfolded]
            exact quoted
      · have notUnary : ∀ argument, Pattern.apply name arguments ≠ .apply "NQuote" [argument] := by
          intro argument same
          simp only [Pattern.apply.injEq] at same
          exact quote ⟨same.1, argument, same.2⟩
        let caller := bindings .canonical [patternValue (.apply name arguments)]
        let selected := [("arguments", patternsValue arguments), ("name", encoded (.string name))] ++ caller
        let final := ("inner", patternsValue (lexCanonList arguments)) :: selected
        rw [lexCanon_apply_general name arguments quote]
        apply helper_call .canonical [] state _ [patternValue (.apply name arguments)] _ rfl (closed_arguments _)
        rw [canonical_shape]
        apply branch_returns caller selected state _ (patternValue (.apply name arguments)) canonicalCases
          (a "let" [v "inner", a "rho:lex:canonical-list" [v "arguments"], a "PApp" [v "name", v "inner"]]) _
        · exact variable_returns runtime caller state "pattern"
        · simp only [canonicalCases, SpaceSemantics.selectCase]
          rw [unary_row_fail caller "NQuote" "argument" _ notUnary]
          simp [selected, caller, bindings, Helper.names, patternValue, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · apply named_let_returns selected state "inner" _ (patternsValue (lexCanonList arguments))
          · simp [selected, caller, bindings, Helper.names, Subst.lookup]
          · exact helper_capture .canonicalList selected state [v "arguments"] [patternsValue arguments] _ rfl
              (by simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup])
              (canonical_list_returns state arguments fun argument member =>
                ih argument member (argumentShapes argument member))
          · have template : PureData.Template runtime (a "PApp" [v "name", v "inner"]) := by rho_template
            simpa [final, selected, patternValue, patternsValue, InferenceCettaWire.encodePattern,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
              PureData.template_return runtime final state _ template
  | hlambda binder body ih =>
      cases shaped with
      | lambda bodyShaped =>
      let caller := bindings .canonical [patternValue (.lambda none body)]
      let selected := [("body", patternValue body), ("binder", .symbol "BNone")] ++ caller
      let final := ("inner", patternValue (lexCanon body)) :: selected
      apply helper_call .canonical [] state _ [patternValue (.lambda none body)] _ rfl (closed_arguments _)
      rw [canonical_shape]
      apply branch_returns caller selected state _ (patternValue (.lambda none body)) canonicalCases
        (a "let" [v "inner", a "rho:lex:canonical" [v "body"], a "PLam" [v "binder", v "inner"]]) _
      · exact variable_returns runtime caller state "pattern"
      · simp [canonicalCases, SpaceSemantics.selectCase, selected, caller,
          bindings, Helper.names, patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodeBinder,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · apply named_let_returns selected state "inner" _ (patternValue (lexCanon body))
        · simp [selected, caller, bindings, Helper.names, Subst.lookup]
        · exact helper_capture .canonical selected state [v "body"] [patternValue body] _ rfl
            (by simp [selected, applySubst, Subst.lookup]) (ih bodyShaped)
        · have template : PureData.Template runtime (a "PLam" [v "binder", v "inner"]) := by rho_template
          simpa [lexCanon, final, selected, patternValue, InferenceCettaWire.encodePattern,
            InferenceCettaWire.encodeBinder, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
            applySubst.applySubstList, Subst.lookup] using PureData.template_return runtime final state _ template
  | hmultiLambda arity binders body _ => cases shaped
  | hsubst body replacement _ _ => cases shaped
  | hcollection kind elements rest ih =>
      cases shaped with
      | bag elementsShaped =>
      have elementShapes := (rhoShapedList_iff elements).mp elementsShaped
      let canonicalElements := lexCanonList elements
      let contents := bagContents canonicalElements
      let sorted := sortLex contents
      have canonicalShapes : ∀ member ∈ canonicalElements, RhoShaped member :=
        (rhoShapedList_iff _).mp (lexCanonList_rhoShaped elementsShaped)
      have contentShapes : ∀ member ∈ contents, RhoShaped member := bagContents_rhoShaped canonicalShapes
      let caller := bindings .canonical [patternValue (.collection .hashBag elements none)]
      let selected := ("elements", patternsValue elements) :: caller
      let withInner := ("inner", patternsValue canonicalElements) :: selected
      let withContents := ("contents", patternsValue contents) :: withInner
      let final := ("sorted", patternsValue sorted) :: withContents
      apply helper_call .canonical [] state _ [patternValue (.collection .hashBag elements none)] _ rfl
        (closed_arguments _)
      rw [canonical_shape]
      apply branch_returns caller selected state _ (patternValue (.collection .hashBag elements none))
        canonicalCases (a "let*" [pairsAtom canonicalBagPairs, a "rho:lex:collapse" [v "sorted"]]) _
      · exact variable_returns runtime caller state "pattern"
      · simp [canonicalCases, SpaceSemantics.selectCase, selected, caller,
          bindings, Helper.names, patternValue, InferenceCettaWire.encodePattern,
          InferenceCettaWire.encodeCollectionType, InferenceCettaWire.encodeRest, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup]
      · apply let_star_bindings (final := final)
        · apply bind_fresh (by simp [selected, caller, bindings, Helper.names, Subst.lookup])
            (helper_capture .canonicalList selected state [v "elements"] [patternsValue elements] _ rfl
              (by simp [selected, applySubst, Subst.lookup])
              (canonical_list_returns state elements fun element member =>
                ih element member (elementShapes element member)))
          apply bind_fresh (by simp [withInner, selected, caller, bindings, Helper.names, Subst.lookup])
            (helper_capture .contents withInner state [v "inner"] [patternsValue canonicalElements] _ rfl
              (by simp [withInner, applySubst, Subst.lookup])
              (contents_returns state canonicalElements canonicalShapes))
          apply bind_fresh
            (by simp [withContents, withInner, selected, caller, bindings, Helper.names, Subst.lookup])
            (helper_capture .sort withContents state [v "contents"] [patternsValue contents] _ rfl
              (by simp [withContents, applySubst, Subst.lookup]) (sort_returns state contents contentShapes))
          exact .nil _ _
        · have collapsed := helper_capture .collapse final state [v "sorted"] [patternsValue sorted] _ rfl
            (by simp [final, applySubst, Subst.lookup]) (collapse_returns state sorted)
          have unfolded : lexCanon (.collection .hashBag elements none) = collapseBag sorted := by
            simp only [lexCanon]
            rfl
          rw [unfolded]
          exact collapsed

/-- On closed processes, the MeTTa canonicalizer returns the lexicographic canonical form. -/
theorem canonical_process_returns (state : State) {process : Pattern}
    (typed : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process) :
    PureReturns runtime [] state (a "rho:lex:canonical" [patternValue process]) state
      (patternValue (lexCanon process)) :=
  canonical_returns state process (proc_rhoShaped typed)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RhoLexCanonicalExecution
