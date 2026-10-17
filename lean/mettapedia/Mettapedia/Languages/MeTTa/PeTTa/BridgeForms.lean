import Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
import Mettapedia.Languages.MeTTa.PeTTa.PureData

/-!
# The evaluator's forms, for bridge proofs

`if` on a boolean, `let` binding a fresh variable, and `case` on literal rows, with the side
conditions every library bridge repeats already discharged. `selected_case_returns` takes the
selected branch as a hypothesis, so a proof reads the selection off by computation instead of
writing the bindings out.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BridgeKit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open SpaceSemantics (Program)
open Effects (State)
open Eval

/-- `if` on a boolean. -/
theorem bool_if_returns (program : Program) (caller : Subst) (before middle after : State)
    (condition : Atom) (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller before condition middle (Effects.boolean value))
    (continued : PureReturns program caller middle (if value then yes else no) after answer) :
    PureReturns program caller before (.expression [.symbol "if", condition, yes, no]) after answer := by
  apply if_returns program caller before middle after condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using continued

/-- `let` binding a variable the caller does not bind. -/
theorem fresh_let_returns (program : Program) (caller : Subst) (before middle after : State)
    (name : String) (expression value body answer : Atom)
    (fresh : caller.lookup name = none)
    (computed : PureReturns program caller before expression middle value)
    (continued : PureReturns program ((name, value) :: caller) middle body after answer) :
    PureReturns program caller before (.expression [.symbol "let", .var name, expression, body]) after answer := by
  apply let_returns program caller ((name, value) :: caller) before middle after (.var name) expression body value
    answer computed
  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]
  · exact continued

/-- `case` on literal rows. -/
theorem rows_case_returns (program : Program) (caller selected : Subst) (before middle after : State)
    (expression value body answer : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases)
    (decoded : readCases rows = some cases)
    (computed : PureReturns program caller before expression middle value)
    (matched : SpaceSemantics.selectCase caller value cases = some (selected, body))
    (continued : PureReturns program selected middle body after answer) :
    PureReturns program caller before (.expression [.symbol "case", expression, .expression rows]) after answer :=
  case_returns program caller selected before middle after expression value body answer rows cases decoded
    computed matched continued

/-- `case` on literal rows, with the selection read off by computation: the continuation is proved
for whatever the selection is, so no bindings need to be written out. -/
theorem selected_case_returns (program : Program) (caller : Subst) (before middle after : State)
    (expression value answer : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases)
    (decoded : readCases rows = some cases)
    (computed : PureReturns program caller before expression middle value)
    (found : (SpaceSemantics.selectCase caller value cases).isSome = true)
    (continued : ∀ selected body, SpaceSemantics.selectCase caller value cases = some (selected, body) →
      PureReturns program selected middle body after answer) :
    PureReturns program caller before (.expression [.symbol "case", expression, .expression rows]) after answer := by
  obtain ⟨⟨selected, body⟩, selection⟩ := Option.isSome_iff_exists.mp found
  exact case_returns program caller selected before middle after expression value body answer rows cases decoded
    computed selection (continued selected body selection)

/-! ## The same forms for computations that keep the state -/

theorem pure_if_returns (program : Program) (caller : Subst) (state : State)
    (condition : Atom) (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller state condition state (Effects.boolean value))
    (continued : PureReturns program caller state (if value then yes else no) state answer) :
    PureReturns program caller state (.expression [.symbol "if", condition, yes, no]) state answer :=
  bool_if_returns program caller state state state condition value yes no answer tested continued

theorem pure_let_returns (program : Program) (caller : Subst) (state : State)
    (name : String) (expression value body answer : Atom)
    (fresh : caller.lookup name = none)
    (computed : PureReturns program caller state expression state value)
    (continued : PureReturns program ((name, value) :: caller) state body state answer) :
    PureReturns program caller state (.expression [.symbol "let", .var name, expression, body]) state answer :=
  fresh_let_returns program caller state state state name expression value body answer fresh computed continued

theorem pure_case_returns (program : Program) (caller : Subst) (state : State)
    (expression value answer : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases)
    (decoded : readCases rows = some cases)
    (computed : PureReturns program caller state expression state value)
    (found : (SpaceSemantics.selectCase caller value cases).isSome = true)
    (continued : ∀ selected body, SpaceSemantics.selectCase caller value cases = some (selected, body) →
      PureReturns program selected state body state answer) :
    PureReturns program caller state (.expression [.symbol "case", expression, .expression rows]) state answer :=
  selected_case_returns program caller state state state expression value answer rows cases decoded computed found
    continued

theorem pure_let_star_returns (program : Program) (caller : Subst) (state : State)
    (pairs : List Atom) (body nested answer : Atom)
    (expanded : nestedLets pairs body = some nested)
    (returned : PureReturns program caller state nested state answer) :
    PureReturns program caller state (.expression [.symbol "let*", .expression pairs, body]) state answer :=
  let_star_returns program caller state state pairs body nested answer expanded returned

/-! ## Data -/

/-- A data constructor of a program: not native, not effectful, not a special form, not defined. -/
def inertHead (program : Program) (head : String) : Bool :=
  !(ioHead head || StdLib.known head || program.equations.any (·.head == head)) && !specialForms.contains head

mutual
  /-- Code that is data: variables, literals, and inert constructors applied to data. -/
  def templateCheck (program : Program) : Atom → Bool
    | .expression items => itemsCheck program items
    | _ => true

  def itemsCheck (program : Program) : List Atom → Bool
    | .symbol head :: arguments => inertHead program head && argumentsCheck program arguments
    | _ => false

  def argumentsCheck (program : Program) : List Atom → Bool
    | [] => true
    | first :: rest => templateCheck program first && argumentsCheck program rest
end

mutual
  theorem template_of_check (program : Program) :
      ∀ code : Atom, templateCheck program code = true → PureData.Template program code
    | .var name, _ => .captured name
    | .grounded value, _ => .grounded value
    | .symbol name, _ => .symbol name
    | .expression items, checked => items_template program items (by simpa [templateCheck] using checked)
  termination_by structural code => code

  theorem items_template (program : Program) :
      ∀ items : List Atom, itemsCheck program items = true → PureData.Template program (.expression items)
    | [], checked => by simp [itemsCheck] at checked
    | .symbol head :: arguments, checked => by
        simp only [itemsCheck, inertHead, Bool.and_eq_true, Bool.not_eq_true'] at checked
        refine .constructor head arguments checked.1.1 ?_ (arguments_template program arguments checked.2)
        intro special
        have : specialForms.contains head = true := by simpa [specialForms] using special
        rw [this] at checked
        cases checked.1.2
    | .var _ :: _, checked => by simp [itemsCheck] at checked
    | .grounded _ :: _, checked => by simp [itemsCheck] at checked
    | .expression _ :: _, checked => by simp [itemsCheck] at checked
  termination_by structural items => items

  theorem arguments_template (program : Program) :
      ∀ arguments : List Atom, argumentsCheck program arguments = true →
        ∀ argument ∈ arguments, PureData.Template program argument
    | [], _ => by simp
    | first :: rest, checked => by
        simp only [argumentsCheck, Bool.and_eq_true] at checked
        have head := template_of_check program first checked.1
        have tail := arguments_template program rest checked.2
        intro argument member
        rcases List.mem_cons.mp member with same | later
        · exact same ▸ head
        · exact tail argument later
  termination_by structural arguments => arguments
end

/-- **Data returns itself**, with its variables substituted. -/
theorem data_returns (program : Program) (caller : Subst) (state : State) (code answer : Atom)
    (checked : templateCheck program code = true) (same : applySubst caller code = answer) :
    PureReturns program caller state code state answer :=
  same ▸ PureData.template_return program caller state code (template_of_check program code checked)

/-- Compute a case selection, in the goal or at a hypothesis: pattern matching against values,
variable lookup in bindings, and the formals' bindings of a call. Extra lemmas unfold the encoders
of the values involved. -/
syntax "metta_select" (" [" term,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| metta_select $[[$extra,*]]? $[$location]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let extra ← extra.mapM fun term => `(Lean.Parser.Tactic.simpLemma| $term:term)
    `(tactic|
      simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, Library.bind,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, $extra,*] $[$location]?)

end Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
