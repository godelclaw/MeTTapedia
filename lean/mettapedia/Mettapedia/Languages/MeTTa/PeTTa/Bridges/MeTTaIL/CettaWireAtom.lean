import Mettapedia.GSLT.LanguageDef.CettaWireTerm
import Mettapedia.GSLT.LanguageDef.CettaWireEquality
import Mettapedia.Languages.ProcessCalculi.MORK.Space
import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# The shared CeTTa data carrier as PeTTa atoms

This adapter retains symbols, quoted strings, naturals and applications.
Applications stay expressions even at arity zero. Captured wire values have
no program variables, so substitution cannot reinterpret their contents.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtom

open Mettapedia.GSLT.LanguageDef.CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.ProcessCalculi.MORK.applySubst (applySubstList)

mutual
  def encode : Term → Atom
    | .symbol name => .symbol name
    | .string value => .grounded (.string value)
    | .natural value => .grounded (.int value)
    | .application head arguments => .expression (.symbol head :: encodeMany arguments)

  def encodeMany : List Term → List Atom
    | [] => []
    | first :: rest => encode first :: encodeMany rest
end

mutual
  theorem encode_injective (left right : Term) (same : encode left = encode right) : left = right := by
    cases left <;> cases right <;> simp only [encode, Atom.symbol.injEq,
      Atom.grounded.injEq, Atom.expression.injEq, List.cons.injEq,
      Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue.string.injEq,
      Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue.int.injEq] at same
    all_goals first
      | (cases same; rfl)
      | (obtain ⟨heads, arguments⟩ := same
         exact congrArg₂ Term.application heads (encodeMany_injective _ _ arguments))
      | (simp at same)

  theorem encodeMany_injective (left right : List Term)
      (same : encodeMany left = encodeMany right) : left = right := by
    cases left with
    | nil => cases right <;> simp_all [encodeMany]
    | cons first rest =>
        cases right with
        | nil => simp [encodeMany] at same
        | cons other tail =>
            obtain ⟨heads, tails⟩ := List.cons.inj same
            exact congrArg₂ List.cons (encode_injective first other heads)
              (encodeMany_injective rest tail tails)
end

mutual
  @[simp] theorem applySubst_encode (bindings : Subst) (value : Term) :
      applySubst bindings (encode value) = encode value := by
    cases value with
    | symbol name => rfl
    | string value => rfl
    | natural value => rfl
    | application head arguments =>
        simp only [encode, applySubst, applySubstList, applySubst_encodeMany]

  @[simp] theorem applySubst_encodeMany (bindings : Subst) (values : List Term) :
      applySubstList bindings (encodeMany values) = encodeMany values := by
    cases values with
    | nil => rfl
    | cons first rest => simp only [encodeMany, applySubstList, applySubst_encode,
        applySubst_encodeMany]
end

@[simp] theorem encodeMany_map (values : List Term) : encodeMany values = values.map encode := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [encodeMany, ih]

@[simp] theorem encode_eq_encode (left right : Term) : encode left = encode right ↔ left = right :=
  ⟨encode_injective left right, congrArg encode⟩

private theorem equality_boolean (left right : Term) :
    (encode left == encode right) = decide (left = right) := by
  apply Bool.eq_iff_iff.mpr
  simp [encode_eq_encode]

/-- The target's structural equality compares captured wire values exactly.
Payloads are read through variables, so equality never evaluates their contents. -/
theorem equality_captured_returns (program : SpaceSemantics.Program)
    (bindings : Subst) (state : Effects.State) (left right : Term)
    (leftName rightName : String)
    (leftCaptured : applySubst bindings (.var leftName) = encode left)
    (rightCaptured : applySubst bindings (.var rightName) = encode right) :
    Eval.PureReturns program bindings state
      (.expression [.symbol "==", .var leftName, .var rightName]) state
      (Effects.boolean (decide (left = right))) := by
  apply Eval.native_variable_call_returns program bindings state state "==" [leftName, rightName] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, leftCaptured, rightCaptured,
    StdLib.structural_equality, equality_boolean]

/-- Demand-based equality compares the actual returned wire values. The
operand computations and the loaded program's demand policy remain explicit. -/
theorem equality_evaluated_returns (program : SpaceSemantics.Program)
    (bindings : Subst) (state : Effects.State) (left right : Term)
    (leftCode rightCode : Atom)
    (leftDemanded : Eval.argumentIsRaw program "==" 0 = false)
    (rightDemanded : Eval.argumentIsRaw program "==" 1 = false)
    (leftReturned : Eval.PureReturns program bindings state leftCode state (encode left))
    (rightReturned : Eval.PureReturns program bindings state rightCode state (encode right)) :
    Eval.PureReturns program bindings state
      (.expression [.symbol "==", leftCode, rightCode]) state
      (Effects.boolean (decide (left = right))) := by
  apply Eval.native_binary_call_returns program bindings state state state state "=="
    leftCode rightCode (encode left) (encode right) _
    (by decide) (by decide) leftDemanded rightDemanded leftReturned rightReturned _ (by decide)
  simp only [StdLib.structural_equality, equality_boolean]

@[simp] theorem encode_list_nil {α : Type} (element : α → Term) :
    encode (encodeList element []) = .symbol "LNil" := rfl

@[simp] theorem encode_list_cons {α : Type} (element : α → Term) (first : α) (rest : List α) :
    encode (encodeList element (first :: rest)) =
      .expression [.symbol "LCons", encode (element first), encode (encodeList element rest)] := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtom
