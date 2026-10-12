import Mettapedia.Languages.HOLLight.MeTTa.ProofLookup

/-!
# Actual receipt-key inspection in the authored HOL checker

The guard walks the retained receipt sequence and compares complete keys.
Requests and ordered premise occurrences remain in the data. The guard does
not justify their derivations; it prevents a command from reusing an address.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.ReceiptKeys

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)

structure Entry where
  key : Atom
  request : Atom
  premises : List Atom

def entryAtom (entry : Entry) : Atom :=
  .expression [.symbol "HOL:Receipt", entry.key, entry.request, Premises.keys entry.premises]

def table (entries : List Entry) : Atom := Premises.keys (entries.map entryAtom)

def presentB (key : Atom) (entries : List Entry) : Bool := entries.any fun entry => key == entry.key

theorem presentB_eq_true_iff (key : Atom) (entries : List Entry) :
    presentB key entries = true ↔ key ∈ entries.map Entry.key := by
  simp only [presentB, List.any_eq_true, beq_iff_eq, List.mem_map]
  constructor <;> rintro ⟨entry, member, same⟩ <;> exact ⟨entry, member, same.symm⟩

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:receipt-key-present"))[0]'(by decide)
private def consBody : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .var "key", .var "previous"], boolean true,
  .expression [.symbol "hol-light:receipt-key-present", .var "key", .var "rest"]]
private def cases : SpaceSemantics.Cases :=
  [(.symbol "HOL:Nil", boolean false),
   (.expression [.symbol "HOL:Cons",
     .expression [.symbol "HOL:Receipt", .var "previous", .var "request", .var "premises"], .var "rest"], consBody),
   (.var "malformed", boolean true)]
private def environment (key : Atom) (entries : List Entry) : Subst := [("receipts", table entries), ("key", key)]
private def boundEnvironment (key : Atom) (first : Entry) (rest : List Entry) : Subst :=
  [("rest", table rest), ("premises", Premises.keys first.premises), ("request", first.request), ("previous", first.key)] ++
    environment key (first :: rest)
private theorem shape : equation.body = .expression [.symbol "case", .var "receipts",
    .expression (cases.map fun row => .expression [row.1,row.2])] := by decide
private theorem clause (key : Atom) (entries : List Entry) :
    clauses program "hol-light:receipt-key-present" [key, table entries] =
      [.evaluate (environment key entries) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:receipt-key-present") = [equation] := rfl
  rw [unique]
  have formals : equation.arguments = [.var "key", .var "receipts"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (key : Atom) (entries : List Entry) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment key entries) state equation.body state (boolean (presentB key entries)) := by
  induction entries with
  | nil =>
      rw [shape]
      apply BoundCalls.CorePath.case_returns program (environment key []) (environment key []) state state state
        (.var "receipts") (.symbol "HOL:Nil") (boolean false) _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "receipts"
      · simp [cases, table, Premises.keys, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [presentB, boolean] using BoundCalls.CorePath.grounded_returns program (environment key []) state (.bool false)
  | cons first rest ih =>
      rw [shape]
      apply BoundCalls.CorePath.case_returns program (environment key (first :: rest)) (boundEnvironment key first rest) state state state
        (.var "receipts") (table (first :: rest)) consBody _ _ cases (read_cases_encoded cases)
      · exact BoundCalls.CorePath.variable_returns program _ state "receipts"
      · simp [cases, table, entryAtom, Premises.keys, environment, boundEnvironment, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        apply BoundCalls.CorePath.if_returns program (boundEnvironment key first rest) state state state
          (.expression [.symbol "==", .var "key", .var "previous"]) (boolean (key == first.key)) _ _ _
        · apply BoundCalls.CorePath.native_variable_call_returns program (boundEnvironment key first rest) state state "==" ["key","previous"]
            _ (by decide) (by decide) _ (by decide)
          simp [StdLib.structural_equality, boundEnvironment, environment, applySubst, Subst.lookup]
        · by_cases same : key = first.key
          · simpa [same, presentB, boolean, BEq.rfl] using BoundCalls.CorePath.grounded_returns program (boundEnvironment key first rest) state (.bool true)
          · simp only [beq_eq_false_iff_ne.mpr same]
            apply BoundCalls.CorePath.authored_variable_call_returns program (boundEnvironment key first rest) (environment key rest)
              state state "hol-light:receipt-key-present" ["key","rest"] equation.body _
              (by decide) (by decide) (by decide) _ _ (by decide)
            · simpa [boundEnvironment, environment, applySubst, Subst.lookup] using clause key rest
            · simpa [presentB, same, beq_eq_false_iff_ne.mpr same] using ih

/-- Every guard transition has a conservative certificate for arbitrary
finite receipt sequences, retaining complete keys, requests and occurrences. -/
theorem authored_receipt_key_present_certificate (bindings : Subst) (state : State) (key : Atom) (entries : List Entry)
    (keyName receiptsName : String) (keyCaptured : applySubst bindings (.var keyName) = key)
    (receiptsCaptured : applySubst bindings (.var receiptsName) = table entries) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:receipt-key-present", .var keyName, .var receiptsName]) state
      (boolean (presentB key entries)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment key entries) state state
    "hol-light:receipt-key-present" [keyName,receiptsName] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns key entries state) (by decide)
  simpa only [List.map_cons, List.map_nil, keyCaptured, receiptsCaptured] using clause key entries

/-- Actual inspection agrees with complete-key membership in the original
fragment, leaving the complete source store unchanged. -/
theorem authored_receipt_key_present_return (bindings : Subst) (state : State) (key : Atom) (entries : List Entry)
    (keyName receiptsName : String) (keyCaptured : applySubst bindings (.var keyName) = key)
    (receiptsCaptured : applySubst bindings (.var receiptsName) = table entries) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:receipt-key-present", .var keyName, .var receiptsName]) state
      (boolean (presentB key entries)) :=
  (authored_receipt_key_present_certificate bindings state key entries keyName receiptsName keyCaptured receiptsCaptured).original

/-- The same guard certificate supplies the captured-call execution; a key
comparison does not execute a function-shaped request or premise value. -/
theorem authored_receipt_key_present_bound_return (bindings : Subst) (state : State) (key : Atom) (entries : List Entry)
    (keyName receiptsName : String) (keyCaptured : applySubst bindings (.var keyName) = key)
    (receiptsCaptured : applySubst bindings (.var receiptsName) = table entries) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:receipt-key-present", .var keyName, .var receiptsName]) state
      (boolean (presentB key entries)) :=
  (authored_receipt_key_present_certificate bindings state key entries keyName receiptsName keyCaptured receiptsCaptured).extended

end Mettapedia.Languages.HOLLight.MeTTa.ReceiptKeys
