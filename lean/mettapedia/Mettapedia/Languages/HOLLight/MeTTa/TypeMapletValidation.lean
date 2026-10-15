import Mettapedia.Languages.HOLLight.MeTTa.TypeFormation
import Mettapedia.Languages.HOLLight.MeTTa.ProofLookup

/-!
# Executed type-maplet admission

The source guard checks both components of each maplet against the retained
signature, including keys ignored by type substitution. This is formation
admission, independently of the first-match substitution action. Operator
resolution does not assume the correct arity and can therefore yield refusal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeMapletValidation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation
open Eval
open Effects (State boolean)
open Representation (registeredOperatorAtom)
open TypeSubstitution (typeAtom maplets)

def admittedB (signature : Signature) (entries : List (Ty × Ty)) : Bool :=
  entries.all fun entry => typeFormedB signature entry.1 && typeFormedB signature entry.2

theorem admittedB_eq_true_iff (signature : Signature) (entries : List (Ty × Ty)) :
    admittedB signature entries = true ↔
      ∀ entry ∈ entries, TypeFormed signature entry.1 ∧ TypeFormed signature entry.2 := by
  simp only [admittedB, List.all_eq_true, Bool.and_eq_true, typeFormedB_eq_true_iff]

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:type-maplets-valid"))[0]'(by decide)
private def stateExpression : Atom := .expression [.symbol "HOL:State", .var "operators", .var "constants",
  .var "axioms", .var "cache", .var "receipts"]
private def consBody : Atom := .expression [.symbol "if",
  .expression [.symbol "hol-light:type-formed", .var "operators", .var "replacement"],
  .expression [.symbol "if", .expression [.symbol "hol-light:type-formed", .var "operators", .var "key"],
    .expression [.symbol "hol-light:type-maplets-valid", stateExpression, .var "rest"], boolean false], boolean false]
private def cases : SpaceSemantics.Cases :=
  [(.symbol "HOL:Nil", boolean true),
   (.expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Maplet", .var "replacement", .var "key"], .var "rest"], consBody),
   (.var "malformed", boolean false)]
private def environment (operators constants axioms receipts : Atom) (cache : List (Atom × Atom))
    (entries : Atom) : Subst :=
  [("entries", entries), ("receipts", receipts), ("cache", Lookup.table cache),
   ("axioms", axioms), ("constants", constants), ("operators", operators)]
private theorem shape : equation.body = .expression [.symbol "case", .var "entries",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (operators constants axioms receipts entries : Atom) (cache : List (Atom × Atom)) :
    clauses program "hol-light:type-maplets-valid"
      [ProofLookup.sourceState operators constants axioms receipts cache, entries] =
      [.evaluate (environment operators constants axioms receipts cache entries) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:type-maplets-valid") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [stateExpression, .var "entries"] := by decide
  simp [formals, stateExpression, ProofLookup.sourceState, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (world : DefinitionAdapters.TheoryContext) (table : OperatorTable.Table world)
    (origins : TypeOp → Atom) (constants axioms receipts : Atom) (cache : List (Atom × Atom))
    (entries : List (Ty × Ty))
    (resolved : ∀ entry ∈ entries, TypeFormation.Resolved world.signature entry.1 ∧
      TypeFormation.Resolved world.signature entry.2) (state : State) :
    PureReturns program (environment (OperatorTable.tableAtom table origins) constants axioms receipts cache
      (maplets registeredOperatorAtom entries)) state equation.body state (boolean (admittedB world.signature entries)) := by
  induction entries with
  | nil =>
      let before := environment (OperatorTable.tableAtom table origins) constants axioms receipts cache
        (maplets registeredOperatorAtom [])
      rw [shape]
      apply case_returns program before before state state state (.var "entries") (.symbol "HOL:Nil") (boolean true)
        _ _ cases (read_cases_encoded cases)
      · simpa [before, environment, maplets, Premises.keys, applySubst, Subst.lookup] using variable_returns program before state "entries"
      · simp [cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [admittedB, boolean] using grounded_returns program before state (.bool true)
  | cons entry rest ih =>
      rcases entry with ⟨replacement, key⟩
      let operators := OperatorTable.tableAtom table origins
      let before := environment operators constants axioms receipts cache (maplets registeredOperatorAtom ((replacement,key)::rest))
      let bound := [("rest", maplets registeredOperatorAtom rest), ("key", typeAtom registeredOperatorAtom key),
        ("replacement", typeAtom registeredOperatorAtom replacement)] ++ before
      have replacementReturned := TypeFormation.authored_type_formed_return world table origins bound state replacement
        (resolved (replacement,key) (by simp)).1 "operators" "replacement"
        (by simp [bound, before, environment, operators, applySubst, Subst.lookup])
        (by simp [bound, applySubst, Subst.lookup])
      have keyReturned := TypeFormation.authored_type_formed_return world table origins bound state key
        (resolved (replacement,key) (by simp)).2 "operators" "key"
        (by simp [bound, before, environment, operators, applySubst, Subst.lookup])
        (by simp [bound, applySubst, Subst.lookup])
      rw [shape]
      apply case_returns program before bound state state state (.var "entries")
        (maplets registeredOperatorAtom ((replacement,key)::rest)) consBody _ _ cases (read_cases_encoded cases)
      · simpa [before, environment, applySubst, Subst.lookup] using variable_returns program before state "entries"
      · simp [cases, maplets, Premises.keys, bound, before, environment, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        apply if_returns program bound state state state _ (boolean (typeFormedB world.signature replacement)) _ _ _
          replacementReturned
        cases replacementFormed : typeFormedB world.signature replacement with
        | false =>
            simpa [replacementFormed, admittedB, boolean] using grounded_returns program bound state (.bool false)
        | true =>
            simp only [boolean, BEq.rfl, ↓reduceIte]
            apply if_returns program bound state state state _ (boolean (typeFormedB world.signature key)) _ _ _ keyReturned
            cases keyFormed : typeFormedB world.signature key with
            | false =>
                simpa [replacementFormed, keyFormed, admittedB, boolean] using grounded_returns program bound state (.bool false)
            | true =>
                simp only [boolean, BEq.rfl, ↓reduceIte]
                have recursive := ih (fun entry member => resolved entry (by simp [member]))
                have returned : PureReturns program bound state
                    (.expression [.symbol "hol-light:type-maplets-valid", stateExpression, .var "rest"]) state
                    (boolean (admittedB world.signature rest)) := by
                  apply authored_binary_call_returns program bound
                    (environment operators constants axioms receipts cache (maplets registeredOperatorAtom rest))
                    state state state state "hol-light:type-maplets-valid" stateExpression (.var "rest")
                    (ProofLookup.sourceState operators constants axioms receipts cache) (maplets registeredOperatorAtom rest)
                    equation.body _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _
                    (clause operators constants axioms receipts _ cache) recursive (by decide)
                  · simpa [stateExpression, ProofLookup.sourceState, bound, before, environment, applySubst, Subst.lookup] using
                      constructor_variables_return program bound state "HOL:State"
                        ["operators","constants","axioms","cache","receipts"] (by decide) (by decide)
                  · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "rest"
                simpa only [admittedB, List.all_cons, replacementFormed, keyFormed, Bool.true_and, boolean] using returned

/-- All finite resolved source maplets execute the actual formation guard.
Resolved malformed arities return false rather than being assumed formed. -/
theorem authored_type_maplets_valid_return (world : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table world) (origins : TypeOp → Atom)
    (constants axioms receipts : Atom) (cache : List (Atom × Atom)) (entries : List (Ty × Ty))
    (resolved : ∀ entry ∈ entries, TypeFormation.Resolved world.signature entry.1 ∧
      TypeFormation.Resolved world.signature entry.2)
    (bindings : Subst) (state : State) (stateKey entriesKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) =
      ProofLookup.sourceState (OperatorTable.tableAtom table origins) constants axioms receipts cache)
    (entriesCaptured : applySubst bindings (.var entriesKey) = maplets registeredOperatorAtom entries) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:type-maplets-valid", .var stateKey, .var entriesKey]) state
      (boolean (admittedB world.signature entries)) := by
  apply authored_variable_call_returns program bindings
    (environment (OperatorTable.tableAtom table origins) constants axioms receipts cache (maplets registeredOperatorAtom entries))
    state state "hol-light:type-maplets-valid" [stateKey, entriesKey] equation.body _
    (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, entriesCaptured] using
      clause (OperatorTable.tableAtom table origins) constants axioms receipts (maplets registeredOperatorAtom entries) cache
  · exact body_returns world table origins constants axioms receipts cache entries resolved state

end Mettapedia.Languages.HOLLight.MeTTa.TypeMapletValidation
