import Mettapedia.Languages.HOLLight.MeTTa.Lookup

/-!
# Lookup in the authored HOL proof cache

The complete source state remains the argument of the actual known operation.
Only its cache is consulted, through the already proved finite-table helper.
First-match order is retained. Looking up a stored value does not establish
that its insertion was authorized; admission is a separate execution law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.ProofLookup

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)

def sourceState (operators constants axioms receipts : Atom) (cache : List (Atom × Atom)) : Atom :=
  .expression [.symbol "HOL:State", operators, constants, axioms, Lookup.table cache, receipts]

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:known"))[0]'(by decide)

private def environment (operators constants axioms receipts key : Atom) (cache : List (Atom × Atom)) : Subst :=
  [("key", key), ("receipts", receipts), ("cache", Lookup.table cache),
    ("axioms", axioms), ("constants", constants), ("operators", operators)]

private theorem body_shape : equation.body = .expression [.symbol "hol-light:lookup", .var "key", .var "cache"] := by decide

private theorem clause (operators constants axioms receipts key : Atom) (cache : List (Atom × Atom)) :
    clauses program "hol-light:known" [sourceState operators constants axioms receipts cache, key] =
      [.evaluate (environment operators constants axioms receipts key cache) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:known") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.expression [.symbol "HOL:State", .var "operators", .var "constants",
      .var "axioms", .var "cache", .var "receipts"], .var "key"] := by decide
  simp [formals, sourceState, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- The actual authored proof lookup computes the first cache entry while
retaining operators, definitions, commitments, receipts and the source store. -/
theorem authored_known_certificate (bindings : Subst) (state : State)
    (operators constants axioms receipts key : Atom) (cache : List (Atom × Atom))
    (stateKey proofKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = sourceState operators constants axioms receipts cache)
    (keyCaptured : applySubst bindings (.var proofKey) = key) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:known", .var stateKey, .var proofKey]) state
      (Lookup.answer (cache.lookup key)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings
    (environment operators constants axioms receipts key cache) state state
    "hol-light:known" [stateKey, proofKey] equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, keyCaptured] using
      clause operators constants axioms receipts key cache
  · rw [body_shape]
    exact Lookup.authored_lookup_certificate (environment operators constants axioms receipts key cache) state key cache
      "key" "cache" (by simp [environment, applySubst, Subst.lookup])
      (by simp [environment, applySubst, Subst.lookup])


/-- The certified cache path also runs in the original evaluator. -/
theorem authored_known_return (bindings : Subst) (state : State)
    (operators constants axioms receipts key : Atom) (cache : List (Atom × Atom))
    (stateKey proofKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = sourceState operators constants axioms receipts cache)
    (keyCaptured : applySubst bindings (.var proofKey) = key) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:known", .var stateKey, .var proofKey]) state
      (Lookup.answer (cache.lookup key)) :=
  (authored_known_certificate bindings state operators constants axioms receipts key cache
    stateKey proofKey stateCaptured keyCaptured).original

theorem missing_proof_refused (bindings : Subst) (state : State)
    (operators constants axioms receipts key : Atom) (cache : List (Atom × Atom))
    (stateKey proofKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = sourceState operators constants axioms receipts cache)
    (keyCaptured : applySubst bindings (.var proofKey) = key) (missing : cache.lookup key = none) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:known", .var stateKey, .var proofKey]) state (.symbol "None") := by
  simpa only [missing, Lookup.answer] using
    authored_known_return bindings state operators constants axioms receipts key cache
      stateKey proofKey stateCaptured keyCaptured

end Mettapedia.Languages.HOLLight.MeTTa.ProofLookup
