import Mettapedia.Languages.Megalodon.HenkinTermInterpretation
import Mettapedia.Logic.HOL.NaturalClosure

/-!
# The natural closure predicate in Mathdata and intrinsic HOL

The definition uses only implication, universal quantification and simple
functions. Its independently typed HOL body erases to the native Mathdata
body. No zero/successor separation, injectivity, recursion or infinite-carrier
axiom is implicit in this predicate.

The accompanying Megalodon source proves closure and induction. Native replay
is a separate implementation gate; the syntactic comparisons here retain the
exact statements submitted there.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NaturalClosure

open Mettapedia.Logic.HOL
open MathdataKernel Mettapedia.Logic.HOL.NaturalClosure

def closureName : String :=
  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be"

def nativeType : Tp := .arr (.base 0) (.arr (.arr (.base 0) (.base 0))
  (.arr (.base 0) .prop))

/-- The definition printed by the independent Megalodon source checker. -/
def nativeBody : Tm :=
  .lam (.base 0) (.lam (.arr (.base 0) (.base 0)) (.lam (.base 0)
    (.all (.arr (.base 0) .prop)
      (.imp (.app (.db 0) (.db 3))
        (.imp (.all (.base 0) (.imp (.app (.db 1) (.db 0))
          (.app (.db 1) (.app (.db 3) (.db 0))))) (.app (.db 0) (.db 1)))))))

def environment : Environment :=
  { terms := [{ name := closureName, type := nativeType, definition := some nativeBody }] }

def nativePredicate (zero successor number : Tm) : Tm :=
  .app (.app (.app (.named closureName) zero) successor) number

def nativeZero : Tm := .all (.base 0) (.all (.arr (.base 0) (.base 0))
  (nativePredicate (.db 1) (.db 0) (.db 1)))

def nativeSuccessor : Tm := .all (.base 0) (.all (.arr (.base 0) (.base 0))
  (.all (.base 0) (.imp (nativePredicate (.db 2) (.db 1) (.db 0))
    (nativePredicate (.db 2) (.db 1) (.app (.db 1) (.db 0))))))

def nativeInduction : Tm := .all (.base 0) (.all (.arr (.base 0) (.base 0))
  (.all (.arr (.base 0) .prop) (.imp (.app (.db 0) (.db 2))
    (.imp (.all (.base 0) (.imp (nativePredicate (.db 3) (.db 2) (.db 0))
      (.imp (.app (.db 1) (.db 0)) (.app (.db 1) (.app (.db 2) (.db 0))))))
      (.all (.base 0) (.imp (nativePredicate (.db 3) (.db 2) (.db 0))
        (.app (.db 1) (.db 0))))))))

/-- The zero proof uses the base hypothesis, under exactly the source binders. -/
def zeroProof : Pf :=
  .termLam (.base 0) (.termLam (.arr (.base 0) (.base 0))
    (.termLam (.arr (.base 0) .prop) (.proofLam (.app (.db 0) (.db 2))
      (.proofLam (.all (.base 0) (.imp (.app (.db 1) (.db 0))
        (.app (.db 1) (.app (.db 2) (.db 0))))) (.hyp 1)))))

def successorProof : Pf :=
  .termLam (.base 0) (.termLam (.arr (.base 0) (.base 0)) (.termLam (.base 0)
    (.proofLam (nativePredicate (.db 2) (.db 1) (.db 0))
      (.termLam (.arr (.base 0) .prop) (.proofLam (.app (.db 0) (.db 3))
        (.proofLam (.all (.base 0) (.imp (.app (.db 1) (.db 0))
          (.app (.db 1) (.app (.db 3) (.db 0)))))
          (.proofApp (.termApp (.hyp 0) (.db 1))
            (.proofApp (.proofApp (.termApp (.hyp 2) (.db 0)) (.hyp 1)) (.hyp 0)))))))))

open HenkinTermInterpretation in
theorem body_erases :
    erase (body (.base (Sum.inr 0 : HenkinTermInterpretation.Base)) : ClosedTerm (Constant environment)
      (.base (.inr 0) ⇒ (.base (.inr 0) ⇒ .base (.inr 0)) ⇒ .base (.inr 0) ⇒ .prop)) =
      some nativeBody := rfl

theorem native_body_typed : inferTerm environment 0 [] nativeBody = some nativeType := by decide

theorem native_statements_formed :
    [nativeZero, nativeSuccessor, nativeInduction].all
      (checkProposition environment 0 []) = true := by decide

open HenkinTermInterpretation in
theorem zero_statement_erases :
    deltaNormalize environment 1 nativeZero =
      erase (zeroStatement (.base (.inr 0)) : ClosedFormula (Constant environment)) := by
  simp [nativeZero, nativePredicate, zeroStatement, predicate, body, declarationBody, nativeBody,
    environment, deltaNormalize, Environment.lookupTerm?, lookupTermList?, erase,
    reifyType, variableIndex]

open HenkinTermInterpretation in
theorem successor_statement_erases :
    deltaNormalize environment 1 nativeSuccessor =
      erase (successorStatement (.base (.inr 0)) : ClosedFormula (Constant environment)) := by
  simp [nativeSuccessor, nativePredicate, successorStatement, predicate, body, declarationBody, nativeBody,
    environment, deltaNormalize, Environment.lookupTerm?, lookupTermList?, erase,
    reifyType, variableIndex]

open HenkinTermInterpretation in
theorem induction_statement_erases :
    deltaNormalize environment 1 nativeInduction =
      erase (inductionStatement (.base (.inr 0)) : ClosedFormula (Constant environment)) := by
  simp [nativeInduction, nativePredicate, inductionStatement, predicate, body, declarationBody, nativeBody,
    environment, deltaNormalize, Environment.lookupTerm?, lookupTermList?, erase,
    reifyType, variableIndex]

theorem zero_proof_checked : checkProof environment 8 0 [] [] zeroProof nativeZero = true := by
  simp [checkProof, checkNormalizedProof, zeroProof, nativeZero, nativePredicate, nativeBody,
    environment, inferProof, inferTerm, normalize, deltaNormalize, Environment.lookupTerm?,
    lookupTermList?, Tm.normalize, Tm.normalizeOne, Tm.instantiate, Tm.instantiateAt,
    Tm.shift, Tp.plainWellFormed]

theorem successor_proof_checked :
    checkProof environment 8 0 [] [] successorProof nativeSuccessor = true := by
  simp [checkProof, checkNormalizedProof, successorProof, nativeSuccessor, nativePredicate,
    nativeBody, nativeType, environment, inferProof, inferTerm, normalize, deltaNormalize,
    Environment.lookupTerm?, lookupTermList?, Tm.normalize, Tm.normalizeOne,
    Tm.instantiate, Tm.instantiateAt, Tm.shift, Tp.plainWellFormed]

def verdicts : List (String × Bool) :=
  [("native natural closure body type", inferTerm environment 0 [] nativeBody == some nativeType),
   ("native natural statements formed", [nativeZero, nativeSuccessor, nativeInduction].all
     (checkProposition environment 0 [])),
   ("native zero proof", checkProof environment 8 0 [] [] zeroProof nativeZero),
   ("native successor proof", checkProof environment 8 0 [] [] successorProof nativeSuccessor),
   ("native altered conclusion refused", !checkProof environment 8 0 [] [] zeroProof
     (.all .prop (.db 0))),
   ("native unbound hypothesis refused", !checkProof environment 8 0 [] [] (.hyp 0) nativeZero)]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp [verdicts, nativeZero, nativeSuccessor, nativeInduction, nativeType, nativeBody,
    nativePredicate, zeroProof, successorProof, environment, checkProposition,
    checkProof, checkNormalizedProof, inferProof, inferTerm, normalize, deltaNormalize,
    Environment.lookupTerm?, lookupTermList?, Tm.normalize, Tm.normalizeOne,
    Tm.instantiate, Tm.instantiateAt, Tm.shift, Tp.plainWellFormed]

end Mettapedia.Languages.Megalodon.NaturalClosure
