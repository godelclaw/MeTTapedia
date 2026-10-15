import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.FixedPointSyntax
import Mettapedia.OSLF.NativeTypes.Certificates.Interpretation

/-!
# Finite native monotonicity certificates for arbitrary native operators

An operator is an ordinary term of type `(A → Prop) → (A → Prop)`.
Monotonicity is the ordinary higher-order native proposition quantified over
both complete predicates. The finite native rule-tree checker checks the
operator's typing and this proposition before emitting either derived formula.
The operator may use the complete native grammar.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneSyntax

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open FixedPointSyntax

universe v
variable {S : Symbols.{v}} {n m : Nat}

def operatorType (domain : TypeExpr S n) : TypeExpr S n :=
  .pi (predicateType domain) ((predicateType domain).rename Fin.succ)

def applyOperator (domain : TypeExpr S n) (operator candidate : TermExpr S n) : TermExpr S n :=
  .app (predicateType domain) ((predicateType domain).rename Fin.succ) operator candidate

def inclusion (domain : TypeExpr S n) (first second : TermExpr S n) : PropExpr S n :=
  .all domain (.implies
    (application (domain.rename Fin.succ) (first.rename Fin.succ) (.var 0))
    (application (domain.rename Fin.succ) (second.rename Fin.succ) (.var 0)))

def monotonicityAt (domain : TypeExpr S n) (operator first second : TermExpr S n) : PropExpr S n :=
  .implies (inclusion domain first second)
    (inclusion domain (applyOperator domain operator first) (applyOperator domain operator second))

def monotonicityUnderPredicate (domain : TypeExpr S n) (operator : TermExpr S n) : PropExpr S (n + 1) :=
  .all (predicateType (domain.rename Fin.succ))
    (monotonicityAt (domain.rename Fin.succ |>.rename Fin.succ)
      (operator.rename Fin.succ |>.rename Fin.succ) (.var 1) (.var 0))

/-- Both bound predicates range over the full native predicate type. -/
def monotonicity (domain : TypeExpr S n) (operator : TermExpr S n) : PropExpr S n :=
  .all (predicateType domain) (monotonicityUnderPredicate domain operator)

def prefixed (domain : TypeExpr S n) (operator : TermExpr S n) : PropExpr S (n + 1) :=
  inclusion (domain.rename Fin.succ)
    (applyOperator (domain.rename Fin.succ) (operator.rename Fin.succ) (.var 0)) (.var 0)

def postfixed (domain : TypeExpr S n) (operator : TermExpr S n) : PropExpr S (n + 1) :=
  inclusion (domain.rename Fin.succ) (.var 0)
    (applyOperator (domain.rename Fin.succ) (operator.rename Fin.succ) (.var 0))

def least (domain : TypeExpr S n) (operator tested : TermExpr S n) : PropExpr S n :=
  .all (predicateType domain)
    (.implies (prefixed domain operator)
      (application (domain.rename Fin.succ) (.var 0) (tested.rename Fin.succ)))

def greatest (domain : TypeExpr S n) (operator tested : TermExpr S n) : PropExpr S n :=
  .exists (predicateType domain)
    (.and (postfixed domain operator)
      (application (domain.rename Fin.succ) (.var 0) (tested.rename Fin.succ)))

variable (signature : Signature S)
variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

def check (context : ContextExpr S n) (domain : TypeExpr S n) (operator tested : TermExpr S n)
    (operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate signature) : Bool :=
  Certificates.Refinement.check operatorCertificate (.term context operator (operatorType domain)) &&
    Certificates.Refinement.check monotonicityCertificate (.entails context (monotonicity domain operator)) &&
    Certificates.Refinement.check argumentCertificate (.term context tested domain)

def generate (context : ContextExpr S n) (domain : TypeExpr S n) (operator tested : TermExpr S n)
    (operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate signature) : Option (PropExpr S n × PropExpr S n) :=
  if check signature context domain operator tested
      operatorCertificate monotonicityCertificate argumentCertificate then
    some (least domain operator tested, greatest domain operator tested) else none

theorem check_exact (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator tested : TermExpr S n)
    (operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate signature) :
    check signature context domain operator tested
        operatorCertificate monotonicityCertificate argumentCertificate = true ↔
      Certificates.Refinement.check operatorCertificate (.term context operator (operatorType domain)) = true ∧
      Certificates.Refinement.check monotonicityCertificate (.entails context (monotonicity domain operator)) = true ∧
      Certificates.Refinement.check argumentCertificate (.term context tested domain) = true := by
  simp only [check, Bool.and_eq_true]
  exact and_assoc

def checked_operator_derives (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator tested : TermExpr S n)
    (operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate signature)
    (accepted : check signature context domain operator tested
      operatorCertificate monotonicityCertificate argumentCertificate = true) :
    Derivation signature (.term context operator (operatorType domain)) :=
  Certificates.Refinement.reconstruct operatorCertificate _
    ((check_exact signature context domain operator tested _ _ _).mp accepted).1

def checked_monotonicity_derives (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator tested : TermExpr S n)
    (operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate signature)
    (accepted : check signature context domain operator tested
      operatorCertificate monotonicityCertificate argumentCertificate = true) :
    Derivation signature (.entails context (monotonicity domain operator)) :=
  Certificates.Refinement.reconstruct monotonicityCertificate _
    ((check_exact signature context domain operator tested _ _ _).mp accepted).2.1

theorem generate_of_checked (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator tested : TermExpr S n)
    (operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate signature)
    (accepted : check signature context domain operator tested
      operatorCertificate monotonicityCertificate argumentCertificate = true) :
    generate signature context domain operator tested
        operatorCertificate monotonicityCertificate argumentCertificate =
      some (least domain operator tested, greatest domain operator tested) := by
  simp only [generate, accepted, ↓reduceIte]

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneSyntax
