import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneGeneration

/-!
# Finite monotonicity certificate substitution

Typed native substitution constructs an actual substitution-rule occurrence
for the checked monotonicity proposition. The full generation check is
preserved using these finite certificates for the transported operator,
monotonicity premise and dependent tested argument.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneCertificateTransport

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Certificates NativeMonotoneSyntaxTransport

universe v
variable {S : Symbols.{v}} {signature : Signature S} {n m : Nat}
variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

def substituteMonotonicity (source : ContextExpr S n) (target : ContextExpr S m)
    (substitution : Substitution S m n) (domain : TypeExpr S m) (operator : TermExpr S m)
    (substitutionCertificate monotonicityCertificate : Certificates.Refinement.Certificate signature) :
    Certificates.Refinement.Certificate signature :=
  .node (.substituteEntailment source target substitution (NativeMonotoneSyntax.monotonicity domain operator))
    (Fin.cases substitutionCertificate (fun _ => monotonicityCertificate))

theorem substituteMonotonicity_checked (source : ContextExpr S n) (target : ContextExpr S m)
    (substitution : Substitution S m n) (domain : TypeExpr S m) (operator : TermExpr S m)
    (substitutionCertificate monotonicityCertificate : Certificates.Refinement.Certificate signature)
    (substitutionChecked : Certificates.Refinement.check substitutionCertificate (.substitution source target substitution) = true)
    (monotonicityChecked : Certificates.Refinement.check monotonicityCertificate
      (.entails target (NativeMonotoneSyntax.monotonicity domain operator)) = true) :
    Certificates.Refinement.check
      (substituteMonotonicity source target substitution domain operator substitutionCertificate monotonicityCertificate)
      (.entails source (NativeMonotoneSyntax.monotonicity (domain.substitute substitution) (operator.substitute substitution))) = true := by
  rw [← monotonicity_substitution]
  simp only [Certificates.Refinement.check, substituteMonotonicity, Tree.check,
    Certificates.Refinement.presentation, RuleCode.conclusion, RuleCode.premises, decide_true, Bool.true_and]
  apply decide_eq_true
  intro position
  cases position using Fin.cases with
  | zero => exact substitutionChecked
  | succ position =>
      cases position using Fin.cases with
      | zero => exact monotonicityChecked
      | succ impossible => exact Fin.elim0 impossible

theorem check_substitution (source : ContextExpr S n) (target : ContextExpr S m)
    (substitution : Substitution S m n) (domain : TypeExpr S m) (operator tested : TermExpr S m)
    (substitutionCertificate operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate signature)
    (substitutionChecked : Certificates.Refinement.check substitutionCertificate (.substitution source target substitution) = true)
    (accepted : NativeMonotoneSyntax.check signature target domain operator tested
      operatorCertificate monotonicityCertificate argumentCertificate = true) :
    NativeMonotoneSyntax.check signature source (domain.substitute substitution)
      (operator.substitute substitution) (tested.substitute substitution)
      (Certificates.Refinement.substituteTerm source target substitution operator
        (NativeMonotoneSyntax.operatorType domain) substitutionCertificate operatorCertificate)
      (substituteMonotonicity source target substitution domain operator substitutionCertificate monotonicityCertificate)
      (Certificates.Refinement.substituteTerm source target substitution tested domain
        substitutionCertificate argumentCertificate) = true := by
  have checked := (NativeMonotoneSyntax.check_exact signature target domain operator tested _ _ _).mp accepted
  apply (NativeMonotoneSyntax.check_exact signature source (domain.substitute substitution)
    (operator.substitute substitution) (tested.substitute substitution) _ _ _).mpr
  refine ⟨?_,substituteMonotonicity_checked source target substitution domain operator _ _ substitutionChecked checked.2.1,?_⟩
  · rw [← operatorType_substitution]
    exact Certificates.Refinement.substituteTerm_checked source target substitution operator
      (NativeMonotoneSyntax.operatorType domain) _ _ substitutionChecked checked.1
  · exact Certificates.Refinement.substituteTerm_checked source target substitution tested domain
      _ _ substitutionChecked checked.2.2

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneCertificateTransport
