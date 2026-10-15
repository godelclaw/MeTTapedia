import Mettapedia.OSLF.NativeTypes.Certificates.FiniteTree
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementDecidableSyntax

/-!
# Executable certificates for the full native dependent judgments

The checker consumes the existing external native presentation, including all
dependent, proposition, refinement and logical-conversion rule codes. It does
not introduce a second type grammar or replace dependent families by object-sort
predicates. Checked substitution builds an actual substitution-rule occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.Refinement

open Mettapedia.TypeTheory.Calculi

universe u

variable {S : NativeDependent.Refinement.Symbols.{u}}

abbrev presentation (D : NativeDependent.Refinement.Signature S) : Presentation.{u} where
  Judgment := NativeDependent.Refinement.Judgment S
  Rule := NativeDependent.Refinement.RuleCode D
  conclusion := NativeDependent.Refinement.RuleCode.conclusion
  premises := NativeDependent.Refinement.RuleCode.premises

abbrev Certificate (D : NativeDependent.Refinement.Signature S) := Tree (presentation D)

variable {D : NativeDependent.Refinement.Signature S}
variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol]
  [DecidableEq S.PredicateSymbol]

def check (certificate : Certificate D) (judgment : NativeDependent.Refinement.Judgment S) : Bool :=
  certificate.check judgment

def erase {judgment : NativeDependent.Refinement.Judgment S}
    (derivation : NativeDependent.Refinement.Derivation D judgment) : Certificate D :=
  Tree.erase (P := presentation D) derivation

def reconstruct (certificate : Certificate D) (judgment : NativeDependent.Refinement.Judgment S)
    (accepted : check certificate judgment = true) :
    NativeDependent.Refinement.Derivation D judgment := Tree.reconstruct certificate judgment accepted

theorem check_exact (certificate : Certificate D) (judgment : NativeDependent.Refinement.Judgment S) :
    check certificate judgment = true ↔
      ∃ derivation : NativeDependent.Refinement.Derivation D judgment,
        erase derivation = certificate := Tree.check_exact (P := presentation D) certificate judgment

theorem check_complete (judgment : NativeDependent.Refinement.Judgment S) :
    Nonempty (NativeDependent.Refinement.Derivation D judgment) ↔
      ∃ certificate : Certificate D, check certificate judgment = true :=
  Tree.check_complete (P := presentation D) judgment

theorem check_erase {judgment : NativeDependent.Refinement.Judgment S}
    (derivation : NativeDependent.Refinement.Derivation D judgment) :
    check (erase derivation) judgment = true := Tree.check_erase (P := presentation D) derivation

theorem erase_reconstruct (certificate : Certificate D)
    (judgment : NativeDependent.Refinement.Judgment S) (accepted : check certificate judgment = true) :
    erase (reconstruct certificate judgment accepted) = certificate :=
  Tree.erase_reconstruct certificate judgment accepted

/-- Both supplied certificate occurrences remain separate under substitution. -/
def substituteTerm {n m : Nat}
    (source : NativeDependent.Refinement.ContextExpr S n)
    (target : NativeDependent.Refinement.ContextExpr S m)
    (substitution : NativeDependent.Refinement.Substitution S m n)
    (term : NativeDependent.Refinement.TermExpr S m)
    (type : NativeDependent.Refinement.TypeExpr S m)
    (substitutionCertificate termCertificate : Certificate D) : Certificate D :=
  .node (.substituteTerm source target substitution term type)
    (Fin.cases substitutionCertificate (fun _ => termCertificate))

theorem substituteTerm_checked {n m : Nat}
    (source : NativeDependent.Refinement.ContextExpr S n)
    (target : NativeDependent.Refinement.ContextExpr S m)
    (substitution : NativeDependent.Refinement.Substitution S m n)
    (term : NativeDependent.Refinement.TermExpr S m)
    (type : NativeDependent.Refinement.TypeExpr S m)
    (substitutionCertificate termCertificate : Certificate D)
    (substitutionChecked : check substitutionCertificate (.substitution source target substitution) = true)
    (termChecked : check termCertificate (.term target term type) = true) :
    check (substituteTerm source target substitution term type substitutionCertificate termCertificate)
      (.term source (term.substitute substitution) (type.substitute substitution)) = true := by
  simp only [check, substituteTerm, Tree.check, presentation,
    NativeDependent.Refinement.RuleCode.conclusion, NativeDependent.Refinement.RuleCode.premises,
    decide_true, Bool.true_and]
  apply decide_eq_true
  intro position
  cases position using Fin.cases with
  | zero => exact substitutionChecked
  | succ position =>
      cases position using Fin.cases with
      | zero => exact termChecked
      | succ impossible => exact Fin.elim0 impossible

theorem substituted_certificate_derives {n m : Nat}
    (source : NativeDependent.Refinement.ContextExpr S n)
    (target : NativeDependent.Refinement.ContextExpr S m)
    (substitution : NativeDependent.Refinement.Substitution S m n)
    (term : NativeDependent.Refinement.TermExpr S m)
    (type : NativeDependent.Refinement.TypeExpr S m)
    (substitutionCertificate termCertificate : Certificate D)
    (substitutionChecked : check substitutionCertificate (.substitution source target substitution) = true)
    (termChecked : check termCertificate (.term target term type) = true) :
    ∃ derivation : NativeDependent.Refinement.Derivation D
        (.term source (term.substitute substitution) (type.substitute substitution)),
      erase derivation = substituteTerm source target substitution term type
        substitutionCertificate termCertificate :=
  (check_exact _ _).mp (substituteTerm_checked source target substitution term type
    substitutionCertificate termCertificate substitutionChecked termChecked)

end Mettapedia.OSLF.NativeTypes.Certificates.Refinement
