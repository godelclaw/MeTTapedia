import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneCertificateControls
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneGeneration
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotonePredicates
import Mettapedia.OSLF.NativeTypes.Certificates.Controls

/-!
# Executing full quantified native monotonicity checks

The independent scalar presentation supplies the object declaration and a
real scoped argument. A native operator returns the quoted true predicate.
Its complete typing and quantified monotonicity certificates are checked by
the ordinary finite rule-tree checker. Replacing the quantified witness by a
well-formed proof of truth refuses fixed-point generation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneExecutionControls

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Controls
open NativeMonotoneSyntax NativeMonotoneCertificateControls

def domain : TypeExpr symbols 1 := scalar 1
def tested : TermExpr symbols 1 := .var 0
def operator : TermExpr symbols 1 := constantOperator domain (truthPredicate domain)

def domainFormed : Derivation signature (.type (.snoc .nil (scalar 0)) domain) :=
  scalarFormed scalarContext

def testedTyped : Derivation signature (.term (.snoc .nil (scalar 0)) tested domain) := by
  simpa only [RuleCode.conclusion, ContextExpr.lookup_zero, scalar_rename, domain, tested] using
    lookupVariable scalarContext 0

def operatorCertificate : Certificates.Refinement.Certificate signature :=
  Certificates.Refinement.erase
    (constantTyping _ domain (truthPredicate domain) scalarContext domainFormed
      (truthPredicateTyping _ domain scalarContext domainFormed))

def monotonicityCertificate : Certificates.Refinement.Certificate signature :=
  Certificates.Refinement.erase
    (constantMonotonicity _ domain (truthPredicate domain) scalarContext domainFormed
      (truthPredicateTyping _ domain scalarContext domainFormed))

def argumentCertificate : Certificates.Refinement.Certificate signature :=
  Certificates.Refinement.erase testedTyped

def accepted : Bool :=
  NativeMonotoneSyntax.check signature (.snoc .nil (scalar 0)) domain operator tested
    operatorCertificate monotonicityCertificate argumentCertificate

def malformed : Certificates.Refinement.Certificate signature :=
  wrongMonotonicity (.snoc .nil (scalar 0)) scalarContext

def refused : Bool :=
  NativeMonotoneSyntax.check signature (.snoc .nil (scalar 0)) domain operator tested
    operatorCertificate malformed argumentCertificate

theorem accepted_true : accepted = true :=
  constant_checked _ domain (truthPredicate domain) tested scalarContext domainFormed
    (truthPredicateTyping _ domain scalarContext domainFormed) testedTyped

theorem refused_false : refused = false := by
  simp only [refused, NativeMonotoneSyntax.check, malformed,
    wrongMonotonicity_rejected, Bool.and_false, Bool.false_and]

def contextCertificate : Certificates.Refinement.Certificate signature :=
  Certificates.Refinement.erase scalarContext

def domainCertificate : Certificates.Refinement.Certificate signature :=
  Certificates.Refinement.erase domainFormed

def certified : Option (NativeMonotoneGeneration.GeneratedFormulas signature 1) :=
  NativeMonotoneGeneration.certifiedGenerate (.snoc .nil (scalar 0)) domain operator tested
    contextCertificate domainCertificate operatorCertificate monotonicityCertificate argumentCertificate

def certifiedChecks : Bool :=
  match certified with
  | none => false
  | some output =>
      Certificates.Refinement.check output.leastCertificate
        (.predicate (.snoc .nil (scalar 0)) output.leastCode) &&
      Certificates.Refinement.check output.greatestCertificate
        (.predicate (.snoc .nil (scalar 0)) output.greatestCode)

theorem certified_present : certified.isSome = true := by
  apply (NativeMonotoneGeneration.certifiedGenerate_isSome _ _ _ _ _ _ _ _ _).mpr
  exact ⟨Certificates.Refinement.check_erase _, Certificates.Refinement.check_erase _, accepted_true⟩

def certifiedPredicates : Option (NativeMonotonePredicates.GeneratedPredicates signature 1) :=
  NativeMonotonePredicates.certifiedGenerate (.snoc .nil (scalar 0)) domain operator
    contextCertificate domainCertificate operatorCertificate monotonicityCertificate

def certifiedPredicateChecks : Bool :=
  match certifiedPredicates with
  | none => false
  | some output =>
      Certificates.Refinement.check output.leastCertificate
        (.term (.snoc .nil (scalar 0)) output.leastCode (FixedPointSyntax.predicateType domain)) &&
      Certificates.Refinement.check output.greatestCertificate
        (.term (.snoc .nil (scalar 0)) output.greatestCode (FixedPointSyntax.predicateType domain))

theorem certified_predicates_present : certifiedPredicates.isSome = true := by
  apply (NativeMonotonePredicates.certifiedGenerate_isSome _ _ _ _ _ _ _).mpr
  apply (NativeMonotonePredicates.checkInputs_exact _ _ _ _ _ _ _).mpr
  have acceptedInputs := (NativeMonotoneSyntax.check_exact signature _ _ _ _ _ _ _).mp accepted_true
  exact ⟨Certificates.Refinement.check_erase _, Certificates.Refinement.check_erase _,
    acceptedInputs.1, acceptedInputs.2.1⟩

#guard accepted
#guard !refused
#guard (NativeMonotoneSyntax.generate signature (.snoc .nil (scalar 0)) domain operator tested
  operatorCertificate malformed argumentCertificate).isNone
#guard certifiedChecks
#guard (NativeMonotoneGeneration.certifiedGenerate (.snoc .nil (scalar 0)) domain operator tested
  contextCertificate domainCertificate operatorCertificate malformed argumentCertificate).isNone
#guard certifiedPredicateChecks
#guard (NativeMonotonePredicates.certifiedGenerate (.snoc .nil (scalar 0)) domain operator
  contextCertificate domainCertificate operatorCertificate malformed).isNone

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneExecutionControls
