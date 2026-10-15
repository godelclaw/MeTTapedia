import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneComparison
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneSyntaxTransport
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneFormation

/-!
# Checked generation of arbitrary native operator fixed points

Successful finite checking extracts the actual authored operator and tested
argument from the original native evaluator. The emitted formulas compute
the independent least and greatest fixed points of that actual operator.
Every finite native typing and monotonicity derivation yields accepted
certificates for this same executable generation interface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneGeneration

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualLocalUniverses ContextualModelTelescopes
open NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PredicateVariables NativeMonotoneFunctions NativeMonotoneReadout NativeMonotoneCertificate
open NativeMonotoneBaseChange NativeMonotoneEvaluation NativeMonotoneComparison

universe u v
variable {C : Type u} [Category.{u} C] {S : Symbols.{v}} {signature : Signature S} {n : Nat}
variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]
attribute [local irreducible] NativeLocalTypeFormers.pi PresheafNativePropositionReadout.nativeOmega

theorem check_complete (context : ContextExpr S n) (domain : TypeExpr S n) (operator tested : TermExpr S n)
    (operatorTyped : Derivation signature (.term context operator (NativeMonotoneSyntax.operatorType domain)))
    (monotonicityProved : Derivation signature (.entails context (NativeMonotoneSyntax.monotonicity domain operator)))
    (argumentTyped : Derivation signature (.term context tested domain)) :
    NativeMonotoneSyntax.check signature context domain operator tested
      (Certificates.Refinement.erase operatorTyped) (Certificates.Refinement.erase monotonicityProved)
        (Certificates.Refinement.erase argumentTyped) = true := by
  simp only [NativeMonotoneSyntax.check, Certificates.Refinement.check_erase, Bool.and_self]

theorem finite_generation_complete (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator tested : TermExpr S n)
    (operatorTyped : Derivation signature (.term context operator (NativeMonotoneSyntax.operatorType domain)))
    (monotonicityProved : Derivation signature (.entails context (NativeMonotoneSyntax.monotonicity domain operator)))
    (argumentTyped : Derivation signature (.term context tested domain)) :
    NativeMonotoneSyntax.generate signature context domain operator tested
      (Certificates.Refinement.erase operatorTyped) (Certificates.Refinement.erase monotonicityProved)
        (Certificates.Refinement.erase argumentTyped) =
      some (NativeMonotoneSyntax.least domain operator tested, NativeMonotoneSyntax.greatest domain operator tested) :=
  NativeMonotoneSyntax.generate_of_checked signature context domain operator tested _ _ _
    (check_complete context domain operator tested operatorTyped monotonicityProved argumentTyped)

structure GeneratedFormulas (signature : Signature S) (n : Nat) where
  leastCode : PropExpr S n
  greatestCode : PropExpr S n
  leastCertificate : Certificates.Refinement.Certificate signature
  greatestCertificate : Certificates.Refinement.Certificate signature

/-- Generation retains independently checked formation evidence for both
emitted native formulas. Its inputs are finite native certificate trees. -/
def certifiedGenerate (context : ContextExpr S n) (domain : TypeExpr S n) (operator tested : TermExpr S n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate signature) : Option (GeneratedFormulas signature n) :=
  if contextAccepted : Certificates.Refinement.check contextCertificate (.context context) = true then
    if domainAccepted : Certificates.Refinement.check domainCertificate (.type context domain) = true then
      if accepted : NativeMonotoneSyntax.check signature context domain operator tested
          operatorCertificate monotonicityCertificate argumentCertificate = true then
        let formed := Certificates.Refinement.reconstruct contextCertificate _ contextAccepted
        let domainFormed := Certificates.Refinement.reconstruct domainCertificate _ domainAccepted
        let checked := (NativeMonotoneSyntax.check_exact signature context domain operator tested _ _ _).mp accepted
        let operatorTyped := Certificates.Refinement.reconstruct operatorCertificate _ checked.1
        let argumentTyped := Certificates.Refinement.reconstruct argumentCertificate _ checked.2.2
        some {
          leastCode := NativeMonotoneSyntax.least domain operator tested
          greatestCode := NativeMonotoneSyntax.greatest domain operator tested
          leastCertificate := Certificates.Refinement.erase
            (NativeMonotoneFormation.leastFormation context domain operator tested formed domainFormed operatorTyped argumentTyped)
          greatestCertificate := Certificates.Refinement.erase
            (NativeMonotoneFormation.greatestFormation context domain operator tested formed domainFormed operatorTyped argumentTyped) }
      else none
    else none
  else none

theorem certifiedGenerate_checked (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator tested : TermExpr S n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate signature)
    (generated : GeneratedFormulas signature n)
    (result : certifiedGenerate context domain operator tested contextCertificate domainCertificate
      operatorCertificate monotonicityCertificate argumentCertificate = some generated) :
    generated.leastCode = NativeMonotoneSyntax.least domain operator tested ∧
      generated.greatestCode = NativeMonotoneSyntax.greatest domain operator tested ∧
      Certificates.Refinement.check generated.leastCertificate (.predicate context generated.leastCode) = true ∧
      Certificates.Refinement.check generated.greatestCertificate (.predicate context generated.greatestCode) = true := by
  unfold certifiedGenerate at result
  split at result
  · split at result
    · split at result
      · cases Option.some.inj result
        exact ⟨rfl,rfl,Certificates.Refinement.check_erase _,Certificates.Refinement.check_erase _⟩
      · contradiction
    · contradiction
  · contradiction

theorem certifiedGenerate_isSome (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator tested : TermExpr S n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate signature) :
    (certifiedGenerate context domain operator tested contextCertificate domainCertificate
      operatorCertificate monotonicityCertificate argumentCertificate).isSome = true ↔
      Certificates.Refinement.check contextCertificate (.context context) = true ∧
      Certificates.Refinement.check domainCertificate (.type context domain) = true ∧
      NativeMonotoneSyntax.check signature context domain operator tested
        operatorCertificate monotonicityCertificate argumentCertificate = true := by
  unfold certifiedGenerate
  split
  · split
    · split <;> simp_all
    · simp_all
  · simp_all

theorem checked_values (model : ModelData S C) (realized : SignatureRealization model signature)
    (contextCode : ContextExpr S n) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode tested : TermExpr S n)
    (contextRead : model.evaluateContext contextCode = some context)
    (domainRead : model.evaluateType context domain = some A)
    (operatorCertificate monotonicityCertificate argumentCertificate : Certificates.Refinement.Certificate signature)
    (accepted : NativeMonotoneSyntax.check signature contextCode domain operatorCode tested
      operatorCertificate monotonicityCertificate argumentCertificate = true) :
    ∃ (operator : (operatorType A).decoded.sections) (value : A.decoded.sections),
      model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩ ∧
      model.evaluateTerm context tested = some ⟨A,value⟩ ∧ monotonicityMeaning A operator = ⊤ := by
  have checked := (NativeMonotoneSyntax.check_exact signature contextCode domain operatorCode tested _ _ _).mp accepted
  rcases (Certificates.Refinement.checked_native_sound model realized operatorCertificate _ checked.1).termAt
    context (operatorType A) contextRead (evaluate_operatorType model context domain A domainRead) with
      ⟨operator,operatorRead⟩
  rcases (Certificates.Refinement.checked_native_sound model realized argumentCertificate _ checked.2.2).termAt
    context A contextRead domainRead with ⟨value,valueRead⟩
  exact ⟨operator,value,operatorRead,valueRead,checked_monotonicity model realized contextCode context domain A
    operatorCode operator contextRead domainRead operatorRead monotonicityCertificate checked.2.1⟩

theorem generated_meanings (model : ModelData S C) (realized : SignatureRealization model signature)
    (contextCode : ContextExpr S n) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode tested : TermExpr S n)
    (contextRead : model.evaluateContext contextCode = some context)
    (domainRead : model.evaluateType context domain = some A)
    (operatorCertificate monotonicityCertificate argumentCertificate : Certificates.Refinement.Certificate signature)
    (accepted : NativeMonotoneSyntax.check signature contextCode domain operatorCode tested
      operatorCertificate monotonicityCertificate argumentCertificate = true) :
    ∃ (operator : (operatorType A).decoded.sections) (value : A.decoded.sections)
      (certified : monotonicityMeaning A operator = ⊤),
      model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩ ∧
      model.evaluateTerm context tested = some ⟨A,value⟩ ∧
      NativeMonotoneSyntax.generate signature contextCode domain operatorCode tested
        operatorCertificate monotonicityCertificate argumentCertificate =
          some (NativeMonotoneSyntax.least domain operatorCode tested, NativeMonotoneSyntax.greatest domain operatorCode tested) ∧
      model.evaluatePredicate context (NativeMonotoneSyntax.least domain operatorCode tested) =
        some ((NativeFixedPointEncodings.leastMeaning (semanticOperator A operator certified)).preimage
          (sectionLift A.decoded value)) ∧
      model.evaluatePredicate context (NativeMonotoneSyntax.greatest domain operatorCode tested) =
        some ((NativeFixedPointEncodings.greatestMeaning (semanticOperator A operator certified)).preimage
          (sectionLift A.decoded value)) := by
  rcases checked_values model realized contextCode context domain A operatorCode tested contextRead domainRead
    operatorCertificate monotonicityCertificate argumentCertificate accepted with
      ⟨operator,value,operatorRead,valueRead,certified⟩
  refine ⟨operator,value,certified,operatorRead,valueRead,
    NativeMonotoneSyntax.generate_of_checked signature contextCode domain operatorCode tested _ _ _ accepted,?_,?_⟩
  · exact (evaluate_least model context domain A operatorCode tested operator value domainRead operatorRead valueRead).trans
      (congrArg some (least_eq_meaning A operator certified value))
  · exact (evaluate_greatest model context domain A operatorCode tested operator value domainRead operatorRead valueRead).trans
      (congrArg some (greatest_eq_meaning A operator certified value))

/-- Every successful executable receipt has actual original-evaluator
context, dependent carrier, operator and argument values. Its two emitted
codes compute the independently specified lattice fixed points. -/
theorem certifiedGenerate_sound (model : ModelData S C) (realized : SignatureRealization model signature)
    (contextCode : ContextExpr S n) (domain : TypeExpr S n) (operatorCode tested : TermExpr S n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate signature)
    (generated : GeneratedFormulas signature n)
    (result : certifiedGenerate contextCode domain operatorCode tested contextCertificate domainCertificate
      operatorCertificate monotonicityCertificate argumentCertificate = some generated) :
    ∃ (context : Scope C n) (A : NativeType context.1)
      (operator : (operatorType A).decoded.sections) (value : A.decoded.sections)
      (certified : monotonicityMeaning A operator = ⊤),
      model.evaluateContext contextCode = some context ∧ model.evaluateType context domain = some A ∧
      model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩ ∧
      model.evaluateTerm context tested = some ⟨A,value⟩ ∧
      model.evaluatePredicate context generated.leastCode =
        some ((NativeFixedPointEncodings.leastMeaning (semanticOperator A operator certified)).preimage
          (sectionLift A.decoded value)) ∧
      model.evaluatePredicate context generated.greatestCode =
        some ((NativeFixedPointEncodings.greatestMeaning (semanticOperator A operator certified)).preimage
          (sectionLift A.decoded value)) := by
  have accepted := (certifiedGenerate_isSome contextCode domain operatorCode tested contextCertificate
    domainCertificate operatorCertificate monotonicityCertificate argumentCertificate).mp
      (show (certifiedGenerate contextCode domain operatorCode tested contextCertificate domainCertificate
        operatorCertificate monotonicityCertificate argumentCertificate).isSome = true by rw [result]; rfl)
  rcases Certificates.Refinement.checked_native_sound model realized contextCertificate _ accepted.1 with
    ⟨context,contextRead⟩
  rcases (Certificates.Refinement.checked_native_sound model realized domainCertificate _ accepted.2.1).typeAt
    context contextRead with ⟨A,domainRead⟩
  rcases generated_meanings model realized contextCode context domain A operatorCode tested contextRead domainRead
    operatorCertificate monotonicityCertificate argumentCertificate accepted.2.2 with
      ⟨operator,value,certified,operatorRead,valueRead,_,leastRead,greatestRead⟩
  have codes := certifiedGenerate_checked contextCode domain operatorCode tested contextCertificate domainCertificate
    operatorCertificate monotonicityCertificate argumentCertificate generated result
  rw [← codes.1] at leastRead
  rw [← codes.2.1] at greatestRead
  exact ⟨context,A,operator,value,certified,contextRead,domainRead,operatorRead,valueRead,leastRead,greatestRead⟩

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneGeneration
