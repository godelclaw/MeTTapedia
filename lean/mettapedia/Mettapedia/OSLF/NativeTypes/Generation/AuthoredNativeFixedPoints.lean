import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeSemantics
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneGeneration
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotonePredicateReadout

/-!
# Checked fixed points in an authored native installation

The installed signature and selected vocabulary govern the original operator,
its full quantified monotonicity certificate and both emitted formulas.
Rejected evidence and refused vocabulary have distinct results.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf

variable (installed : AuthoredPipeline.Installed)

def checkedNativeCertificate (certificate : Certificates.Refinement.Certificate installed.signature)
    (judgment : Judgment installed.symbols) : Except NativeLogic.CheckResult Unit :=
  match installed.check certificate judgment with
  | .accepted => .ok ()
  | .certificateRejected => .error .certificateRejected
  | .vocabularyRefused => .error .vocabularyRefused

theorem checkedNativeCertificate_exact
    (certificate : Certificates.Refinement.Certificate installed.signature)
    (judgment : Judgment installed.symbols) :
    installed.checkedNativeCertificate certificate judgment = .ok () ↔
      installed.check certificate judgment = .accepted := by
  unfold checkedNativeCertificate
  cases installed.check certificate judgment <;> simp

def fixedPoints {n : Nat} (context : ContextExpr installed.symbols n)
    (domain : TypeExpr installed.symbols n) (operator tested : TermExpr installed.symbols n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate installed.signature) :
    Except NativeLogic.CheckResult (NativeMonotoneGeneration.GeneratedFormulas installed.signature n) := do
  installed.checkedNativeCertificate contextCertificate (.context context)
  installed.checkedNativeCertificate domainCertificate (.type context domain)
  installed.checkedNativeCertificate operatorCertificate
    (.term context operator (NativeMonotoneSyntax.operatorType domain))
  installed.checkedNativeCertificate monotonicityCertificate
    (.entails context (NativeMonotoneSyntax.monotonicity domain operator))
  installed.checkedNativeCertificate argumentCertificate (.term context tested domain)
  match NativeMonotoneGeneration.certifiedGenerate context domain operator tested
      contextCertificate domainCertificate operatorCertificate monotonicityCertificate argumentCertificate with
  | none => .error .certificateRejected
  | some generated =>
      installed.checkedNativeCertificate generated.leastCertificate (.predicate context generated.leastCode)
      installed.checkedNativeCertificate generated.greatestCertificate (.predicate context generated.greatestCode)
      return generated

theorem fixedPoints_checked {n : Nat} (context : ContextExpr installed.symbols n)
    (domain : TypeExpr installed.symbols n) (operator tested : TermExpr installed.symbols n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate installed.signature)
    (generated : NativeMonotoneGeneration.GeneratedFormulas installed.signature n)
    (result : installed.fixedPoints context domain operator tested contextCertificate domainCertificate
      operatorCertificate monotonicityCertificate argumentCertificate = .ok generated) :
    NativeMonotoneGeneration.certifiedGenerate context domain operator tested contextCertificate
      domainCertificate operatorCertificate monotonicityCertificate argumentCertificate = some generated ∧
      installed.check generated.leastCertificate (.predicate context generated.leastCode) = .accepted ∧
      installed.check generated.greatestCertificate (.predicate context generated.greatestCode) = .accepted := by
  unfold fixedPoints at result
  dsimp only [Bind.bind, Except.instMonad, Except.bind] at result
  split at result <;> try cases result
  split at result <;> try cases result
  split at result <;> try cases result
  split at result <;> try cases result
  split at result <;> try cases result
  split at result <;> try cases result
  rename_i output produced
  split at result <;> try cases result
  rename_i leastAccepted
  split at result <;> try cases result
  rename_i greatestAccepted
  exact ⟨produced,
    (installed.checkedNativeCertificate_exact _ _).mp (by simpa using leastAccepted),
    (installed.checkedNativeCertificate_exact _ _).mp (by simpa using greatestAccepted)⟩

theorem fixedPoints_semantic_formation {n : Nat} (context : ContextExpr installed.symbols n)
    (domain : TypeExpr installed.symbols n) (operator tested : TermExpr installed.symbols n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate argumentCertificate :
      Certificates.Refinement.Certificate installed.signature)
    (generated : NativeMonotoneGeneration.GeneratedFormulas installed.signature n)
    (result : installed.fixedPoints context domain operator tested contextCertificate domainCertificate
      operatorCertificate monotonicityCertificate argumentCertificate = .ok generated) :
    Interprets installed.generatedModel (.predicate context generated.leastCode) ∧
      Interprets installed.generatedModel (.predicate context generated.greatestCode) := by
  have checked := installed.fixedPoints_checked context domain operator tested contextCertificate
    domainCertificate operatorCertificate monotonicityCertificate argumentCertificate generated result
  exact ⟨installed.checked_semantic_sound _ _ checked.2.1,
    installed.checked_semantic_sound _ _ checked.2.2⟩

/-- Native predicate outputs require no chosen test argument. Each returned
term has the full native predicate function type, with its finite certificate. -/
def fixedPointPredicates {n : Nat} (context : ContextExpr installed.symbols n)
    (domain : TypeExpr installed.symbols n) (operator : TermExpr installed.symbols n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate :
      Certificates.Refinement.Certificate installed.signature) :
    Except NativeLogic.CheckResult (NativeMonotonePredicates.GeneratedPredicates installed.signature n) := do
  installed.checkedNativeCertificate contextCertificate (.context context)
  installed.checkedNativeCertificate domainCertificate (.type context domain)
  installed.checkedNativeCertificate operatorCertificate
    (.term context operator (NativeMonotoneSyntax.operatorType domain))
  installed.checkedNativeCertificate monotonicityCertificate
    (.entails context (NativeMonotoneSyntax.monotonicity domain operator))
  match NativeMonotonePredicates.certifiedGenerate context domain operator
      contextCertificate domainCertificate operatorCertificate monotonicityCertificate with
  | none => .error .certificateRejected
  | some generated =>
      installed.checkedNativeCertificate generated.leastCertificate
        (.term context generated.leastCode (FixedPointSyntax.predicateType domain))
      installed.checkedNativeCertificate generated.greatestCertificate
        (.term context generated.greatestCode (FixedPointSyntax.predicateType domain))
      return generated

theorem fixedPointPredicates_checked {n : Nat} (context : ContextExpr installed.symbols n)
    (domain : TypeExpr installed.symbols n) (operator : TermExpr installed.symbols n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate :
      Certificates.Refinement.Certificate installed.signature)
    (generated : NativeMonotonePredicates.GeneratedPredicates installed.signature n)
    (result : installed.fixedPointPredicates context domain operator contextCertificate domainCertificate
      operatorCertificate monotonicityCertificate = .ok generated) :
    NativeMonotonePredicates.certifiedGenerate context domain operator contextCertificate
      domainCertificate operatorCertificate monotonicityCertificate = some generated ∧
      installed.check generated.leastCertificate
        (.term context generated.leastCode (FixedPointSyntax.predicateType domain)) = .accepted ∧
      installed.check generated.greatestCertificate
        (.term context generated.greatestCode (FixedPointSyntax.predicateType domain)) = .accepted := by
  unfold fixedPointPredicates at result
  dsimp only [Bind.bind, Except.instMonad, Except.bind] at result
  split at result <;> try cases result
  split at result <;> try cases result
  split at result <;> try cases result
  split at result <;> try cases result
  split at result <;> try cases result
  rename_i output produced
  split at result <;> try cases result
  rename_i leastAccepted
  split at result <;> try cases result
  rename_i greatestAccepted
  exact ⟨produced,
    (installed.checkedNativeCertificate_exact _ _).mp (by simpa using leastAccepted),
    (installed.checkedNativeCertificate_exact _ _).mp (by simpa using greatestAccepted)⟩

theorem fixedPointPredicates_semantic_typing {n : Nat} (context : ContextExpr installed.symbols n)
    (domain : TypeExpr installed.symbols n) (operator : TermExpr installed.symbols n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate :
      Certificates.Refinement.Certificate installed.signature)
    (generated : NativeMonotonePredicates.GeneratedPredicates installed.signature n)
    (result : installed.fixedPointPredicates context domain operator contextCertificate domainCertificate
      operatorCertificate monotonicityCertificate = .ok generated) :
    Interprets installed.generatedModel
      (.term context generated.leastCode (FixedPointSyntax.predicateType domain)) ∧
      Interprets installed.generatedModel
        (.term context generated.greatestCode (FixedPointSyntax.predicateType domain)) := by
  have checked := installed.fixedPointPredicates_checked context domain operator contextCertificate
    domainCertificate operatorCertificate monotonicityCertificate generated result
  exact ⟨installed.checked_semantic_sound _ _ checked.2.1,
    installed.checked_semantic_sound _ _ checked.2.2⟩

open Mettapedia.TypeTheory.ContextualLocalUniverses
open Mettapedia.TypeTheory.NativeLocalTypeFormers
open NativeMonotoneFunctions NativeMonotoneReadout NativeMonotoneCertificate NativeMonotoneBaseChange PredicateVariables
open Mettapedia.GSLT.Topos.NativeFixedPointEncodings

/-- The complete native outputs denote the independent fixed points of the
operator that the installed evaluator actually reads from its input syntax. -/
theorem fixedPointPredicates_meaning {n : Nat} (contextCode : ContextExpr installed.symbols n)
    (domain : TypeExpr installed.symbols n) (operatorCode : TermExpr installed.symbols n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate :
      Certificates.Refinement.Certificate installed.signature)
    (generated : NativeMonotonePredicates.GeneratedPredicates installed.signature n)
    (result : installed.fixedPointPredicates contextCode domain operatorCode contextCertificate domainCertificate
      operatorCertificate monotonicityCertificate = .ok generated) :
    ∃ (context : Scope
        (CurriedBindingLanguage.Worlds (BindingPipeline.plan installed.operational.generated).snapshot.language) n)
      (A : NativeType context.1) (operator : (operatorType A).decoded.sections)
      (certified : monotonicityMeaning A operator = ⊤),
      installed.generatedModel.evaluateContext contextCode = some context ∧
      installed.generatedModel.evaluateType context domain = some A ∧
      installed.generatedModel.evaluateTerm context operatorCode = some ⟨operatorType A, operator⟩ ∧
      installed.generatedModel.evaluateTerm context generated.leastCode =
        some ⟨predicate A, predicateName A (leastMeaning (semanticOperator A operator certified))⟩ ∧
      installed.generatedModel.evaluateTerm context generated.greatestCode =
        some ⟨predicate A, predicateName A (greatestMeaning (semanticOperator A operator certified))⟩ := by
  exact NativeMonotonePredicateReadout.certifiedGenerate_sound installed.generatedModel
    installed.generatedModelRealization contextCode domain operatorCode contextCertificate domainCertificate
    operatorCertificate monotonicityCertificate generated
    (installed.fixedPointPredicates_checked contextCode domain operatorCode contextCertificate domainCertificate
      operatorCertificate monotonicityCertificate generated result).1

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed
