import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalEqualityInterpreter

/-!
# Native certificates for received annotated natural equalities

The receiver supplies a source-checked contextual equality and its retained
HOL proof. The established compiler constructs an original HOL Light
certificate under the empty axiom policy, with the exact translated
conclusion and hypothesis set. Selection and natural-recursion assumptions
remain hypotheses until discharged by separately qualified source facts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AnnotatedNaturalCompilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open NativeNaturalPredicateReading AnnotatedConversion CertificateInterpretation
open ReverseTranslation

variable {operations : Operations AtomicTy Symbol} {profile : Programs.ComputationProfiles.Selection}
    {Γ : HOL.Ctx AtomicTy} {context : CCtx Tower.Head Γ.length} {source target type : CTm Tower.Head Γ.length}

@[irreducible, noinline] def compile (received : CheckedEquality operations profile Γ context source target type)
    (names : Naming Γ) (origin : ProofExecution.Origin) :
    RetainedCompilation.Compiled emptyAxiomPolicy names
      ((assumptions operations Γ).map HOL.ImpredicativeConnectives.expand)
      (HOL.ImpredicativeConnectives.expand (.eq received.sourceState.code received.targetState.code)) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy
    received.rootProof received.rootProof_free names origin

theorem compile_accepted (received : CheckedEquality operations profile Γ context source target type)
    (names : Naming Γ) (origin : ProofExecution.Origin) :
    (ProofSystem.checker emptyAxiomPolicy).check (compile received names origin).proof.result
      (compile received names origin).proof.certificate = true :=
  (compile received names origin).proof.accepted

theorem compile_sequent (received : CheckedEquality operations profile Γ context source target type)
    (names : Naming Γ) (origin : ProofExecution.Origin) :
    (compile received names origin).proof.result.sequent.hyp =
        reverseHypotheses names ((assumptions operations Γ).map HOL.ImpredicativeConnectives.expand) ∧
      (compile received names origin).proof.result.sequent.concl =
        reverseCanonical names (HOL.ImpredicativeConnectives.expand
          (.eq received.sourceState.code received.targetState.code)) :=
  ⟨(compile received names origin).hypotheses_exact, (compile received names origin).conclusion_exact⟩

theorem compile_refuses_changed_conclusion (received : CheckedEquality operations profile Γ context source target type)
    (names : Naming Γ) (origin : ProofExecution.Origin) (claim : Theorem)
    (different : claim.sequent.concl ≠ reverseCanonical names (HOL.ImpredicativeConnectives.expand
      (.eq received.sourceState.code received.targetState.code))) :
    (ProofSystem.checker emptyAxiomPolicy).check claim (compile received names origin).proof.certificate = false := by
  simpa only [compile] using
    RetainedCompilation.compileWithoutFunctionExtensionality_refuses_changed_conclusion
      emptyAxiomPolicy received.rootProof received.rootProof_free names origin claim different

structure Result (operations : Operations AtomicTy Symbol) (profile : Programs.ComputationProfiles.Selection)
    (Γ : HOL.Ctx AtomicTy) (context : CCtx Tower.Head Γ.length) (source target type : CTm Tower.Head Γ.length)
    (names : Naming Γ) where
  received : CheckedEquality operations profile Γ context source target type
  compiled : RetainedCompilation.Compiled emptyAxiomPolicy names
    ((assumptions operations Γ).map HOL.ImpredicativeConnectives.expand)
    (HOL.ImpredicativeConnectives.expand (.eq received.sourceState.code received.targetState.code))

def checkAndCompile? [DecidableEq AtomicTy]
    (operations : Operations AtomicTy Symbol) (profile : Programs.ComputationProfiles.Selection)
    (Γ : HOL.Ctx AtomicTy) (context : CCtx Tower.Head Γ.length) (source target type : CTm Tower.Head Γ.length)
    (contextCertificate : Programs.Annotated.JudgmentReplay.ContextCertificate profile Γ.length)
    (certificate : Programs.Annotated.JudgmentReplay.Certificate profile)
    (names : Naming Γ) (origin : ProofExecution.Origin) :
    Option (Result operations profile Γ context source target type names) :=
  (CertificateInterpretation.check? operations profile Γ context source target type contextCertificate certificate).map
    fun received => ⟨received, compile received names origin⟩

#print axioms compile
#print axioms compile_accepted
#print axioms compile_sequent
#print axioms compile_refuses_changed_conclusion

end Mettapedia.Languages.HOLLight.AnnotatedNaturalCompilation
