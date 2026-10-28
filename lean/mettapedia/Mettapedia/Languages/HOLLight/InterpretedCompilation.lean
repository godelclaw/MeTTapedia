import Mettapedia.Logic.HOL.ProofSyntaxInterpretation
import Mettapedia.Languages.HOLLight.RetainedCompilation

/-!
# Compiling retained proofs through a typed term interpretation

The source signature may use its own base types and constants. Its explicit
interpretation supplies closed terms at the native HOL types. Compilation
retains the complete translated hypothesis set and conclusion; source facts
must discharge those hypotheses separately.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.InterpretedCompilation
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
  (interpretation : HOL.TermInterpretation Base Const AtomicTy Symbol)
  {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {formula : HOL.Formula Const Γ}

@[irreducible, noinline] def compile (proof : HOL.ProofSyntax Const Δ formula)
    (free : proof.FunctionExtensionalityFree)
    (names : Naming (Γ.map (HOL.Ty.substitute interpretation.types))) (origin : ProofExecution.Origin) :
    RetainedCompilation.Compiled emptyAxiomPolicy names
      ((Δ.map interpretation.term).map HOL.ImpredicativeConnectives.expand)
      (HOL.ImpredicativeConnectives.expand (interpretation.term formula)) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy
    (interpretation.proof proof) (interpretation.proof_free proof free) names origin

theorem accepted (proof : HOL.ProofSyntax Const Δ formula) (free : proof.FunctionExtensionalityFree)
    (names : Naming (Γ.map (HOL.Ty.substitute interpretation.types))) (origin : ProofExecution.Origin) :
    (ProofSystem.checker emptyAxiomPolicy).check (compile interpretation proof free names origin).proof.result
      (compile interpretation proof free names origin).proof.certificate = true :=
  (compile interpretation proof free names origin).proof.accepted

theorem sequent (proof : HOL.ProofSyntax Const Δ formula) (free : proof.FunctionExtensionalityFree)
    (names : Naming (Γ.map (HOL.Ty.substitute interpretation.types))) (origin : ProofExecution.Origin) :
    (compile interpretation proof free names origin).proof.result.sequent.hyp =
      reverseHypotheses names ((Δ.map interpretation.term).map HOL.ImpredicativeConnectives.expand) ∧
    (compile interpretation proof free names origin).proof.result.sequent.concl =
      reverseCanonical names (HOL.ImpredicativeConnectives.expand (interpretation.term formula)) :=
  ⟨(compile interpretation proof free names origin).hypotheses_exact,
    (compile interpretation proof free names origin).conclusion_exact⟩

theorem axioms_empty (proof : HOL.ProofSyntax Const Δ formula) (free : proof.FunctionExtensionalityFree)
    (names : Naming (Γ.map (HOL.Ty.substitute interpretation.types))) (origin : ProofExecution.Origin) :
    (compile interpretation proof free names origin).proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _ (accepted interpretation proof free names origin)))

theorem refuses_changed_conclusion (proof : HOL.ProofSyntax Const Δ formula) (free : proof.FunctionExtensionalityFree)
    (names : Naming (Γ.map (HOL.Ty.substitute interpretation.types))) (origin : ProofExecution.Origin)
    (claim : Theorem)
    (different : claim.sequent.concl ≠ reverseCanonical names
      (HOL.ImpredicativeConnectives.expand (interpretation.term formula))) :
    (ProofSystem.checker emptyAxiomPolicy).check claim (compile interpretation proof free names origin).proof.certificate = false :=
  (compile interpretation proof free names origin).proof.refuses_changed_conclusion claim
    (by simpa only [(compile interpretation proof free names origin).conclusion_exact] using different)

#print axioms accepted
#print axioms sequent
#print axioms axioms_empty
#print axioms refuses_changed_conclusion
end Mettapedia.Languages.HOLLight.InterpretedCompilation
