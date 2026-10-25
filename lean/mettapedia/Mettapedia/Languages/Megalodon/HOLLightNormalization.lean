import Mettapedia.Languages.Megalodon.RetainedNormalization
import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Logic.HOL.ProofSyntaxTypeSubstitution

/-!
# Megalodon normalization elaborated into HOL Light certificates

A successful finite beta/eta run on a supplied intrinsic monomorphic term
produces an ordinary retained equality proof. Its typed signature translation
then feeds the constructive HOL Light compiler. The resulting primitive graph
is checked at its exact conclusion, with eta admitted explicitly by policy.

Type variables, base types, named constants and primitive indices occupy
separate name classes. This comparison certifies the normalization equality;
it does not yet translate an arbitrary Megalodon proof term, definition
unfolding or prefix-polymorphic proof application.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLLightNormalization

open Mettapedia.Logic
open Mettapedia.Languages
open OpenTheory ReverseTranslation
open HenkinTermInterpretation

def variableName (index : Nat) : OpenTheory.Name := ⟨["Megalodon", "typeVariable"], toString index⟩
def baseName (index : Nat) : OpenTheory.Name := ⟨["Megalodon", "baseType"], toString index⟩

def atomic : HenkinTermInterpretation.Base → AtomicTy
  | .inl index => ⟨.var (variableName index), ⟨rfl, rfl⟩⟩
  | .inr index => ⟨.op (.mk (baseName index) .undefined) [], by
      constructor
      · rfl
      · apply Bool.eq_false_iff.mpr
        intro recognized
        have same := (OpenTheory.Ty.isBool_eq_true_iff _).mp recognized
        simp [OpenTheory.Ty.bool, TypeOp.bool, baseName, OpenTheory.Name.global] at same⟩

def base (sort : HenkinTermInterpretation.Base) : HOL.Ty AtomicTy := .base (atomic sort)

def constantName {environment : MathdataKernel.Environment} {type : HOL.Ty HenkinTermInterpretation.Base} :
    Constant environment type → OpenTheory.Name
  | .named name _ _ _ => ⟨["Megalodon", "named"], name⟩
  | .primitive index _ => ⟨["Megalodon", "primitive"], toString index⟩

def constant {environment : MathdataKernel.Environment} {type : HOL.Ty HenkinTermInterpretation.Base}
    (symbol : Constant environment type) : OpenTheory.Symbol (HOL.Ty.substitute base type) :=
  .constant (.mk (constantName symbol) .undefined) (reverseTy (HOL.Ty.substitute base type))
    (toHOL_reverseTy _)

variable {environment : MathdataKernel.Environment} {Γ : HOL.Ctx HenkinTermInterpretation.Base}
  {type : HOL.Ty HenkinTermInterpretation.Base}

def certificate (policy : AxiomPolicy) [DecidablePred policy] (eta : policy EtaAxiom.sequent)
    (fuel : Nat) (source : HOL.Term (Constant environment) Γ type) {raw target : MathdataKernel.Tm}
    (erased : erase source = some raw) (accepted : MathdataKernel.Tm.normalize fuel raw = some target)
    (names : Naming (Γ.map (HOL.Ty.substitute base))) (origin : HOLLight.ProofExecution.Origin) :=
  let retained := RetainedNormalization.readback fuel source erased accepted
  let proof := HOL.ProofSyntax.mapTypes base constant retained.val.proof
  HOLLight.RetainedCompilation.compile policy eta proof names origin

theorem certificate_accepted (policy : AxiomPolicy) [DecidablePred policy] (eta : policy EtaAxiom.sequent)
    (fuel : Nat) (source : HOL.Term (Constant environment) Γ type) {raw target : MathdataKernel.Tm}
    (erased : erase source = some raw) (accepted : MathdataKernel.Tm.normalize fuel raw = some target)
    (names : Naming (Γ.map (HOL.Ty.substitute base))) (origin : HOLLight.ProofExecution.Origin) :
    (HOLLight.ProofSystem.checker policy).check
      (certificate policy eta fuel source erased accepted names origin).proof.result
      (certificate policy eta fuel source erased accepted names origin).proof.certificate = true :=
  (certificate policy eta fuel source erased accepted names origin).proof.accepted

/-- The checked theorem has no logical assumptions and the exact translated
normalization equation. Source and target retain their native erasure evidence. -/
theorem certificate_sequent (policy : AxiomPolicy) [DecidablePred policy] (eta : policy EtaAxiom.sequent)
    (fuel : Nat) (source : HOL.Term (Constant environment) Γ type) {raw target : MathdataKernel.Tm}
    (erased : erase source = some raw) (accepted : MathdataKernel.Tm.normalize fuel raw = some target)
    (names : Naming (Γ.map (HOL.Ty.substitute base))) (origin : HOLLight.ProofExecution.Origin) :
    (certificate policy eta fuel source erased accepted names origin).proof.result.sequent =
      ⟨∅, reverseCanonical names (HOL.ImpredicativeConnectives.expand
        (HOL.mapTypes base constant (.eq source
          (RetainedNormalization.readback fuel source erased accepted).val.target)))⟩ :=
  Sequent.ext (certificate policy eta fuel source erased accepted names origin).hypotheses_exact
    (certificate policy eta fuel source erased accepted names origin).conclusion_exact

end Mettapedia.Languages.Megalodon.HOLLightNormalization
