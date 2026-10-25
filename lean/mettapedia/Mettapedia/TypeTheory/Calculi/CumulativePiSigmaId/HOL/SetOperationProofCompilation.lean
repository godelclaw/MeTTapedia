import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationExtensionalOperations
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLImpredicativeProofCompilation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationPredicateProofs

/-!
# Total retained HOL proof compilation at the material signature

Every retained source proof compiles through the explicit extensional profile.
The computed native term is typed at the represented conclusion in the same
object context and expanded ordered hypothesis environment. Native substitution
commutes with the actual output. The source uses all 29 proof constructors.

The constructive profile and this extensional extension remain distinct:
propositional extensionality is unavailable in the former, while its concrete
four-argument application is produced here. This module establishes compilation
and typing; interpreting the resulting proof terms is a separate construction.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationProofCompilation
open Presentation Presentation.FormationSensitive FormationSensitiveHOLInterface
open Mettapedia.Logic HOL.Embedding.ZFSetHenkinInterpretation
open SetOperationSignature (proofName)
open SetOperationExtensionalProfile (reading)
open SetOperationExtensionalOperations (operations total natural)

def compile {Γ : HOL.Ctx Unit} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (source : HOL.ProofSyntax Symbol Δ φ) {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) : Tower.Tm n :=
  HOLImpredicativeProofCompilation.translateProof reading proofName operations total source objects hypotheses

theorem compile_typed {Γ : HOL.Ctx Unit} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (source : HOL.ProofSyntax Symbol Δ φ) {n : Nat} {context : Tower.Ctx n}
    {objects : Sub Tower.Head Γ.length n}
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (objectTyped : HOLNativeGenericProofCompiler.GenericTyping.Objects reading context objects)
    (hypothesisTyped : HOLNativeGenericProofCompiler.GenericTyping.Hypotheses reading operations context objects hypotheses) :
    Typing operations.target context (compile source objects hypotheses)
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (subst objects (HOLImpredicativeRepresentation.translate reading φ))) :=
  HOLImpredicativeProofCompilation.translateProof_typed reading proofName operations total source
    objectTyped hypothesisTyped

theorem compile_closed_typed {φ : HOL.ClosedFormula Symbol} (source : HOL.ProofSyntax Symbol [] φ) :
    Typing operations.target .nil (compile source Fin.elim0 Fin.elim0)
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (HOLImpredicativeRepresentation.translate reading φ)) :=
  HOLImpredicativeProofCompilation.translateProof_closed_typed reading proofName operations total source

theorem compile_substitute {Γ : HOL.Ctx Unit} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (source : HOL.ProofSyntax Symbol Δ φ) {n m : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n)
    (sigma : Sub Tower.Head n m) :
    compile source (fun index => subst sigma (objects index)) (fun index => subst sigma (hypotheses index)) =
      subst sigma (compile source objects hypotheses) :=
  HOLImpredicativeProofCompilation.translateProof_substitute reading proofName operations total natural
    source objects hypotheses sigma

def extensionalTruthProgram : Tower.Tm 0 :=
  SetOperationExtensionalApplications.propositionExtensionalityApp
    (HOLImpredicativeRepresentation.translate reading (HOL.Term.top : HOL.ClosedFormula Symbol))
    (HOLImpredicativeRepresentation.translate reading (HOL.Term.top : HOL.ClosedFormula Symbol))
    (.lam (.var 0)) (.lam (.var 0))

theorem extensionalTruth_compiles :
    compile SetOperationPredicateProofs.extensionalTruth Fin.elim0 Fin.elim0 = extensionalTruthProgram := rfl

theorem extensionalTruth_typed :
    Typing operations.target .nil extensionalTruthProgram
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (HOLImpredicativeRepresentation.translate reading
          (HOL.Term.eq .top .top : HOL.ClosedFormula Symbol))) := by
  rw [← extensionalTruth_compiles]
  exact HOLImpredicativeProofCompilation.translateProof_closed_typed
    reading proofName operations total SetOperationPredicateProofs.extensionalTruth

theorem proposition_extension_is_explicit :
    SetOperationPredicateProofs.operations.target.constantType
      SetOperationExtensionalProfile.propositionExtensionalityName = none ∧
    operations.target.constantType SetOperationExtensionalProfile.propositionExtensionalityName =
      some SetOperationExtensionalProfile.propositionExtensionalityType := by decide

theorem function_extension_is_explicit :
    SetOperationPredicateProofs.operations.target.constantType
      SetOperationExtensionalProfile.functionExtensionalityName = none ∧
    operations.target.constantType SetOperationExtensionalProfile.functionExtensionalityName =
      some SetOperationExtensionalProfile.functionExtensionalityType := by decide

#print axioms compile_typed
#print axioms compile_closed_typed
#print axioms compile_substitute
#print axioms extensionalTruth_compiles
#print axioms extensionalTruth_typed
#print axioms proposition_extension_is_explicit
#print axioms function_extension_is_explicit
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationProofCompilation
