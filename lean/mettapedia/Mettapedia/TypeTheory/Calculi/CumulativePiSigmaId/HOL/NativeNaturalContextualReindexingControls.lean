import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalContextualNaturality
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalContextualControls

/-!
# Contextual substitution and permission controls

An open natural computation moves beneath an additional binder. A real caller
replaces the predecessor variable by zero in a dependent application. Closed
type-valued computations are embedded into the original open telescope, where
their domain annotations and predicate products remain checked separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.Contextual.ReindexingControls

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies
open AnnotatedConversion.Controls AnnotatedConversion.ReindexingControls Contextual.Controls

def openTelescope : Substitution operations profile [] operations.parameters .nil (Row.zero.context operations) where
  targetFormed := zeroInstance.contextFormed
  source := fun index => Fin.elim0 index
  target := fun index => nomatch index
  typed := fun index => Fin.elim0 index
  represented := fun index => nomatch index

def weakenedBinder := underBinder.substitute weaken
def instantiatedApplication := dependentApplication.substitute closeZero
def openAnnotation := annotationProof.substitute openTelescope
def openProduct := productProof.substitute openTelescope

theorem binder_natural : weakenedBinder.hol = weaken.proof underBinder.hol :=
  underBinder.hol_substitute weaken

theorem application_natural : instantiatedApplication.hol = closeZero.proof dependentApplication.hol :=
  dependentApplication.hol_substitute closeZero

theorem annotation_natural : openAnnotation.hol = openTelescope.proof annotationProof.hol :=
  annotationProof.hol_substitute openTelescope

theorem product_natural : openProduct.hol = openTelescope.proof productProof.hol :=
  productProof.hol_substitute openTelescope

theorem retained_renaming : HEq (HOL.ProofSyntax.rename (HOL.Rename.weaken (σ := operations.number)) mixedProof)
    (HOL.ProofSyntax.subst (HOL.Subst.ofRename (HOL.Rename.weaken (σ := operations.number))) mixedProof) :=
  HOL.ProofSyntax.rename_subst_heq _ mixedProof

theorem predicate_product_natural :
    HEq (HOL.ProofSyntax.subst openTelescope.target predicateProductProof)
      (HOL.PredicateProducts.congruence (HOL.ProofSyntax.subst openTelescope.target typeProof.hol)
        (HOL.ProofSyntax.castIndices (HOL.ProofSyntax.subst_weakenHyps openTelescope.target _) rfl
          (HOL.ProofSyntax.subst (HOL.Subst.lift openTelescope.target)
            (HOL.ProofSyntax.eqRefl
              (Δ := HOL.weakenHyps (σ := operations.number) (assumptions operations [])) naturalFamily.code)))) :=
  HOL.PredicateProducts.subst_congruence_heq openTelescope.target typeProof.hol _

theorem binder_work : weakenedBinder.work = 2 := by
  rw [weakenedBinder, Proof.work_substitute]
  simp only [underBinder, Proof.lam, Proof.work, zero_add, weakening_work]

theorem application_work : instantiatedApplication.work = 1 := by
  rw [instantiatedApplication, Proof.work_substitute]
  simp only [dependentApplication, Proof.app, Proof.work, numberProof,
    BubbleElaboration.stepCount_step, zero_add]

theorem binder_checked :
    ((underBinder.certificate.code).substitute SourceCertificates.substituteRoot (CTm.eraseSub weaken.source)).check
      Tower.rules.headEq (Programs.ComputationProfiles.decoder profile).decode
      (weaken.state (abstractionSource naturalDomain
        (weaken.state zeroInstance.source) (.sort _) open_lambda_formed (.sort _))).term.erase
      (weaken.state (abstractionTarget naturalDomain naturalDomain
        (weaken.state zeroInstance.source) (weaken.state identityBeta.source)
        (.sort _) open_lambda_formed (.sort _) (.refl naturalDomain.typed)
        (source_equal weakenedPath))).term.erase = true :=
  underBinder.substituted_checked weaken

/-- The typed annotation step survives context transport although the raw
lambda code does not record it. -/
theorem annotation_work_gap : openAnnotation.work = 1 ∧ openAnnotation.certificate.code.stepCount = 0 := by
  constructor
  · rw [openAnnotation, Proof.work_substitute, annotation_work]
  · rfl

def restrictedType : Proof operations profile (fun _ => false) typeBeta.source typeBeta.target
    (SourceCertificates.emit (.step (Step.beta (enabled := fun _ => false) typeBeta))).code :=
  .base (.step (.beta typeBeta))

def restrictedProduct := Proof.pi (.sort Tower.zero) (.sort Tower.zero) (.sorts Tower.zero Tower.zero)
  restrictedType (Proof.refl (enabled := fun _ => false) naturalFamily)

theorem permissions_commute :
    ((restrictedProduct.widen (large := profile) (fun _ _ => rfl)).substitute openTelescope).hol =
      ((restrictedProduct.substitute openTelescope).widen (large := profile) (fun _ _ => rfl)).hol :=
  restrictedProduct.hol_widen_substitute (fun _ _ => rfl) openTelescope

/-- Replacing the original natural row by reflexivity does not prove its
changed endpoint, even after the source caller has been transported. -/
theorem forged_binder_refused :
    (StructuralConversionCode.Code.refl
      (weaken.state (abstractionSource naturalDomain
        (weaken.state zeroInstance.source) (.sort _) open_lambda_formed (.sort _))).term.erase :
      SourceCertificates.Code 4).check Tower.rules.headEq
      (Programs.ComputationProfiles.decoder profile).decode
      (weaken.state (abstractionSource naturalDomain
        (weaken.state zeroInstance.source) (.sort _) open_lambda_formed (.sort _))).term.erase
      (weaken.state (abstractionTarget naturalDomain naturalDomain
        (weaken.state zeroInstance.source) (weaken.state identityBeta.source)
        (.sort _) open_lambda_formed (.sort _) (.refl naturalDomain.typed)
        (source_equal weakenedPath))).term.erase = false := by decide

theorem dependent_displayed_types_remain_distinct :
    (CTm.inst0 numberBeta.source.term methodFamily).subst closeZero.source ≠
      (CTm.inst0 numberBeta.target.term methodFamily).subst closeZero.source := by
  intro same
  cases same

#print axioms binder_natural
#print axioms application_natural
#print axioms product_natural
#print axioms permissions_commute
#print axioms annotation_work_gap
#print axioms forged_binder_refused
#print axioms dependent_displayed_types_remain_distinct

end AnnotatedConversion.Contextual.ReindexingControls
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
