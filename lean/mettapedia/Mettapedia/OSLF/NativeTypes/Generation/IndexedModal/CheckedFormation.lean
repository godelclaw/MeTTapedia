import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SharedChecking

/-! # Shared certificates at the joined indexed-modal checker -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Joined.Installed

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf

variable (installed : Joined.Installed)

abbrev SharedCertificate := SharedChecking.Certificate installed.signature

def checkShared (certificate : installed.SharedCertificate) (judgment : Judgment installed.symbols) :=
  SharedChecking.check installed.signature installed.indexed.operational.logic certificate judgment

theorem checkShared_exact (certificate : installed.SharedCertificate) (judgment : Judgment installed.symbols) :
    installed.checkShared certificate judgment = .accepted ↔
      ∃ derivation : Derivation installed.signature judgment,
        SharedChecking.reconstruct installed.signature certificate judgment = some derivation ∧
        installed.check (Certificates.Refinement.erase derivation) judgment = .accepted :=
  SharedChecking.check_exact installed.signature installed.indexed.operational.logic certificate judgment

def formationCertificate (index : installed.Index) :=
  SharedChecking.emit installed.signature (installed.m_form index)

def focusCertificate (index : installed.Index) :=
  SharedChecking.emit installed.signature (installed.focusClassifier index)

def focusEvidence (index : installed.Index) :=
  SourceInjection.classifierDerivation installed.indexed
    (SignatureSum.derivationRight installed.indexed.operational.signature installed.indexed.classifiers
      (Declarations.focusEvidenceFormed installed.indexed.classifierVertex installed.indexed.interfaces index))

def evidenceCertificate (index : installed.Index) :=
  SharedChecking.emit installed.signature (installed.focusEvidence index)

theorem formation_shared_checked (index : installed.Index) :
    SharedChecking.check installed.signature NativeLogic.full (installed.formationCertificate index)
      (SignatureSum.judgmentLeft (SignatureSum.judgmentRight
        (.term (SignatureSum.contextLeft (parameters (D := Pipeline.classifierSignature installed.indexed.operational)
          (installed.indexed.interfaces index)))
          (Declarations.modalCode (D := Pipeline.classifierSignature installed.indexed.operational)
            installed.indexed.interfaces index)
          (SignatureSum.typeLeft (result (D := Pipeline.classifierSignature installed.indexed.operational)
            (installed.indexed.interfaces index)))))) = .accepted :=
  SharedChecking.emit_checked _ _

def focusJudgment (index : installed.Index) : Judgment installed.symbols :=
  SignatureSum.judgmentLeft (SignatureSum.judgmentRight
    (.term (SignatureSum.contextLeft (parameters (D := Pipeline.classifierSignature installed.indexed.operational)
      (installed.indexed.interfaces index)))
      (Declarations.focusCode (D := Pipeline.classifierSignature installed.indexed.operational) installed.indexed.interfaces index)
      (Declarations.focusDomain (D := Pipeline.classifierSignature installed.indexed.operational) installed.indexed.interfaces index)))

theorem focus_shared_checked (index : installed.Index) :
    SharedChecking.check installed.signature NativeLogic.full (installed.focusCertificate index)
      (installed.focusJudgment index) = .accepted :=
  SharedChecking.emit_checked _ _

def evidenceJudgment (index : installed.Index) : Judgment installed.symbols :=
  SignatureSum.judgmentLeft (SignatureSum.judgmentRight
    (.term (SignatureSum.contextLeft (parameters (D := Pipeline.classifierSignature installed.indexed.operational)
      (installed.indexed.interfaces index)))
      (Declarations.focusEvidence (D := Pipeline.classifierSignature installed.indexed.operational) installed.indexed.interfaces index)
      ((Declarations.focusBody (D := Pipeline.classifierSignature installed.indexed.operational) installed.indexed.interfaces index).substitute
        (instantiate (Declarations.focusCode (D := Pipeline.classifierSignature installed.indexed.operational) installed.indexed.interfaces index)))))

theorem evidence_shared_checked (index : installed.Index) :
    SharedChecking.check installed.signature NativeLogic.full (installed.evidenceCertificate index)
      (installed.evidenceJudgment index) = .accepted :=
  SharedChecking.emit_checked _ _

/-- Existing native source values are admitted by the computed source-code
injection; this does not identify source carriers with code carriers. -/
def sourceCode {n : Nat} (carrier : NativeSignature.Carrier (NativeCubeProfile.language installed.indexed.operational))
    (context : ContextExpr installed.symbols n) (value : TermExpr installed.symbols n)
    (formed : Derivation installed.signature (.context context))
    (typed : Derivation installed.signature (.term context value ((SourceInjection.sourceType installed.indexed carrier).rename Fin.elim0))) :=
  SourceInjection.injectFormation installed.indexed carrier value formed typed

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Joined.Installed
