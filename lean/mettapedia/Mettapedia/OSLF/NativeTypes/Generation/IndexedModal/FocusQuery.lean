import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusOSLF

/-!
# Generated focus questions with retained membership certificates

The installation determines the family and its slots. A question supplies
finite semantic rely domains and a dependent executable postcondition.
Verification returns proof, an invalid certificate, or unfinished work.
It does not turn an invalid certificate into a semantic refutation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusQuery

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open FiniteFocusChecking

def formationJudgment (installed : Joined.Installed) (index : installed.Index) : Judgment installed.symbols :=
  SignatureSum.judgmentLeft (SignatureSum.judgmentRight
    (.term (SignatureSum.contextLeft (parameters (D := Pipeline.classifierSignature installed.indexed.operational)
      (installed.indexed.interfaces index)))
      (Declarations.modalCode (D := Pipeline.classifierSignature installed.indexed.operational)
        installed.indexed.interfaces index)
      (SignatureSum.typeLeft (result (D := Pipeline.classifierSignature installed.indexed.operational)
        (installed.indexed.interfaces index)))))

structure Question (installed : Joined.Installed) (ambient : List String) where
  index : installed.Index
  parameters : Parameters installed index ambient
  focus : Pattern
  nativeFormation : installed.checkShared (installed.formationCertificate index)
    (formationJudgment installed index) = .accepted

variable {installed : Joined.Installed} {ambient : List String}

/-- Full vocabulary uses the already proved checker law. Other fragments
run the identical checker and return its refusal reason. -/
def prepare (installed : Joined.Installed) (index : installed.Index)
    (parameters : Parameters installed index ambient) (focus : Pattern) :
    Except NativeLogic.CheckResult (Question installed ambient) :=
  if full : installed.indexed.operational.logic = NativeLogic.full then
    .ok ⟨index, parameters, focus, by
      change SharedChecking.check installed.signature installed.indexed.operational.logic
        (installed.formationCertificate index) (formationJudgment installed index) = .accepted
      rw [full]
      exact installed.formation_shared_checked index⟩
  else
    let result := installed.checkShared (installed.formationCertificate index) (formationJudgment installed index)
    if accepted : result = .accepted then .ok ⟨index, parameters, focus, accepted⟩ else .error result

theorem prepared_native_formation (question : Question installed ambient) :
    ∃ derivation : Derivation installed.signature (formationJudgment installed question.index),
      installed.check (Mettapedia.OSLF.NativeTypes.Certificates.Refinement.erase derivation)
        (formationJudgment installed question.index) = .accepted := by
  obtain ⟨derivation, _, checked⟩ :=
    (installed.checkShared_exact _ _).mp question.nativeFormation
  exact ⟨derivation, checked⟩

def Question.Meaning (question : Question installed ambient) : Prop :=
  (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
    (FocusOSLF.theory installed question.index ambient)).satisfies (S := ()) question.focus
      (FocusOSLF.nativeType question.parameters.meaning).pred

structure Verification (question : Question installed ambient) where
  certificate : List Witness
  session : Session question.parameters question.focus certificate

def verify (question : Question installed ambient) (certificate : List Witness) (budget : Nat) :
    Verification question :=
  ⟨certificate, (begin question.parameters question.focus certificate).resume budget⟩

def Verification.resume {question : Question installed ambient} (verification : Verification question) (budget : Nat) :
    Verification question :=
  ⟨verification.certificate, verification.session.resume budget⟩

def Verification.verdict {question : Question installed ambient} (verification : Verification question) : Verdict :=
  verification.session.verdict

theorem Verification.resume_add {question : Question installed ambient} (verification : Verification question)
    (first extra : Nat) : verification.resume (first + extra) = (verification.resume first).resume extra := by
  cases verification
  exact congrArg (Verification.mk _) (Session.resume_add _ first extra)

theorem Verification.proved {question : Question installed ambient} (verification : Verification question)
    (proved : verification.verdict = .proved) : question.Meaning :=
  verification.session.proved proved

theorem Verification.rejected {question : Question installed ambient} (verification : Verification question)
    (rejected : verification.verdict = .certificateRejected) :
    check question.parameters question.focus verification.certificate = false :=
  verification.session.rejected rejected

theorem verify_decided (question : Question installed ambient) (certificate : List Witness) (budget : Nat)
    (enough : (requests question.parameters).length ≤ budget) :
    (verify question certificate budget).verdict =
      if check question.parameters question.focus certificate then .proved else .certificateRejected :=
  check_decided question.parameters question.focus certificate budget enough

/-- Native membership has a finite certificate that verification accepts
within the computed request bound. This does not enumerate certificates. -/
theorem native_membership_iff_verified (question : Question installed ambient) :
    question.Meaning ↔
      ∃ certificate, (verify question certificate (requests question.parameters).length).verdict = .proved := by
  constructor
  · intro member
    obtain ⟨certificate, accepted⟩ := (FocusOSLF.native_membership_iff_certificate
      question.parameters question.focus).mp member
    refine ⟨certificate, ?_⟩
    rw [verify_decided _ _ _ (Nat.le_refl _), accepted]
    rfl
  · rintro ⟨certificate, proved⟩
    exact (verify question certificate _).proved proved

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusQuery
