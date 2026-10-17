import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Declarations
import Mettapedia.OSLF.NativeTypes.Generation.NativeLogicFragment

/-! # Indexed modal formation through the existing native certificate checker -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Declarations

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open CubeEnrichment

variable {D : CubeEnrichment.Signature} {I : Type}
    (vertex : Vertex D) (interfaces : I → Interface D.Carrier)

def modalCode (index : I) : TermExpr (symbols interfaces) (arity (interfaces index)) :=
  .primitive (.inr index) (fun position => .var position)

/-- Supplied arguments may contain ambient indices and dependent rely
continuations. Scope and typing are checked by the actual native substitution
judgment over the computed declaration header. -/
def m_form_at (index : I) {n : Nat} (context : ContextExpr (symbols interfaces) n)
    (arguments : Substitution (symbols interfaces) (arity (interfaces index)) n)
    (formed : Derivation (signature vertex interfaces) (.context context))
    (typed : Derivation (signature vertex interfaces)
      (.substitution context (SignatureSum.contextLeft (parameters (interfaces index))) arguments)) :
    Derivation (signature vertex interfaces) (.term context (.primitive (.inr index) arguments)
      ((SignatureSum.typeLeft (result (interfaces index))).substitute arguments)) :=
  let headers := headerFormation vertex interfaces
  deriveList (.primitive context (.inr index) arguments)
    (.cons formed (.cons (headers.termHeader (.inr index))
      (.cons (headers.termResult (.inr index)) (.cons typed .nil))))

/-- Formation consumes the entire computed parameter context. In particular,
the newest parameter is the dependent target classifier even with no relies. -/
def m_form (index : I) : Derivation (signature vertex interfaces)
    (.term (SignatureSum.contextLeft (parameters (interfaces index))) (modalCode interfaces index)
      (SignatureSum.typeLeft (result (interfaces index)))) := by
  let headers := headerFormation vertex interfaces
  let context : ContextExpr (symbols interfaces) (arity (interfaces index)) :=
    SignatureSum.contextLeft (parameters (interfaces index))
  let formed : Derivation (signature vertex interfaces) (.context context) :=
    headers.termHeader (.inr index)
  have tree := deriveList (.primitive context (.inr index) (fun position => .var position))
    (.cons formed (.cons formed (.cons (headers.termResult (.inr index))
      (.cons (deriveList (.substitutionIdentity context) (.cons formed .nil)) .nil))))
  change Derivation (signature vertex interfaces) (.term context (modalCode interfaces index)
    ((SignatureSum.typeLeft (result (interfaces index))).substitute (fun position => .var position))) at tree
  rw [TypeExpr.substitute_variables] at tree
  change Derivation (signature vertex interfaces) (.term context (modalCode interfaces index)
    ((SignatureSum.typeLeft (result (interfaces index))).rename id)) at tree
  rw [TypeExpr.rename_identity] at tree
  exact tree

def certificate (index : I) : Certificates.Refinement.Certificate (signature vertex interfaces) :=
  Certificates.Refinement.erase (m_form vertex interfaces index)

variable [DecidableEq D.Carrier] [DecidableEq D.Former] [DecidableEq I]

def check (fragment : NativeLogic.Fragment)
    (certificate : Certificates.Refinement.Certificate (signature vertex interfaces))
    (judgment : Judgment (symbols interfaces)) : NativeLogic.CheckResult :=
  NativeLogic.check fragment certificate judgment

theorem check_exact (fragment : NativeLogic.Fragment)
    (certificate : Certificates.Refinement.Certificate (signature vertex interfaces))
    (judgment : Judgment (symbols interfaces)) :
    check vertex interfaces fragment certificate judgment = .accepted ↔
      fragment.permits judgment ∧ NativeLogic.CertificatePermitted fragment certificate ∧
      ∃ derivation : Derivation (signature vertex interfaces) judgment,
        Certificates.Refinement.erase derivation = certificate :=
  NativeLogic.check_exact fragment certificate judgment

theorem m_form_checked (index : I) :
    check vertex interfaces NativeLogic.full (certificate vertex interfaces index)
      (.term (SignatureSum.contextLeft (parameters (interfaces index))) (modalCode interfaces index)
        (SignatureSum.typeLeft (result (interfaces index)))) = .accepted := by
  unfold check NativeLogic.check
  simp only [if_true, certificate, Certificates.Refinement.check_erase]

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Declarations
