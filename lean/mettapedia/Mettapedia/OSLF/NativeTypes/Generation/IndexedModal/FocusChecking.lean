import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Checking

/-! # Focus classifiers and their sort witnesses extracted by native rules -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Declarations

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open CubeEnrichment CubeNativeDeclarations

variable {D : CubeEnrichment.Signature} {I : Type}
    (vertex : Vertex D) (interfaces : I → Interface D.Carrier)

def focusDomain (index : I) : TypeExpr (Declarations.symbols (D := D) interfaces) (arity (interfaces index)) :=
  SignatureSum.typeLeft (codeType (interfaces index).focus (arity (interfaces index)))

def focusBody (index : I) : TypeExpr (Declarations.symbols (D := D) interfaces) (arity (interfaces index) + 1) :=
  SignatureSum.typeLeft (typingType (interfaces index).focus (.var 0)
    (sortCode (interfaces index).focus (interfaces index).resultSort _))

def focusCode (index : I) : TermExpr (Declarations.symbols (D := D) interfaces) (arity (interfaces index)) :=
  .fst (focusDomain interfaces index) (focusBody interfaces index) (modalCode interfaces index)

def focusEvidence (index : I) : TermExpr (Declarations.symbols (D := D) interfaces) (arity (interfaces index)) :=
  .snd (focusDomain interfaces index) (focusBody interfaces index) (modalCode interfaces index)

def focusDomainFormed (index : I) :=
  carry vertex interfaces (codeFormed vertex (interfaces index).focus
    (parametersFormed vertex (interfaces index)))

def focusBodyFormed (index : I) :=
  let prior := parametersFormed vertex (interfaces index)
  let extended := extendFormed vertex prior (codeFormed vertex (interfaces index).focus prior)
  carry vertex interfaces (typingFormed vertex (interfaces index).focus extended (.var 0)
    (sortCode (interfaces index).focus (interfaces index).resultSort _)
    (codeVariable vertex (interfaces index).focus prior)
    (sortFormed vertex (interfaces index).focus (interfaces index).resultSort extended))

def focusCodeFormed (index : I) : Derivation (Declarations.signature vertex interfaces)
    (.term (SignatureSum.contextLeft (parameters (interfaces index))) (focusCode interfaces index)
      (focusDomain interfaces index)) :=
  deriveList (.firstProjection _ (focusDomain interfaces index) (focusBody interfaces index) (modalCode interfaces index))
    (.cons (focusDomainFormed vertex interfaces index)
      (.cons (focusBodyFormed vertex interfaces index) (.cons (m_form vertex interfaces index) .nil)))

def focusEvidenceFormed (index : I) : Derivation (Declarations.signature vertex interfaces)
    (.term (SignatureSum.contextLeft (parameters (interfaces index))) (focusEvidence interfaces index)
      ((focusBody interfaces index).substitute (instantiate (focusCode interfaces index)))) :=
  deriveList (.secondProjection _ (focusDomain interfaces index) (focusBody interfaces index) (modalCode interfaces index))
    (.cons (focusDomainFormed vertex interfaces index)
      (.cons (focusBodyFormed vertex interfaces index) (.cons (m_form vertex interfaces index) .nil)))

variable [DecidableEq D.Carrier] [DecidableEq D.Former] [DecidableEq I]

theorem focus_code_checked (index : I) :
    Certificates.Refinement.check (Certificates.Refinement.erase (focusCodeFormed vertex interfaces index))
      (.term (SignatureSum.contextLeft (parameters (interfaces index))) (focusCode interfaces index)
        (focusDomain interfaces index)) = true :=
  Certificates.Refinement.check_erase (focusCodeFormed vertex interfaces index)

theorem focus_evidence_checked (index : I) :
    Certificates.Refinement.check (Certificates.Refinement.erase (focusEvidenceFormed vertex interfaces index))
      (.term (SignatureSum.contextLeft (parameters (interfaces index))) (focusEvidence interfaces index)
        ((focusBody interfaces index).substitute (instantiate (focusCode interfaces index)))) = true :=
  Certificates.Refinement.check_erase (focusEvidenceFormed vertex interfaces index)

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Declarations
