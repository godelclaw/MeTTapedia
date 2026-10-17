import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusChecking
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.CheckingLaws
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.ReceiptChecking
import Mettapedia.OSLF.NativeTypes.Generation.BindingControls

/-! # Formation, carrier, vocabulary and authored-language separating controls -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Controls

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.MeTTaIL.Syntax

inductive Carrier where
  | focus
  | program
  deriving DecidableEq, Encodable, Repr

/-- Only the classifier alphabet is supplied here; the modal operations are
the generated declarations tested below. -/
abbrev alphabet : CubeEnrichment.Signature where
  Carrier := Carrier
  Former := Empty
  arity symbol := nomatch symbol
  input symbol := nomatch symbol
  output symbol := nomatch symbol

def vertex : CubeEnrichment.Vertex alphabet := fun impossible => nomatch impossible

def targetOnly : Interface Carrier := ⟨[], [], .program, .focus, .star⟩
def indexed : Interface Carrier := ⟨[(.focus, .star)], [(.program, .box)], .program, .focus, .box⟩
def interfaces : Fin 2 → Interface Carrier := Fin.cases targetOnly (fun _ => indexed)

def targetCertificate := Declarations.certificate vertex interfaces 0

def targetJudgment : Judgment (Declarations.symbols (D := alphabet) interfaces) :=
  .term (SignatureSum.contextLeft (parameters (D := alphabet) targetOnly)) (Declarations.modalCode (D := alphabet) interfaces 0)
    (SignatureSum.typeLeft (result (D := alphabet) targetOnly))

theorem target_formation_checked :
    Declarations.check vertex interfaces NativeLogic.full targetCertificate targetJudgment = .accepted :=
  Declarations.m_form_checked vertex interfaces 0

def wrongCarrierJudgment : Judgment (Declarations.symbols (D := alphabet) interfaces) :=
  .term (SignatureSum.contextLeft (parameters (D := alphabet) targetOnly)) (Declarations.modalCode (D := alphabet) interfaces 0)
    (SignatureSum.typeLeft (CubeNativeDeclarations.certifiedCode (D := alphabet) Carrier.program .star 1))

theorem source_carrier_rejected :
    Declarations.check vertex interfaces NativeLogic.full targetCertificate wrongCarrierJudgment = .certificateRejected :=
  full_check_erased_rejected (Declarations.m_form vertex interfaces 0) wrongCarrierJudgment (by decide)

def missingTargetJudgment : Judgment (Declarations.symbols (D := alphabet) interfaces) :=
  .term (.snoc .nil (SignatureSum.typeLeft (CubeNativeDeclarations.codeType (D := alphabet) Carrier.program 0)))
    (Declarations.modalCode (D := alphabet) interfaces 0) (SignatureSum.typeLeft (result (D := alphabet) targetOnly))

theorem unclassified_target_rejected :
    Declarations.check vertex interfaces NativeLogic.full targetCertificate missingTargetJudgment = .certificateRejected :=
  full_check_erased_rejected (Declarations.m_form vertex interfaces 0) missingTargetJudgment (by decide)

theorem target_required_at_empty_interface : arity (D := alphabet) targetOnly = 1 := by decide

theorem indexed_formation_checked :
    Declarations.check vertex interfaces NativeLogic.full (Declarations.certificate vertex interfaces 1)
      (.term (SignatureSum.contextLeft (parameters (D := alphabet) indexed)) (Declarations.modalCode (D := alphabet) interfaces 1)
        (SignatureSum.typeLeft (result (D := alphabet) indexed))) = .accepted :=
  Declarations.m_form_checked vertex interfaces 1

theorem focus_classifier_checked :
    Certificates.Refinement.check (Certificates.Refinement.erase (Declarations.focusCodeFormed vertex interfaces 1))
      (.term (SignatureSum.contextLeft (parameters (D := alphabet) indexed)) (Declarations.focusCode (D := alphabet) interfaces 1)
        (Declarations.focusDomain (D := alphabet) interfaces 1)) = true :=
  Declarations.focus_code_checked vertex interfaces 1

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Controls
