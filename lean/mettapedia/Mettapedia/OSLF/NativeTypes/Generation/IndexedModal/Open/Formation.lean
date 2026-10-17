import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.Interpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureExtensionFormation

/-!
# Computed modal formation in the ambient focus signature

The original formation algorithm is instantiated at the curried focus
interfaces, then embedded rule by rule into the source-and-classifier
signature. Its certificate is consumed by the existing native checker.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.Formation

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

variable (installed : Joined.Installed)

theorem preservesCore :
    SignatureExtension.Preserves (SourceModel.coreSignature installed) (Interpretation.signature installed) where
  typeParameters _ := rfl
  termParameters _ := rfl
  predicateParameters _ := rfl
  termResult _ := rfl
  typeRank _ := rfl
  termRank _ := rfl
  predicateRank _ := rfl

def judgment (index : installed.Index) : Judgment installed.symbols :=
  .term ((Interpretation.signature installed).termParameters (installed.modalSymbol index))
    (.primitive (installed.modalSymbol index) TermExpr.var)
    ((Interpretation.signature installed).termResult (installed.modalSymbol index))

def tree (index : installed.Index) : Derivation (Interpretation.signature installed) (judgment installed index) :=
  SignatureExtension.derivation (SourceModel.coreSignature installed) (Interpretation.signature installed)
    (preservesCore installed)
    (SignatureSum.derivationRight installed.indexed.operational.signature
      (Declarations.signature installed.indexed.classifierVertex (CurriedInterfaces.interface installed.indexed))
      (Declarations.m_form installed.indexed.classifierVertex (CurriedInterfaces.interface installed.indexed) index))

def certificate (index : installed.Index) := Certificates.Refinement.erase (tree installed index)

/-- Arbitrary open arguments enter through the original typed substitution
rule, including every dependent index and target-continuation parameter. -/
def instantiate (index : installed.Index) {n : Nat} (context : ContextExpr installed.symbols n)
    (arguments : Substitution installed.symbols
      (installed.symbols.termArity (installed.modalSymbol index)) n)
    (typed : Derivation (Interpretation.signature installed)
      (.substitution context
        ((Interpretation.signature installed).termParameters (installed.modalSymbol index)) arguments)) :
    Derivation (Interpretation.signature installed)
      (.term context (.primitive (installed.modalSymbol index) arguments)
        (((Interpretation.signature installed).termResult (installed.modalSymbol index)).substitute arguments)) := by
  have result := deriveList (.substituteTerm context
    ((Interpretation.signature installed).termParameters (installed.modalSymbol index)) arguments
    (.primitive (installed.modalSymbol index) TermExpr.var)
    ((Interpretation.signature installed).termResult (installed.modalSymbol index)))
    (.cons typed (.cons (tree installed index) .nil))
  simpa only [RuleCode.conclusion, TermExpr.substitute] using result

theorem certificate_checked (index : installed.Index) :
    Certificates.Refinement.check (certificate installed index) (judgment installed index) = true :=
  Certificates.Refinement.check_erase (tree installed index)

theorem selected_check_exact (index : installed.Index) :
    Interpretation.check installed (certificate installed index) (judgment installed index) = .accepted ↔
      installed.indexed.operational.logic.permits (judgment installed index) ∧
      NativeLogic.CertificatePermitted installed.indexed.operational.logic (certificate installed index) := by
  rw [Interpretation.check_exact]
  exact ⟨fun accepted => ⟨accepted.1, accepted.2.1⟩,
    fun permitted => ⟨permitted.1, permitted.2, tree installed index, rfl⟩⟩

theorem full_check (index : installed.Index) :
    NativeLogic.check NativeLogic.full (certificate installed index) (judgment installed index) = .accepted := by
  unfold NativeLogic.check
  simp only [if_true, certificate, Certificates.Refinement.check_erase]

theorem meaning (index : installed.Index) :
    Interprets (Interpretation.model installed) (judgment installed index) :=
  Interpretation.sound installed (tree installed index)

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.Formation
