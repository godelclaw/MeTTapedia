import Mettapedia.Languages.Megalodon.HOLTermEncodingProofs
import Mettapedia.Languages.Megalodon.ExtensionalityAxioms
import Mettapedia.Languages.Megalodon.CheckedProofReconstruction

/-!
# Retained source proofs of the common Megalodon extensionality schemas

Primitive function and proposition equality derive the declared relation-equality
schemas in the existing extensional HOL source calculus. The actual normalization
runs then produce their precise native known-formula readings and retained proofs.
These proofs discharge the common profile's imported extensionality facts during
source reconstruction; a declaration lookup is not used as a proof of truth.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Megalodon.ExtensionalityAxiomProofs
open Mettapedia.Logic.HOL
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

def functional (domain result : Ty Base) :
    ProofSyntax Const [] (ExtensionalityAxioms.functional domain result) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply RelationEqualityComparison.ofPrimitive
  apply ProofSyntax.funExt
  exact RelationEqualityComparison.pointwiseToPrimitive (.hyp 0)

def propositional : ProofSyntax Const [] (ExtensionalityAxioms.propositional (Base := Base)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  exact RelationEqualityComparison.ofPrimitive (.eqPropI (.andEL (.hyp 0)) (.andER (.hyp 0)))

open HenkinTermInterpretation
variable {environment : MathdataKernel.Environment}

def normalize {formula : ClosedFormula (Constant environment)}
    (proof : ProofSyntax (Constant environment) [] formula) (fuel : Nat) {target : MathdataKernel.Tm}
    (completed : MathdataKernel.Tm.normalize fuel (HOLTermEncoding.native formula) = some target) :
    CheckedProofReconstruction.Result (environment := environment) (Γ := []) [] target := by
  let result := RetainedNormalization.readback fuel (HOLTermEncoding.encode formula)
    (HOLTermEncoding.native_erased formula) completed
  exact ⟨result.val.target, result.property,
    .impE (.eqPropEL result.val.proof) (HOLTermEncodingProofs.toEncoding proof)⟩

def functionalNative (domain result : Ty HenkinTermInterpretation.Base) :
    CheckedProofReconstruction.Result (environment := environment) (Γ := []) []
      (ExtensionalityAxioms.Native.functional (reifyType domain) (reifyType result)) :=
  normalize (functional domain result) 32 (ExtensionalityAxioms.Native.functional_normalizes domain result)

def propositionalNative : CheckedProofReconstruction.Result (environment := environment) (Γ := []) []
    ExtensionalityAxioms.Native.propositional :=
  normalize propositional 32 ExtensionalityAxioms.Native.propositional_normalizes

#print axioms functional
#print axioms propositional
#print axioms functionalNative
#print axioms propositionalNative
end Mettapedia.Languages.Megalodon.ExtensionalityAxiomProofs
