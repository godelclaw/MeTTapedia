import Mettapedia.Logic.HOL.FiniteConstructorGuardRestrictions
import Mettapedia.Languages.HOLLight.ConstructorPayload

/-!
# Primitive membership certificates with a data restriction

The source proof supplies evidence that the first Boolean field is true before
introducing the restricted constructor guard. All beta, conjunction and
existential steps are retained and compiled under the empty axiom policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ConstructorPayloadRestrictions

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open RetainedCompilation ReverseTranslation
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def dataProof : HOL.ProofSyntax Symbol []
    (HOL.FiniteConstructorEncoding.applyArguments [.prop, .prop]
      ConstructorPayload.firstField (.top, .bot, PUnit.unit)) :=
  .impE (.eqPropER (ConstructorPayload.betaTwo .top .bot (.var (.vs .vz)))) .topI

theorem dataProof_free : dataProof.FunctionExtensionalityFree := by
  simp [dataProof, ConstructorPayload.betaTwo, HOL.ProofSyntax.FunctionExtensionalityFree]

def membership := HOL.FiniteConstructorEncoding.restrictedGuard_intro
  ConstructorPayload.signature ⟨0, by decide⟩ ConstructorPayload.firstField (.top, .bot, PUnit.unit) dataProof

theorem membership_free : membership.FunctionExtensionalityFree :=
  HOL.FiniteConstructorEncoding.restrictedGuard_intro_free _ _ _ _ _ dataProof_free

def native := compileWithoutFunctionExtensionality emptyAxiomPolicy membership membership_free
  Naming.empty ("restricted-payload-membership", 0)

theorem accepted : (ProofSystem.checker emptyAxiomPolicy).check native.proof.result native.proof.certificate = true :=
  native.proof.accepted

#print axioms membership
#print axioms accepted

end Mettapedia.Languages.HOLLight.ConstructorPayloadRestrictions
