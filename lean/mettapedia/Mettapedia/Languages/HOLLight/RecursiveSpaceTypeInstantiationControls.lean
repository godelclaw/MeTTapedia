import Mettapedia.Languages.HOLLight.RecursiveSpaceFunctionPayload
import Mettapedia.Languages.HOLLight.VectorContainerGuardSource

/-!
# Type-instance and root-readback controls

A small registered REFL input exercises the six-command instantiation batch.
All six proof commands check, but their conclusions are deliberately not the
recursive-space roots, so the combined root receiver refuses them. The full
source-history control is run by `hol_light_indexed_export.lean`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RecursiveSpaceTypeInstantiation.Controls

open Mettapedia.Languages.OpenTheory ProofExecution
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def signature : List (List Ty) := [[], [Ty.var RegisteredSubstitution.Controls.parameter, Ty.bool]]
def entries := [(RegisteredSubstitution.Controls.parameter, constructorPayload signature)]
def indices : RecursiveSpaceSourceReadback.CacheIndices := ⟨0, 0, 0, 0, 0, 0⟩
def before := RegisteredSubstitution.Controls.before

def operations : RecursiveSpaceSourceReadback.Operations :=
  ⟨Ty.bool, Ty.var RegisteredSubstitution.Controls.parameter, Ty.bool,
    .mk (Name.global "zero") .undefined, .mk (Name.global "numeral") .undefined,
    .mk (Name.global "successor") .undefined, .mk (Name.global "bottom") .undefined,
    .mk (Name.global "constructor") .undefined⟩

theorem simultaneous_payload :
    (Operations.instantiate operations (effectiveTypes entries)).payload =
      constructorPayload signature :=
  RecursiveSpaceFunctionPayload.payload_instantiated operations _ rfl signature

theorem payload_has_function_type :
    (constructorPayload signature).same
      (Ty.function Ty.bool (Ty.function
        (Ty.function (Ty.var RegisteredSubstitution.Controls.parameter)
          (Ty.function Ty.bool Ty.bool)) Ty.bool)) = true := by
  decide +kernel

theorem proof_batch_accepted :
    ((commands? before indices entries).bind
      (Registered.replayFrom emptyAxiomPolicy before)).isSome = true := by
  decide +kernel

theorem proof_batch_not_carrier_roots :
    (instantiate? emptyAxiomPolicy before operations indices entries).isNone = true := by
  decide +kernel

theorem missing_parent_refused :
    (commands? before {indices with recursiveInduction := 1} entries).isNone = true := by
  decide +kernel

def unusedBadEntries := entries ++ [(Name.global "unusedParameter",
  Ty.op (.mk (Name.global "undeclaredType") .undefined) [])]

theorem unused_type_refused :
    ((commands? before indices unusedBadEntries).bind
      (Registered.replayFrom emptyAxiomPolicy before)).isNone = true := by
  decide +kernel

/-- These controls check type compatibility only; they supply no Peano or
recursive-space facts for the Boolean-number fixture. -/
def vectorOperations : RecursiveSpaceSourceReadback.Operations :=
  {operations with payload := .var (Name.global "A")}

theorem vector_instance_compatible :
    (VectorContainerGuardSource.compatible? vectorOperations).isSome = true := by
  decide +kernel

theorem vector_number_change_refused :
    (VectorContainerGuardSource.compatible?
      {vectorOperations with number := .var (Name.global "A")}).isNone = true := by
  decide +kernel

theorem vector_wrong_payload_refused :
    (VectorContainerGuardSource.compatible? {vectorOperations with payload := Ty.bool}).isNone = true := by
  decide +kernel

def verdicts : List (String × Bool) :=
  [("recspace-type-instance/vector-compatible", (VectorContainerGuardSource.compatible? vectorOperations).isSome),
   ("recspace-type-instance/vector-number-change", (VectorContainerGuardSource.compatible?
      {vectorOperations with number := .var (Name.global "A")}).isNone),
   ("recspace-type-instance/vector-wrong-payload", (VectorContainerGuardSource.compatible?
      {vectorOperations with payload := Ty.bool}).isNone),
   ("recspace-type-instance/function-payload",
      (Operations.instantiate operations (effectiveTypes entries)).payload.same (constructorPayload signature)),
   ("recspace-type-instance/proof-batch-accepted", ((commands? before indices entries).bind
      (Registered.replayFrom emptyAxiomPolicy before)).isSome),
   ("recspace-type-instance/proofs-are-not-root-readings",
      (instantiate? emptyAxiomPolicy before operations indices entries).isNone),
   ("recspace-type-instance/missing-parent", (commands? before
      {indices with recursiveInduction := 1} entries).isNone),
   ("recspace-type-instance/unused-type", ((commands? before indices unusedBadEntries).bind
      (Registered.replayFrom emptyAxiomPolicy before)).isNone)]

#print axioms vector_instance_compatible
#print axioms vector_number_change_refused
#print axioms vector_wrong_payload_refused
#print axioms simultaneous_payload
#print axioms proof_batch_accepted
#print axioms proof_batch_not_carrier_roots
#print axioms unused_type_refused

end Mettapedia.Languages.HOLLight.RecursiveSpaceTypeInstantiation.Controls
