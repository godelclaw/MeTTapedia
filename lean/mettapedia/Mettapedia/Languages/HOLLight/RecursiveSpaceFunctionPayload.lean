import Mettapedia.Languages.HOLLight.RecursiveSpaceTypeInstantiation

/-!+# Constructor-function payloads in the source replay model

A type instance of the six source roots supplies the recursive-space
correspondence. Its payload is the actual function type of the constructor
encoding. The equivalence below interprets that type structurally in the same
replay model; it does not assign an arbitrary carrier to a function type.
Constructor occurrences and all fields remain distinguishable, while an
unused function remains outside the constructor-data image.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RecursiveSpaceFunctionPayload

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ProofExecution RecursiveSpaceTypeInstantiation

universe w

theorem effectiveTypes_apply (entries : List (Name × Ty)) (type : Ty) :
    (effectiveTypes entries).apply type = (TypeSubst.ofList entries).apply type := by
  change (SourceSubstitution.typeSubstitution (PrimitiveTransport.typeEntries
    (SourceSubstitution.typeSubstitution (PrimitiveTransport.typeEntries
      (TypeSubst.ofList entries))))).apply type = _
  rw [PrimitiveTransport.typeEntries_apply, PrimitiveTransport.typeEntries_apply]

theorem payload_instantiated (operations : RecursiveSpaceSourceReadback.Operations)
    (parameter : Name) (parameter_eq : operations.payload = Ty.var parameter)
    (signature : List (List Ty)) :
    (Operations.instantiate operations
      (effectiveTypes [(parameter, constructorPayload signature)])).payload =
        constructorPayload signature := by
  change (effectiveTypes _).apply operations.payload = _
  rw [effectiveTypes_apply, parameter_eq]
  exact TypeSubst.apply_insert_same TypeSubst.empty parameter _

variable {before : Registered.State} {operations : RecursiveSpaceSourceReadback.Operations}
  (parameter : Name) (parameter_eq : operations.payload = Ty.var parameter)
  (signature : List (List Ty))
  (result : Result SourceProfileModels.policy before operations
    [(parameter, constructorPayload signature)])
  (earlier : List Registered.Command)
  (accepted : Registered.replayFrom SourceProfileModels.policy
    (Registered.empty SourceProfile.primitiveContext) earlier = some before)
  (other : TypeFamilySemantics.OperatorFamilies.{w})
  (assignment : TypeFamilySemantics.Assignment.{w})

noncomputable def model :=
  (SourceProfileModels.sourceReplayFrame (earlier ++ result.commands) result.after
    (result.full_replay _ earlier accepted)).frame.model other assignment

abbrev sourceOperations := Operations.instantiate operations
  (effectiveTypes [(parameter, constructorPayload signature)])

noncomputable def payloadEquivalence :
    (sourceOperations parameter signature (operations := operations)).recursive.Payload
      (model parameter signature result earlier accepted other assignment) ≃
    Mettapedia.TypeTheory.FiniteConstructorEncoding.Payload
      (HOL.Ty.denote.{0,w+1} (model parameter signature result earlier accepted other assignment).Carrier)
      (signature.map (List.map Ty.toHOL)) :=
  (Equiv.cast (congrArg (HOL.Ty.denote.{0,w+1}
    (model parameter signature result earlier accepted other assignment).Carrier)
    ((congrArg Ty.toHOL (payload_instantiated operations parameter parameter_eq signature)).trans
      (constructorPayload_toHOL signature)))).trans
    (HOL.FiniteConstructorEncoding.payloadEquivalence
      (model parameter signature result earlier accepted other assignment) _)

noncomputable def encode (data : Mettapedia.TypeTheory.FiniteConstructorEncoding.Data
    (HOL.Ty.denote.{0,w+1} (model parameter signature result earlier accepted other assignment).Carrier)
    (signature.map (List.map Ty.toHOL))) :=
  (payloadEquivalence parameter parameter_eq signature result earlier accepted other assignment).symm
    (Mettapedia.TypeTheory.FiniteConstructorEncoding.encode _ _ data)

theorem encode_injective : Function.Injective
    (encode parameter parameter_eq signature result earlier accepted other assignment) := by
  intro first second equal
  apply Mettapedia.TypeTheory.FiniteConstructorEncoding.encode_injective
  exact (payloadEquivalence parameter parameter_eq signature result earlier accepted other assignment).symm.injective equal

noncomputable def unused :=
  (payloadEquivalence parameter parameter_eq signature result earlier accepted other assignment).symm
    (Mettapedia.TypeTheory.FiniteConstructorEncoding.unused _ _)

theorem unused_not_encoded : ¬ ∃ data,
    encode parameter parameter_eq signature result earlier accepted other assignment data =
      unused parameter parameter_eq signature result earlier accepted other assignment := by
  rintro ⟨data, equal⟩
  apply Mettapedia.TypeTheory.FiniteConstructorEncoding.unused_not_valid
  exact ⟨data, (payloadEquivalence parameter parameter_eq signature result earlier accepted other assignment).symm.injective equal⟩

noncomputable def correspondence :=
  result.correspondence earlier accepted other assignment (fun _ _ => False)

/-- The constructor equation uses the encoded data in the same source model
and retains the complete child function through the natural-carrier map. -/
theorem encoded_constructor (tag : Nat)
    (data : Mettapedia.TypeTheory.FiniteConstructorEncoding.Data
      (HOL.Ty.denote.{0,w+1} (model parameter signature result earlier accepted other assignment).Carrier)
      (signature.map (List.map Ty.toHOL)))
    (children : Nat → (sourceOperations parameter signature (operations := operations)).recursive.Carrier
      (model parameter signature result earlier accepted other assignment)) :
    (correspondence parameter signature result earlier accepted other assignment).relation
      ((sourceOperations parameter signature (operations := operations)).recursive.constructor
        (model parameter signature result earlier accepted other assignment)
        ((correspondence parameter signature result earlier accepted other assignment).numbers tag)
        (encode parameter parameter_eq signature result earlier accepted other assignment data)
        (fun number => children
          ((correspondence parameter signature result earlier accepted other assignment).numbers.symm number))) =
      RecursiveSpaceSemantics.construct (fun _ _ => False) tag
        (encode parameter parameter_eq signature result earlier accepted other assignment data)
        (fun number => (correspondence parameter signature result earlier accepted other assignment).relation
          (children number)) := by
  simpa only [sourceOperations, model, Equiv.symm_apply_apply] using
    (correspondence parameter signature result earlier accepted other assignment).constructor
      ((correspondence parameter signature result earlier accepted other assignment).numbers tag)
      (encode parameter parameter_eq signature result earlier accepted other assignment data)
      (fun number => children
        ((correspondence parameter signature result earlier accepted other assignment).numbers.symm number))

#print axioms payload_instantiated
#print axioms encode_injective
#print axioms unused_not_encoded
#print axioms encoded_constructor

end Mettapedia.Languages.HOLLight.RecursiveSpaceFunctionPayload
