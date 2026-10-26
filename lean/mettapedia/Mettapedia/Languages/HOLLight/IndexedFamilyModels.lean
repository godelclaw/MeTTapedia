import Mettapedia.Languages.HOLLight.RecursiveSpaceSourceReadback
import Mettapedia.Languages.HOLLight.ModelParameterInterpretation
import Mettapedia.TypeTheory.IndexedPolynomialRecursiveSpaceRepresentation

/-!
# Indexed families in the model constructed from source replay

The input is an accepted source-policy replay with the six checked root
readings. Assigning its payload type parameter to an inhabited carrier earns
the payload equivalence from the model family's actual carrier equation.
The source recursive-space operations then supply the algebra used by the
generic indexed-polynomial representation.

Natural-slot encodings remain explicit. Constructor equations retain the
original result index, shape and complete padded child map. The representation
and its inverse are semantic; this module supplies no executable decoder.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.IndexedFamilyModels

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ProofExecution SourceProfileModels TypeFamilySemantics
open Mettapedia.TypeTheory
open IndexedPolynomial RecursiveSpaceRepresentation

universe u b i s p

/-- Actual replay and root-reading evidence, together with the source payload
parameter identified in that operation table. -/
structure ReceivedRoots where
  operations : RecursiveSpaceSourceReadback.Operations
  commands : List Registered.Command
  state : Registered.State
  accepted : Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) commands = some state
  readings : RecursiveSpaceSourceReadback.Readings operations state
  parameter : Name
  payload_parameter : operations.payload = Ty.var parameter

/-- Check the six source roots and retain the actual replay equation. A source
type operator is not reinterpreted as a freely assignable type parameter. -/
def receive? (operations : RecursiveSpaceSourceReadback.Operations)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (indices : RecursiveSpaceSourceReadback.CacheIndices) : Option ReceivedRoots :=
  match parameter : operations.payload with
  | .op .. => none
  | .var name => do
      let readings ← RecursiveSpaceSourceReadback.read? operations state indices
      return ⟨operations,commands,state,accepted,readings,name,parameter⟩

namespace ReceivedRoots

noncomputable def frame (roots : ReceivedRoots) :=
  (sourceReplayFrame.{u} roots.commands roots.state roots.accepted).frame

variable (roots : ReceivedRoots) (carrier : Type u) (point : carrier)
  (other : OperatorFamilies.{u}) (prior : Assignment.{u})

noncomputable def model : HOL.HenkinModel.{0,0,u+1} AtomicTy Symbol :=
  roots.frame.model other (ModelParameterInterpretation.assignment prior roots.parameter carrier point)

noncomputable def payloadEquivalence : carrier ≃ roots.operations.recursive.Payload
    (roots.model carrier point other prior) := by
  change carrier ≃ HOL.Ty.denote.{0,u+1} (roots.model carrier point other prior).Carrier roots.operations.payload.toHOL
  rw [roots.payload_parameter]
  exact ModelParameterInterpretation.parameterEquivalence roots.frame.family other prior roots.parameter carrier point

noncomputable def correspondence : RecursiveSpaceModelComparison.Correspondence roots.operations.recursive
    (roots.model carrier point other prior) (fun _ _ => False) :=
  RecursiveSpaceSourceReadback.correspondence roots.operations roots.commands roots.state roots.accepted
    roots.readings other (ModelParameterInterpretation.assignment prior roots.parameter carrier point) (fun _ _ => False)

noncomputable def sourceAlgebra : RecursiveSpace.Model
    (roots.operations.recursive.Payload (roots.model carrier point other prior))
    (roots.operations.recursive.Carrier (roots.model carrier point other prior)) := by
  let _ : Nonempty (roots.operations.recursive.Payload (roots.model carrier point other prior)) :=
    ⟨roots.payloadEquivalence carrier point other prior point⟩
  exact (RecursiveSpaceSemantics.model (fun _ _ => False)).changeCarrier
    (roots.correspondence carrier point other prior).relation

noncomputable def algebra : RecursiveSpace.Model carrier
    (roots.operations.recursive.Carrier (roots.model carrier point other prior)) :=
  (roots.sourceAlgebra carrier point other prior).changePayload (roots.payloadEquivalence carrier point other prior)

theorem algebra_bottom : (roots.algebra carrier point other prior).bottom =
    roots.operations.recursive.origin (roots.model carrier point other prior) := by
  let _ : Nonempty (roots.operations.recursive.Payload (roots.model carrier point other prior)) :=
    ⟨roots.payloadEquivalence carrier point other prior point⟩
  apply (roots.correspondence carrier point other prior).relation.injective
  change (roots.correspondence carrier point other prior).relation
    ((RecursiveSpaceSemantics.model (fun _ _ => False)).changeCarrier
      (roots.correspondence carrier point other prior).relation).bottom = _
  rw [RecursiveSpace.Model.changeCarrier_bottom, (roots.correspondence carrier point other prior).bottom]
  rfl

theorem algebra_constructor (tag : Nat) (payload : carrier)
    (children : Nat → roots.operations.recursive.Carrier (roots.model carrier point other prior)) :
    (roots.algebra carrier point other prior).construct tag payload children =
      roots.operations.recursive.constructor (roots.model carrier point other prior)
        ((roots.correspondence carrier point other prior).numbers tag)
        (roots.payloadEquivalence carrier point other prior payload)
        (fun n => children ((roots.correspondence carrier point other prior).numbers.symm n)) := by
  let _ : Nonempty (roots.operations.recursive.Payload (roots.model carrier point other prior)) :=
    ⟨roots.payloadEquivalence carrier point other prior point⟩
  apply (roots.correspondence carrier point other prior).relation.injective
  change (roots.correspondence carrier point other prior).relation
    (((RecursiveSpaceSemantics.model (fun _ _ => False)).changeCarrier
      (roots.correspondence carrier point other prior).relation).construct tag
        (roots.payloadEquivalence carrier point other prior payload) children) = _
  rw [RecursiveSpace.Model.changeCarrier_construct,
    (roots.correspondence carrier point other prior).constructor]
  simp only [Equiv.symm_apply_apply]
  rfl

end ReceivedRoots

variable {Base : Type b} {Index : Base → Type i}
  (roots : ReceivedRoots) (presentation : Presentation.{b,i,s,p} (Base := Base) (Index := Index))
  (environment : Base) (other : OperatorFamilies.{max i s}) (prior : Assignment.{max i s})

noncomputable def familyAlgebra :=
  roots.algebra (RecursivePayload presentation environment) none other prior

abbrev Carrier := roots.operations.recursive.Carrier
  (roots.model (RecursivePayload presentation environment) none other prior)

def Family (index : Index environment) :=
  {value : Carrier roots presentation environment other prior //
    RecursiveValid presentation
      ((RecursiveSpace.equivalence (familyAlgebra roots presentation environment other prior)).symm value) index}

/-- Both directions are constructed through the existing guarded polynomial
comparison, using the algebra earned from the received source facts. -/
noncomputable def representation (index : Index environment) :
    Fix presentation.polynomial environment index ≃ Family roots presentation environment other prior index :=
  interpretedRepresentation presentation environment
    (familyAlgebra roots presentation environment other prior) index

noncomputable def encode {index : Index environment}
    (source : Fix presentation.polynomial environment index) : Carrier roots presentation environment other prior :=
  interpretedEncode presentation (familyAlgebra roots presentation environment other prior) source

theorem encode_constructor {index : Index environment} (shape : presentation.polynomial.Shape environment index)
    (children : ∀ position, Fix presentation.polynomial environment (presentation.polynomial.next shape position)) :
    encode roots presentation environment other prior (Fix.roll shape children) =
      roots.operations.recursive.constructor
        (roots.model (RecursivePayload presentation environment) none other prior)
        ((roots.correspondence (RecursivePayload presentation environment) none other prior).numbers
          (presentation.tag shape))
        (roots.payloadEquivalence (RecursivePayload presentation environment) none other prior (some ⟨index,shape⟩))
        (fun n => ((positions presentation).coding shape).extend
          (roots.operations.recursive.origin
            (roots.model (RecursivePayload presentation environment) none other prior))
          (fun position => encode roots presentation environment other prior (children position))
          ((roots.correspondence (RecursivePayload presentation environment) none other prior).numbers.symm n)) := by
  unfold encode
  rw [interpretedEncode_constructor]
  dsimp only [familyAlgebra, positions]
  rw [ReceivedRoots.algebra_constructor, ReceivedRoots.algebra_bottom]

theorem roundtrip {index : Index environment}
    (source : Fix presentation.polynomial environment index) :
    (representation roots presentation environment other prior index).symm
      (representation roots presentation environment other prior index source) = source :=
  (representation roots presentation environment other prior index).symm_apply_apply source

theorem guarded_roundtrip {index : Index environment}
    (value : Family roots presentation environment other prior index) :
    representation roots presentation environment other prior index
      ((representation roots presentation environment other prior index).symm value) = value :=
  (representation roots presentation environment other prior index).apply_symm_apply value

#print axioms ReceivedRoots.payloadEquivalence
#print axioms ReceivedRoots.algebra
#print axioms representation
#print axioms encode_constructor

end Mettapedia.Languages.HOLLight.IndexedFamilyModels
