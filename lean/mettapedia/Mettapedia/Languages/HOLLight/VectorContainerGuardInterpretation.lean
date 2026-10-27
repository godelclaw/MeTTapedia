import Mettapedia.Languages.HOLLight.VectorContainerGuardSource
import Mettapedia.GSLT.LanguageDef.IndexedVectorContainerFamilyReading

/-!
# Vector-container position bounds in the received source model

The source model and its natural-number equivalence are constructed from
accepted replay and exact Peano-root readings. The generated position program
then relates exactly the slots below the stored length and the represented
outer-family index. No order-interpretation field is supplied by the caller.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.VectorContainerGuardSource
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open SourceProfileModels TypeFamilySemantics
universe w

variable (operations : RecursiveSpaceSourceReadback.Operations)
  (commands : List ProofExecution.Registered.Command) (after : ProofExecution.Registered.State)
  (accepted : ProofExecution.Registered.replayFrom policy
    (ProofExecution.Registered.empty SourceProfile.primitiveContext) commands = some after)
  (facts : NaturalModelCategoricity.CachedFacts operations.natural after)
  (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

noncomputable def receivedNumbers :=
  NaturalModelCategoricity.replayNaturalEquivalence operations.natural commands after accepted facts other assignment

theorem received_position_relation
    (values : ((sourceReplayFrame commands after accepted).frame.model other assignment).Valuation [])
    (length slot : Nat)
    (index : HOL.Ty.denote.{0,w+1}
      ((sourceReplayFrame commands after accepted).frame.model other assignment).Carrier .prop) :
    (positions operations).related
      ((sourceReplayFrame commands after accepted).frame.model other assignment) values
      ⟨⟨0, by change 0 < 1; decide⟩,
        receivedNumbers operations commands after accepted facts other assignment length, PUnit.unit⟩
      (receivedNumbers operations commands after accepted facts other assignment slot) index ↔
      slot < length ∧ index = ULift.up True := by
  have bound := NaturalModelCategoricity.replay_order_iff operations.natural commands after accepted facts
    other assignment values
    (receivedNumbers operations commands after accepted facts other assignment slot)
    (receivedNumbers operations commands after accepted facts other assignment length)
  simp only [receivedNumbers, Equiv.symm_apply_apply] at bound
  exact (HOL.VectorContainerPositionPrograms.related_iff
    ((sourceReplayFrame commands after accepted).frame.model other assignment)
    ((sourceReplayFrame commands after accepted).frame.model_fullDomains other assignment)
    operations.number.toHOL
    (IndexedConstructorGuardSource.numeral operations.natural.zero operations.natural.successor)
    (HOL.SuccessorOrder.less operations.natural.successor) values
    (receivedNumbers operations commands after accepted facts other assignment length)
    (receivedNumbers operations commands after accepted facts other assignment slot) index).trans
      (and_congr bound Iff.rfl)

#print axioms received_position_relation

theorem received_position_exact
    (values : ((sourceReplayFrame commands after accepted).frame.model other assignment).Valuation [])
    (length slot : Nat)
    (index : HOL.Ty.denote.{0,w+1}
      ((sourceReplayFrame commands after accepted).frame.model other assignment).Carrier .prop) :
    (positions operations).related
      ((sourceReplayFrame commands after accepted).frame.model other assignment) values
      ⟨⟨0, by change 0 < 1; decide⟩,
        receivedNumbers operations commands after accepted facts other assignment length, PUnit.unit⟩
      (receivedNumbers operations commands after accepted facts other assignment slot) index ↔
      ∃ position,
        ((Mettapedia.TypeTheory.IndexedPositiveContainer.RecursiveSpaceRepresentation.codePresentation
          Mettapedia.TypeTheory.IndexedPositiveContainer.VectorControl.orderedFinitary
          Mettapedia.TypeTheory.IndexedPositiveContainer.VectorControl.code).coding
          (Mettapedia.TypeTheory.IndexedPositiveContainer.VectorControl.shapeAt length)).decode slot = some position ∧
        index = ULift.up True := by
  rw [received_position_relation operations commands after accepted facts other assignment values length slot index]
  constructor
  · rintro ⟨inside, same⟩
    obtain ⟨position, decoded⟩ :=
      (Mettapedia.TypeTheory.IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_active_iff length slot).mpr inside
    exact ⟨position, decoded, same⟩
  · rintro ⟨position, decoded, same⟩
    exact ⟨(Mettapedia.TypeTheory.IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_active_iff length slot).mp
      ⟨position, decoded⟩, same⟩

#print axioms received_position_exact

/-- The defining-equation reader earns the meaning of installed guards in
the model of the same accepted history. No family-membership premise is
required to preserve the generated least predicate. -/
theorem received_installed_member_agreement
    (shape : HOL.ClosedTerm Symbol ((signature operations).number.arr
      ((signature operations).payload.arr .prop)))
    (active : HOL.ClosedTerm Symbol ((signature operations).payload.arr
      ((signature operations).number.arr .prop)))
    (edge : HOL.ClosedTerm Symbol ((signature operations).payload.arr
      ((signature operations).number.arr ((signature operations).space.arr .prop))))
    (readings : IndexedConstructorDefinitions.GuardReadings after (signature operations) shape active edge)
    (tree : HOL.Ty.denote.{0,w+1}
      ((sourceReplayFrame commands after accepted).frame.model other assignment).Carrier (signature operations).space) :
    (HOL.RecursiveSpacePredicate.Signature.denotes
      ((sourceReplayFrame commands after accepted).frame.model other assignment)
      (HOL.PredicateFixedPoint.least ((signature operations).withGuards shape active edge).operator) tree).down ↔
    (HOL.RecursiveSpacePredicate.Signature.denotes
      ((sourceReplayFrame commands after accepted).frame.model other assignment)
      ((positions operations).member (bottom operations) (constructor operations)) tree).down := by
  have same := readings.least_denote (sourceReplayFrame commands after accepted).frame other assignment
  exact Iff.of_eq (congrArg (fun predicate => (predicate tree).down) same)

namespace ReceivedFamily
open Mettapedia.TypeTheory
open IndexedPositiveContainer IndexedPolynomial.RecursiveSpaceRepresentation
open Mettapedia.GSLT.LanguageDef.IndexedVectorContainerFamilyModel (CarrierReading presentation)

variable (compatible : Compatible operations)
  (readings : RecursiveSpaceSourceReadback.Readings (instanceOperations operations) after)

noncomputable def naturalFacts : NaturalModelCategoricity.CachedFacts operations.natural after :=
  instanceNatural_eq operations compatible ▸ readings.naturalFacts

noncomputable def comparison : RecursiveSpaceModelComparison.Correspondence
    (recursiveSignature operations)
    ((sourceReplayFrame commands after accepted).frame.model other assignment) (fun _ _ => False) :=
  RecursiveSpaceModelComparison.replayCorrespondence (recursiveSignature operations)
    operations.natural.zero operations.natural.successor commands after accepted
    (naturalFacts operations after compatible readings)
    (instanceSignature_eq operations compatible ▸ readings.recursiveFacts) other assignment (fun _ _ => False)

local instance payload_nonempty : Nonempty
    ((recursiveSignature operations).Payload
      ((sourceReplayFrame commands after accepted).frame.model other assignment)) :=
  ⟨fun _ => ULift.up False⟩

/-- All structural laws are earned from the six cached source roots. -/
noncomputable def carrierReading : CarrierReading
    ((sourceReplayFrame commands after accepted).frame.model other assignment) where
  number := operations.number.toHOL
  space := (instanceOperations operations).space.toHOL
  numeral := IndexedConstructorGuardSource.numeral operations.natural.zero operations.natural.successor
  less := HOL.SuccessorOrder.less operations.natural.successor
  bottom := VectorContainerGuardSource.bottom operations
  construct := VectorContainerGuardSource.constructor operations
  numbers := (comparison operations commands after accepted other assignment compatible readings).numbers
  trees := (comparison operations commands after accepted other assignment compatible readings).trees
  zero := rfl
  less_iff := by
    intro slot length
    have law := NaturalModelCategoricity.replay_order_iff operations.natural commands after accepted
      (naturalFacts operations after compatible readings) other assignment
      (fun impossible => nomatch impossible)
      ((comparison operations commands after accepted other assignment compatible readings).numbers slot)
      ((comparison operations commands after accepted other assignment compatible readings).numbers length)
    simpa only [comparison, RecursiveSpaceModelComparison.replayCorrespondence, recursiveSignature,
      RecursiveSpaceSourceReadback.Operations.natural, Equiv.symm_apply_apply,
      HOL.RecursiveSpacePredicate.Signature.denote_closed] using law
  bottom_eq := (comparison operations commands after accepted other assignment compatible readings).trees_bottom
  construct_eq := (comparison operations commands after accepted other assignment compatible readings).trees_construct

/-- Exact whole-family recognition in the source model returned by replay. -/
theorem member_iff (tree : (carrierReading operations commands after accepted other assignment compatible readings).Tree) :
    (HOL.RecursiveSpacePredicate.Signature.denotes
      ((sourceReplayFrame commands after accepted).frame.model other assignment)
      ((positions operations).member (VectorContainerGuardSource.bottom operations)
        (VectorContainerGuardSource.constructor operations))
      ((carrierReading operations commands after accepted other assignment compatible readings).trees tree)).down ↔
      Mapped.FamilyValid presentation VectorControl.environment
        (carrierReading operations commands after accepted other assignment compatible readings).payloadMap tree :=
  (carrierReading operations commands after accepted other assignment compatible readings).member_iff
    ((sourceReplayFrame commands after accepted).frame.model_fullDomains other assignment) tree

/-- Installing the three checked guard equations preserves that exact family. -/
theorem installed_member_iff
    (shape : HOL.ClosedTerm Symbol ((signature operations).number.arr
      ((signature operations).payload.arr .prop)))
    (active : HOL.ClosedTerm Symbol ((signature operations).payload.arr
      ((signature operations).number.arr .prop)))
    (edge : HOL.ClosedTerm Symbol ((signature operations).payload.arr
      ((signature operations).number.arr ((signature operations).space.arr .prop))))
    (guards : IndexedConstructorDefinitions.GuardReadings after (signature operations) shape active edge)
    (tree : (carrierReading operations commands after accepted other assignment compatible readings).Tree) :
    (HOL.RecursiveSpacePredicate.Signature.denotes
      ((sourceReplayFrame commands after accepted).frame.model other assignment)
      (HOL.PredicateFixedPoint.least ((signature operations).withGuards shape active edge).operator)
      ((carrierReading operations commands after accepted other assignment compatible readings).trees tree)).down ↔
      Mapped.FamilyValid presentation VectorControl.environment
        (carrierReading operations commands after accepted other assignment compatible readings).payloadMap tree :=
  (received_installed_member_agreement operations commands after accepted other assignment
    shape active edge guards _).trans
    (member_iff operations commands after accepted other assignment compatible readings tree)

#print axioms carrierReading
#print axioms member_iff
#print axioms installed_member_iff
end ReceivedFamily

#print axioms received_installed_member_agreement
end Mettapedia.Languages.HOLLight.VectorContainerGuardSource
