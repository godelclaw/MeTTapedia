import Mettapedia.Languages.HOLLight.DefinitionAdapters
import Mettapedia.Languages.HOLLight.EqualityExpansion
import Mettapedia.Languages.OpenTheory.CheckedSourceTheorem

/-!
# Equality reflection through witnessed HOL Light type definitions

The pointwise abstraction/representation equations come from the actual
type-definition admission operation. Their instances use the original
capture-avoiding substitution and retain the existence theorem's dependencies.
The local proof blocks consume these stored equations; they do not introduce
them as axioms or replace the preceding existence proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.TypeDefinitionEquality

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open DefinitionAdapters GraphExpansion EqualityExpansion PrimitiveTransport SignatureFormation

def carrier (request : TypeOperatorDefinitionRequest) : Ty :=
  .op (.mk request.typeName (.defined request.predicateSource request.typeVariables))
    (request.typeVariables.map Ty.var)

def abstraction (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult) :
    CanonicalTerm :=
  .constant result.output.abstractionConstant (.function result.core.witness.ty (carrier request))

def representation (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult) :
    CanonicalTerm :=
  .constant result.output.representationConstant (.function (carrier request) result.core.witness.ty)

def represented (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult)
    (value : CheckedSourceTerm) (typed : value.ty = carrier request) : CanonicalTerm :=
  .applicationOfFunction (representation request result) value.canonical result.core.witness.ty
    (by
      simpa only [representation, CanonicalTerm.constant,
        CheckedSourceTerm.canonical_ty, typed] using
        Ty.destFunction?_function (carrier request) result.core.witness.ty)

def roundtrip (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult)
    (value : CheckedSourceTerm) (typed : value.ty = carrier request) : CanonicalTerm :=
  .applicationOfFunction (abstraction request result) (represented request result value typed)
    (carrier request) (Ty.destFunction?_function _ _)

def abstractionVariable (request : TypeOperatorDefinitionRequest) : SourceVar :=
  ⟨Name.global "a", carrier request⟩

def atValue (request : TypeOperatorDefinitionRequest) (value : CheckedSourceTerm)
    (typed : value.ty = carrier request) : TypeCorrectTermSubstitution :=
  ⟨⟨TypeSubst.empty, [(abstractionVariable request, value)]⟩, by
    intro entry member
    obtain rfl := List.mem_singleton.mp member
    exact typed⟩

def roundtripTheorem (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult)
    (value : CheckedSourceTerm) (typed : value.ty = carrier request) : Theorem :=
  substituteTheorem (atValue request value typed) result.output.abstractionRepresentationTheorem

theorem roundtrip_view {context : TheoryContext} {instances : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (value : CheckedSourceTerm) (typed : value.ty = carrier request) :
    CanonicalTerm.EqualityViewSemantics
      (roundtripTheorem request result value typed).sequent.concl
      (roundtrip request result value typed) value.canonical := by
  have facts := admitSourceTypeInTheory_pointwise accepted
  dsimp only [PointwiseTypeDefinitionSemantics] at facts
  obtain ⟨_, absSame, repSame, equation, _⟩ := facts
  refine ⟨typed.symm, ?_⟩
  change (atValue request value typed).raw.applyDB
      result.output.abstractionRepresentationTheorem.sequent.concl.term = _
  rw [equation]
  simp [roundtrip, represented, abstraction, representation, absSame, repSame,
    CanonicalTerm.applicationOfFunction, CanonicalTerm.constant, CanonicalTerm.equalityDB,
    atValue, abstractionVariable, TermSubst.applyDB, TermSubst.lookup,
    TermSubst.keySame, sourceVarSame, TypeSubst.applyVar, TypeSubst.apply_empty,
    Function.comp_def, carrier, Ty.same_eq_true_iff]

section Representation

variable (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult)
  (left right : CheckedSourceTerm)
  (leftTyped : left.ty = carrier request) (rightTyped : right.ty = carrier request)
  (input : Theorem)

def mappedEquality : Theorem :=
  appResult (reflexivity (abstraction request result)) input
    (roundtrip request result left leftTyped) (roundtrip request result right rightTyped) rfl

def reversedRoundtrip : Theorem :=
  symmetryResult (roundtripTheorem request result left leftTyped)
    (roundtrip request result left leftTyped) left.canonical leftTyped.symm

def intermediateEquality : Theorem :=
  transResult (reversedRoundtrip request result left leftTyped)
    (mappedEquality request result left right leftTyped rightTyped input)
    left.canonical (roundtrip request result right rightTyped) leftTyped

def representationEqualityResult : Theorem :=
  transResult (intermediateEquality request result left right leftTyped rightTyped input)
    (roundtripTheorem request result right rightTyped)
    left.canonical right.canonical (leftTyped.trans rightTyped.symm)

/-- The stored definition equation is shared by both instantiations. All
subsequent operations are existing primitive or checked derived blocks. -/
def representationPlan (origin : ProofExecution.Origin) : List BlockRequest :=
  [⟨roundtripTheorem request result left leftTyped,
      substitutionBlock (atValue request left leftTyped)
        result.output.abstractionRepresentationTheorem origin, [0], origin⟩,
   ⟨roundtripTheorem request result right rightTyped,
      substitutionBlock (atValue request right rightTyped)
        result.output.abstractionRepresentationTheorem origin, [0], origin⟩,
   ⟨reflexivity (abstraction request result),
      primitiveBlock (.inference (.refl (abstraction request result)))
        (reflexivity (abstraction request result)) origin, [], origin⟩,
   ⟨mappedEquality request result left right leftTyped rightTyped input,
      primitiveBlock (.inference (.mkComb (reflexivity (abstraction request result)) input))
        (mappedEquality request result left right leftTyped rightTyped input) origin, [4, 1], origin⟩,
   ⟨reversedRoundtrip request result left leftTyped,
      symmetryBlock (roundtripTheorem request result left leftTyped)
        (roundtrip request result left leftTyped) left.canonical leftTyped.symm origin, [2], origin⟩,
   ⟨intermediateEquality request result left right leftTyped rightTyped input,
      primitiveBlock (.inference (.trans (reversedRoundtrip request result left leftTyped)
        (mappedEquality request result left right leftTyped rightTyped input)))
        (intermediateEquality request result left right leftTyped rightTyped input) origin, [6, 5], origin⟩,
   ⟨representationEqualityResult request result left right leftTyped rightTyped input,
      primitiveBlock (.inference (.trans
        (intermediateEquality request result left right leftTyped rightTyped input)
        (roundtripTheorem request result right rightTyped)))
        (representationEqualityResult request result left right leftTyped rightTyped input) origin, [7, 3], origin⟩]

/-- Compute a local certificate over the original stored definition theorem
and the caller's representation equality, without adding either as an axiom. -/
def compileRepresentation (policy : AxiomPolicy) [DecidablePred policy]
    (origin : ProofExecution.Origin) : Option ProofSystem.Certificate :=
  finishPlan policy (start [result.output.abstractionRepresentationTheorem, input]) #[0, 1]
    (representationPlan request result left right leftTyped rightTyped input origin) 8

theorem representationPlan_checked (policy : AxiomPolicy) [DecidablePred policy]
    {context : TheoryContext} {instances : InstanceWitnesses}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (compared : CanonicalTerm.EqualityViewSemantics input.sequent.concl
      (represented request result left leftTyped) (represented request result right rightTyped))
    (origin : ProofExecution.Origin) :
    LocallyChecked policy #[result.output.abstractionRepresentationTheorem, input]
      (representationPlan request result left right leftTyped rightTyped input origin) := by
  have leftView := roundtrip_view accepted left leftTyped
  have rightView := roundtrip_view accepted right rightTyped
  have mappedChecked : checkApp (reflexivity (abstraction request result)) input =
      some (mappedEquality request result left right leftTyped rightTyped input) :=
    appResult_checked (reflexivity (abstraction request result)) input
      (abstraction request result) (abstraction request result)
      (represented request result left leftTyped) (represented request result right rightTyped)
      (roundtrip request result left leftTyped) (roundtrip request result right rightTyped) rfl
      (equality_view _ _ rfl) compared
      (CanonicalTerm.applicationOfFunction_semantics (abstraction request result)
        (represented request result left leftTyped) (carrier request) (Ty.destFunction?_function _ _))
      (CanonicalTerm.applicationOfFunction_semantics (abstraction request result)
        (represented request result right rightTyped) (carrier request) (Ty.destFunction?_function _ _))
  have intermediateChecked : checkTrans (reversedRoundtrip request result left leftTyped)
      (mappedEquality request result left right leftTyped rightTyped input) =
      some (intermediateEquality request result left right leftTyped rightTyped input) :=
    transResult_checked (reversedRoundtrip request result left leftTyped)
      (mappedEquality request result left right leftTyped rightTyped input)
      left.canonical (roundtrip request result left leftTyped)
      (roundtrip request result right rightTyped) leftTyped
      (equality_view left.canonical (roundtrip request result left leftTyped) leftTyped)
      (equality_view (roundtrip request result left leftTyped)
        (roundtrip request result right rightTyped) rfl)
  have finalChecked : checkTrans
      (intermediateEquality request result left right leftTyped rightTyped input)
      (roundtripTheorem request result right rightTyped) =
      some (representationEqualityResult request result left right leftTyped rightTyped input) :=
    transResult_checked
      (intermediateEquality request result left right leftTyped rightTyped input)
      (roundtripTheorem request result right rightTyped)
      left.canonical (roundtrip request result right rightTyped) right.canonical
      (leftTyped.trans rightTyped.symm)
      (equality_view left.canonical (roundtrip request result right rightTyped) leftTyped) rightView
  unfold representationPlan
  refine .cons rfl (substitutionBlock_checked policy _ _ _) ?_
  refine .cons rfl (substitutionBlock_checked policy _ _ _) ?_
  refine .cons rfl (primitiveBlock_checked (policy := policy)
    (.inference (.refl (abstraction request result))) _ origin
    (reflexivity_checked (abstraction request result))) ?_
  refine .cons rfl (primitiveBlock_checked (policy := policy)
    (.inference (.mkComb (reflexivity (abstraction request result)) input)) _ origin mappedChecked) ?_
  refine .cons rfl (symmetryBlock_checked policy _ _ _ _ leftView origin) ?_
  refine .cons rfl (primitiveBlock_checked (policy := policy)
    (.inference (.trans (reversedRoundtrip request result left leftTyped)
      (mappedEquality request result left right leftTyped rightTyped input))) _ origin intermediateChecked) ?_
  refine .cons rfl (primitiveBlock_checked (policy := policy)
    (.inference (.trans (intermediateEquality request result left right leftTyped rightTyped input)
      (roundtripTheorem request result right rightTyped))) _ origin finalChecked) ?_
  exact .nil _

theorem compileRepresentation_checked (policy : AxiomPolicy) [DecidablePred policy]
    {context : TheoryContext} {instances : InstanceWitnesses}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (compared : CanonicalTerm.EqualityViewSemantics input.sequent.concl
      (represented request result left leftTyped) (represented request result right rightTyped))
    (origin : ProofExecution.Origin) :
    ∃ block, compileRepresentation request result left right leftTyped rightTyped input policy origin = some block ∧
      BlockChecked policy [result.output.abstractionRepresentationTheorem, input]
        (representationEqualityResult request result left right leftTyped rightTyped input) block := by
  apply finishPlan_checked (start_checked policy _) (by rfl)
    (representationPlan_checked request result left right leftTyped rightTyped input policy accepted compared origin)
  rfl

theorem compileRepresentation_nodes (policy : AxiomPolicy) [DecidablePred policy]
    (origin : ProofExecution.Origin) {block : ProofSystem.Certificate}
    (compiled : compileRepresentation request result left right leftTyped rightTyped input policy origin = some block) :
    block.1.length = 13 := by
  have size := finishPlan_size compiled
  simpa [representationPlan, substitutionBlock, symmetryBlock, primitiveBlock, start] using size

theorem representationEqualityResult_conclusion :
    (representationEqualityResult request result left right leftTyped rightTyped input).sequent.concl.term =
      CanonicalTerm.equalityDB left.ty left.canonical.term right.canonical.term := rfl

/-- The block preserves the original existence proof's axiom dependencies;
the definition equations do not acquire independent axiom tags. -/
theorem representationEqualityResult_axioms {context : TheoryContext} {instances : InstanceWitnesses}
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    (representationEqualityResult request result left right leftTyped rightTyped input).axioms =
      request.existence.axioms ∪ input.axioms := by
  have lawAxioms := (admitSourceTypeInTheory_result accepted).2.2.1
  simp [representationEqualityResult, intermediateEquality, reversedRoundtrip, mappedEquality,
    roundtripTheorem, transResult, symmetryResult, appResult, reflexivity, substituteTheorem,
    Theorem.unionResult, Theorem.preserveAxiomsResult, Theorem.emptyResult,
    lawAxioms, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]

end Representation

#print axioms roundtrip_view
#print axioms compileRepresentation_checked
#print axioms representationEqualityResult_axioms

end Mettapedia.Languages.HOLLight.TypeDefinitionEquality
