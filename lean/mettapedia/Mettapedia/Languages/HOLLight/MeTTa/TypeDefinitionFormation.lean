import Mettapedia.Languages.OpenTheory.PrimitiveEqualityFormation
import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionAdmission

/-!
# Formation and earned derivations of the source type-definition laws

Formation is constructed from the admitted carrier and maps, the original
polymorphic equality declaration, and the retained existence theorem. No
formation or derivation of either returned law is assumed. Execution of the
complete two-publication event remains a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionFormation

open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters PrimitiveEqualityFormation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa

/-- The successful source operation retains the actual application view and
uses the same registered extension as the shared gate. -/
theorem source_result_components (context : TheoryContext) (witnesses : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (boolean : request.existence.sequent.concl.IsBool) (result : SourceTypeDefinitionResult)
    (accepted : admitSourceTypeInTheory context witnesses request = some result) :
    admitTypeInTheoryFromApplication context witnesses request predicate witness application = some result.core ∧
      result.output = makePointwiseTypeOperatorDefinition request predicate witness application boolean := by
  unfold admitSourceTypeInTheory at accepted
  rw [CanonicalTerm.applicationView?_eq_some _ _ _ application] at accepted
  cases coreChecked : admitTypeInTheoryFromApplication context witnesses request predicate witness application with
  | none => simp [coreChecked] at accepted
  | some core =>
      simp only [coreChecked] at accepted
      have booleanChecked := (CanonicalTerm.isBoolB_eq_true_iff _).mpr boolean
      simp only [booleanChecked, ↓reduceDIte] at accepted
      have equal := Option.some.inj accepted
      subst result
      exact ⟨rfl, rfl⟩

/-- The source result registers precisely the provenance-bearing operator
and the abstraction/representation maps occurring in its pointwise laws. -/
theorem source_symbols_registered (context : TheoryContext) (witnesses : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (boolean : request.existence.sequent.concl.IsBool) (result : SourceTypeDefinitionResult)
    (accepted : admitSourceTypeInTheory context witnesses request = some result) :
    let operator := TypeOp.mk request.typeName (.defined request.predicateSource request.typeVariables)
    let carrier := Ty.op operator (request.typeVariables.map Ty.var)
    result.context.signature.typeOperators operator = some request.typeVariables.length ∧
      result.context.signature.constants (.mk request.abstractionName (.abstraction operator)) =
        some (.function witness.ty carrier) ∧
      result.context.signature.constants (.mk request.representationName (.representation operator)) =
        some (.function carrier witness.ty) := by
  have core := (source_result_components context witnesses request predicate witness application boolean result accepted).1
  have details := admitTypeInTheoryFromApplication_result core
  have checked := details.2.2.2.2.2.2.1
  obtain ⟨sourcePredicate, sourceWitness, sourceApplication, sourceBool, _, _, _, _, _, outputEqual⟩ :=
    checkTypeOperatorDefinition_result checked
  have provenance := makeTypeOperatorDefinition_provenance request sourcePredicate sourceWitness sourceApplication sourceBool
  rw [← outputEqual] at provenance
  have registered := admitTypeInTheoryFromApplication_registered core
  simpa only [provenance.1, provenance.2.1, provenance.2.2.1, details.2.1] using registered

/-- Build annotation formation of both laws, including the nested Boolean
equality and all retained axiom commitments, from actual registered symbols. -/
theorem source_outputs_formed (context : TheoryContext) (witnesses : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (boolean : request.existence.sequent.concl.IsBool) (result : SourceTypeDefinitionResult)
    (accepted : admitSourceTypeInTheory context witnesses request = some result)
    (existenceFormed : TheoremFormed context.signature request.existence)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (booleanFormed : TypeFormed context.signature Ty.bool) (equalityParameter : Name)
    (equalityRegistered : context.signature.constants Const.equality =
      some (Ty.equality (.var equalityParameter))) :
    TheoremFormed result.context.signature result.output.abstractionRepresentationTheorem ∧
      TheoremFormed result.context.signature result.output.representationAbstractionTheorem := by
  let signature := result.context.signature
  let operator := TypeOp.mk request.typeName (.defined request.predicateSource request.typeVariables)
  let carrier := Ty.op operator (request.typeVariables.map Ty.var)
  let abstraction := Const.mk request.abstractionName (.abstraction operator)
  let representation := Const.mk request.representationName (.representation operator)
  have components := source_result_components context witnesses request predicate witness application boolean result accepted
  have details := admitTypeInTheoryFromApplication_result components.1
  have included := (admitSourceTypeInTheory_result accepted).1
  have registered := source_symbols_registered context witnesses request predicate witness application boolean result accepted
  have functionInExtension : signature.typeOperators TypeOp.function = some 2 := included.1 _ _ functionArity
  have booleanInExtension : TypeFormed signature Ty.bool := booleanFormed.mono included
  have equalityInExtension : signature.constants Const.equality = some (Ty.equality (.var equalityParameter)) :=
    included.2 _ _ equalityRegistered
  have carrierFormed : TypeFormed signature carrier := by
    simp only [carrier, TypeFormed]
    refine ⟨?_, ?_⟩
    · simpa only [carrier, List.length_map] using registered.1
    · intro argument member
      obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
      simp only [TypeFormed]
  have witnessFormed := details.2.2.2.1
  have representedFormed : TypeFormed signature witness.ty :=
    (AnnotationsFormed.inferredType context.signature functionArity witnessFormed
      (by simp [ContextFormed]) witness.checked).mono included
  have abstractionFormed : AnnotationsFormed signature (.const abstraction (.function witness.ty carrier)) := by
    refine .constant (TypeFormed.function signature functionInExtension representedFormed carrierFormed) ?_
    exact ⟨.function witness.ty carrier, TypeSubst.empty, registered.2.1, by simp⟩
  have representationFormed : AnnotationsFormed signature (.const representation (.function carrier witness.ty)) := by
    refine .constant (TypeFormed.function signature functionInExtension carrierFormed representedFormed) ?_
    exact ⟨.function carrier witness.ty, TypeSubst.empty, registered.2.2, by simp⟩
  have aFormed : AnnotationsFormed signature (.free ⟨Name.global "a", carrier⟩) := .free carrierFormed
  have rFormed : AnnotationsFormed signature (.free ⟨Name.global "r", witness.ty⟩) := .free representedFormed
  have predicateFormed : AnnotationsFormed signature predicate.term := details.2.2.1.mono included
  have firstFormed := equation_annotations signature equalityParameter carrier functionInExtension booleanInExtension
    carrierFormed equalityInExtension _ _ (.app abstractionFormed (.app representationFormed aFormed)) aFormed
  have retractionFormed := equation_annotations signature equalityParameter witness.ty functionInExtension booleanInExtension
    representedFormed equalityInExtension _ _ (.app representationFormed (.app abstractionFormed rFormed)) rFormed
  have secondFormed := equation_annotations signature equalityParameter Ty.bool functionInExtension booleanInExtension
    booleanInExtension equalityInExtension _ _ (.app predicateFormed rFormed) retractionFormed
  have pointwise := makePointwiseTypeOperatorDefinition_semantics request predicate witness application boolean
  rw [← components.2] at pointwise
  have retained := admitSourceTypeInTheory_result accepted
  constructor
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [pointwise.2.2.2.1]
      exact firstFormed
    · rw [retained.2.2.2.2.1]
      intro hypothesis member
      exact (existenceFormed.1.2 hypothesis member).mono included
    · rw [retained.2.2.1]
      intro commitment member
      exact (existenceFormed.2 commitment member).mono included
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [pointwise.2.2.2.2]
      exact secondFormed
    · rw [retained.2.2.2.2.2]
      intro hypothesis member
      exact (existenceFormed.1.2 hypothesis member).mono included
    · rw [retained.2.2.2.1]
      intro commitment member
      exact (existenceFormed.2 commitment member).mono included

/-- Both source laws are earned in the existing registered calculus from
the actual existence derivation; output formation is constructed above. -/
theorem source_outputs_derived (policy : AxiomPolicy) (context : TheoryContext)
    (witnesses : InstanceWitnesses) (request : TypeOperatorDefinitionRequest)
    (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (boolean : request.existence.sequent.concl.IsBool) (result : SourceTypeDefinitionResult)
    (accepted : admitSourceTypeInTheory context witnesses request = some result)
    (existence : TheoryDerives policy context request.existence)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (booleanFormed : TypeFormed context.signature Ty.bool) (equalityParameter : Name)
    (equalityRegistered : context.signature.constants Const.equality =
      some (Ty.equality (.var equalityParameter))) :
    TheoryDerives policy result.context result.output.abstractionRepresentationTheorem ∧
      TheoryDerives policy result.context result.output.representationAbstractionTheorem := by
  have formed := source_outputs_formed context witnesses request predicate witness application boolean result accepted
    existence.wellFormed functionArity booleanFormed equalityParameter equalityRegistered
  exact ⟨.typeAbstractionDefinition accepted existence formed.1,
    .typeRepresentationDefinition accepted existence formed.2⟩

/-- No equality annotation can be formed by relying on a printed equality
name when that primitive identity is absent from the signature. -/
theorem absent_equality_refuses_equation (signature : Signature) (operand : Ty)
    (left right : DBTerm) (missing : signature.constants Const.equality = none) :
    ¬ AnnotationsFormed signature (CanonicalTerm.equalityDB operand left right) := by
  intro formed
  cases formed with
  | app leftFormed _ =>
      cases leftFormed with
      | app equalityFormed _ =>
          cases equalityFormed with
          | constant _ registered =>
              obtain ⟨schema, _, found, _⟩ := registered
              rw [missing] at found
              cases found

def command (typeName abstractionName representationName : String) (premise : Atom) : Atom :=
  .expression [.symbol "TYPE_DEFINITION", .grounded (.string typeName),
    .grounded (.string abstractionName), .grounded (.string representationName), premise]

def representationKey (key : Atom) : Atom := .expression [.symbol "HOL:RepKey", key]

/-- Each output keeps the original ordered dependency occurrences and its
own publication address, with the same defining command as its origin. -/
def outputRecord (key request : Atom) (conclusion : CanonicalTerm)
    (dependencies : List CacheAuthorization.Dependency) : CacheAuthorization.Record :=
  ⟨[], conclusion, dependencies, .expression [.symbol "HOL:Origin", key, request]⟩

theorem output_record_fact (key request : Atom) (prior : CacheAuthorization.Record) (output : Theorem)
    (empty : output.sequent.hyp = ∅) (dependencies : output.axioms = prior.fact.axioms) :
    (outputRecord key request output.sequent.concl prior.dependencies).fact = output := by
  apply Theorem.ext
  · simpa only [outputRecord, CacheAuthorization.Record.fact] using dependencies.symm
  · apply Sequent.ext
    · simpa only [outputRecord, CacheAuthorization.Record.fact, List.toFinset_nil] using empty.symm
    · rfl

/-- The actual parameter execution and earned lookup produce derivations
for both output records and preserve the old cache invariant. This proves
logical admissibility of those records, not execution of their two insertions. -/
theorem authored_parameters_earn_output_records (policy : AxiomPolicy) (context : TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies context constants)
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy context cache)
    (premise : Atom) (record : CacheAuthorization.Record)
    (recordFormed : TheoremFormed context.signature record.fact)
    (found : (CacheAuthorization.entries constants cache).lookup premise = some (record.atom constants))
    (key : Atom) (typeName abstractionName representationName : String)
    (predicate : CheckedSourceTerm) (witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate.canonical witness record.conclusion)
    (empty : record.hypotheses = []) (boolean : record.conclusion.IsBool)
    (closed : predicate.canonical.term.HasNoFreeVariables)
    (global : TypeParameterOrdering.globalParameters predicate.canonical.term)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (booleanFormed : TypeFormed context.signature Ty.bool) (equalityParameter : Name)
    (equalityRegistered : context.signature.constants Const.equality =
      some (Ty.equality (.var equalityParameter)))
    (typeFresh : .typeOperator (sourceOperatorName (Name.global typeName)) ∉ context.names)
    (abstractionFresh : .constant (Name.global abstractionName) ∉ context.names)
    (representationFresh : .constant (Name.global representationName) ∉ context.names)
    (different : abstractionName ≠ representationName)
    (bindings : Subst) (state : Effects.State) (termKey : String)
    (captured : applySubst bindings (.var termKey) =
      Representation.termAtom Representation.registeredOperatorAtom constants [] predicate.canonical.term) :
    ∃ texts witnesses result,
      let request := TypeDefinitionAdmission.request typeName abstractionName representationName texts predicate record.fact
      let origin := command typeName abstractionName representationName premise
      let first := outputRecord key origin result.output.abstractionRepresentationTheorem.sequent.concl record.dependencies
      let second := outputRecord (representationKey key) origin
        result.output.representationAbstractionTheorem.sequent.concl record.dependencies
      BoundCalls.CorePath.PureReturns program bindings state
        (.expression [.symbol "hol-light:type-parameters", .expression [.symbol "hol-light:sorted-names",
          .expression [.symbol "hol-light:term-type-vars", .var termKey]]]) state
        (Premises.keys (TypeParameterOrdering.Parameters.atoms texts)) ∧
      admitSourceTypeInTheory context witnesses request = some result ∧
      TheoryDerives policy result.context first.fact ∧
      TheoryDerives policy result.context second.fact ∧
      CacheAuthorization.Valid policy result.context ((representationKey key, second) :: (key, first) :: cache) ∧
      first.dependencies = record.dependencies ∧ second.dependencies = record.dependencies ∧
      first.origin = .expression [.symbol "HOL:Origin", key, origin] ∧
      second.origin = .expression [.symbol "HOL:Origin", representationKey key, origin] := by
  obtain ⟨texts, witnesses, result, path, accepted, earned, oldValid, _, _, _⟩ :=
    TypeDefinitionAdmission.authored_parameters_feed_earned_admission policy context constants identified cache valid
      premise record recordFormed found typeName abstractionName representationName predicate witness application
      empty boolean closed global functionArity typeFresh abstractionFresh representationFresh different
      bindings state termKey captured
  have derived := source_outputs_derived policy context witnesses _ predicate.canonical witness application boolean
    result accepted earned functionArity booleanFormed equalityParameter equalityRegistered
  have retained := admitSourceTypeInTheory_result accepted
  have hypothesesEmpty : record.fact.sequent.hyp = ∅ := by simp [CacheAuthorization.Record.fact, empty]
  have firstEmpty : result.output.abstractionRepresentationTheorem.sequent.hyp = ∅ :=
    retained.2.2.2.2.1.trans hypothesesEmpty
  have secondEmpty : result.output.representationAbstractionTheorem.sequent.hyp = ∅ :=
    retained.2.2.2.2.2.trans hypothesesEmpty
  let origin := command typeName abstractionName representationName premise
  have firstFact := output_record_fact key origin record result.output.abstractionRepresentationTheorem
    firstEmpty retained.2.2.1
  have secondFact := output_record_fact (representationKey key) origin record
    result.output.representationAbstractionTheorem secondEmpty retained.2.2.2.1
  have firstDerived := firstFact ▸ derived.1
  have secondDerived := secondFact ▸ derived.2
  refine ⟨texts, witnesses, result, path, accepted, firstDerived, secondDerived, ?_, rfl, rfl, rfl, rfl⟩
  exact CacheAuthorization.insert_valid (CacheAuthorization.insert_valid oldValid key _ firstDerived)
    (representationKey key) _ secondDerived

end Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionFormation
