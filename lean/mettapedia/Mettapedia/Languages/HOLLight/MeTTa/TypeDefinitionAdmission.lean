import Mettapedia.Languages.HOLLight.MeTTa.TypeParameterOrdering
import Mettapedia.Languages.HOLLight.MeTTa.DefinitionExecution

/-!
# Constructed type admission from retained source evidence

The authored parameter path supplies the exact ordered request to the shared
registered gate. Its premise comes from the actual proof cache, with the
existing derivation invariant. The two returned formulas retain the source
pointwise presentation and dependencies. Execution of the enclosing source
type-definition event and publication of both new records are separate laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters

def request (typeName abstractionName representationName : String) (texts : List String)
    (predicate : CheckedSourceTerm) (existence : Theorem) : TypeOperatorDefinitionRequest :=
  { typeName := sourceOperatorName (Name.global typeName)
    abstractionName := Name.global abstractionName
    representationName := Name.global representationName
    typeVariables := texts.map Name.global
    predicateSource := predicate.source
    existence := existence }

/-- New operators pass through the same involutive name translation as
existing declarations. Both source spellings remain available faithfully. -/
theorem request_operator_spelling (typeName abstractionName representationName : String)
    (texts : List String) (predicate : CheckedSourceTerm) (existence : Theorem) :
    sourceOperatorName (request typeName abstractionName representationName texts predicate existence).typeName =
      Name.global typeName := by
  exact sourceOperatorName_roundtrip _

/-- The source's reserved function spelling denotes the shared primitive
operator, rather than a second fresh declaration with a similar name. -/
theorem function_spelling_reserved (abstractionName representationName : String)
    (texts : List String) (predicate : CheckedSourceTerm) (existence : Theorem) :
    (request "fun" abstractionName representationName texts predicate existence).typeName =
      operatorName TypeOp.function := by
  simp [request, sourceOperatorName, operatorName, TypeOp.function]

/-- A fresh source operator spelled '->' remains distinct from the reserved
source 'fun'; the conversion is a bijection, not a one-way replacement. -/
theorem arrow_spelling_distinct (abstractionName representationName : String)
    (texts : List String) (predicate : CheckedSourceTerm) (existence : Theorem) :
    (request "->" abstractionName representationName texts predicate existence).typeName ≠
      operatorName TypeOp.function := by
  simp [request, sourceOperatorName, operatorName, TypeOp.function, Name.global]

/-- The computed source order supplies all parameter conditions of the
existing declaration gate; application, closedness and hypotheses remain
the actual kernel's independent side conditions. -/
theorem request_admissible (context : TheoryContext)
    (typeName abstractionName representationName : String) (texts : List String)
    (predicate : CheckedSourceTerm) (existence : Theorem) (witness : CanonicalTerm)
    (ordered : texts.map Name.global = sortedParameters predicate.source)
    (application : CanonicalTerm.ApplicationSemantics predicate.canonical witness existence.sequent.concl)
    (empty : existence.sequent.hyp = ∅) (boolean : existence.sequent.concl.IsBool)
    (closed : predicate.canonical.term.HasNoFreeVariables)
    (typeFresh : .typeOperator (sourceOperatorName (Name.global typeName)) ∉ context.names)
    (abstractionFresh : .constant (Name.global abstractionName) ∉ context.names)
    (representationFresh : .constant (Name.global representationName) ∉ context.names)
    (different : abstractionName ≠ representationName) :
    TypeAdmissible context.names (request typeName abstractionName representationName texts predicate existence) := by
  have namesDifferent : Name.global abstractionName ≠ Name.global representationName := by
    intro same
    exact different (congrArg Name.component same)
  refine ⟨⟨typeFresh, abstractionFresh, representationFresh, namesDifferent⟩, ?_, ordered⟩
  refine ⟨predicate.canonical, witness, application, DefinitionExecution.source_check predicate,
    empty, boolean, closed, ?_, ?_⟩
  · simpa only [request, ordered] using sortedParameters_nodup predicate.source
  · simpa only [request, ordered, CheckedSourceTerm.canonical] using sortedParameters_support predicate.source

/-- Both annotation checks use constructed instantiation witnesses. A
successful registered source result is obtained from the guards, rather
than assumed as an interface to the rest of the proof. -/
theorem registered_admission_constructed (context : TheoryContext)
    (typeName abstractionName representationName : String) (texts : List String)
    (predicate : CheckedSourceTerm) (existence : Theorem) (witness : CanonicalTerm)
    (ordered : texts.map Name.global = sortedParameters predicate.source)
    (application : CanonicalTerm.ApplicationSemantics predicate.canonical witness existence.sequent.concl)
    (empty : existence.sequent.hyp = ∅) (boolean : existence.sequent.concl.IsBool)
    (closed : predicate.canonical.term.HasNoFreeVariables)
    (predicateFormed : AnnotationsFormed context.signature predicate.canonical.term)
    (witnessFormed : AnnotationsFormed context.signature witness.term)
    (representedFormed : TypeFormed context.signature witness.ty)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (typeFresh : .typeOperator (sourceOperatorName (Name.global typeName)) ∉ context.names)
    (abstractionFresh : .constant (Name.global abstractionName) ∉ context.names)
    (representationFresh : .constant (Name.global representationName) ∉ context.names)
    (different : abstractionName ≠ representationName) :
    ∃ witnesses result, admitSourceTypeInTheory context witnesses
      (request typeName abstractionName representationName texts predicate existence) = some result := by
  obtain ⟨witnesses, realizes⟩ := exists_instanceWitnesses context.signature
  have admitted := (admitTypeInTheoryFromApplication_isSome_iff context witnesses
    (request typeName abstractionName representationName texts predicate existence)
    predicate.canonical witness application).mpr
      ⟨annotationsFormedB_complete context.signature witnesses realizes predicateFormed,
       annotationsFormedB_complete context.signature witnesses realizes witnessFormed,
       representedFormed, functionArity,
       request_admissible context typeName abstractionName representationName texts predicate existence witness
         ordered application empty boolean closed typeFresh abstractionFresh representationFresh different⟩
  rw [← admitTypeInTheory_eq_fromApplication context witnesses
    (request typeName abstractionName representationName texts predicate existence)
    predicate.canonical witness application] at admitted
  have accepted : (admitSourceTypeInTheory context witnesses
      (request typeName abstractionName representationName texts predicate existence)).isSome = true := by
    rw [admitSourceTypeInTheory_isSome_eq]
    exact admitted
  cases result : admitSourceTypeInTheory context witnesses
      (request typeName abstractionName representationName texts predicate existence) with
  | none => simp [result] at accepted
  | some output => exact ⟨witnesses, output, result⟩

/-- The actual annotation traversal, lexical sort and parameter construction
feed admitted source equations from an earned cache premise. Earlier cache
derivations transport along the constructed signature extension. This does
not yet assert execution or logical publication of the two output records. -/
theorem authored_parameters_feed_earned_admission (policy : AxiomPolicy) (context : TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies context constants)
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy context cache)
    (key : Atom) (record : CacheAuthorization.Record)
    (recordFormed : TheoremFormed context.signature record.fact)
    (found : (CacheAuthorization.entries constants cache).lookup key = some (record.atom constants))
    (typeName abstractionName representationName : String)
    (predicate : CheckedSourceTerm) (witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate.canonical witness record.conclusion)
    (empty : record.hypotheses = []) (boolean : record.conclusion.IsBool)
    (closed : predicate.canonical.term.HasNoFreeVariables)
    (global : TypeParameterOrdering.globalParameters predicate.canonical.term)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (typeFresh : .typeOperator (sourceOperatorName (Name.global typeName)) ∉ context.names)
    (abstractionFresh : .constant (Name.global abstractionName) ∉ context.names)
    (representationFresh : .constant (Name.global representationName) ∉ context.names)
    (different : abstractionName ≠ representationName)
    (bindings : Subst) (state : Effects.State) (termKey : String)
    (captured : applySubst bindings (.var termKey) =
      Representation.termAtom Representation.registeredOperatorAtom constants [] predicate.canonical.term) :
    ∃ texts witnesses result,
      BoundCalls.CorePath.PureReturns program bindings state
        (.expression [.symbol "hol-light:type-parameters", .expression [.symbol "hol-light:sorted-names",
          .expression [.symbol "hol-light:term-type-vars", .var termKey]]]) state
        (Premises.keys (TypeParameterOrdering.Parameters.atoms texts)) ∧
      admitSourceTypeInTheory context witnesses
        (request typeName abstractionName representationName texts predicate record.fact) = some result ∧
      TheoryDerives policy context record.fact ∧
      CacheAuthorization.Valid policy result.context cache ∧
      PointwiseTypeDefinitionSemantics
        (request typeName abstractionName representationName texts predicate record.fact)
        result.core.predicate result.core.witness result.output ∧
      result.output.abstractionRepresentationTheorem.axioms = record.fact.axioms ∧
      result.output.representationAbstractionTheorem.axioms = record.fact.axioms := by
  obtain ⟨texts, ordered, parameterPath⟩ := TypeParameterOrdering.authored_admission_parameters
    constants predicate global bindings state termKey captured
  have applicationAnnotations : AnnotationsFormed context.signature
      (.app predicate.canonical.term witness.term) := by
    obtain ⟨domain, codomain, arrow, carrier, shape⟩ := application
    rw [← shape]
    exact recordFormed.1.1
  have componentAnnotations : AnnotationsFormed context.signature predicate.canonical.term ∧
      AnnotationsFormed context.signature witness.term := by
    cases applicationAnnotations with
    | app function argument => exact ⟨function, argument⟩
  have representedFormed := AnnotationsFormed.inferredType context.signature functionArity componentAnnotations.2
    (by simp [ContextFormed]) witness.checked
  have hypothesesEmpty : record.fact.sequent.hyp = ∅ := by simp [CacheAuthorization.Record.fact, empty]
  obtain ⟨witnesses, result, accepted⟩ := registered_admission_constructed context
    typeName abstractionName representationName texts predicate record.fact witness ordered application hypothesesEmpty
    boolean closed componentAnnotations.1 componentAnnotations.2 representedFormed functionArity
    typeFresh abstractionFresh representationFresh different
  have retained := admitSourceTypeInTheory_result accepted
  exact ⟨texts, witnesses, result, parameterPath, accepted,
    CacheAuthorization.lookup_derived policy context constants identified cache valid key record recordFormed found,
    CacheAuthorization.weaken_valid retained.1 valid, admitSourceTypeInTheory_pointwise accepted,
    retained.2.2.1, retained.2.2.2.1⟩

end Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionAdmission
