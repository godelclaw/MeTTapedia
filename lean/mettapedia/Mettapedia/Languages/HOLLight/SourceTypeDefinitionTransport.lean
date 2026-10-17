import Mettapedia.Languages.HOLLight.ModelInterpretation

/-!
# Original source carriers for witnessed type-definition instances

The transport retains the admitted operator identity and its complete source
arguments. One selected instance acquires the actual witnessed predicate
subtype; the full original atomic-source-type carrier remains the indexing
language. Every older formed carrier is preserved. The type substitution and
predicate application use the original canonical source operations.

This is a fixed-instance construction. A uniform family across arbitrary
semantic parameter domains additionally needs assignment-indexed prior
symbol meanings with proved support and instantiation coherence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.SourceTypeDefinitionTransport

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open DefinitionAdapters SignatureFormation ModelInterpretation

universe w

variable {context : TheoryContext} {instances : InstanceWitnesses}
  {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}

def operator (request : TypeOperatorDefinitionRequest) : TypeOp :=
  .mk request.typeName (.defined request.predicateSource request.typeVariables)

def sourceCarrierType (request : TypeOperatorDefinitionRequest) (substitution : TypeSubst) : Ty :=
  .op (operator request) (request.typeVariables.map fun name => substitution.apply (.var name))

theorem admitted_operator
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    result.output.typeOperator = operator request :=
  (admitSourceTypeInTheory_pointwise accepted).1

private theorem defined_operator_ne_bool (request : TypeOperatorDefinitionRequest) :
    operator request ≠ TypeOp.bool := by
  intro equal
  have origins := (TypeOp.mk.inj equal).2
  cases origins

private theorem defined_operator_ne_function (request : TypeOperatorDefinitionRequest) :
    operator request ≠ TypeOp.function := by
  intro equal
  have origins := (TypeOp.mk.inj equal).2
  cases origins

/-- The provenance-bearing defined operator is never the primitive function
or Boolean operator, regardless of its printed name or actual parameters. -/
theorem sourceCarrierType_atomic (request : TypeOperatorDefinitionRequest)
    (substitution : TypeSubst) : (sourceCarrierType request substitution).IsAtomic := by
  constructor
  · have different : (operator request).same TypeOp.function = false := by
      apply Bool.eq_false_iff.mpr
      intro same
      exact defined_operator_ne_function request ((TypeOp.same_eq_true_iff _ _).mp same)
    simp only [sourceCarrierType, Ty.destFunction?]
    split <;> simp only [different, Bool.false_eq_true, if_false]
  · apply Bool.eq_false_iff.mpr
    intro recognized
    have same := (Ty.isBool_eq_true_iff _).mp recognized
    have operators := (Ty.op.inj same).1
    exact defined_operator_ne_bool request operators

/-- The actual pointwise source gate carries the same freshness conditions
as the registered core gate. -/
theorem admitted_names_fresh
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    TypeNamesFresh context.names request := by
  have core := (admitSourceTypeInTheory_result accepted).2.1
  have application := (admitTypeInTheory_result core).1
  rw [admitTypeInTheory_eq_fromApplication context instances request
    result.core.predicate result.core.witness application] at core
  have profile := (admitTypeInTheoryFromApplication_isSome_iff context instances request
    result.core.predicate result.core.witness application).mp (by simp [core])
  exact profile.2.2.2.2.1

theorem admitted_operator_fresh
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    context.signature.typeOperators (operator request) = none :=
  context.operator_unregistered _ (admitted_names_fresh accepted).1

/-- The instance uses the original checked type-only canonical substitution. -/
def instanceTerm (substitution : TypeSubst) (term : CanonicalTerm) : CanonicalTerm :=
  (TypeCorrectTermSubstitution.ofTypes substitution).apply term

theorem instance_application (substitution : TypeSubst)
    {predicate witness conclusion : CanonicalTerm}
    (application : CanonicalTerm.ApplicationSemantics predicate witness conclusion) :
    CanonicalTerm.ApplicationSemantics (instanceTerm substitution predicate)
      (instanceTerm substitution witness) (instanceTerm substitution conclusion) := by
  have functionType := Ty.eq_function_of_destFunction? application.functionType
  refine ⟨substitution.apply witness.ty, substitution.apply conclusion.ty, ?_, rfl, ?_⟩
  · change (substitution.apply predicate.ty).destFunction? = _
    rw [functionType, TypeSubst.apply_function, Ty.destFunction?_function]
  · change (TermSubst.mk substitution []).applyDB conclusion.term =
      .app ((TermSubst.mk substitution []).applyDB predicate.term)
        ((TermSubst.mk substitution []).applyDB witness.term)
    obtain ⟨domain, codomain, functionChecked, argumentType, shape⟩ := application
    rw [shape, TermSubst.applyDB_app]

theorem instance_boolean (substitution : TypeSubst) {term : CanonicalTerm}
    (boolean : term.IsBool) : (instanceTerm substitution term).IsBool := by
  change substitution.apply term.ty = Ty.bool
  rw [show term.ty = Ty.bool from boolean, TypeSubst.apply_bool]

noncomputable def instanceImage
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst) :
    TypeAdmission.ApplicationImage (instanceTerm substitution result.core.predicate)
      (instanceTerm substitution result.core.witness)
      (instanceTerm substitution request.existence.sequent.concl) :=
  TypeAdmission.applicationImage
    (instance_application substitution
      (admitTypeInTheory_result (admitSourceTypeInTheory_result accepted).2.1).1)
    (instance_boolean substitution (TypeAdmission.existence_boolean accepted))

/-- The original atomic indexing language is retained: only the selected
new instance maps to the genuinely new summand. -/
noncomputable def sourceBase (request : TypeOperatorDefinitionRequest) (substitution : TypeSubst)
    (atomic : AtomicTy) : HOL.Ty (HOL.TypeDefinitionModel.ExtendedBase AtomicTy) := by
  classical
  exact if atomic.val = sourceCarrierType request substitution then HOL.TypeDefinitionModel.newType
    else HOL.TypeDefinitionModel.includeBase atomic

theorem sourceBase_new (request : TypeOperatorDefinitionRequest) (substitution : TypeSubst) :
    HOL.Ty.substitute (sourceBase request substitution)
      (sourceCarrierType request substitution).toHOL = HOL.TypeDefinitionModel.newType := by
  rw [Ty.toHOL_of_isAtomic (sourceCarrierType_atomic request substitution)]
  simp [HOL.Ty.substitute, sourceBase]

theorem sourceBase_old_atomic
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst) (atomic : AtomicTy)
    (formed : TypeFormed context.signature atomic.val) :
    sourceBase request substitution atomic = HOL.TypeDefinitionModel.includeBase atomic := by
  have different : atomic.val ≠ sourceCarrierType request substitution := by
    intro equal
    rw [equal] at formed
    have absent := admitted_operator_fresh accepted
    rw [sourceCarrierType, TypeFormed, absent] at formed
    cases formed.1
  simp [sourceBase, different]

/-- Recursive translation keeps every old formed function/Boolean/atomic
carrier, not just the root constructor of its type. -/
theorem sourceBase_old_type
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst) (type : Ty)
    (formed : TypeFormed context.signature type) :
    HOL.Ty.substitute (sourceBase request substitution) type.toHOL =
      HOL.TypeDefinitionModel.includeType type.toHOL := by
  rcases Ty.function_or_bool_or_isAtomic type with ⟨domain, codomain, rfl⟩ | rfl | atomic
  · obtain ⟨domainFormed, codomainFormed⟩ := formed.function_components context.signature
    rw [Ty.toHOL_function]
    change HOL.Ty.arr _ _ = HOL.Ty.arr _ _
    rw [sourceBase_old_type accepted substitution domain domainFormed,
      sourceBase_old_type accepted substitution codomain codomainFormed]
  · rw [Ty.toHOL_bool]; rfl
  · rw [Ty.toHOL_of_isAtomic atomic]
    exact sourceBase_old_atomic accepted substitution ⟨type, atomic⟩ formed
termination_by sizeOf type
decreasing_by
  all_goals subst_vars
  · exact Ty.sizeOf_domain_lt _ _
  · exact Ty.sizeOf_codomain_lt _ _

/-- The selected instance has an actual predicate subtype as its carrier.
The witness is the denotation of the retained source witness, not an
inhabitation axiom or an assumed extension interface. -/
noncomputable def extendedModel
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (holds : model.models (instanceImage accepted substitution).formula) :
    HOL.HenkinModel.{0, 0, w + 1} (HOL.TypeDefinitionModel.ExtendedBase AtomicTy)
      (HOL.TypeDefinitionModel.Symbol Symbol (instanceTerm substitution result.core.witness).ty.toHOL) :=
  TypeAdmission.extension.{w} (instanceImage accepted substitution) model holds

noncomputable def sourceCarrier
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (holds : model.models (instanceImage accepted substitution).formula)
    (atomic : AtomicTy) : Type (w + 1) :=
  HOL.Ty.denote.{0, w + 1} (extendedModel accepted substitution model holds).Carrier
    (sourceBase request substitution atomic)

/-- This is the subtype of the interpreted actual source predicate, indexed
at the selected original source operator application. -/
theorem sourceCarrier_new
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (holds : model.models (instanceImage accepted substitution).formula) :
    sourceCarrier accepted substitution model holds
        ⟨sourceCarrierType request substitution, sourceCarrierType_atomic request substitution⟩ =
      HOL.WitnessedTypeDefinition.Carrier
        (TypeAdmission.representedPredicate (instanceImage accepted substitution) model) := by
  simp only [sourceCarrier, sourceBase]
  rfl

theorem sourceCarrier_old
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (holds : model.models (instanceImage accepted substitution).formula)
    (atomic : AtomicTy) (formed : TypeFormed context.signature atomic.val) :
    sourceCarrier accepted substitution model holds atomic = model.Carrier atomic := by
  rw [sourceCarrier, sourceBase_old_atomic accepted substitution atomic formed]
  rfl

/-- The registered gate checks the represented type in the original signature. -/
theorem admitted_represented_formed
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    TypeFormed context.signature result.core.witness.ty := by
  have core := (admitSourceTypeInTheory_result accepted).2.1
  have application := (admitTypeInTheory_result core).1
  rw [admitTypeInTheory_eq_fromApplication context instances request
    result.core.predicate result.core.witness application] at core
  exact ((admitTypeInTheoryFromApplication_isSome_iff context instances request
    result.core.predicate result.core.witness application).mp (by simp [core])).2.2.1

/-- Formation of the actual substitution replacements is the original source
condition, rather than a new restriction on the semantics of the predicate. -/
theorem instance_represented_formed
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst)
    (replacements : ∀ name replacement, substitution.lookup name = some replacement →
      TypeFormed context.signature replacement) :
    TypeFormed context.signature (instanceTerm substitution result.core.witness).ty :=
  (admitted_represented_formed accepted).substitute context.signature substitution replacements

/-- Every old formed source type keeps its complete interpreted carrier,
including all recursive function arguments. -/
theorem sourceType_old
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (holds : model.models (instanceImage accepted substitution).formula)
    (type : Ty) (formed : TypeFormed context.signature type) :
    HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds) type.toHOL =
      HOL.Ty.denote.{0, w + 1} model.Carrier type.toHOL := by
  change HOL.Ty.denote (fun atomic => HOL.Ty.denote
    (extendedModel accepted substitution model holds).Carrier (sourceBase request substitution atomic))
    type.toHOL = _
  rw [HOL.Ty.denote_substitute, sourceBase_old_type accepted substitution type formed]
  exact (HOL.Ty.denote_substitute HOL.TypeDefinitionModel.includeBase
    (extendedModel accepted substitution model holds).Carrier type.toHOL).symm

/-- The selected new source type is the actual interpreted predicate subtype. -/
theorem sourceType_new
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (holds : model.models (instanceImage accepted substitution).formula) :
    HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds)
      (sourceCarrierType request substitution).toHOL =
      HOL.WitnessedTypeDefinition.Carrier
        (TypeAdmission.representedPredicate (instanceImage accepted substitution) model) := by
  rw [Ty.toHOL_of_isAtomic (sourceCarrierType_atomic request substitution)]
  exact sourceCarrier_new accepted substitution model holds

noncomputable def oldSourceValue
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (holds : model.models (instanceImage accepted substitution).formula)
    (type : Ty) (formed : TypeFormed context.signature type) :
    HOL.Ty.denote.{0, w + 1} model.Carrier type.toHOL ≃
      HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds) type.toHOL :=
  Equiv.cast (sourceType_old accepted substitution model holds type formed).symm

noncomputable def newSourceValue
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst)
    (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (holds : model.models (instanceImage accepted substitution).formula) :
    HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds)
      (sourceCarrierType request substitution).toHOL ≃
      HOL.WitnessedTypeDefinition.Carrier
        (TypeAdmission.representedPredicate (instanceImage accepted substitution) model) :=
  Equiv.cast (sourceType_new accepted substitution model holds)

variable (accepted : admitSourceTypeInTheory context instances request = some result)
  (substitution : TypeSubst)
  (replacements : ∀ name replacement, substitution.lookup name = some replacement →
    TypeFormed context.signature replacement)
  (model : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
  (holds : model.models (instanceImage accepted substitution).formula)

/-- The new abstraction is typed at the original, instantiated source types.
The represented argument is transported through canonical carrier equalities. -/
noncomputable def sourceAbstraction :
    HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds)
        (instanceTerm substitution result.core.witness).ty.toHOL →
      HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds)
        (sourceCarrierType request substitution).toHOL := fun value =>
  (newSourceValue accepted substitution model holds).symm
    (HOL.WitnessedTypeDefinition.abstraction
      (TypeAdmission.representedPredicate (instanceImage accepted substitution) model)
      (TypeAdmission.representedWitness (instanceImage accepted substitution) model)
      (TypeAdmission.witness_valid (instanceImage accepted substitution) model holds)
      ((oldSourceValue accepted substitution model holds _
        (instance_represented_formed accepted substitution replacements)).symm value))

noncomputable def sourceRepresentation :
    HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds)
        (sourceCarrierType request substitution).toHOL →
      HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds)
        (instanceTerm substitution result.core.witness).ty.toHOL := fun value =>
  oldSourceValue accepted substitution model holds _
    (instance_represented_formed accepted substitution replacements)
    (HOL.WitnessedTypeDefinition.representation
      (newSourceValue accepted substitution model holds value))

noncomputable def sourcePredicate :
    HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds)
      (instanceTerm substitution result.core.witness).ty.toHOL → Prop := fun value =>
  TypeAdmission.representedPredicate (instanceImage accepted substitution) model
    ((oldSourceValue accepted substitution model holds _
      (instance_represented_formed accepted substitution replacements)).symm value)

/-- The first defining equation holds at every value of the actual new carrier. -/
theorem source_abstraction_representation
    (value : HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds)
      (sourceCarrierType request substitution).toHOL) :
    sourceAbstraction accepted substitution replacements model holds
      (sourceRepresentation accepted substitution replacements model holds value) = value := by
  simp only [sourceAbstraction, sourceRepresentation, Equiv.symm_apply_apply]
  rw [HOL.WitnessedTypeDefinition.abstraction_representation, Equiv.symm_apply_apply]

/-- The second equation characterizes the actual admitted predicate, including
values outside the subtype where abstraction uses the admitted witness. -/
theorem source_predicate_iff_representation_abstraction
    (value : HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds)
      (instanceTerm substitution result.core.witness).ty.toHOL) :
    sourcePredicate accepted substitution replacements model holds value ↔
      sourceRepresentation accepted substitution replacements model holds
        (sourceAbstraction accepted substitution replacements model holds value) = value := by
  simp only [sourcePredicate, sourceRepresentation, sourceAbstraction, Equiv.apply_symm_apply]
  rw [HOL.WitnessedTypeDefinition.predicate_iff_representation_abstraction
    (TypeAdmission.representedPredicate (instanceImage accepted substitution) model)
    (TypeAdmission.representedWitness (instanceImage accepted substitution) model)
    (TypeAdmission.witness_valid (instanceImage accepted substitution) model holds)
    ((oldSourceValue accepted substitution model holds _
      (instance_represented_formed accepted substitution replacements)).symm value)]
  exact Equiv.eq_symm_apply _

/-- The same source schema, under the source's actual simultaneous type operation. -/
theorem sourceCarrierType_instance (request : TypeOperatorDefinitionRequest)
    (substitution : TypeSubst) :
    substitution.apply (sourceCarrierType request TypeSubst.empty) =
      sourceCarrierType request substitution := by
  simp only [sourceCarrierType, TypeSubst.apply_op, List.map_map, TypeSubst.apply_empty, Function.comp_def]

/-- Freshness excludes the new instance from the entire old signature. -/
theorem sourceCarrierType_not_formed
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst) :
    ¬ TypeFormed context.signature (sourceCarrierType request substitution) := by
  intro formed
  have absent := admitted_operator_fresh accepted
  rw [sourceCarrierType, TypeFormed, absent] at formed
  cases formed.1

noncomputable def extendedBaseWitness :
    (base : HOL.TypeDefinitionModel.ExtendedBase AtomicTy) →
      (extendedModel accepted substitution model holds).Carrier base
  | .inl atomic => model.constDen (.variable ⟨Name.global "carrier-witness", atomic.val⟩
      (Ty.toHOL_of_isAtomic atomic.property))
  | .inr _ => HOL.WitnessedTypeDefinition.inhabitant
      (TypeAdmission.representedPredicate (instanceImage accepted substitution) model)
      (TypeAdmission.representedWitness (instanceImage accepted substitution) model)
      (TypeAdmission.witness_valid (instanceImage accepted substitution) model holds)

/-- Unlicensed source occurrences still have model data, obtained from the
actual inhabited carriers. This does not admit their source declarations. -/
noncomputable def sourceDefault (type : HOL.Ty AtomicTy) :
    HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds) type :=
  (HOL.Ty.denoteSubstituteEquiv (sourceBase request substitution)
    (extendedModel accepted substitution model holds).Carrier type).symm
    ((extendedModel accepted substitution model holds).defaultValue
      (extendedBaseWitness accepted substitution model holds)
      (HOL.Ty.substitute (sourceBase request substitution) type))

/-- Interpret the original symbols themselves. Older formed annotations
retain their actual meaning. The two fresh identities at the selected
instance acquire the constructed subtype maps; other occurrences use
inhabited model data without becoming licensed source instances. -/
noncomputable def sourceMeanings : ∀ {type}, Symbol type →
    HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds) type
  | type, .variable sourceVar typed => by
      classical
      exact if formed : TypeFormed context.signature sourceVar.ty then
        typed ▸ oldSourceValue accepted substitution model holds sourceVar.ty formed
          (model.constDen (.variable sourceVar rfl))
      else sourceDefault accepted substitution model holds type
  | type, .constant constant annotation typed => by
      classical
      exact if formed : TypeFormed context.signature annotation then
        typed ▸ oldSourceValue accepted substitution model holds annotation formed
          (model.constDen (.constant constant annotation rfl))
      else if abstraction : constant = result.output.abstractionConstant ∧
          annotation = Ty.function (instanceTerm substitution result.core.witness).ty
            (sourceCarrierType request substitution) then
        have typeEq : HOL.Ty.arr (instanceTerm substitution result.core.witness).ty.toHOL
            (sourceCarrierType request substitution).toHOL = type :=
          (Ty.toHOL_function _ _).symm.trans
            ((congrArg Ty.toHOL abstraction.2).symm.trans typed)
        typeEq ▸ sourceAbstraction accepted substitution replacements model holds
      else if representation : constant = result.output.representationConstant ∧
          annotation = Ty.function (sourceCarrierType request substitution)
            (instanceTerm substitution result.core.witness).ty then
        have typeEq : HOL.Ty.arr (sourceCarrierType request substitution).toHOL
            (instanceTerm substitution result.core.witness).ty.toHOL = type :=
          (Ty.toHOL_function _ _).symm.trans
            ((congrArg Ty.toHOL representation.2).symm.trans typed)
        typeEq ▸ sourceRepresentation accepted substitution replacements model holds
      else sourceDefault accepted substitution model holds type

noncomputable def sourceModel : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard (sourceCarrier accepted substitution model holds)
    (sourceMeanings accepted substitution replacements model holds)

theorem sourceModel_carrier :
    (sourceModel accepted substitution replacements model holds).Carrier =
      sourceCarrier accepted substitution model holds := rfl

theorem sourceModel_fullDomains :
    (sourceModel accepted substitution replacements model holds).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

/-- No old formed symbol is replaced merely because of its printed name.
The theorem compares actual values across the changed carrier families. -/
theorem sourceMeanings_old_constant (constant : Const) (annotation : Ty)
    (formed : TypeFormed context.signature annotation) :
    HEq (sourceMeanings accepted substitution replacements model holds
        (.constant constant annotation rfl))
      (model.constDen (.constant constant annotation rfl)) := by
  classical
  simp only [sourceMeanings, dif_pos formed]
  exact cast_heq _ _

theorem sourceMeanings_old_variable (sourceVar : SourceVar)
    (formed : TypeFormed context.signature sourceVar.ty) :
    HEq (sourceMeanings accepted substitution replacements model holds
        (.variable sourceVar rfl)) (model.constDen (.variable sourceVar rfl)) := by
  classical
  simp only [sourceMeanings, dif_pos formed]
  exact cast_heq _ _

set_option backward.isDefEq.respectTransparency false in
theorem sourceMeanings_abstraction :
    sourceMeanings accepted substitution replacements model holds
      (.constant result.output.abstractionConstant
        (Ty.function (instanceTerm substitution result.core.witness).ty
          (sourceCarrierType request substitution)) (Ty.toHOL_function _ _)) =
      sourceAbstraction accepted substitution replacements model holds := by
  classical
  have absent : ¬ TypeFormed context.signature
      (Ty.function (instanceTerm substitution result.core.witness).ty
        (sourceCarrierType request substitution)) := by
    intro formed
    exact sourceCarrierType_not_formed accepted substitution (formed.function_components _).2
  simp [sourceMeanings, absent]

/-- The two fresh constants remain distinct even if other provenance-bearing
symbols happen to have the same displayed spelling. -/
theorem admitted_constants_distinct
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    result.output.representationConstant ≠ result.output.abstractionConstant := by
  have parts := admitSourceTypeInTheory_pointwise accepted
  rw [parts.2.1, parts.2.2.1]
  intro impossible
  have origins := (Const.mk.inj impossible).2
  cases origins

set_option backward.isDefEq.respectTransparency false in
theorem sourceMeanings_representation :
    sourceMeanings accepted substitution replacements model holds
      (.constant result.output.representationConstant
        (Ty.function (sourceCarrierType request substitution)
          (instanceTerm substitution result.core.witness).ty) (Ty.toHOL_function _ _)) =
      sourceRepresentation accepted substitution replacements model holds := by
  classical
  have absent : ¬ TypeFormed context.signature
      (Ty.function (sourceCarrierType request substitution)
        (instanceTerm substitution result.core.witness).ty) := by
    intro formed
    exact sourceCarrierType_not_formed accepted substitution (formed.function_components _).1
  have miss : ¬ (result.output.representationConstant = result.output.abstractionConstant ∧
      Ty.function (sourceCarrierType request substitution)
        (instanceTerm substitution result.core.witness).ty =
      Ty.function (instanceTerm substitution result.core.witness).ty
        (sourceCarrierType request substitution)) := fun hit => admitted_constants_distinct accepted hit.1
  simp [sourceMeanings, absent, miss]

/-- The installed original source constants satisfy the first defining law
at the selected instance in the constructed model. -/
theorem sourceModel_abstraction_representation
    (value : HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds)
      (sourceCarrierType request substitution).toHOL) :
    (sourceModel accepted substitution replacements model holds).constDen
        (.constant result.output.abstractionConstant
          (Ty.function (instanceTerm substitution result.core.witness).ty
            (sourceCarrierType request substitution)) (Ty.toHOL_function _ _))
      ((sourceModel accepted substitution replacements model holds).constDen
        (.constant result.output.representationConstant
          (Ty.function (sourceCarrierType request substitution)
            (instanceTerm substitution result.core.witness).ty) (Ty.toHOL_function _ _)) value) = value := by
  simp only [sourceModel, HOL.HenkinModel.standard]
  rw [sourceMeanings_abstraction, sourceMeanings_representation]
  exact source_abstraction_representation accepted substitution replacements model holds value

/-- The second law uses the actual predicate interpretation and total
abstraction, rather than assuming every represented value satisfies it. -/
theorem sourceModel_predicate_iff_representation_abstraction
    (value : HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds)
      (instanceTerm substitution result.core.witness).ty.toHOL) :
    sourcePredicate accepted substitution replacements model holds value ↔
      (sourceModel accepted substitution replacements model holds).constDen
          (.constant result.output.representationConstant
            (Ty.function (sourceCarrierType request substitution)
              (instanceTerm substitution result.core.witness).ty) (Ty.toHOL_function _ _))
        ((sourceModel accepted substitution replacements model holds).constDen
          (.constant result.output.abstractionConstant
            (Ty.function (instanceTerm substitution result.core.witness).ty
              (sourceCarrierType request substitution)) (Ty.toHOL_function _ _)) value) = value := by
  simp only [sourceModel, HOL.HenkinModel.standard]
  rw [sourceMeanings_abstraction, sourceMeanings_representation]
  exact source_predicate_iff_representation_abstraction accepted substitution replacements model holds value

theorem admitted_function_arity
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    context.signature.typeOperators TypeOp.function = some 2 := by
  have core := (admitSourceTypeInTheory_result accepted).2.1
  have application := (admitTypeInTheory_result core).1
  rw [admitTypeInTheory_eq_fromApplication context instances request
    result.core.predicate result.core.witness application] at core
  exact ((admitTypeInTheoryFromApplication_isSome_iff context instances request
    result.core.predicate result.core.witness application).mp (by simp [core])).2.2.2.1

private theorem translated_type_formed {Γ : HOL.Ctx AtomicTy} {term : DBTerm}
    {type : HOL.Ty AtomicTy} {target : HOL.Term Symbol Γ type}
    (translation : TranslatesCompositionally Γ term type target)
    {sourceContext : List Ty} (contextImage : sourceContext.map Ty.toHOL = Γ)
    (contextFormed : ContextFormed context.signature sourceContext)
    (annotations : AnnotationsFormed context.signature term)
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    TypeFormed context.signature (Ty.fromHOL type) := by
  obtain ⟨sourceType, typed, typeImage⟩ := translation.inferType_eq contextImage
  have formed := annotations.inferredType context.signature
    (admitted_function_arity accepted) contextFormed typed
  simpa only [← typeImage, Ty.fromHOL_toHOL] using formed

private theorem apply_heq {A A' B B' : Type (w + 1)}
    (domain : A = A') (codomain : B = B') {function : A → B} {other : A' → B'}
    {argument : A} {otherArgument : A'} (functions : HEq function other)
    (arguments : HEq argument otherArgument) : HEq (function argument) (other otherArgument) := by
  cases domain
  cases codomain
  exact heq_of_eq (congrArg₂ (fun f x => f x) (eq_of_heq functions) (eq_of_heq arguments))

private theorem equality_heq {A A' : Type (w + 1)} (carrier : A = A')
    {left right : A} {otherLeft otherRight : A'}
    (lefts : HEq left otherLeft) (rights : HEq right otherRight) :
    (left = right) ↔ (otherLeft = otherRight) := by
  cases carrier
  rw [eq_of_heq lefts, eq_of_heq rights]

private theorem eqv_iff_eq (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (type : HOL.Ty AtomicTy)
    (left right : HOL.Ty.denote.{0, w + 1} M.Carrier type) :
    M.Eqv type left right ↔ left = right := by
  constructor
  · exact M.eq_of_eqv_of_fullDomains full
  · intro equal
    subst right
    exact M.eqv_refl (full type left)

set_option backward.isDefEq.respectTransparency false in
/-- Old source annotations and old binder contexts retain term meaning in
full-domain models. The valuations are compared at the original bound
variables, across the carrier equalities already proved above. -/
theorem sourceModel_denote_old_translation (full : model.FullDomains)
    {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol Γ type}
    (translation : TranslatesCompositionally Γ term type target) :
    ∀ {sourceContext : List Ty}, sourceContext.map Ty.toHOL = Γ →
      ContextFormed context.signature sourceContext →
      AnnotationsFormed context.signature term →
      ∀ (newValuation : HOL.HenkinModel.Valuation.{0, 0, w + 1} (sourceModel accepted substitution replacements model holds) Γ)
        (oldValuation : HOL.HenkinModel.Valuation.{0, 0, w + 1} model Γ),
      (∀ type (boundVar : HOL.Var Γ type), HEq (newValuation boundVar) (oldValuation boundVar)) →
      HEq (HOL.HenkinModel.denote.{0, 0, w + 1} (sourceModel accepted substitution replacements model holds) target newValuation)
        (HOL.HenkinModel.denote.{0, 0, w + 1} model target oldValuation) := by
  induction translation with
  | @equality Γ constant annotation operand type recognized typed =>
      intro sourceContext contextImage contextFormed annotations newValuation oldValuation same
      obtain ⟨rfl, rfl⟩ := (equalityOperand?_eq_some_iff _ _ _).mp recognized
      have operandFormed : TypeFormed context.signature operand := by
        cases annotations with
        | constant formed _ => exact (formed.function_components _).1
      have domain : HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds) type =
          HOL.Ty.denote.{0, w + 1} model.Carrier type := by
        rw [← typed]
        exact sourceType_old accepted substitution model holds operand operandFormed
      change HEq (fun left right => ULift.up
        ((sourceModel accepted substitution replacements model holds).Eqv type left right))
        (fun left right => ULift.up (model.Eqv type left right))
      apply Function.hfunext domain
      intro left otherLeft lefts
      apply Function.hfunext domain
      intro right otherRight rights
      apply heq_of_eq
      apply ULift.ext
      apply propext
      exact (eqv_iff_eq _ (sourceModel_fullDomains accepted substitution replacements model holds)
        type left right).trans ((equality_heq domain lefts rights).trans
          (eqv_iff_eq model full type otherLeft otherRight).symm)
  | @constant Γ constant annotation type unrecognized typed =>
      intro sourceContext contextImage contextFormed annotations newValuation oldValuation same
      cases annotations with
      | constant formed _ =>
          cases typed
          exact sourceMeanings_old_constant accepted substitution replacements model holds
            constant annotation formed
  | @free Γ sourceVar type typed =>
      intro sourceContext contextImage contextFormed annotations newValuation oldValuation same
      cases annotations with
      | free formed =>
          cases typed
          exact sourceMeanings_old_variable accepted substitution replacements model holds sourceVar formed
  | bound boundVar =>
      intro sourceContext contextImage contextFormed annotations newValuation oldValuation same
      exact same _ boundVar
  | @app Γ function argument domain codomain functionTarget argumentTarget functionTranslation
      argumentTranslation functionIH argumentIH =>
      intro sourceContext contextImage contextFormed annotations newValuation oldValuation same
      cases annotations with
      | app functionAnnotations argumentAnnotations =>
          have domainFormed := translated_type_formed argumentTranslation contextImage
            contextFormed argumentAnnotations accepted
          have codomainFormed := translated_type_formed (.app functionTranslation argumentTranslation)
            contextImage contextFormed (.app functionAnnotations argumentAnnotations) accepted
          have domainEqual := sourceType_old accepted substitution model holds
            (Ty.fromHOL domain) domainFormed
          have codomainEqual := sourceType_old accepted substitution model holds
            (Ty.fromHOL codomain) codomainFormed
          simp only [Ty.toHOL_fromHOL] at domainEqual codomainEqual
          exact apply_heq domainEqual codomainEqual
            (functionIH contextImage contextFormed functionAnnotations newValuation oldValuation same)
            (argumentIH contextImage contextFormed argumentAnnotations newValuation oldValuation same)
  | @abs Γ domain body type codomain bodyTarget typed bodyTranslation bodyIH =>
      intro sourceContext contextImage contextFormed annotations newValuation oldValuation same
      cases annotations with
      | abs domainFormed bodyAnnotations =>
          have domainEqual : HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds) type =
              HOL.Ty.denote.{0, w + 1} model.Carrier type := by
            rw [← typed]
            exact sourceType_old accepted substitution model holds domain domainFormed
          apply Function.hfunext domainEqual
          intro value otherValue values
          apply bodyIH (sourceContext := domain :: sourceContext)
            (by simp only [List.map_cons, typed, contextImage])
            (contextFormed.cons context.signature domainFormed) bodyAnnotations
          intro type boundVar
          cases boundVar with
          | vz => exact values
          | vs boundVar => exact same _ boundVar

set_option backward.isDefEq.respectTransparency false in
/-- Every old translated closed source term keeps its value, without
requiring a globally unchanged carrier table. -/
theorem sourceModel_denote_old_closed (full : model.FullDomains) {term : DBTerm}
    (annotations : AnnotationsFormed context.signature term)
    {type : HOL.Ty AtomicTy} {target : HOL.ClosedTerm Symbol type}
    (translation : TranslatesCompositionally [] term type target) :
    HEq (HOL.HenkinModel.denote.{0, 0, w + 1} (sourceModel accepted substitution replacements model holds)
      target (fun boundVar => nomatch boundVar))
      (HOL.HenkinModel.denote.{0, 0, w + 1} model target (fun boundVar => nomatch boundVar)) :=
  sourceModel_denote_old_translation accepted substitution replacements model holds full translation
    (sourceContext := []) rfl (ContextFormed.nil _) annotations _ _ (fun _ boundVar => nomatch boundVar)

set_option backward.isDefEq.respectTransparency false in
/-- Old source sentences retain truth in the complete original-symbol model. -/
theorem sourceModel_models_old (full : model.FullDomains) {term : DBTerm}
    (annotations : AnnotationsFormed context.signature term)
    {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula) :
    (sourceModel accepted substitution replacements model holds).models formula ↔ model.models formula := by
  have values := sourceModel_denote_old_closed accepted substitution replacements model holds
    full annotations translation
  have same : (sourceModel accepted substitution replacements model holds).denote formula
      (fun boundVar => nomatch boundVar) = model.denote formula (fun boundVar => nomatch boundVar) :=
    eq_of_heq values
  have propositions := congrArg (fun value : ULift.{w + 1, 0} Prop => value.down) same
  apply Iff.of_eq
  calc
    _ = (HOL.HenkinModel.denote.{0, 0, w + 1}
        (sourceModel accepted substitution replacements model holds) formula
        (fun boundVar => nomatch boundVar)).down :=
      congrArg (fun value : ULift.{w + 1, 0} Prop => value.down)
        ((sourceModel accepted substitution replacements model holds).denote_closed_valuation_eq formula _ _)
    _ = _ := propositions
    _ = _ := congrArg (fun value : ULift.{w + 1, 0} Prop => value.down)
      (model.denote_closed_valuation_eq formula _ _)

theorem instance_predicate_formed
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst)
    (replacements : ∀ name replacement, substitution.lookup name = some replacement →
      TypeFormed context.signature replacement) :
    AnnotationsFormed context.signature (instanceTerm substitution result.core.predicate).term := by
  have original := (admitTypeInTheory_result (admitSourceTypeInTheory_result accepted).2.1).2.1
  exact original.substitute context.signature ⟨substitution, []⟩ replacements
    (by intro sourceVar replacement found; simp [TermSubst.lookup] at found)

set_option backward.isDefEq.respectTransparency false in
/-- The original predicate term keeps its meaning in the constructed model;
the right side is its old denotation transported to the new source carrier. -/
theorem sourceModel_predicate (full : model.FullDomains)
    (value : HOL.Ty.denote.{0, w + 1} (sourceCarrier accepted substitution model holds)
      (instanceTerm substitution result.core.witness).ty.toHOL) :
    (((sourceModel accepted substitution replacements model holds).denote
      (instanceImage accepted substitution).predicateTerm
      (fun v => nomatch v)) value).down =
        sourcePredicate accepted substitution replacements model holds value := by
  have functions := sourceModel_denote_old_closed accepted substitution replacements model holds
    full (instance_predicate_formed accepted substitution replacements)
    (instanceImage accepted substitution).predicateTranslated
  have arguments : HEq value
      ((oldSourceValue accepted substitution model holds _
        (instance_represented_formed accepted substitution replacements)).symm value) :=
    (cast_heq _ _).symm
  have outputs := apply_heq
    (sourceType_old accepted substitution model holds _
      (instance_represented_formed accepted substitution replacements)) rfl functions arguments
  have propositions := congrArg (fun truth : ULift.{w + 1, 0} Prop => truth.down) (eq_of_heq outputs)
  calc
    _ = _ := congrArg (fun function => (function value).down)
      ((sourceModel accepted substitution replacements model holds).denote_closed_valuation_eq
        (instanceImage accepted substitution).predicateTerm _ _)
    _ = _ := propositions
    _ = _ := congrArg (fun function =>
      (function ((oldSourceValue accepted substitution model holds _
        (instance_represented_formed accepted substitution replacements)).symm value)).down)
      (model.denote_closed_valuation_eq (instanceImage accepted substitution).predicateTerm _ _)

private theorem admitted_abs_ne_equality
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    result.output.abstractionConstant ≠ Const.equality := by
  rw [(admitSourceTypeInTheory_pointwise accepted).2.1]
  intro same
  have origins := (Const.mk.inj same).2
  cases origins

private theorem admitted_rep_ne_equality
    (accepted : admitSourceTypeInTheory context instances request = some result) :
    result.output.representationConstant ≠ Const.equality := by
  rw [(admitSourceTypeInTheory_pointwise accepted).2.2.1]
  intro same
  have origins := (Const.mk.inj same).2
  cases origins

private theorem equalityOperand?_none {constant : Const} (annotation : Ty)
    (different : constant ≠ Const.equality) : equalityOperand? constant annotation = none := by
  unfold equalityOperand?
  rw [show constant.same Const.equality = false from
    Bool.eq_false_iff.mpr (fun same => different ((Const.same_eq_true_iff _ _).mp same))]
  rfl

noncomputable def abstractionTerm : HOL.ClosedTerm Symbol
    (.arr (instanceTerm substitution result.core.witness).ty.toHOL
      (sourceCarrierType request substitution).toHOL) :=
  .const (.constant result.output.abstractionConstant
    (Ty.function (instanceTerm substitution result.core.witness).ty
      (sourceCarrierType request substitution)) (Ty.toHOL_function _ _))

noncomputable def representationTerm : HOL.ClosedTerm Symbol
    (.arr (sourceCarrierType request substitution).toHOL
      (instanceTerm substitution result.core.witness).ty.toHOL) :=
  .const (.constant result.output.representationConstant
    (Ty.function (sourceCarrierType request substitution)
      (instanceTerm substitution result.core.witness).ty) (Ty.toHOL_function _ _))

noncomputable def abstractionRepresentationFormula : HOL.ClosedFormula Symbol :=
  let value : HOL.ClosedTerm Symbol (sourceCarrierType request substitution).toHOL :=
    .const (.variable ⟨Name.global "a", sourceCarrierType request substitution⟩ rfl)
  .app (.app (equalityLambda (sourceCarrierType request substitution).toHOL)
    (.app (abstractionTerm (request := request) (result := result) substitution)
      (.app (representationTerm (request := request) (result := result) substitution) value))) value

noncomputable def representationAbstractionFormula : HOL.ClosedFormula Symbol :=
  let value : HOL.ClosedTerm Symbol (instanceTerm substitution result.core.witness).ty.toHOL :=
    .const (.variable ⟨Name.global "r", (instanceTerm substitution result.core.witness).ty⟩ rfl)
  .app (.app (equalityLambda .prop)
      (.app (instanceImage accepted substitution).predicateTerm value))
    (.app (.app (equalityLambda (instanceTerm substitution result.core.witness).ty.toHOL)
      (.app (representationTerm (request := request) (result := result) substitution)
        (.app (abstractionTerm (request := request) (result := result) substitution) value))) value)

private theorem typeInstance_equalityDB (substitution : TypeSubst) (operand : Ty)
    (left right : DBTerm) :
    (TermSubst.mk substitution []).applyDB (CanonicalTerm.equalityDB operand left right) =
      CanonicalTerm.equalityDB (substitution.apply operand)
        ((TermSubst.mk substitution []).applyDB left)
        ((TermSubst.mk substitution []).applyDB right) := by
  simp only [CanonicalTerm.equalityDB, TermSubst.applyDB_app, TermSubst.applyDB_const,
    TypeSubst.apply_equality]

private theorem rawCarrier_instance (request : TypeOperatorDefinitionRequest)
    (substitution : TypeSubst) :
    substitution.apply (.op (operator request) (request.typeVariables.map Ty.var)) =
      sourceCarrierType request substitution := by
  simp only [sourceCarrierType, TypeSubst.apply_op, List.map_map, Function.comp_def]

/-- The retained first equation is translated after the original type-only
substitution, with its original free-variable spelling and constant identities. -/
theorem abstractionRepresentation_translated
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (substitution : TypeSubst) :
    TranslatesCompositionally []
      (instanceTerm substitution result.output.abstractionRepresentationTheorem.sequent.concl).term
      .prop (abstractionRepresentationFormula (request := request) (result := result) substitution) := by
  change TranslatesCompositionally [] ((TermSubst.mk substitution []).applyDB
    result.output.abstractionRepresentationTheorem.sequent.concl.term) .prop _
  rw [(admitSourceTypeInTheory_pointwise accepted).2.2.2.1]
  simp only [typeInstance_equalityDB, TermSubst.applyDB_app, TermSubst.applyDB_const,
    TypeSubst.apply_op, List.map_map, Function.comp_def, TypeSubst.apply_function]
  simp only [TermSubst.applyDB, TermSubst.lookup, List.find?_nil, Option.map_none,
    TypeSubst.applyVar, TypeSubst.apply_op, List.map_map, Function.comp_def]
  rw [← (admitSourceTypeInTheory_pointwise accepted).2.1,
    ← (admitSourceTypeInTheory_pointwise accepted).2.2.1]
  apply TranslatesCompositionally.equalityDB rfl
  · apply TranslatesCompositionally.app
    · exact .constant (equalityOperand?_none _ (admitted_abs_ne_equality accepted))
        (Ty.toHOL_function _ _)
    · exact .app (.constant (equalityOperand?_none _ (admitted_rep_ne_equality accepted))
        (Ty.toHOL_function _ _)) (.free rfl)
  · exact .free rfl

/-- The retained second equation includes the actual predicate body and the
source equation's Boolean-equality orientation. -/
theorem representationAbstraction_translated :
    TranslatesCompositionally []
      (instanceTerm substitution result.output.representationAbstractionTheorem.sequent.concl).term
      .prop (representationAbstractionFormula accepted substitution) := by
  change TranslatesCompositionally [] ((TermSubst.mk substitution []).applyDB
    result.output.representationAbstractionTheorem.sequent.concl.term) .prop _
  rw [(admitSourceTypeInTheory_pointwise accepted).2.2.2.2]
  simp only [typeInstance_equalityDB, TypeSubst.apply_bool, TermSubst.applyDB_app,
    TermSubst.applyDB_const, TypeSubst.apply_function, TypeSubst.apply_op, List.map_map,
    Function.comp_def]
  simp only [TermSubst.applyDB, TermSubst.lookup, List.find?_nil, Option.map_none, TypeSubst.applyVar]
  rw [← (admitSourceTypeInTheory_pointwise accepted).2.1,
    ← (admitSourceTypeInTheory_pointwise accepted).2.2.1]
  apply TranslatesCompositionally.equalityDB Ty.toHOL_bool
  · exact .app (instanceImage accepted substitution).predicateTranslated (.free rfl)
  · apply TranslatesCompositionally.equalityDB rfl
    · exact .app (.constant (equalityOperand?_none _ (admitted_rep_ne_equality accepted))
        (Ty.toHOL_function _ _)) (.app
          (.constant (equalityOperand?_none _ (admitted_abs_ne_equality accepted))
            (Ty.toHOL_function _ _)) (.free rfl))
    · exact .free rfl

set_option backward.isDefEq.respectTransparency false in
/-- The constructed model satisfies the actual retained first source equation. -/
theorem sourceModel_models_abstractionRepresentation :
    (sourceModel accepted substitution replacements model holds).models
      (abstractionRepresentationFormula (request := request) (result := result) substitution) := by
  change (sourceModel accepted substitution replacements model holds).Eqv _ _ _
  apply (eqv_iff_eq _ (sourceModel_fullDomains accepted substitution replacements model holds) _ _ _).mpr
  exact sourceModel_abstraction_representation accepted substitution replacements model holds _

set_option backward.isDefEq.respectTransparency false in
/-- The constructed model satisfies the actual retained second source
formula, using old predicate meaning preservation and the witnessed subtype law. -/
theorem sourceModel_models_representationAbstraction (full : model.FullDomains) :
    (sourceModel accepted substitution replacements model holds).models
      (representationAbstractionFormula accepted substitution) := by
  let value := (sourceModel accepted substitution replacements model holds).constDen
    (.variable ⟨Name.global "r", (instanceTerm substitution result.core.witness).ty⟩ rfl)
  have meaning : (((sourceModel accepted substitution replacements model holds).denote
      (instanceImage accepted substitution).predicateTerm (fun v => nomatch v)) value).down ↔
      (sourceModel accepted substitution replacements model holds).Eqv
        (instanceTerm substitution result.core.witness).ty.toHOL
        ((sourceModel accepted substitution replacements model holds).constDen
          (.constant result.output.representationConstant
            (Ty.function (sourceCarrierType request substitution)
              (instanceTerm substitution result.core.witness).ty) (Ty.toHOL_function _ _))
          ((sourceModel accepted substitution replacements model holds).constDen
            (.constant result.output.abstractionConstant
              (Ty.function (instanceTerm substitution result.core.witness).ty
                (sourceCarrierType request substitution)) (Ty.toHOL_function _ _)) value)) value := by
    rw [sourceModel_predicate accepted substitution replacements model holds full]
    exact (sourceModel_predicate_iff_representation_abstraction accepted substitution replacements model holds _).trans
      (eqv_iff_eq _ (sourceModel_fullDomains accepted substitution replacements model holds) _ _ _).symm
  convert meaning using 1
  simp only [representationAbstractionFormula, abstractionTerm, representationTerm,
    equalityLambda, HOL.HenkinModel.models, HOL.PreModel.models, HOL.HenkinModel.denote,
    HOL.PreModel.denote, HOL.PreModel.extend, HOL.PreModel.Eqv, value]
  apply iff_congr
  · exact iff_of_eq (congrArg (fun function => (function value).down)
      (HOL.HenkinModel.denote_closed_valuation_eq
        (sourceModel accepted substitution replacements model holds)
        (instanceImage accepted substitution).predicateTerm _ _))
  · rfl

/-- Every compositional translation of the two actual retained conclusions
is true in the constructed source model; the conclusion is independent of
which well-typed translation derivation supplies the formulas. -/
theorem sourceModel_models_retained_equations (full : model.FullDomains)
    {first second : HOL.ClosedFormula Symbol}
    (firstTranslation : TranslatesCompositionally []
      (instanceTerm substitution result.output.abstractionRepresentationTheorem.sequent.concl).term
      .prop first)
    (secondTranslation : TranslatesCompositionally []
      (instanceTerm substitution result.output.representationAbstractionTheorem.sequent.concl).term
      .prop second) :
    (sourceModel accepted substitution replacements model holds).models first ∧
      (sourceModel accepted substitution replacements model holds).models second := by
  rw [← (abstractionRepresentation_translated accepted substitution).unique_eq firstTranslation,
    ← (representationAbstraction_translated accepted substitution).unique_eq secondTranslation]
  exact ⟨sourceModel_models_abstractionRepresentation accepted substitution replacements model holds,
    sourceModel_models_representationAbstraction accepted substitution replacements model holds full⟩

/-- Fresh source names cannot be redeclared in the actual admitted successor
context, even when the second request supplies an otherwise checked witness. -/
theorem repeated_source_definition_refused
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (otherInstances : InstanceWitnesses) :
    admitSourceTypeInTheory result.context otherInstances request = none := by
  have names := (admitTypeInTheory_result
    (admitSourceTypeInTheory_result accepted).2.1).2.2.2.2.1
  cases repeated : admitSourceTypeInTheory result.context otherInstances request with
  | none => rfl
  | some other =>
      have fresh := (admitted_names_fresh repeated).1
      rw [names] at fresh
      exact False.elim (fresh (by simp [extendTypeNames]))

theorem instanceTerm_empty (term : CanonicalTerm) : instanceTerm TypeSubst.empty term = term := by
  apply CanonicalTerm.ext_term
  exact TermSubst.typeInstance_identity term.term

namespace Controls

open DefinitionAdapters.ContextControls

/-- A genuine original source admission yields a model of both actual
retained equation translations, without assuming either equation's truth. -/
theorem identity_retained_equations_have_model :
    ∃ output, ∃ accepted : admitSourceTypeInTheory coreContext equalityCertificates
      identityTypeRequest = some output,
      ∃ source : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol,
        source.models (abstractionRepresentationFormula
          (request := identityTypeRequest) (result := output) TypeSubst.empty) ∧
        source.models (representationAbstractionFormula accepted TypeSubst.empty) := by
  have actualOutput : ∃ output, admitSourceTypeInTheory coreContext equalityCertificates
      identityTypeRequest = some output := by
    cases admitted : admitSourceTypeInTheory coreContext equalityCertificates identityTypeRequest with
    | none =>
        have nonempty := ModelInterpretation.Controls.identity_source_admitted
        rw [admitted] at nonempty
        cases nonempty
    | some output => exact ⟨output, rfl⟩
  obtain ⟨output, admitted⟩ := actualOutput
  have replacements : ∀ name replacement, TypeSubst.empty.lookup name = some replacement →
      TypeFormed coreContext.signature replacement := by
    intro name replacement found
    simp [TypeSubst.lookup, TypeSubst.empty] at found
  have imageHolds : ModelInterpretation.Controls.initialModel.{w}.models
      (instanceImage admitted TypeSubst.empty).formula := by
    apply ((instanceImage admitted TypeSubst.empty).holds_iff
      ModelInterpretation.Controls.initialModel
      (ModelInterpretation.Controls.identityImage.conclusionTranslated.of_term_eq
        (congrArg CanonicalTerm.term (instanceTerm_empty
          identityTypeRequest.existence.sequent.concl)).symm)).mpr
    exact ModelInterpretation.Controls.identityImage_holds _
      ModelInterpretation.Controls.initialModel_fullDomains
  refine ⟨output, admitted, sourceModel admitted TypeSubst.empty replacements
    ModelInterpretation.Controls.initialModel imageHolds, ?_, ?_⟩
  · exact sourceModel_models_abstractionRepresentation admitted TypeSubst.empty replacements
      ModelInterpretation.Controls.initialModel imageHolds
  · exact sourceModel_models_representationAbstraction admitted TypeSubst.empty replacements
      ModelInterpretation.Controls.initialModel imageHolds
      ModelInterpretation.Controls.initialModel_fullDomains

/-- The actual admitted identity type cannot be admitted twice. -/
theorem identity_redeclaration_refused {output : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory coreContext equalityCertificates identityTypeRequest = some output) :
    admitSourceTypeInTheory output.context equalityCertificates identityTypeRequest = none :=
  repeated_source_definition_refused accepted equalityCertificates

/-- Primitive spellings do not collapse a defined operator's provenance. -/
theorem defined_function_spelling_atomic (substitution : TypeSubst) :
    (sourceCarrierType { identityTypeRequest with typeName := Name.global "->" } substitution).IsAtomic :=
  sourceCarrierType_atomic _ _

end Controls

end Mettapedia.Languages.HOLLight.SourceTypeDefinitionTransport
