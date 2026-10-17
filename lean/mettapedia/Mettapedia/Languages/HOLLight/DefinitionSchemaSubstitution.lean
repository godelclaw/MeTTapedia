import Mettapedia.Languages.HOLLight.DefinitionSchemaInstances

/-!
# Earned source-substitution closure of universal definition schemas

Originally formed closed source bodies translate with equality expanded and
without free-variable Symbols. Actual source substitution therefore acts on
their universal closures through its type component. The resulting orbit is
an actual substitution-closed HOL background, not an assumed closure licence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.DefinitionSchemaSubstitution

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters MixedDefinitionHistory MixedDefinitionModelFamily
open SourceTypeDefinitionTransport UniformTypeDefinitionModels DefinitionSchemaClosure DefinitionSchemaInstances

universe w

/-- A syntactic support property of original translated schemas. Constants
retain their source identities; primitive equality is already translated into
the original equality lambda rather than retained as a raw constant. -/
inductive OrdinarySymbols : {context : HOL.Ctx AtomicTy} → {type : HOL.Ty AtomicTy} →
    HOL.Term Symbol context type → Prop where
  | var {context type} (index : HOL.Var context type) : OrdinarySymbols (.var index)
  | constant {context type} (constant : Const) (annotation : Ty) (typed : annotation.toHOL = type)
      (different : constant ≠ Const.equality) :
      OrdinarySymbols (.const (.constant constant annotation typed) : HOL.Term Symbol context type)
  | app {context domain codomain} {function : HOL.Term Symbol context (.arr domain codomain)}
      {argument : HOL.Term Symbol context domain} :
      OrdinarySymbols function → OrdinarySymbols argument → OrdinarySymbols (.app function argument)
  | lam {context domain codomain} {body : HOL.Term Symbol (domain :: context) codomain} :
      OrdinarySymbols body → OrdinarySymbols (.lam body)
  | top {context} : OrdinarySymbols (.top : HOL.Formula Symbol context)
  | bot {context} : OrdinarySymbols (.bot : HOL.Formula Symbol context)
  | and {context} {first second : HOL.Formula Symbol context} :
      OrdinarySymbols first → OrdinarySymbols second → OrdinarySymbols (.and first second)
  | or {context} {first second : HOL.Formula Symbol context} :
      OrdinarySymbols first → OrdinarySymbols second → OrdinarySymbols (.or first second)
  | imp {context} {first second : HOL.Formula Symbol context} :
      OrdinarySymbols first → OrdinarySymbols second → OrdinarySymbols (.imp first second)
  | not {context} {body : HOL.Formula Symbol context} : OrdinarySymbols body → OrdinarySymbols (.not body)
  | eq {context type} {first second : HOL.Term Symbol context type} :
      OrdinarySymbols first → OrdinarySymbols second → OrdinarySymbols (.eq first second)
  | all {context type} {body : HOL.Formula Symbol (type :: context)} :
      OrdinarySymbols body → OrdinarySymbols (.all body)
  | ex {context type} {body : HOL.Formula Symbol (type :: context)} :
      OrdinarySymbols body → OrdinarySymbols (.ex body)

/-- The original translation and equality declaration earn the support
property from actual source closedness and annotation admission. -/
theorem ordinary_of_closed_translation (signature : Signature) (parameter : Name)
    (registered : signature.constants Const.equality = some (Ty.equality (.var parameter)))
    {context : HOL.Ctx AtomicTy} {source : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol context type}
    (translation : TranslatesCompositionally context source type target)
    (formed : AnnotationsFormed signature source) (closed : source.HasNoFreeVariables) :
    OrdinarySymbols target := by
  induction translation with
  | equality => exact .lam (.lam (.eq (.var _) (.var _)))
  | constant unrecognized typed =>
      cases formed with
      | constant _ declared =>
          exact .constant _ _ typed
            (ConstantHistoryInstanceCoherence.ordinary_constant_ne_equality signature parameter registered declared unrecognized)
  | free => cases closed
  | bound index => exact .var index
  | app _ _ functionIH argumentIH =>
      cases formed with
      | app functionFormed argumentFormed =>
          cases closed with
          | app functionClosed argumentClosed =>
              exact .app (functionIH functionFormed functionClosed)
                (argumentIH argumentFormed argumentClosed)
  | abs _ _ bodyIH =>
      cases formed with
      | abs _ bodyFormed =>
          cases closed with
          | abs bodyClosed => exact .lam (bodyIH bodyFormed bodyClosed)

/-- The source constant identities and their non-equality status are
unchanged by every original type substitution. -/
theorem OrdinarySymbols.typeInstance {context : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    {term : HOL.Term Symbol context type} (ordinary : OrdinarySymbols term) (substitution : TypeSubst) :
    OrdinarySymbols (HOL.mapTypes substitution.baseInstance substitution.symbolInstance term) := by
  induction ordinary with
  | var index => exact .var _
  | constant constant annotation typed different =>
      exact .constant constant (substitution.apply annotation) _ different
  | app _ _ functionIH argumentIH => exact .app functionIH argumentIH
  | lam _ bodyIH => exact .lam bodyIH
  | top => exact .top
  | bot => exact .bot
  | and _ _ firstIH secondIH => exact .and firstIH secondIH
  | or _ _ firstIH secondIH => exact .or firstIH secondIH
  | imp _ _ firstIH secondIH => exact .imp firstIH secondIH
  | not _ bodyIH => exact .not bodyIH
  | eq _ _ firstIH secondIH => exact .eq firstIH secondIH
  | all _ bodyIH => exact .all bodyIH
  | ex _ bodyIH => exact .ex bodyIH

private theorem symbolImage_constant (substitution : TypeCorrectTermSubstitution)
    (constant : Const) (annotation : Ty) {type : HOL.Ty AtomicTy} (typed : annotation.toHOL = type)
    (different : constant ≠ Const.equality) :
    substitution.symbolImage (.constant constant annotation typed) = .const (.constant constant annotation typed) := by
  unfold TypeCorrectTermSubstitution.symbolImage
  apply TranslatesCompositionally.unique_eq (closedTranslation_spec _ _)
  apply TranslatesCompositionally.constant
  simp [equalityOperand?, Const.same_eq_true_iff, different]

private theorem OrdinarySymbols.substConst_self {context : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    {term : HOL.Term Symbol context type} (ordinary : OrdinarySymbols term)
    (substitution : TypeCorrectTermSubstitution) :
    HOL.substConst substitution.symbolImage term = term := by
  induction ordinary with
  | var index => rfl
  | constant constant annotation typed different =>
      simp only [HOL.substConst, symbolImage_constant substitution constant annotation typed different,
        HOL.weakenCtx_const]
  | app _ _ functionIH argumentIH => simp only [HOL.substConst, functionIH, argumentIH]
  | lam _ bodyIH => simp only [HOL.substConst, bodyIH]
  | top => rfl
  | bot => rfl
  | and _ _ firstIH secondIH => simp only [HOL.substConst, firstIH, secondIH]
  | or _ _ firstIH secondIH => simp only [HOL.substConst, firstIH, secondIH]
  | imp _ _ firstIH secondIH => simp only [HOL.substConst, firstIH, secondIH]
  | not _ bodyIH => simp only [HOL.substConst, bodyIH]
  | eq _ _ firstIH secondIH => simp only [HOL.substConst, firstIH, secondIH]
  | all _ bodyIH => simp only [HOL.substConst, bodyIH]
  | ex _ bodyIH => simp only [HOL.substConst, bodyIH]

/-- This is equality of the actual complete source substitution operation.
It includes the symbol replacement phase rather than assuming it disappears. -/
theorem targetMap_eq_typeMap {context : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    {term : HOL.Term Symbol context type} (ordinary : OrdinarySymbols term)
    (substitution : TypeCorrectTermSubstitution) :
    substitution.targetMap term = HOL.mapTypes substitution.raw.types.baseInstance
      substitution.raw.types.symbolInstance term :=
  (ordinary.typeInstance substitution.raw.types).substConst_self substitution

/-- Every free source-variable Symbol is absent from these actual terms. -/
theorem OrdinarySymbols.variableFree {context : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    {term : HOL.Term Symbol context type} (ordinary : OrdinarySymbols term) (sourceVar : SourceVar) :
    HOL.NoConstOccurrence (Symbol.ofVar sourceVar) term := by
  induction ordinary with
  | var => exact .var
  | constant constant annotation typed _ =>
      exact Symbol.noConstOccurrence_const _ _ (Symbol.sigma_constant_ne_ofVar constant annotation typed sourceVar)
  | app _ _ functionIH argumentIH => exact .app functionIH argumentIH
  | lam _ bodyIH => exact .lam bodyIH
  | top => exact .top
  | bot => exact .bot
  | and _ _ firstIH secondIH => exact .and firstIH secondIH
  | or _ _ firstIH secondIH => exact .or firstIH secondIH
  | imp _ _ firstIH secondIH => exact .imp firstIH secondIH
  | not _ bodyIH => exact .not bodyIH
  | eq _ _ firstIH secondIH => exact .eq firstIH secondIH
  | all _ bodyIH => exact .all bodyIH
  | ex _ bodyIH => exact .ex bodyIH

/-- The background contains exactly finite iterations of the original type
image operation. This is a set of source formula images, not a proof checker
or an alternative source certificate carrier. -/
inductive TypeImageOrbit (original : HOL.ClosedFormula Symbol) : HOL.ClosedFormula Symbol → Prop where
  | original : TypeImageOrbit original original
  | image (substitution : TypeSubst) {formula : HOL.ClosedFormula Symbol} :
      TypeImageOrbit original formula → TypeImageOrbit original
        (HOL.mapTypes substitution.baseInstance substitution.symbolInstance formula)

def schemaTheory (original : HOL.ClosedFormula Symbol) : HOL.ClosedTheorySet Symbol :=
  {formula | TypeImageOrbit original formula}

theorem TypeImageOrbit.ordinary {original formula : HOL.ClosedFormula Symbol}
    (images : TypeImageOrbit original formula) (ordinary : OrdinarySymbols original) :
    OrdinarySymbols formula := by
  induction images with
  | original => exact ordinary
  | image substitution _ ih => exact ih.typeInstance substitution

/-- Actual full source-substitution closure is derived from the original
support proof and the actual targetMap equality, including its symbol phase. -/
theorem schemaTheory_closed {original : HOL.ClosedFormula Symbol} (ordinary : OrdinarySymbols original) :
    VariableFreeSubstitutionClosed (schemaTheory original) where
  variableFree := fun _ member sourceVar => (member.ordinary ordinary).variableFree sourceVar
  substitutionClosed := by
    intro substitution formula member
    rw [targetMap_eq_typeMap (member.ordinary ordinary)]
    exact TypeImageOrbit.image substitution.raw.types member

/-- Every iterated image is truthful whenever all actual model reducts
validate the original schema. Composition uses the original source type
substitution and its full model data, including Symbol meanings. -/
theorem schemaTheory_models (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) {original : HOL.ClosedFormula Symbol}
    (valid : ∀ substitution : TypeSubst, (reindexedModel substitution M).models original) :
    ∀ formula ∈ schemaTheory original, M.models formula := by
  intro formula member
  have allReducts : ∀ substitution : TypeSubst, (reindexedModel substitution M).models formula := by
    induction member with
    | original => exact valid
    | image next _ ih =>
        intro substitution
        apply (reindexedModel_models next _ (reindexedModel_fullDomains substitution M) _).mp
        rw [reindexedModel_composition]
        exact ih (next.compose substitution)
  have identity := allReducts TypeSubst.empty
  rwa [reindexedModel_identity M full] at identity

theorem OrdinarySymbols.rename {context target : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    {term : HOL.Term Symbol context type} (ordinary : OrdinarySymbols term)
    (contextMap : HOL.Rename AtomicTy context target) : OrdinarySymbols (HOL.rename contextMap term) := by
  induction ordinary generalizing target with
  | var index => exact .var _
  | constant constant annotation typed different => exact .constant constant annotation typed different
  | app _ _ functionIH argumentIH => exact .app (functionIH contextMap) (argumentIH contextMap)
  | lam _ bodyIH => exact .lam (bodyIH (HOL.Rename.lift contextMap))
  | top => exact .top
  | bot => exact .bot
  | and _ _ firstIH secondIH => exact .and (firstIH contextMap) (secondIH contextMap)
  | or _ _ firstIH secondIH => exact .or (firstIH contextMap) (secondIH contextMap)
  | imp _ _ firstIH secondIH => exact .imp (firstIH contextMap) (secondIH contextMap)
  | not _ bodyIH => exact .not (bodyIH contextMap)
  | eq _ _ firstIH secondIH => exact .eq (firstIH contextMap) (secondIH contextMap)
  | all _ bodyIH => exact .all (bodyIH (HOL.Rename.lift contextMap))
  | ex _ bodyIH => exact .ex (bodyIH (HOL.Rename.lift contextMap))

private theorem equalityLambda_ordinary (type : HOL.Ty AtomicTy) {context : HOL.Ctx AtomicTy} :
    OrdinarySymbols (equalityLambda (Γ := context) type) :=
  .lam (.lam (.eq (.var _) (.var _)))

section TypeDefinition

variable {context : TheoryContext} {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest}
  {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)

include accepted in
private theorem abstraction_ne_equality : result.output.abstractionConstant ≠ Const.equality := by
  rw [(admitSourceTypeInTheory_pointwise accepted).2.1]
  intro same
  have origins := (Const.mk.inj same).2
  cases origins

include accepted in
private theorem representation_ne_equality : result.output.representationConstant ≠ Const.equality := by
  rw [(admitSourceTypeInTheory_pointwise accepted).2.2.1]
  intro same
  have origins := (Const.mk.inj same).2
  cases origins

include accepted in
/-- Source admission supplies the exact declared constant provenance used
by the first original universal schema. -/
theorem ordinary_abstractionSchema : OrdinarySymbols
    (abstractionRepresentationSchema (request := request) (result := result) TypeSubst.empty) := by
  apply OrdinarySymbols.all
  apply OrdinarySymbols.app
  · apply OrdinarySymbols.app
    · exact equalityLambda_ordinary _
    · apply OrdinarySymbols.app
      · exact (OrdinarySymbols.constant _ _ _ (abstraction_ne_equality accepted)).rename HOL.Rename.weaken
      · apply OrdinarySymbols.app
        · exact (OrdinarySymbols.constant _ _ _ (representation_ne_equality accepted)).rename HOL.Rename.weaken
        · exact .var _
  · exact .var _

/-- The actual admitted predicate's source closedness and equality declaration
also earn the support of the second original universal schema. -/
theorem ordinary_representationSchema (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter))) :
    OrdinarySymbols (representationAbstractionSchema accepted TypeSubst.empty) := by
  have predicateFormed := (admitTypeInTheory_result (admitSourceTypeInTheory_result accepted).2.1).2.1
  have predicateClosed := predicate_closed accepted
  have predicateOrdinary := ordinary_of_closed_translation context.signature parameter registered
    (instanceImage accepted TypeSubst.empty).predicateTranslated
    (by simpa only [instanceTerm, TypeCorrectTermSubstitution.apply, TermSubst.applyChecked, TermSubst.typeInstance_identity] using predicateFormed)
    (by simpa only [instanceTerm, TypeCorrectTermSubstitution.apply, TermSubst.applyChecked, TermSubst.typeInstance_identity] using predicateClosed)
  apply OrdinarySymbols.all
  apply OrdinarySymbols.app
  · apply OrdinarySymbols.app
    · exact equalityLambda_ordinary _
    · exact .app (predicateOrdinary.rename HOL.Rename.weaken) (.var _)
  · apply OrdinarySymbols.app
    · apply OrdinarySymbols.app
      · exact equalityLambda_ordinary _
      · apply OrdinarySymbols.app
        · exact (OrdinarySymbols.constant _ _ _ (representation_ne_equality accepted)).rename HOL.Rename.weaken
        · apply OrdinarySymbols.app
          · exact (OrdinarySymbols.constant _ _ _ (abstraction_ne_equality accepted)).rename HOL.Rename.weaken
          · exact .var _
    · exact .var _

/-- This background is made from the original two universal schemas and
their iterated actual type images. Pointwise free-variable rows remain source
consequences obtained by universal elimination, not background members. -/
noncomputable def typeDefinitionTheory : HOL.ClosedTheorySet Symbol :=
  schemaTheory (abstractionRepresentationSchema (request := request) (result := result) TypeSubst.empty) ∪
    schemaTheory (representationAbstractionSchema accepted TypeSubst.empty)

/-- The actual full source-substitution background licence is constructed
from admission and the original primitive equality declaration. -/
theorem typeDefinitionTheory_closed (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter))) :
    VariableFreeSubstitutionClosed (typeDefinitionTheory accepted) := by
  have first := schemaTheory_closed (ordinary_abstractionSchema accepted)
  have second := schemaTheory_closed (ordinary_representationSchema accepted parameter registered)
  constructor
  · intro formula member sourceVar
    rcases member with firstMember | secondMember
    · exact first.variableFree formula firstMember sourceVar
    · exact second.variableFree formula secondMember sourceVar
  · intro substitution formula member
    rcases member with firstMember | secondMember
    · exact Or.inl (first.substitutionClosed substitution formula firstMember)
    · exact Or.inr (second.substitutionClosed substitution formula secondMember)

theorem typeDefinitionTheory_models {initial : TheoryContext} {records : List Theorem}
    {history : History initial context records} (prior : Construction.{w} history)
    (proof : HOL.ClosedTheorySet.Provable (equationTheory records)
      (TypeAdmission.admittedImage accepted).formula)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (primitives : Primitives initial) :
    ∀ formula ∈ typeDefinitionTheory accepted,
      (MixedTypeDefinitionModels.model prior accepted proof other assignment).models formula := by
  let M := MixedTypeDefinitionModels.model prior accepted proof other assignment
  have full := MixedTypeDefinitionModels.model_fullDomains prior accepted proof other assignment
  intro formula member
  rcases member with firstMember | secondMember
  · apply schemaTheory_models M full _ formula firstMember
    intro substitution
    apply (reindexedModel_models substitution M full _).mpr
    exact models_typeMapped_abstractionSchema prior accepted proof other assignment primitives substitution
  · apply schemaTheory_models M full _ formula secondMember
    intro substitution
    apply (reindexedModel_models substitution M full _).mpr
    exact models_typeMapped_representationSchema prior accepted proof other assignment primitives substitution

/-- The exact original first finite axiom is a consequence of its genuine
universal background schema, rather than a background free-variable axiom. -/
theorem abstraction_row_provable :
    CompositionallyProvable (typeDefinitionTheory accepted)
      result.output.abstractionRepresentationTheorem.sequent := by
  refine ⟨_, (abstractionRepresentation_translated accepted TypeSubst.empty).of_term_eq
    (TermSubst.typeInstance_identity _), ?_⟩
  apply HOL.ClosedTheorySet.provable_mono (fun member => Or.inl member)
  apply abstractionRepresentation_provable _ TypeSubst.empty
  apply HOL.ClosedTheorySet.provable_of_mem
  exact Or.inl TypeImageOrbit.original

/-- Universal elimination also recovers the exact second returned finite
axiom, with the original predicate and source-variable identity. -/
theorem representation_row_provable :
    CompositionallyProvable (typeDefinitionTheory accepted)
      result.output.representationAbstractionTheorem.sequent := by
  refine ⟨_, (representationAbstraction_translated accepted TypeSubst.empty).of_term_eq
    (TermSubst.typeInstance_identity _), ?_⟩
  apply HOL.ClosedTheorySet.provable_mono (fun member => Or.inl member)
  apply representationAbstraction_provable accepted _ TypeSubst.empty
  apply HOL.ClosedTheorySet.provable_of_mem
  exact Or.inr TypeImageOrbit.original

/-- Both original returned sequents have their usual kernel translation
proofs in this earned background. This is the finite-axiom interface consumed
by the existing configured HOL/MM0 meaning theorem. -/
theorem definition_rows_translated_provable :
    ∀ sequent ∈ [result.output.abstractionRepresentationTheorem.sequent,
      result.output.representationAbstractionTheorem.sequent],
      TranslatedProvable (typeDefinitionTheory accepted) sequent := by
  intro sequent member
  rcases List.mem_cons.mp member with rfl | member
  · exact (translatedProvable_iff_compositionallyProvable _ _).mpr (abstraction_row_provable accepted)
  · have same := List.mem_singleton.mp member
    subst sequent
    exact (translatedProvable_iff_compositionallyProvable _ _).mpr (representation_row_provable accepted)

/-- The original unbound first row is a derivable consequence but is not
itself a member of the variable-free background. -/
theorem unclosed_first_not_background (parameter : Name)
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter))) :
    abstractionRepresentationFormula (request := request) (result := result) TypeSubst.empty ∉
      typeDefinitionTheory accepted := by
  intro member
  exact original_abstractionRepresentation_has_free_value TypeSubst.empty
    ((typeDefinitionTheory_closed accepted parameter registered).variableFree _ member _)

end TypeDefinition

namespace Controls

open MixedDefinitionHistory.Controls MixedDefinitionModelFamily.Controls

theorem second_background_closed :
    VariableFreeSubstitutionClosed (typeDefinitionTheory second_result_admitted) :=
  typeDefinitionTheory_closed second_result_admitted primitives.equalityParameter
    (afterTypeHistory.includes.2 _ _ primitives.equalityRegistered)

theorem second_background_truth (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∀ formula ∈ typeDefinitionTheory second_result_admitted,
      (MixedTypeDefinitionModels.Controls.secondModel other assignment).models formula :=
  typeDefinitionTheory_models second_result_admitted afterFirstConstruction
    (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived)
    other assignment primitives

theorem second_original_rows_provable :
    ∀ sequent ∈ [secondResult.output.abstractionRepresentationTheorem.sequent,
      secondResult.output.representationAbstractionTheorem.sequent],
      TranslatedProvable (typeDefinitionTheory second_result_admitted) sequent :=
  definition_rows_translated_provable second_result_admitted

theorem second_unclosed_not_background :
    abstractionRepresentationFormula (request := secondRequest) (result := secondResult) TypeSubst.empty ∉
      typeDefinitionTheory second_result_admitted :=
  unclosed_first_not_background second_result_admitted primitives.equalityParameter
    (afterTypeHistory.includes.2 _ _ primitives.equalityRegistered)

end Controls

end Mettapedia.Languages.HOLLight.DefinitionSchemaSubstitution
