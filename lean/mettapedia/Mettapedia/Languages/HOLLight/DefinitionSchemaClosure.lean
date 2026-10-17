import Mettapedia.Languages.HOLLight.MixedDefinitionModels
import Mettapedia.Logic.HOL.CanonicalQuantifierBridges

/-!
# Universal schemas for original HOL definition equations

The original returned type equations contain a free source value. Their
universal closures expose the actual all-value abstraction/representation
laws, and elimination recovers exactly the retained pointwise formulas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.DefinitionSchemaClosure

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation ModelInstanceCoherence
open DefinitionAdapters MixedDefinitionHistory MixedDefinitionModelFamily
open SourceTypeDefinitionTransport UniformTypeDefinitionModels

universe w

variable {initial context : TheoryContext} {records : List Theorem}
  {history : History initial context records} (prior : Construction.{w} history)
  {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest}
  {result : SourceTypeDefinitionResult}
  (accepted : admitSourceTypeInTheory context instances request = some result)
  (proof : HOL.ClosedTheorySet.Provable (equationTheory records)
    (TypeAdmission.admittedImage accepted).formula)
  (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

noncomputable def abstractionRepresentationBody (substitution : TypeSubst) :
    HOL.Formula Symbol [(sourceCarrierType request substitution).toHOL] :=
  .app (.app (equalityLambda (sourceCarrierType request substitution).toHOL)
    (.app (HOL.weaken (abstractionTerm (request := request) (result := result) substitution))
      (.app (HOL.weaken (representationTerm (request := request) (result := result) substitution)) (.var .vz))))
    (.var .vz)

noncomputable def abstractionRepresentationSchema (substitution : TypeSubst) : HOL.ClosedFormula Symbol :=
  .all (abstractionRepresentationBody (request := request) (result := result) substitution)

noncomputable def representationAbstractionBody (substitution : TypeSubst) :
    HOL.Formula Symbol [(instanceTerm substitution result.core.witness).ty.toHOL] :=
  .app (.app (equalityLambda .prop)
    (.app (HOL.weaken (instanceImage accepted substitution).predicateTerm) (.var .vz)))
    (.app (.app (equalityLambda (instanceTerm substitution result.core.witness).ty.toHOL)
      (.app (HOL.weaken (representationTerm (request := request) (result := result) substitution))
        (.app (HOL.weaken (abstractionTerm (request := request) (result := result) substitution)) (.var .vz))))
      (.var .vz))

noncomputable def representationAbstractionSchema (substitution : TypeSubst) : HOL.ClosedFormula Symbol :=
  .all (representationAbstractionBody accepted substitution)

private theorem instantiate_equalityLambda {type : HOL.Ty AtomicTy}
    (value : HOL.ClosedTerm Symbol type) (operand : HOL.Ty AtomicTy) :
    HOL.instantiate value (equalityLambda operand) = equalityLambda operand := by
  rfl

/-- Universal elimination at the original free source value recovers exactly
the returned first equation, including its original Symbol identities. -/
theorem instantiate_abstractionRepresentation (substitution : TypeSubst) :
    HOL.instantiate
      (.const (.variable ⟨Name.global "a", sourceCarrierType request substitution⟩ rfl))
      (abstractionRepresentationBody (request := request) (result := result) substitution) =
      abstractionRepresentationFormula (request := request) (result := result) substitution := by
  simp only [abstractionRepresentationBody, abstractionRepresentationFormula,
    HOL.instantiate, HOL.subst]
  rw [show HOL.subst (HOL.Subst.single
    (.const (.variable ⟨Name.global "a", sourceCarrierType request substitution⟩ rfl)))
    (equalityLambda (sourceCarrierType request substitution).toHOL) = equalityLambda _ from rfl]
  rfl

/-- Universal elimination likewise recovers the second original retained equation. -/
theorem instantiate_representationAbstraction (substitution : TypeSubst) :
    HOL.instantiate
      (.const (.variable ⟨Name.global "r", (instanceTerm substitution result.core.witness).ty⟩ rfl))
      (representationAbstractionBody accepted substitution) =
      representationAbstractionFormula accepted substitution := by
  simp only [representationAbstractionBody, representationAbstractionFormula,
    HOL.instantiate, HOL.subst]
  rw [show HOL.subst (HOL.Subst.single
    (.const (.variable ⟨Name.global "r", (instanceTerm substitution result.core.witness).ty⟩ rfl)))
    (equalityLambda .prop) = equalityLambda _ from rfl]
  rw [show HOL.subst (HOL.Subst.single
    (.const (.variable ⟨Name.global "r", (instanceTerm substitution result.core.witness).ty⟩ rfl)))
    (equalityLambda (instanceTerm substitution result.core.witness).ty.toHOL) = equalityLambda _ from rfl]
  congr 2
  congr 1
  exact HOL.instantiate_weaken _ _

theorem abstractionRepresentation_provable (theory : HOL.ClosedTheorySet Symbol)
    (substitution : TypeSubst)
    (schema : theory.Provable (abstractionRepresentationSchema (request := request) (result := result) substitution)) :
    theory.Provable (abstractionRepresentationFormula (request := request) (result := result) substitution) := by
  have instantiated :=  HOL.ClosedTheorySet.provable_all_elim
    (.const (.variable ⟨Name.global "a", sourceCarrierType request substitution⟩ rfl)) schema
  rw [instantiate_abstractionRepresentation] at instantiated
  exact instantiated

theorem representationAbstraction_provable (theory : HOL.ClosedTheorySet Symbol)
    (substitution : TypeSubst)
    (schema : theory.Provable (representationAbstractionSchema accepted substitution)) :
    theory.Provable (representationAbstractionFormula accepted substitution) := by
  have instantiated :=  HOL.ClosedTheorySet.provable_all_elim
    (.const (.variable ⟨Name.global "r", (instanceTerm substitution result.core.witness).ty⟩ rfl)) schema
  rw [instantiate_representationAbstraction] at instantiated
  exact instantiated

set_option backward.isDefEq.respectTransparency false in
theorem family_models_abstractionRepresentation {initial context : TheoryContext}
    {theory : HOL.ClosedTheorySet Symbol} (prior : DefinitionModelFamily.Family.{w} initial context theory)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable theory (TypeAdmission.admittedImage accepted).formula)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst) :
    (TypeDefinitionModels.model prior accepted proof other assignment).models
      (abstractionRepresentationSchema (request := request) (result := result) substitution) := by
  change ∀ value, _ → _
  intro value _
  change (TypeDefinitionModels.model prior accepted proof other assignment).Eqv _ _ _
  apply (HOL.HenkinModel.eqv_iff_eq_of_fullDomains _ (TypeDefinitionModels.model_fullDomains prior accepted proof other assignment) _ _).mpr
  simpa only [abstractionRepresentationSchema, abstractionRepresentationBody, abstractionTerm, representationTerm,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend, HOL.weaken, HOL.rename, abstractionAnnotation, representationAnnotation, instanceTerm, TypeCorrectTermSubstitution.apply, TermSubst.applyChecked] using
      TypeDefinitionModels.model_abstraction_representation prior accepted proof other assignment substitution value

theorem models_abstractionRepresentation (substitution : TypeSubst) :
    (MixedTypeDefinitionModels.model prior accepted proof other assignment).models
      (abstractionRepresentationSchema (request := request) (result := result) substitution) := by
  exact family_models_abstractionRepresentation prior.toFamily accepted proof other assignment substitution

private theorem universal_reconstruction
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (represented new : HOL.Ty AtomicTy)
    (predicate : HOL.ClosedTerm Symbol (.arr represented .prop))
    (abstraction : HOL.ClosedTerm Symbol (.arr represented new))
    (representation : HOL.ClosedTerm Symbol (.arr new represented))
    (law : ∀ (valuation : M.Valuation []) (value : HOL.Ty.denote M.Carrier represented),
      ((M.denote predicate valuation) value).down ↔
        M.Eqv represented ((M.denote representation valuation)
          ((M.denote abstraction valuation) value)) value) :
    M.models (.all (.app (.app (equalityLambda .prop)
      (.app (HOL.weaken predicate) (.var .vz)))
      (.app (.app (equalityLambda represented)
        (.app (HOL.weaken representation) (.app (HOL.weaken abstraction) (.var .vz)))) (.var .vz)))) := by
  change ∀ value, _ → _
  intro value _
  simp only [equalityLambda, HOL.PreModel.denote, HOL.PreModel.extend, HOL.PreModel.Eqv]
  simp only [HOL.Soundness.denote_weaken]
  exact law _ value

/-- The original predicate and both original maps satisfy the second
universal schema for every represented value. -/
theorem family_models_representationAbstraction {initial context : TheoryContext}
    {theory : HOL.ClosedTheorySet Symbol} (prior : DefinitionModelFamily.Family.{w} initial context theory)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable theory (TypeAdmission.admittedImage accepted).formula)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (primitives : Primitives initial) (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature (sourceCarrierType request substitution)) :
    (TypeDefinitionModels.model prior accepted proof other assignment).models
      (representationAbstractionSchema accepted substitution) := by
  apply universal_reconstruction
  intro valuation value
  have meaning := TypeDefinitionModels.model_predicate_iff_representation_abstraction
    prior accepted proof other assignment primitives substitution formedCarrier value
  have converted := meaning.trans (HOL.HenkinModel.eqv_iff_eq_of_fullDomains _
    (TypeDefinitionModels.model_fullDomains prior accepted proof other assignment) _ _).symm
  simp only [abstractionTerm, representationTerm, abstractionAnnotation, representationAnnotation,
    instanceTerm, TypeCorrectTermSubstitution.apply, TermSubst.applyChecked, HOL.PreModel.denote] at converted ⊢
  convert converted using 1
  exact iff_of_eq (congrArg (fun predicate => (predicate value).down)
    ((TypeDefinitionModels.model prior accepted proof other assignment).denote_closed_valuation_eq
      (instanceImage accepted substitution).predicateTerm valuation (fun v => nomatch v)))

theorem models_representationAbstraction (primitives : Primitives initial) (substitution : TypeSubst)
    (formedCarrier : TypeFormed result.context.signature (sourceCarrierType request substitution)) :
    (MixedTypeDefinitionModels.model prior accepted proof other assignment).models
      (representationAbstractionSchema accepted substitution) := by
  exact family_models_representationAbstraction prior.toFamily accepted proof other assignment primitives substitution formedCarrier

include accepted in
/-- The original source admission earns closure of its exact retained predicate. -/
theorem predicate_closed : result.core.predicate.term.HasNoFreeVariables := by
  have admitted := (admitSourceTypeInTheory_result accepted).2.1
  have application := (admitTypeInTheory_result admitted).1
  have checkResult := (admitTypeInTheory_result admitted).2.2.2.2.2.1
  obtain ⟨predicate, witness, sourceApplication, _, _, _, closed, _, _, _⟩ :=
    checkTypeOperatorDefinition_result checkResult
  have sameView := Option.some.inj
    ((CanonicalTerm.applicationView?_eq_some _ _ _ application).symm.trans
      (CanonicalTerm.applicationView?_eq_some _ _ _ sourceApplication))
  have samePredicate := congrArg CanonicalTerm.ApplicationView.function sameView
  change result.core.predicate = predicate at samePredicate
  rw [samePredicate]
  exact closed

private theorem closed_type_instance (substitution : TypeSubst) {term : DBTerm}
    (closed : term.HasNoFreeVariables) :
    ((TermSubst.mk substitution []).applyDB term).HasNoFreeVariables := by
  induction closed with
  | const => rw [TermSubst.applyDB_const]; exact .const
  | bound => rw [TermSubst.applyDB_bound]; exact .bound
  | app _ _ function argument => rw [TermSubst.applyDB_app]; exact .app function argument
  | abs _ body => rw [TermSubst.applyDB_abs]; exact .abs body

private theorem closed_no_free_occurrence {term : DBTerm}
    (closed : term.HasNoFreeVariables) (sourceVar : SourceVar) :
    ¬ DBTerm.FreeOccurrence sourceVar term := by
  induction closed with
  | const => intro occurrence; cases occurrence
  | bound => intro occurrence; cases occurrence
  | app _ _ function argument =>
      intro occurrence
      cases occurrence with
      | appFunction found => exact function found
      | appArgument found => exact argument found
  | abs _ body =>
      intro occurrence
      cases occurrence with
      | absBody found => exact body found

theorem predicate_variableFree (substitution : TypeSubst) (sourceVar : SourceVar) :
    HOL.NoConstOccurrence (Symbol.ofVar sourceVar) (instanceImage accepted substitution).predicateTerm :=
  (instanceImage accepted substitution).predicateTranslated.noConstOccurrence sourceVar
    (closed_no_free_occurrence (closed_type_instance substitution (predicate_closed accepted)) sourceVar)

private theorem equalityLambda_variableFree {context : HOL.Ctx AtomicTy}
    (operand : HOL.Ty AtomicTy) (sourceVar : SourceVar) :
    HOL.NoConstOccurrence (Symbol.ofVar sourceVar) (equalityLambda (Γ := context) operand) :=
  .lam (.lam (.eq .var .var))

/-- The first universal schema binds the retained source value instead of
leaving its free-variable Symbol in the background. -/
theorem abstractionRepresentation_variableFree (substitution : TypeSubst) (sourceVar : SourceVar) :
    HOL.NoConstOccurrence (Symbol.ofVar sourceVar)
      (abstractionRepresentationSchema (request := request) (result := result) substitution) := by
  apply HOL.NoConstOccurrence.all
  apply HOL.NoConstOccurrence.app
  · apply HOL.NoConstOccurrence.app
    · exact equalityLambda_variableFree _ _
    · apply HOL.NoConstOccurrence.app
      · exact HOL.noConstOccurrence_rename HOL.Rename.weaken _
          (Symbol.noConstOccurrence_const _ _ (Symbol.sigma_constant_ne_ofVar _ _ _ _))
      · apply HOL.NoConstOccurrence.app
        · exact HOL.noConstOccurrence_rename HOL.Rename.weaken _
            (Symbol.noConstOccurrence_const _ _ (Symbol.sigma_constant_ne_ofVar _ _ _ _))
        · exact .var
  · exact .var

/-- The second schema's admitted predicate is closed, and its original
represented value is bound. Every source-variable Symbol is absent. -/
theorem representationAbstraction_variableFree (substitution : TypeSubst) (sourceVar : SourceVar) :
    HOL.NoConstOccurrence (Symbol.ofVar sourceVar) (representationAbstractionSchema accepted substitution) := by
  apply HOL.NoConstOccurrence.all
  apply HOL.NoConstOccurrence.app
  · apply HOL.NoConstOccurrence.app
    · exact equalityLambda_variableFree _ _
    · exact .app (HOL.noConstOccurrence_rename HOL.Rename.weaken _ (predicate_variableFree accepted substitution sourceVar)) .var
  · apply HOL.NoConstOccurrence.app
    · apply HOL.NoConstOccurrence.app
      · exact equalityLambda_variableFree _ _
      · apply HOL.NoConstOccurrence.app
        · exact HOL.noConstOccurrence_rename HOL.Rename.weaken _
            (Symbol.noConstOccurrence_const _ _ (Symbol.sigma_constant_ne_ofVar _ _ _ _))
        · apply HOL.NoConstOccurrence.app
          · exact HOL.noConstOccurrence_rename HOL.Rename.weaken _
              (Symbol.noConstOccurrence_const _ _ (Symbol.sigma_constant_ne_ofVar _ _ _ _))
          · exact .var
    · exact .var

/-- The retained pointwise row itself is not a variable-free background
sentence. Its source variable must be universally bound before kernel schema
closure can use it. -/
theorem original_abstractionRepresentation_has_free_value (substitution : TypeSubst) :
    ¬ HOL.NoConstOccurrence
      (Symbol.ofVar ⟨Name.global "a", sourceCarrierType request substitution⟩)
      (abstractionRepresentationFormula (request := request) (result := result) substitution) := by
  have appRight {σ ρ τ : HOL.Ty AtomicTy} {Γ : HOL.Ctx AtomicTy}
      {c : Symbol σ} {f : HOL.Term Symbol Γ (.arr ρ τ)} {v : HOL.Term Symbol Γ ρ}
      (absent : HOL.NoConstOccurrence c (.app f v)) : HOL.NoConstOccurrence c v := by
    cases absent with
    | app _ value => exact value
  have selfFalse {σ : HOL.Ty AtomicTy} {Γ : HOL.Ctx AtomicTy} (c : Symbol σ) :
      ¬ HOL.NoConstOccurrence c (.const c : HOL.Term Symbol Γ σ) := by
    intro absent
    cases absent with
    | const_diff_type different _ => exact different rfl
    | const_same_ne _ different => exact different rfl
  intro absent
  exact selfFalse _ (appRight absent)

namespace Controls

open MixedDefinitionHistory.Controls MixedDefinitionModelFamily.Controls

theorem second_first_schema_all_values (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (MixedTypeDefinitionModels.Controls.secondModel other assignment).models
      (abstractionRepresentationSchema (request := secondRequest) (result := secondResult) TypeSubst.empty) :=
  models_abstractionRepresentation afterFirstConstruction second_result_admitted
    (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other assignment _

theorem second_second_schema_all_values (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (MixedTypeDefinitionModels.Controls.secondModel other assignment).models
      (representationAbstractionSchema second_result_admitted TypeSubst.empty) := by
  apply models_representationAbstraction afterFirstConstruction second_result_admitted
    (History.existence_proof_of_kernel_derives second_result_admitted _ second_existence_derived) other assignment
      MixedDefinitionModelFamily.Controls.primitives
  have formed := (secondResult.context.constantTypes _ _
    (UniformTypeDefinitionInstances.new_constants_registered second_result_admitted).1).function_components _ |>.2
  simpa only [abstractionAnnotation, TypeSubst.apply_empty] using formed

theorem second_schemas_variable_free (sourceVar : SourceVar) :
    HOL.NoConstOccurrence (Symbol.ofVar sourceVar)
      (abstractionRepresentationSchema (request := secondRequest) (result := secondResult) TypeSubst.empty) ∧
    HOL.NoConstOccurrence (Symbol.ofVar sourceVar)
      (representationAbstractionSchema second_result_admitted TypeSubst.empty) :=
  ⟨abstractionRepresentation_variableFree _ _,
    representationAbstraction_variableFree second_result_admitted _ _⟩

theorem unclosed_original_row_refused_as_variable_free :
    ¬ HOL.NoConstOccurrence
      (Symbol.ofVar ⟨Name.global "a", sourceCarrierType secondRequest TypeSubst.empty⟩)
      (abstractionRepresentationFormula (request := secondRequest) (result := secondResult) TypeSubst.empty) :=
  original_abstractionRepresentation_has_free_value _

end Controls

end Mettapedia.Languages.HOLLight.DefinitionSchemaClosure
