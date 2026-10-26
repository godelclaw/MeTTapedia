import Mettapedia.Languages.HOLLight.ExportReplay
import Mettapedia.Languages.OpenTheory.PrimitiveEqualityFormation

/-!
# Complete type-instantiation certificates for registered HOL occurrences

The existing source receiver matches a declaration schema against its displayed
instance. Every genuine instance produces a proposal whose normalized map has
the required action, including repeated parameters and erased identity entries.
The independent instance check supplies soundness. A successful syntactic match
alone need not be consistent at repeated parameters.

The resulting equivalences discharge the certificate-selection premise in
annotation, sequent, theorem and inference-parameter formation. These are
formation results, rather than completeness of proof search or native
implementation refinement. The matching algorithm remains in `ExportReplay`.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.TypeInstantiationCertificates
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters ExportReplay

mutual
  theorem assignments_instance (substitution : TypeSubst) (schema : Ty) :
      ∃ entries, assignments schema (substitution.apply schema) = some entries ∧
        (∀ entry ∈ entries, substitution.apply (.var entry.1) = entry.2) ∧
        ∀ name ∈ schema.typeVariables, ∃ type, (name,type) ∈ entries := by
    cases schema with
    | var name =>
      refine ⟨[(name,substitution.apply (.var name))],by simp only [assignments],by simp,?_⟩
      intro other member
      have same : other = name := by simpa [Ty.typeVariables] using member
      subst other
      exact ⟨substitution.apply (.var name),by simp⟩
    | op operator arguments =>
      obtain ⟨entries, matched, consistent, covered⟩ := assignments_list_instance substitution arguments
      refine ⟨entries,?_,consistent,covered⟩
      simpa only [TypeSubst.apply_op,assignments,(TypeOp.same_eq_true_iff _ _).mpr rfl,if_true] using matched
  termination_by sizeOf schema

  theorem assignments_list_instance (substitution : TypeSubst) (schemas : List Ty) :
      ∃ entries, assignmentsList schemas (schemas.map substitution.apply) = some entries ∧
        (∀ entry ∈ entries, substitution.apply (.var entry.1) = entry.2) ∧
        ∀ name ∈ Ty.typeVariablesList schemas, ∃ type, (name,type) ∈ entries := by
    cases schemas with
    | nil => exact ⟨[],by simp only [List.map_nil,assignmentsList],by simp,by simp [Ty.typeVariablesList]⟩
    | cons head rest =>
      obtain ⟨first, firstMatched, firstConsistent, firstCovered⟩ := assignments_instance substitution head
      obtain ⟨last, lastMatched, lastConsistent, lastCovered⟩ := assignments_list_instance substitution rest
      refine ⟨first ++ last,?_,?_,?_⟩
      · simp [assignmentsList,firstMatched,lastMatched]
      · intro entry member
        rcases List.mem_append.mp member with member | member
        · exact firstConsistent entry member
        · exact lastConsistent entry member
      · intro name member
        rcases Finset.mem_union.mp member with member | member
        · obtain ⟨type,present⟩ := firstCovered name member
          exact ⟨type,List.mem_append_left _ present⟩
        · obtain ⟨type,present⟩ := lastCovered name member
          exact ⟨type,List.mem_append_right _ present⟩
  termination_by sizeOf schemas
end

theorem normalized_entries_agree (substitution : TypeSubst) (entries : List (Name × Ty))
    (consistent : ∀ entry ∈ entries, substitution.apply (.var entry.1) = entry.2)
    (name : Name) (present : ∃ type, (name,type) ∈ entries) :
    (TypeSubst.ofList entries).apply (.var name) = substitution.apply (.var name) := by
  induction entries using List.reverseRecOn with
  | nil => simp at present
  | append_singleton entries entry ih =>
    rcases entry with ⟨key,value⟩
    rw [TypeSubst.ofList_append_singleton]
    by_cases same : name = key
    · subst key
      rw [TypeSubst.apply_insert_same]
      exact (consistent (name,value) (by simp)).symm
    · rw [TypeSubst.apply_insert_ne _ _ same]
      apply ih (fun pair member => consistent pair (List.mem_append_left _ member))
      obtain ⟨type,member⟩ := present
      rcases List.mem_append.mp member with earlier | later
      · exact ⟨type,earlier⟩
      · have names : name = key := by simpa using congrArg Prod.fst (List.mem_singleton.mp later)
        exact False.elim (same names)

theorem instanceCertificates_complete (signature : Signature) (constant : Const) (annotation : Ty)
    (declared : ConstantInstance signature constant annotation) :
    constantInstanceB signature (instanceCertificates signature) constant annotation = true := by
  obtain ⟨schema,substitution,registered,rfl⟩ := declared
  obtain ⟨entries,matched,consistent,covered⟩ := assignments_instance substitution schema
  have same : (TypeSubst.ofList entries).apply schema = substitution.apply schema :=
    apply_equal_of_parameter_agreement _ _ schema
      (fun name member => normalized_entries_agree substitution entries consistent name (covered name member))
  simpa only [constantInstanceB,instanceCertificates,registered,matched,Option.getD_some] using
    (Ty.same_eq_true_iff _ _).mpr same

theorem constantInstanceB_exact (signature : Signature) (constant : Const) (annotation : Ty) :
    constantInstanceB signature (instanceCertificates signature) constant annotation = true ↔
      ConstantInstance signature constant annotation :=
  ⟨constantInstanceB_sound signature _ constant annotation,
    instanceCertificates_complete signature constant annotation⟩

theorem annotationsFormedB_exact (signature : Signature) (term : DBTerm) :
    annotationsFormedB signature (instanceCertificates signature) term = true ↔
      AnnotationsFormed signature term :=
  ⟨annotationsFormedB_sound signature _,
    annotationsFormedB_complete signature _ (instanceCertificates_complete signature)⟩

theorem sequentFormedB_exact (signature : Signature) (sequent : Sequent) :
    sequentFormedB signature (instanceCertificates signature) sequent = true ↔
      SequentFormed signature sequent :=
  ⟨sequentFormedB_sound signature _,
    sequentFormedB_complete signature _ (instanceCertificates_complete signature)⟩

theorem theoremFormedB_exact (signature : Signature) (fact : Theorem) :
    theoremFormedB signature (instanceCertificates signature) fact = true ↔
      TheoremFormed signature fact :=
  ⟨theoremFormedB_sound signature _,
    theoremFormedB_complete signature _ (instanceCertificates_complete signature)⟩

theorem inferenceFormationCheck_exact (signature : Signature) (request : InferenceRequest) :
    InferenceFormation.check signature (instanceCertificates signature) request = true ↔
      InferenceFormation.Formed signature request :=
  ⟨InferenceFormation.check_sound signature _ _,
    InferenceFormation.check_complete signature _ (instanceCertificates_complete signature)⟩

/-- An extended signature's certificate finder also realizes every instance
of the original signature. New declarations do not change old schemas. -/
theorem instanceCertificates_complete_of_includes (before after : Signature) (included : before.Includes after)
    (constant : Const) (annotation : Ty) (declared : ConstantInstance before constant annotation) :
    constantInstanceB before (ExportReplay.instanceCertificates after) constant annotation = true := by
  obtain ⟨schema,substitution,found,equal⟩ := declared
  have present := included.2 constant schema found
  have complete := TypeInstantiationCertificates.instanceCertificates_complete after constant annotation
    ⟨schema,substitution,present,equal⟩
  simpa only [constantInstanceB,found,present] using complete

theorem annotationsFormedB_complete_of_includes (before after : Signature) (included : before.Includes after)
    (term : DBTerm) (formed : AnnotationsFormed before term) :
    annotationsFormedB before (ExportReplay.instanceCertificates after) term = true :=
  annotationsFormedB_complete before (ExportReplay.instanceCertificates after)
    (instanceCertificates_complete_of_includes before after included) formed

theorem theoremFormedB_complete_of_includes (before after : Signature) (included : before.Includes after)
    (fact : Theorem) (formed : TheoremFormed before fact) :
    theoremFormedB before (ExportReplay.instanceCertificates after) fact = true :=
  theoremFormedB_complete before (ExportReplay.instanceCertificates after)
    (instanceCertificates_complete_of_includes before after included) formed

namespace Controls

def schema : Ty := Ty.equality (.var ContextControls.equalityParameter)
def functionOperand : Ty := Ty.function Ty.bool Ty.bool

def realization : TypeSubst := TypeSubst.ofList [(ContextControls.equalityParameter,functionOperand)]

theorem equality_registered : ContextControls.coreContext.signature.constants Const.equality = some schema := by
  unfold ContextControls.coreContext
  exact ContextControls.baseContext.addConstant_registered _ _ _ _

theorem function_instance : ConstantInstance ContextControls.coreContext.signature Const.equality (Ty.equality functionOperand) := by
  refine ⟨schema,realization,equality_registered,?_⟩
  have action : realization.apply (.var ContextControls.equalityParameter) = functionOperand :=
    TypeSubst.apply_insert_same TypeSubst.empty _ _
  simp only [schema,Ty.equality,TypeSubst.apply_function,TypeSubst.apply_bool,action]

theorem function_instance_checked :
    constantInstanceB ContextControls.coreContext.signature
      (instanceCertificates ContextControls.coreContext.signature) Const.equality (Ty.equality functionOperand) = true :=
  instanceCertificates_complete ContextControls.coreContext.signature Const.equality (Ty.equality functionOperand) function_instance

theorem identity_instance_checked :
    constantInstanceB ContextControls.coreContext.signature
      (instanceCertificates ContextControls.coreContext.signature) Const.equality schema = true := by
  apply (constantInstanceB_exact ContextControls.coreContext.signature Const.equality schema).mpr
  exact ⟨schema,TypeSubst.empty,equality_registered,TypeSubst.apply_empty schema⟩

def operand : CanonicalTerm := CanonicalTerm.constant Const.equality (Ty.equality functionOperand)

theorem function_registered : ContextControls.coreContext.signature.typeOperators TypeOp.function = some 2 :=
  ContextControls.core_includes.1 _ _ ContextControls.function_registered

theorem boolean_formed : TypeFormed ContextControls.coreContext.signature Ty.bool :=
  ContextControls.boolean_formed.mono ContextControls.core_includes

theorem operand_type_formed : TypeFormed ContextControls.coreContext.signature operand.ty := by
  have functionFormed := TypeFormed.function _ function_registered boolean_formed boolean_formed
  exact TypeFormed.function _ function_registered functionFormed
    (TypeFormed.function _ function_registered functionFormed boolean_formed)

theorem operand_formed : AnnotationsFormed ContextControls.coreContext.signature operand.term :=
  .constant operand_type_formed function_instance

theorem operand_checked : annotationsFormedB ContextControls.coreContext.signature
    (instanceCertificates ContextControls.coreContext.signature) operand.term = true :=
  (annotationsFormedB_exact ContextControls.coreContext.signature operand.term).mpr operand_formed

def equation : CanonicalTerm := CanonicalTerm.equalityOfSameType operand operand rfl

theorem equation_formed : AnnotationsFormed ContextControls.coreContext.signature equation.term :=
  PrimitiveEqualityFormation.equation_annotations _ ContextControls.equalityParameter operand.ty
    function_registered boolean_formed operand_type_formed equality_registered _ _ operand_formed operand_formed

def fact : Theorem := Theorem.emptyResult ∅ equation

theorem fact_formed : TheoremFormed ContextControls.coreContext.signature fact := by
  refine ⟨⟨equation_formed,?_⟩,?_⟩ <;> simp [fact,Theorem.emptyResult]

theorem sequent_checked : sequentFormedB ContextControls.coreContext.signature
    (instanceCertificates ContextControls.coreContext.signature) fact.sequent = true :=
  (sequentFormedB_exact ContextControls.coreContext.signature fact.sequent).mpr fact_formed.1

theorem fact_checked : theoremFormedB ContextControls.coreContext.signature
    (instanceCertificates ContextControls.coreContext.signature) fact = true :=
  (theoremFormedB_exact ContextControls.coreContext.signature fact).mpr fact_formed

theorem reflexivity_parameters_checked : InferenceFormation.check ContextControls.coreContext.signature
    (instanceCertificates ContextControls.coreContext.signature) (.refl operand) = true := by
  apply (inferenceFormationCheck_exact ContextControls.coreContext.signature (.refl operand)).mpr
  simp [InferenceFormation.Formed,InferenceFormation.types,InferenceFormation.terms,operand_formed]

def inconsistent : Ty := Ty.function Ty.bool (Ty.function functionOperand Ty.bool)

theorem inconsistent_repetition_refused :
    constantInstanceB ContextControls.coreContext.signature
      (instanceCertificates ContextControls.coreContext.signature) Const.equality inconsistent = false := by decide +kernel

theorem inconsistent_not_instance :
    ¬ ConstantInstance ContextControls.coreContext.signature Const.equality inconsistent := by
  intro declared
  have checked := instanceCertificates_complete _ _ _ declared
  rw [inconsistent_repetition_refused] at checked
  cases checked
end Controls

#print axioms instanceCertificates_complete
end Mettapedia.Languages.HOLLight.TypeInstantiationCertificates
