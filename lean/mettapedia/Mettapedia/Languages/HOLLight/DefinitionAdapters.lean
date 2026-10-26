import Mettapedia.Languages.HOLLight.Rules
import Mettapedia.Languages.OpenTheory.PackageDefinitionOwnership
import Mettapedia.Languages.OpenTheory.SignatureFormation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.String.Basic

/-!
# HOL Light definition-name and parameter admission

HOL Light's successful definition operations require globally fresh names in
their respective namespaces. This differs from package ownership, which may
permit repeated names from the same package. The shared definition operations
still construct the typed, provenance-bearing symbols and defining equations.

The type parameters are canonically sorted, as in the source kernel. These
adapters concern successful operations; they make no rollback claim about a
source operation that fails after changing the source declaration tables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.DefinitionAdapters

open Mettapedia.Languages.OpenTheory
open SignatureFormation

/-- HOL Light and the shared syntax spell their primitive function operator
differently. A bijection, rather than a one-way replacement, leaves both
spellings available for other source declarations. -/
def sourceOperatorName (name : Name) : Name :=
  (Equiv.swap (Name.global "->") (Name.global "fun")) name

theorem sourceOperatorName_injective : Function.Injective sourceOperatorName :=
  (Equiv.swap (Name.global "->") (Name.global "fun")).injective

@[simp] theorem sourceOperatorName_roundtrip (name : Name) :
    sourceOperatorName (sourceOperatorName name) = name := by
  simp [sourceOperatorName]

@[simp] theorem sourceOperatorName_function :
    sourceOperatorName (Name.global "fun") = Name.global "->" := by
  simp [sourceOperatorName]

@[simp] theorem sourceOperatorName_arrow :
    sourceOperatorName (Name.global "->") = Name.global "fun" := by
  simp [sourceOperatorName]

/-- The source freshness table keeps the type and constant namespaces separate.
Typed signature formation is a further condition at declaration ingress. -/
abbrev NameContext := Finset DefinedSymbolName

private def nameKey (name : Name) : List String ×ₗ String :=
  toLex (name.namespaceComponents, name.component)

private theorem nameKey_injective : Function.Injective nameKey := by
  intro left right equal
  cases left
  cases right
  cases equal
  rfl

private instance nameOrder : LinearOrder Name :=
  LinearOrder.lift' nameKey nameKey_injective

/-- On the source's global names this is the lexicographic string ordering
used for HOL Light type-variable names. Namespaces remain part of identity. -/
def sortedParameters (predicate : SourceTerm) : List Name :=
  (predicate.toDB []).typeVariables.sort (· ≤ ·)

theorem sortedParameters_nodup (predicate : SourceTerm) :
    (sortedParameters predicate).Nodup := Finset.sort_nodup _ _

theorem sortedParameters_support (predicate : SourceTerm) :
    (sortedParameters predicate).toFinset = (predicate.toDB []).typeVariables :=
  Finset.sort_toFinset _ _

/-- A distinct source string list with the predicate's complete parameter
support computes the very ordering required by the registered source gate. -/
theorem sortedParameters_of_global_strings (predicate : SourceTerm) (texts : List String)
    (distinct : texts.Nodup)
    (support : (texts.map Name.global).toFinset = (predicate.toDB []).typeVariables) :
    (texts.mergeSort (· ≤ ·)).map Name.global = sortedParameters predicate := by
  have injective : Function.Injective Name.global := by
    intro left right same
    exact congrArg Name.component same
  have nodup : ((texts.mergeSort (· ≤ ·)).map Name.global).Nodup :=
    ((List.mergeSort_perm texts (· ≤ ·)).nodup_iff.mpr distinct).map injective
  have sorted : (((texts.mergeSort (· ≤ ·)).map Name.global)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    apply (List.pairwise_mergeSort' (· ≤ ·) texts).imp
    intro left right ordered
    change toLex (([] : List String), left) ≤ toLex ([], right)
    exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, ordered⟩)
  have sameSupport : ((texts.mergeSort (· ≤ ·)).map Name.global).toFinset =
      (predicate.toDB []).typeVariables := by
    have sortingSupport : (texts.mergeSort (· ≤ ·)).toFinset = texts.toFinset := by
      ext text
      simp only [List.mem_toFinset, (List.mergeSort_perm texts (· ≤ ·)).mem_iff]
    rw [List.toFinset_map, sortingSupport]
    simpa only [List.toFinset_map] using support
  unfold sortedParameters
  rw [← sameSupport]
  exact ((List.toFinset_sort (· ≤ ·) nodup).mpr sorted).symm

theorem globalName_order (left right : String) :
    Name.global left ≤ Name.global right ↔ left ≤ right := by
  change toLex (([] : List String), left) ≤ toLex ([], right) ↔ left ≤ right
  simp [Prod.Lex.toLex_le_toLex]

def ConstantAdmissible (context : NameContext) (name : Name) (body : SourceTerm) : Prop :=
  DefinedSymbolName.constant name ∉ context ∧ ConstantDefinitionAdmissible body

def admitConstant (context : NameContext) (name : Name) (body : SourceTerm) :
    Option (NameContext × ConstantDefinitionResult) :=
  if DefinedSymbolName.constant name ∈ context then none else do
    let result ← checkConstantDefinition name body
    pure (insert (.constant name) context, result)

theorem admitConstant_isSome_iff (context : NameContext) (name : Name) (body : SourceTerm) :
    (admitConstant context name body).isSome = true ↔ ConstantAdmissible context name body := by
  by_cases used : DefinedSymbolName.constant name ∈ context
  · simp [admitConstant, ConstantAdmissible, used]
  · cases checked : checkConstantDefinition name body with
    | none =>
        have rejected := (checkConstantDefinition_isSome_iff name body)
        simp only [checked, Option.isSome_none, Bool.false_eq_true, false_iff] at rejected
        simp [admitConstant, ConstantAdmissible, used, checked, rejected]
    | some result =>
        have admitted := (checkConstantDefinition_isSome_iff name body).mp (by simp [checked])
        simp [admitConstant, ConstantAdmissible, used, checked, admitted]

theorem admitConstant_result {context : NameContext} {name : Name} {body : SourceTerm}
    {result : NameContext × ConstantDefinitionResult}
    (accepted : admitConstant context name body = some result) :
    result.1 = insert (.constant name) context ∧
      checkConstantDefinition name body = some result.2 ∧
      result.2.constant = .mk name (.defined body) ∧
      result.2.definitionTheorem.axioms = ∅ := by
  by_cases used : DefinedSymbolName.constant name ∈ context
  · simp [admitConstant, used] at accepted
  · cases checked : checkConstantDefinition name body with
    | none => simp [admitConstant, used, checked] at accepted
    | some output =>
        have equal : (insert (.constant name) context, output) = result := by
          simpa [admitConstant, used, checked] using accepted
        subst result
        obtain ⟨_, _, _, _, _, provenance, _, _⟩ := checkConstantDefinition_result checked
        exact ⟨rfl, rfl, provenance, checkConstantDefinition_axioms_empty checked⟩

def TypeNamesFresh (context : NameContext) (request : TypeOperatorDefinitionRequest) : Prop :=
  .typeOperator request.typeName ∉ context ∧
    .constant request.abstractionName ∉ context ∧
    .constant request.representationName ∉ context ∧
    request.abstractionName ≠ request.representationName

instance (context : NameContext) (request : TypeOperatorDefinitionRequest) :
    Decidable (TypeNamesFresh context request) := inferInstanceAs
      (Decidable (_ ∧ _ ∧ _ ∧ _))

def extendTypeNames (context : NameContext) (request : TypeOperatorDefinitionRequest) : NameContext :=
  insert (.typeOperator request.typeName)
    (insert (.constant request.abstractionName) (insert (.constant request.representationName) context))

def TypeAdmissible (context : NameContext) (request : TypeOperatorDefinitionRequest) : Prop :=
  TypeNamesFresh context request ∧ TypeOperatorDefinitionAdmissible request ∧
    request.typeVariables = sortedParameters request.predicateSource

def admitType (context : NameContext) (request : TypeOperatorDefinitionRequest) :
    Option (NameContext × TypeOperatorDefinitionResult) :=
  if TypeNamesFresh context request ∧
      request.typeVariables = sortedParameters request.predicateSource then do
    let result ← checkTypeOperatorDefinition request
    pure (extendTypeNames context request, result)
  else none

theorem admitType_isSome_iff (context : NameContext) (request : TypeOperatorDefinitionRequest) :
    (admitType context request).isSome = true ↔ TypeAdmissible context request := by
  by_cases names : TypeNamesFresh context request ∧
      request.typeVariables = sortedParameters request.predicateSource
  · cases checked : checkTypeOperatorDefinition request with
    | none =>
        have rejected := checkTypeOperatorDefinition_isSome_iff request
        simp only [checked, Option.isSome_none, Bool.false_eq_true, false_iff] at rejected
        simp [admitType, TypeAdmissible, names, checked, rejected]
    | some result =>
        have admitted := (checkTypeOperatorDefinition_isSome_iff request).mp (by simp [checked])
        simp [admitType, TypeAdmissible, names, checked, admitted]
  · have rejected : ¬ TypeAdmissible context request :=
      fun admitted => names ⟨admitted.1, admitted.2.2⟩
    simp [admitType, names, rejected]

theorem admitType_result {context : NameContext} {request : TypeOperatorDefinitionRequest}
    {result : NameContext × TypeOperatorDefinitionResult}
    (accepted : admitType context request = some result) :
    result.1 = extendTypeNames context request ∧
      checkTypeOperatorDefinition request = some result.2 := by
  unfold admitType at accepted
  split at accepted
  · cases checked : checkTypeOperatorDefinition request with
    | none => simp [checked] at accepted
    | some output =>
        have equal : (extendTypeNames context request, output) = result := by
          simpa [checked] using accepted
        subst result
        exact ⟨rfl, rfl⟩
  · cases accepted

theorem repeated_constant_refused (context : NameContext) (name : Name) (body : SourceTerm) :
    admitConstant (insert (.constant name) context) name body = none := by
  simp [admitConstant]

theorem repeated_type_refused (context : NameContext) (request : TypeOperatorDefinitionRequest) :
    admitType (extendTypeNames context request) request = none := by
  have used : ¬ TypeNamesFresh (extendTypeNames context request) request := by
    intro fresh
    exact fresh.1 (by simp [extendTypeNames])
  simp [admitType, used]

theorem coincident_representation_names_refused (context : NameContext)
    (request : TypeOperatorDefinitionRequest)
    (coincident : request.abstractionName = request.representationName) :
    admitType context request = none := by
  have bad : ¬ TypeNamesFresh context request := fun fresh => fresh.2.2.2 coincident
  simp [admitType, bad]

theorem type_and_constant_names_distinct (name : Name) :
    DefinedSymbolName.typeOperator name ≠ DefinedSymbolName.constant name := by
  intro impossible
  cases impossible

/-- A witness with undischarged hypotheses cannot create an inhabited type. -/
theorem hypotheses_type_definition_refused (context : NameContext)
    (request : TypeOperatorDefinitionRequest)
    (nonempty : request.existence.sequent.hyp ≠ ∅) : admitType context request = none := by
  cases checked : admitType context request with
  | none => rfl
  | some result =>
      have admitted := (admitType_isSome_iff context request).mp (by simp [checked])
      obtain ⟨_, _, _, _, empty, _⟩ := admitted.2.1
      exact False.elim (nonempty empty)

theorem noncanonical_parameters_refused (context : NameContext)
    (request : TypeOperatorDefinitionRequest)
    (wrong : request.typeVariables ≠ sortedParameters request.predicateSource) :
    admitType context request = none := by
  simp [admitType, wrong]

/-- A printed name cannot identify definitions with different bodies. -/
theorem different_bodies_distinct {first second : SourceTerm} (name : Name)
    (different : first ≠ second) :
    Const.mk name (.defined first) ≠ Const.mk name (.defined second) := by
  intro equal
  cases equal
  exact different rfl

namespace Controls

def identitySource : SourceTerm := .abs (Name.global "x") Ty.bool (.var (Name.global "x") Ty.bool)

def identityTerm : CanonicalTerm :=
  ⟨.abs Ty.bool (.bound 0), .function Ty.bool Ty.bool, by simp [DBTerm.inferType]⟩

theorem identitySource_checked : identitySource.check = some identityTerm := by
  rw [SourceTerm.check_eq_some_iff]
  simp [identitySource, identityTerm, SourceTerm.toDB, boundIndex]

/-- An actual closed identity definition passes the shared source guards. -/
theorem identity_definition_admitted :
    (admitConstant ∅ (Name.global "identity") identitySource).isSome = true := by
  rw [admitConstant_isSome_iff]
  refine ⟨by simp, identityTerm, identitySource_checked, .abs .bound, ?_⟩
  simp [identityTerm, DBTerm.typeVariables, Ty.typeVariables, Ty.typeVariablesList,
    Ty.bool, Ty.function]

theorem identity_definition_repeated_refused :
    admitConstant {DefinedSymbolName.constant (Name.global "identity")}
      (Name.global "identity") identitySource = none := by
  simp [admitConstant]

end Controls

/-! ## Registered theory contexts

Fresh printed names and provenance-sensitive declaration lookup are different
obligations. A theory context joins them and retains formed declaration schemas.
New declarations preserve every old registered symbol; no name-only citation
can substitute a different definition body.
-/

def constantName : Const → Name
  | .mk name _ => name

def operatorName : TypeOp → Name
  | .mk name _ => name

structure TheoryContext where
  names : NameContext
  signature : Signature
  typeNames : ∀ operator arity, signature.typeOperators operator = some arity →
    .typeOperator (operatorName operator) ∈ names
  constantNames : ∀ constant schema, signature.constants constant = some schema →
    .constant (constantName constant) ∈ names
  uniqueTypeNames : ∀ left right leftArity rightArity,
    signature.typeOperators left = some leftArity →
    signature.typeOperators right = some rightArity →
    operatorName left = operatorName right → left = right
  uniqueConstantNames : ∀ left right leftSchema rightSchema,
    signature.constants left = some leftSchema →
    signature.constants right = some rightSchema →
    constantName left = constantName right → left = right
  constantTypes : ∀ constant schema, signature.constants constant = some schema →
    TypeFormed signature schema

namespace TheoryContext

def empty : TheoryContext :=
  { names := ∅
    signature := ⟨fun _ => none, fun _ => none⟩
    typeNames := by intros; contradiction
    constantNames := by intros; contradiction
    uniqueTypeNames := by intros; contradiction
    uniqueConstantNames := by intros; contradiction
    constantTypes := by intros; contradiction }

theorem constant_unregistered (context : TheoryContext) (constant : Const)
    (fresh : .constant (constantName constant) ∉ context.names) :
    context.signature.constants constant = none := by
  cases found : context.signature.constants constant with
  | none => rfl
  | some schema => exact False.elim (fresh (context.constantNames constant schema found))

theorem operator_unregistered (context : TheoryContext) (operator : TypeOp)
    (fresh : .typeOperator (operatorName operator) ∉ context.names) :
    context.signature.typeOperators operator = none := by
  cases found : context.signature.typeOperators operator with
  | none => rfl
  | some arity => exact False.elim (fresh (context.typeNames operator arity found))

def addConstant (context : TheoryContext) (constant : Const) (schema : Ty)
    (formed : TypeFormed context.signature schema)
    (fresh : .constant (constantName constant) ∉ context.names) : TheoryContext :=
  let extended := context.signature.addConstant constant schema
  have included : context.signature.Includes extended :=
    context.signature.includes_addConstant constant schema
      (context.constant_unregistered constant fresh)
  { names := insert (.constant (constantName constant)) context.names
    signature := extended
    typeNames := by
      intro operator arity found
      exact Finset.mem_insert_of_mem (context.typeNames operator arity found)
    constantNames := by
      intro candidate candidateSchema found
      by_cases same : Const.same candidate constant = true
      · have equal := (Const.same_eq_true_iff candidate constant).mp same
        subst candidate
        simp
      · have old : context.signature.constants candidate = some candidateSchema := by
          simpa [extended, Signature.addConstant, same] using found
        exact Finset.mem_insert_of_mem (context.constantNames candidate candidateSchema old)
    uniqueTypeNames := context.uniqueTypeNames
    uniqueConstantNames := by
      intro left right leftSchema rightSchema leftFound rightFound sameName
      by_cases leftSame : Const.same left constant = true
      · have leftEqual := (Const.same_eq_true_iff left constant).mp leftSame
        subst left
        by_cases rightSame : Const.same right constant = true
        · exact ((Const.same_eq_true_iff right constant).mp rightSame).symm
        · have rightOld : context.signature.constants right = some rightSchema := by
            simpa [extended, Signature.addConstant, rightSame] using rightFound
          exact False.elim (fresh (sameName ▸ context.constantNames right rightSchema rightOld))
      · have leftOld : context.signature.constants left = some leftSchema := by
          simpa [extended, Signature.addConstant, leftSame] using leftFound
        by_cases rightSame : Const.same right constant = true
        · have rightEqual := (Const.same_eq_true_iff right constant).mp rightSame
          subst right
          exact False.elim (fresh (sameName ▸ context.constantNames left leftSchema leftOld))
        · have rightOld : context.signature.constants right = some rightSchema := by
            simpa [extended, Signature.addConstant, rightSame] using rightFound
          exact context.uniqueConstantNames left right leftSchema rightSchema leftOld rightOld sameName
    constantTypes := by
      intro candidate candidateSchema found
      by_cases same : Const.same candidate constant = true
      · have equal : schema = candidateSchema := by
          simpa [extended, Signature.addConstant, same] using found
        subst candidateSchema
        exact formed.mono included
      · have old : context.signature.constants candidate = some candidateSchema := by
          simpa [extended, Signature.addConstant, same] using found
        exact (context.constantTypes candidate candidateSchema old).mono included }

theorem addConstant_includes (context : TheoryContext) (constant : Const) (schema : Ty)
    (formed : TypeFormed context.signature schema)
    (fresh : .constant (constantName constant) ∉ context.names) :
    context.signature.Includes (context.addConstant constant schema formed fresh).signature :=
  context.signature.includes_addConstant constant schema
    (context.constant_unregistered constant fresh)

theorem addConstant_registered (context : TheoryContext) (constant : Const) (schema : Ty)
    (formed : TypeFormed context.signature schema)
    (fresh : .constant (constantName constant) ∉ context.names) :
    (context.addConstant constant schema formed fresh).signature.constants constant = some schema := by
  simp [addConstant, Signature.addConstant, Const.same_eq_true_iff]

def addTypeOperator (context : TheoryContext) (operator : TypeOp) (arity : Nat)
    (fresh : .typeOperator (operatorName operator) ∉ context.names) : TheoryContext :=
  let extended := context.signature.addTypeOperator operator arity
  have included : context.signature.Includes extended :=
    context.signature.includes_addTypeOperator operator arity
      (context.operator_unregistered operator fresh)
  { names := insert (.typeOperator (operatorName operator)) context.names
    signature := extended
    typeNames := by
      intro candidate candidateArity found
      by_cases same : TypeOp.same candidate operator = true
      · have equal := (TypeOp.same_eq_true_iff candidate operator).mp same
        subst candidate
        simp
      · have old : context.signature.typeOperators candidate = some candidateArity := by
          simpa [extended, Signature.addTypeOperator, same] using found
        exact Finset.mem_insert_of_mem (context.typeNames candidate candidateArity old)
    constantNames := by
      intro constant schema found
      exact Finset.mem_insert_of_mem (context.constantNames constant schema found)
    uniqueTypeNames := by
      intro left right leftArity rightArity leftFound rightFound sameName
      by_cases leftSame : TypeOp.same left operator = true
      · have leftEqual := (TypeOp.same_eq_true_iff left operator).mp leftSame
        subst left
        by_cases rightSame : TypeOp.same right operator = true
        · exact ((TypeOp.same_eq_true_iff right operator).mp rightSame).symm
        · have rightOld : context.signature.typeOperators right = some rightArity := by
            simpa [extended, Signature.addTypeOperator, rightSame] using rightFound
          exact False.elim (fresh (sameName ▸ context.typeNames right rightArity rightOld))
      · have leftOld : context.signature.typeOperators left = some leftArity := by
          simpa [extended, Signature.addTypeOperator, leftSame] using leftFound
        by_cases rightSame : TypeOp.same right operator = true
        · have rightEqual := (TypeOp.same_eq_true_iff right operator).mp rightSame
          subst right
          exact False.elim (fresh (sameName ▸ context.typeNames left leftArity leftOld))
        · have rightOld : context.signature.typeOperators right = some rightArity := by
            simpa [extended, Signature.addTypeOperator, rightSame] using rightFound
          exact context.uniqueTypeNames left right leftArity rightArity leftOld rightOld sameName
    uniqueConstantNames := context.uniqueConstantNames
    constantTypes := by
      intro constant schema found
      exact (context.constantTypes constant schema found).mono included }

theorem addTypeOperator_includes (context : TheoryContext) (operator : TypeOp) (arity : Nat)
    (fresh : .typeOperator (operatorName operator) ∉ context.names) :
    context.signature.Includes (context.addTypeOperator operator arity fresh).signature :=
  context.signature.includes_addTypeOperator operator arity
    (context.operator_unregistered operator fresh)

theorem addTypeOperator_registered (context : TheoryContext) (operator : TypeOp) (arity : Nat)
    (fresh : .typeOperator (operatorName operator) ∉ context.names) :
    (context.addTypeOperator operator arity fresh).signature.typeOperators operator = some arity := by
  simp [addTypeOperator, Signature.addTypeOperator, TypeOp.same_eq_true_iff]

end TheoryContext

structure ContextConstantDefinitionResult where
  context : TheoryContext
  definition : CanonicalTerm
  output : ConstantDefinitionResult

/-- Declaration ingress checks the existing source term and definition gates,
then registers the exact provenance-bearing symbol at the checked body type. -/
def admitConstantInTheory (context : TheoryContext) (witnesses : InstanceWitnesses)
    (name : Name) (body : SourceTerm) : Option ContextConstantDefinitionResult :=
  match checkSource context.signature witnesses body with
  | none => none
  | some definition =>
      if formed : typeFormedB context.signature definition.ty = true then
        if fresh : .constant name ∉ context.names then
          match admitConstant context.names name body with
          | none => none
          | some result =>
              some
                { context := context.addConstant (.mk name (.defined body)) definition.ty
                    ((typeFormedB_eq_true_iff _ _).mp formed) fresh
                  definition := definition
                  output := result.2 }
        else none
      else none

def ConstantInTheoryAdmissible (context : TheoryContext) (witnesses : InstanceWitnesses)
    (name : Name) (body : SourceTerm) : Prop :=
  ∃ definition, checkSource context.signature witnesses body = some definition ∧
    TypeFormed context.signature definition.ty ∧ ConstantAdmissible context.names name body

theorem admitConstantInTheory_isSome_iff (context : TheoryContext) (witnesses : InstanceWitnesses)
    (name : Name) (body : SourceTerm) :
    (admitConstantInTheory context witnesses name body).isSome = true ↔
      ConstantInTheoryAdmissible context witnesses name body := by
  cases checked : checkSource context.signature witnesses body with
  | none => simp [admitConstantInTheory, ConstantInTheoryAdmissible, checked]
  | some definition =>
      by_cases formed : typeFormedB context.signature definition.ty = true
      · have typeFormed := (typeFormedB_eq_true_iff _ _).mp formed
        by_cases fresh : DefinedSymbolName.constant name ∉ context.names
        · cases admitted : admitConstant context.names name body with
          | none =>
              have refused := admitConstant_isSome_iff context.names name body
              simp only [admitted, Option.isSome_none, Bool.false_eq_true, false_iff] at refused
              simp [admitConstantInTheory, ConstantInTheoryAdmissible, checked, formed,
                fresh, admitted, refused]
          | some result =>
              have conditions := (admitConstant_isSome_iff context.names name body).mp
                (by simp [admitted])
              simp [admitConstantInTheory, ConstantInTheoryAdmissible, checked, formed,
                fresh, admitted, typeFormed, conditions]
        · have used : .constant name ∈ context.names := Classical.not_not.mp fresh
          simp [admitConstantInTheory, ConstantInTheoryAdmissible, ConstantAdmissible,
            checked, formed, used]
      · have unformed : ¬ TypeFormed context.signature definition.ty :=
          fun valid => formed ((typeFormedB_eq_true_iff _ _).mpr valid)
        simp [admitConstantInTheory, ConstantInTheoryAdmissible, checked, formed, unformed]

/-- Successful registration keeps all old declarations, retains the source
definition theorem, and adds neither hypotheses nor primitive axioms. -/
theorem admitConstantInTheory_result {context : TheoryContext} {witnesses : InstanceWitnesses}
    {name : Name} {body : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context witnesses name body = some result) :
    checkSource context.signature witnesses body = some result.definition ∧
      TypeFormed context.signature result.definition.ty ∧
      context.signature.Includes result.context.signature ∧
      result.context.names = insert (.constant name) context.names ∧
      checkConstantDefinition name body = some result.output ∧
      result.context.signature.constants result.output.constant = some result.definition.ty ∧
      result.output.definitionTheorem.axioms = ∅ ∧
      result.output.definitionTheorem.sequent.hyp = ∅ := by
  unfold admitConstantInTheory at accepted
  split at accepted
  · cases accepted
  · rename_i definition sourceChecked
    split at accepted
    · rename_i formed
      split at accepted
      · rename_i fresh
        split at accepted
        · cases accepted
        · rename_i admitted namesAccepted
          have equal := Option.some.inj accepted
          subst result
          have registration := admitConstant_result namesAccepted
          obtain ⟨_, _, _, _, _, _, _, parts⟩ :=
            checkConstantDefinition_result registration.2.1
          refine ⟨sourceChecked, (typeFormedB_eq_true_iff _ _).mp formed,
            context.addConstant_includes (.mk name (.defined body)) definition.ty
              ((typeFormedB_eq_true_iff _ _).mp formed) fresh,
            rfl, registration.2.1, ?_,
            registration.2.2.2, parts.2.1⟩
          rw [registration.2.2.1]
          exact context.addConstant_registered (.mk name (.defined body)) definition.ty
            ((typeFormedB_eq_true_iff _ _).mp formed) fresh
      · cases accepted
    · cases accepted

/-- The same resolved name and source body yield the same checked payload in
any two contexts that admit them. The extended contexts may still differ. -/
theorem admitConstantInTheory_payload_eq
    {firstContext secondContext : TheoryContext} {firstInstances secondInstances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {first second : ContextConstantDefinitionResult}
    (firstAccepted : admitConstantInTheory firstContext firstInstances name source = some first)
    (secondAccepted : admitConstantInTheory secondContext secondInstances name source = some second) :
    first.definition = second.definition ∧ first.output = second.output := by
  have firstResult := admitConstantInTheory_result firstAccepted
  have secondResult := admitConstantInTheory_result secondAccepted
  exact ⟨Option.some.inj (((checkSource_sound _ _ firstResult.1).1).symm.trans
      (checkSource_sound _ _ secondResult.1).1),
    Option.some.inj (firstResult.2.2.2.2.1.symm.trans secondResult.2.2.2.2.1)⟩

/-- Successful instance-certificate providers yield the same admitted
constant, declaration context and equation. They cannot change source checking. -/
theorem admitConstantInTheory_unique {context : TheoryContext}
    {firstWitnesses secondWitnesses : InstanceWitnesses} {name : Name} {body : SourceTerm}
    {first second : ContextConstantDefinitionResult}
    (firstAccepted : admitConstantInTheory context firstWitnesses name body = some first)
    (secondAccepted : admitConstantInTheory context secondWitnesses name body = some second) :
    first = second := by
  have firstChecked := (admitConstantInTheory_result firstAccepted).1
  have secondChecked := (admitConstantInTheory_result secondAccepted).1
  have definitionSame := (admitConstantInTheory_payload_eq firstAccepted secondAccepted).1
  have same : admitConstantInTheory context firstWitnesses name body =
      admitConstantInTheory context secondWitnesses name body := by
    simp only [admitConstantInTheory, firstChecked, secondChecked, definitionSame]
  exact Option.some.inj (firstAccepted.symm.trans (same.trans secondAccepted))

/-- An old typed term stays admitted after registration, using its original
declaration identity rather than a printed-name approximation. -/
theorem admitConstantInTheory_preserves_annotations
    {context : TheoryContext} {witnesses : InstanceWitnesses}
    {name : Name} {body : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context witnesses name body = some result)
    {term : DBTerm} (formed : AnnotationsFormed context.signature term) :
    AnnotationsFormed result.context.signature term :=
  formed.mono (admitConstantInTheory_result accepted).2.2.1

theorem admitConstantInTheory_repeated_refused (context : TheoryContext)
    (witnesses : InstanceWitnesses) (name : Name) (body : SourceTerm)
    (used : .constant name ∈ context.names) :
    admitConstantInTheory context witnesses name body = none := by
  cases checked : checkSource context.signature witnesses body with
  | none => simp [admitConstantInTheory, checked]
  | some definition =>
      simp [admitConstantInTheory, checked, used]

namespace TheoryContext

/-- Register the new carrier and its two maps together. Formation uses the
actual representation type and the operator's declared parameter arity. -/
def typeDefinitionExtension (context : TheoryContext)
    (request : TypeOperatorDefinitionRequest) (represented : Ty)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (representedFormed : TypeFormed context.signature represented)
    (fresh : TypeNamesFresh context.names request) : TheoryContext := by
  let operator : TypeOp := .mk request.typeName
    (.defined request.predicateSource request.typeVariables)
  let carrier : Ty := .op operator (request.typeVariables.map Ty.var)
  let withType := context.addTypeOperator operator request.typeVariables.length fresh.1
  have typeIncluded := context.addTypeOperator_includes operator request.typeVariables.length fresh.1
  have carrierFormed : TypeFormed withType.signature carrier := by
    simp only [carrier, TypeFormed, List.length_map]
    refine ⟨context.addTypeOperator_registered operator request.typeVariables.length fresh.1, ?_⟩
    intro argument member
    obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
    simp only [TypeFormed]
  have representedInType := representedFormed.mono typeIncluded
  have functionInType := typeIncluded.1 TypeOp.function 2 functionArity
  have absFresh : .constant request.abstractionName ∉ withType.names := by
    simpa [withType, addTypeOperator] using fresh.2.1
  let abstraction : Const := .mk request.abstractionName (.abstraction operator)
  let withAbs := withType.addConstant abstraction (.function represented carrier)
    (TypeFormed.function withType.signature functionInType representedInType carrierFormed) absFresh
  have absIncluded := withType.addConstant_includes abstraction (.function represented carrier)
    (TypeFormed.function withType.signature functionInType representedInType carrierFormed) absFresh
  have repFresh : .constant request.representationName ∉ withAbs.names := by
    have different : request.representationName ≠ request.abstractionName := Ne.symm fresh.2.2.2
    simpa [withAbs, abstraction, addConstant, constantName, withType, addTypeOperator, different]
      using fresh.2.2.1
  exact withAbs.addConstant (.mk request.representationName (.representation operator))
    (.function carrier represented)
    (TypeFormed.function withAbs.signature
      (absIncluded.1 TypeOp.function 2 functionInType)
      (carrierFormed.mono absIncluded) (representedInType.mono absIncluded)) repFresh

theorem typeDefinitionExtension_includes (context : TheoryContext)
    (request : TypeOperatorDefinitionRequest) (represented : Ty)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (representedFormed : TypeFormed context.signature represented)
    (fresh : TypeNamesFresh context.names request) :
    context.signature.Includes
      (context.typeDefinitionExtension request represented functionArity representedFormed fresh).signature := by
  unfold typeDefinitionExtension
  exact (context.addTypeOperator_includes _ _ _).trans
    ((TheoryContext.addConstant_includes _ _ _ _ _).trans
      (TheoryContext.addConstant_includes _ _ _ _ _))

theorem typeDefinitionExtension_names (context : TheoryContext)
    (request : TypeOperatorDefinitionRequest) (represented : Ty)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (representedFormed : TypeFormed context.signature represented)
    (fresh : TypeNamesFresh context.names request) :
    (context.typeDefinitionExtension request represented functionArity representedFormed fresh).names =
      extendTypeNames context.names request := by
  simp only [typeDefinitionExtension, addConstant, addTypeOperator, constantName, operatorName,
    extendTypeNames]
  simp [Finset.insert_comm]

theorem typeDefinitionExtension_registered (context : TheoryContext)
    (request : TypeOperatorDefinitionRequest) (represented : Ty)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (representedFormed : TypeFormed context.signature represented)
    (fresh : TypeNamesFresh context.names request) :
    let operator : TypeOp := .mk request.typeName
      (.defined request.predicateSource request.typeVariables)
    let carrier : Ty := .op operator (request.typeVariables.map Ty.var)
    let after := context.typeDefinitionExtension request represented functionArity representedFormed fresh
    after.signature.typeOperators operator = some request.typeVariables.length ∧
      after.signature.constants (.mk request.abstractionName (.abstraction operator)) =
        some (.function represented carrier) ∧
      after.signature.constants (.mk request.representationName (.representation operator)) =
        some (.function carrier represented) := by
  have different :
      Const.mk request.abstractionName
          (.abstraction (.mk request.typeName (.defined request.predicateSource request.typeVariables))) ≠
        Const.mk request.representationName
          (.representation (.mk request.typeName (.defined request.predicateSource request.typeVariables))) := by
    intro equal
    have provenance := congrArg (fun constant : Const =>
      match constant with | .mk _ origin => origin) equal
    cases provenance
  simp [typeDefinitionExtension, addConstant, addTypeOperator, Signature.addConstant,
    Signature.addTypeOperator, Const.same_eq_true_iff, TypeOp.same_eq_true_iff, different]

end TheoryContext

structure ContextTypeDefinitionResult where
  context : TheoryContext
  predicate : CanonicalTerm
  witness : CanonicalTerm
  output : TypeOperatorDefinitionResult

/-- The registration gate is separate from proof validity: its existence
theorem must be supplied by the proof history. This operation checks the
declarations used by its predicate and witness and the source definition
guards, and returns the shared definition equations without new axiom tags. -/
def admitTypeInTheoryFromApplication (context : TheoryContext) (witnesses : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (predicate witness : CanonicalTerm)
    (_application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl) :
    Option ContextTypeDefinitionResult :=
  if annotationsFormedB context.signature witnesses predicate.term = true ∧
      annotationsFormedB context.signature witnesses witness.term = true then
    if representedFormed : typeFormedB context.signature witness.ty = true then
      if functionArity : context.signature.typeOperators TypeOp.function = some 2 then
        if fresh : TypeNamesFresh context.names request then
          match admitType context.names request with
          | none => none
          | some result => some
              { context := context.typeDefinitionExtension request witness.ty functionArity
                  ((typeFormedB_eq_true_iff _ _).mp representedFormed) fresh
                predicate := predicate
                witness := witness
                output := result.2 }
        else none
      else none
    else none
  else none

def admitTypeInTheory (context : TheoryContext) (witnesses : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) : Option ContextTypeDefinitionResult :=
  match request.existence.sequent.concl.applicationView? with
  | none => none
  | some view => admitTypeInTheoryFromApplication context witnesses request
      view.function view.argument view.semantics

/-- A known canonical application supplies the exact same ingress operation
as the executable application-view path. -/
theorem admitTypeInTheory_eq_fromApplication
    (context : TheoryContext) (witnesses : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl) :
    admitTypeInTheory context witnesses request =
      admitTypeInTheoryFromApplication context witnesses request predicate witness application := by
  unfold admitTypeInTheory
  rw [CanonicalTerm.applicationView?_eq_some _ _ _ application]

theorem admitTypeInTheoryFromApplication_isSome_iff
    (context : TheoryContext) (witnesses : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl) :
    (admitTypeInTheoryFromApplication context witnesses request predicate witness application).isSome = true ↔
      annotationsFormedB context.signature witnesses predicate.term = true ∧
      annotationsFormedB context.signature witnesses witness.term = true ∧
      TypeFormed context.signature witness.ty ∧
      context.signature.typeOperators TypeOp.function = some 2 ∧
      TypeAdmissible context.names request := by
  unfold admitTypeInTheoryFromApplication
  by_cases inputs : annotationsFormedB context.signature witnesses predicate.term = true ∧
      annotationsFormedB context.signature witnesses witness.term = true
  · simp only [if_pos inputs]
    by_cases formed : typeFormedB context.signature witness.ty = true
    · simp only [dif_pos formed]
      by_cases functionArity : context.signature.typeOperators TypeOp.function = some 2
      · simp only [dif_pos functionArity]
        by_cases fresh : TypeNamesFresh context.names request
        · simp only [dif_pos fresh]
          cases checked : admitType context.names request with
          | none =>
              have refused := admitType_isSome_iff context.names request
              simp only [checked, Option.isSome_none, Bool.false_eq_true, false_iff] at refused
              simp [inputs.1, inputs.2, refused]
          | some result =>
              have admitted := (admitType_isSome_iff context.names request).mp (by simp [checked])
              simp [inputs.1, inputs.2, (typeFormedB_eq_true_iff _ _).mp formed, functionArity, admitted]
        · have refused : ¬ TypeAdmissible context.names request := fun admitted => fresh admitted.1
          simp [fresh, refused]
      · simp [functionArity]
    · have refused : ¬ TypeFormed context.signature witness.ty :=
        fun formedType => formed ((typeFormedB_eq_true_iff _ _).mpr formedType)
      simp [formed, refused]
  · have refused : ¬ (annotationsFormedB context.signature witnesses predicate.term = true ∧
        annotationsFormedB context.signature witnesses witness.term = true ∧
        TypeFormed context.signature witness.ty ∧
        context.signature.typeOperators TypeOp.function = some 2 ∧
        TypeAdmissible context.names request) := fun admitted => inputs ⟨admitted.1, admitted.2.1⟩
    simp [inputs, refused]

theorem admitTypeInTheoryFromApplication_result
    {context : TheoryContext} {witnesses : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {predicate witness : CanonicalTerm}
    {application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl}
    {result : ContextTypeDefinitionResult}
    (accepted : admitTypeInTheoryFromApplication context witnesses request
      predicate witness application = some result) :
    result.predicate = predicate ∧ result.witness = witness ∧
      AnnotationsFormed context.signature predicate.term ∧
      AnnotationsFormed context.signature witness.term ∧
      context.signature.Includes result.context.signature ∧
      result.context.names = extendTypeNames context.names request ∧
      checkTypeOperatorDefinition request = some result.output ∧
      result.output.abstractionRepresentationTheorem.axioms = request.existence.axioms ∧
      result.output.representationAbstractionTheorem.axioms = request.existence.axioms := by
  unfold admitTypeInTheoryFromApplication at accepted
  split at accepted
  · rename_i inputs
    split at accepted
    · rename_i representedFormed
      split at accepted
      · rename_i functionArity
        split at accepted
        · rename_i fresh
          split at accepted
          · cases accepted
          · rename_i output checked
            have equal := Option.some.inj accepted
            subst result
            have actual := (admitType_result checked).2
            have retained := checkTypeOperatorDefinition_preserves_axioms actual
            exact ⟨rfl, rfl, annotationsFormedB_sound _ _ inputs.1,
              annotationsFormedB_sound _ _ inputs.2,
              context.typeDefinitionExtension_includes request witness.ty functionArity
                ((typeFormedB_eq_true_iff _ _).mp representedFormed) fresh,
              context.typeDefinitionExtension_names request witness.ty functionArity
                ((typeFormedB_eq_true_iff _ _).mp representedFormed) fresh,
              actual, retained⟩
        · cases accepted
      · cases accepted
    · cases accepted
  · cases accepted

theorem admitTypeInTheory_result
    {context : TheoryContext} {witnesses : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : ContextTypeDefinitionResult}
    (accepted : admitTypeInTheory context witnesses request = some result) :
    CanonicalTerm.ApplicationSemantics result.predicate result.witness request.existence.sequent.concl ∧
      AnnotationsFormed context.signature result.predicate.term ∧
      AnnotationsFormed context.signature result.witness.term ∧
      context.signature.Includes result.context.signature ∧
      result.context.names = extendTypeNames context.names request ∧
      checkTypeOperatorDefinition request = some result.output ∧
      result.output.abstractionRepresentationTheorem.axioms = request.existence.axioms ∧
      result.output.representationAbstractionTheorem.axioms = request.existence.axioms := by
  cases viewChecked : request.existence.sequent.concl.applicationView? with
  | none => simp [admitTypeInTheory, viewChecked] at accepted
  | some view =>
      simp only [admitTypeInTheory, viewChecked] at accepted
      have output := admitTypeInTheoryFromApplication_result accepted
      rw [output.1, output.2.1]
      exact ⟨view.semantics, output.2.2⟩

/-- The registry contains the exact symbols returned by the shared operation,
at schemas formed from the actual witness type and declared parameters. -/
theorem admitTypeInTheoryFromApplication_registered
    {context : TheoryContext} {witnesses : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {predicate witness : CanonicalTerm}
    {application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl}
    {result : ContextTypeDefinitionResult}
    (accepted : admitTypeInTheoryFromApplication context witnesses request
      predicate witness application = some result) :
    let carrier := Ty.op result.output.typeOperator (request.typeVariables.map Ty.var)
    result.context.signature.typeOperators result.output.typeOperator = some request.typeVariables.length ∧
      result.context.signature.constants result.output.abstractionConstant =
        some (.function result.witness.ty carrier) ∧
      result.context.signature.constants result.output.representationConstant =
        some (.function carrier result.witness.ty) := by
  have actual := (admitTypeInTheoryFromApplication_result accepted).2.2.2.2.2.2.1
  obtain ⟨sourcePredicate, sourceWitness, sourceApplication, sourceBool, _, _, _, _, _, outputEqual⟩ :=
    checkTypeOperatorDefinition_result actual
  have provenance := makeTypeOperatorDefinition_provenance request sourcePredicate sourceWitness
    sourceApplication sourceBool
  rw [← outputEqual] at provenance
  simp only [provenance.1, provenance.2.1, provenance.2.2.1]
  unfold admitTypeInTheoryFromApplication at accepted
  split at accepted
  · split at accepted
    · rename_i representedFormed
      split at accepted
      · rename_i functionArity
        split at accepted
        · rename_i fresh
          split at accepted
          · cases accepted
          · have equal := Option.some.inj accepted
            subst result
            exact context.typeDefinitionExtension_registered request witness.ty functionArity
              ((typeFormedB_eq_true_iff _ _).mp representedFormed) fresh
        · cases accepted
      · cases accepted
    · cases accepted
  · cases accepted

/-! ## Exact pointwise source outputs

The shared declaration gate and the HOL Light source operation use the same
registered types and constants. Their equation presentations are distinct.
The source adapter computes the pointwise statements from the gate's actual
application view, retaining its definition context and dependencies.
-/

structure SourceTypeDefinitionResult where
  core : ContextTypeDefinitionResult
  output : TypeOperatorDefinitionResult

abbrev SourceTypeDefinitionResult.context (result : SourceTypeDefinitionResult) : TheoryContext :=
  result.core.context

def admitSourceTypeInTheory (context : TheoryContext) (witnesses : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) : Option SourceTypeDefinitionResult :=
  match request.existence.sequent.concl.applicationView? with
  | none => none
  | some view =>
      match admitTypeInTheoryFromApplication context witnesses request
          view.function view.argument view.semantics with
      | none => none
      | some core =>
          if conclusionBool : request.existence.sequent.concl.isBoolB = true then
            some ⟨core, makePointwiseTypeOperatorDefinition request view.function view.argument
              view.semantics ((CanonicalTerm.isBoolB_eq_true_iff _).mp conclusionBool)⟩
          else none

/-- The source kernel's two pointwise results, specified independently as
raw canonical formulas. The abstraction variable has the new carrier; the
representation variable has the witness carrier. -/
def PointwiseTypeDefinitionSemantics (request : TypeOperatorDefinitionRequest)
    (predicate witness : CanonicalTerm) (result : TypeOperatorDefinitionResult) : Prop :=
  let operator := TypeOp.mk request.typeName
    (.defined request.predicateSource request.typeVariables)
  let carrier := Ty.op operator (request.typeVariables.map Ty.var)
  let represented := witness.ty
  let abstraction := Const.mk request.abstractionName (.abstraction operator)
  let representation := Const.mk request.representationName (.representation operator)
  let absTerm := DBTerm.const abstraction (Ty.function represented carrier)
  let repTerm := DBTerm.const representation (Ty.function carrier represented)
  let a := DBTerm.free ⟨Name.global "a", carrier⟩
  let r := DBTerm.free ⟨Name.global "r", represented⟩
  result.typeOperator = operator ∧
    result.abstractionConstant = abstraction ∧ result.representationConstant = representation ∧
    result.abstractionRepresentationTheorem.sequent.concl.term =
      CanonicalTerm.equalityDB carrier (.app absTerm (.app repTerm a)) a ∧
    result.representationAbstractionTheorem.sequent.concl.term =
      CanonicalTerm.equalityDB Ty.bool (.app predicate.term r)
        (CanonicalTerm.equalityDB represented (.app repTerm (.app absTerm r)) r)

/-- The typed construction produces the actual source formulas, including
the second equation's orientation and both variables' carrier annotations. -/
theorem makePointwiseTypeOperatorDefinition_semantics
    (request : TypeOperatorDefinitionRequest) (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (conclusionBool : request.existence.sequent.concl.IsBool) :
    PointwiseTypeDefinitionSemantics request predicate witness
      (makePointwiseTypeOperatorDefinition request predicate witness application conclusionBool) := by
  simp [PointwiseTypeDefinitionSemantics, makePointwiseTypeOperatorDefinition,
    makeTypeOperatorDefinitionWithPresentation, CanonicalTerm.equalityOfSameType,
    CanonicalTerm.applicationOfFunction, CanonicalTerm.constant, CanonicalTerm.free]

/-- Accepted outputs have the pointwise source form for the actual checked
predicate and witness, rather than merely a matching theorem name. -/
theorem admitSourceTypeInTheory_pointwise
    {context : TheoryContext} {witnesses : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context witnesses request = some result) :
    PointwiseTypeDefinitionSemantics request result.core.predicate result.core.witness result.output := by
  cases view : request.existence.sequent.concl.applicationView? with
  | none => simp [admitSourceTypeInTheory, view] at accepted
  | some application =>
      simp only [admitSourceTypeInTheory, view] at accepted
      cases admitted : admitTypeInTheoryFromApplication context witnesses request
          application.function application.argument application.semantics with
      | none => simp [admitted] at accepted
      | some core =>
          simp only [admitted] at accepted
          split at accepted
          · rename_i conclusionBool
            have equal := Option.some.inj accepted
            subst result
            have shape := admitTypeInTheoryFromApplication_result admitted
            simpa only [shape.1, shape.2.1] using
              makePointwiseTypeOperatorDefinition_semantics request application.function
                application.argument application.semantics
                ((CanonicalTerm.isBoolB_eq_true_iff _).mp conclusionBool)
          · contradiction

/-- Every source result retains the very context produced by the shared
admission gate and the exact source dependencies. -/
theorem admitSourceTypeInTheory_result
    {context : TheoryContext} {witnesses : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context witnesses request = some result) :
    context.signature.Includes result.context.signature ∧
      admitTypeInTheory context witnesses request = some result.core ∧
      result.output.abstractionRepresentationTheorem.axioms = request.existence.axioms ∧
      result.output.representationAbstractionTheorem.axioms = request.existence.axioms ∧
      result.output.abstractionRepresentationTheorem.sequent.hyp = request.existence.sequent.hyp ∧
      result.output.representationAbstractionTheorem.sequent.hyp = request.existence.sequent.hyp := by
  cases view : request.existence.sequent.concl.applicationView? with
  | none => simp [admitSourceTypeInTheory, view] at accepted
  | some application =>
      simp only [admitSourceTypeInTheory, view] at accepted
      cases admitted : admitTypeInTheoryFromApplication context witnesses request
          application.function application.argument application.semantics with
      | none => simp [admitted] at accepted
      | some core =>
          simp only [admitted] at accepted
          split at accepted
          · rename_i conclusionBool
            have equal := Option.some.inj accepted
            subst result
            have source := admitTypeInTheoryFromApplication_result admitted
            have metadata := makeTypeOperatorDefinitionWithPresentation_metadata .pointwise request
              application.function application.argument application.semantics
              ((CanonicalTerm.isBoolB_eq_true_iff _).mp conclusionBool)
            refine ⟨source.2.2.2.2.1, ?_, metadata.2.2.2.1, metadata.2.2.2.2.1,
              metadata.2.2.2.2.2.1, metadata.2.2.2.2.2.2⟩
            simp [admitTypeInTheory, view, admitted]
          · contradiction

/-- The redundant source Boolean check does not change which definitions
are admitted by the registered declaration gate. -/
theorem admitSourceTypeInTheory_isSome_eq
    (context : TheoryContext) (witnesses : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) :
    (admitSourceTypeInTheory context witnesses request).isSome =
      (admitTypeInTheory context witnesses request).isSome := by
  cases view : request.existence.sequent.concl.applicationView? with
  | none => simp [admitSourceTypeInTheory, admitTypeInTheory, view]
  | some application =>
      cases admitted : admitTypeInTheoryFromApplication context witnesses request
          application.function application.argument application.semantics with
      | none => simp [admitSourceTypeInTheory, admitTypeInTheory, view, admitted]
      | some core =>
          have actual := (admitTypeInTheoryFromApplication_result admitted).2.2.2.2.2.2.1
          obtain ⟨_, _, _, bool, _, _, _, _, _, _⟩ := checkTypeOperatorDefinition_result actual
          have checkedBool := (CanonicalTerm.isBoolB_eq_true_iff _).mpr bool
          simp [admitSourceTypeInTheory, admitTypeInTheory, view, admitted, checkedBool]

/-- Successful source admissions construct the same registered definition
regardless of which checked instance certificates are supplied. -/
theorem admitTypeInTheoryFromApplication_unique (context : TheoryContext) (first second : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (left right : ContextTypeDefinitionResult)
    (one : admitTypeInTheoryFromApplication context first request predicate witness application = some left)
    (two : admitTypeInTheoryFromApplication context second request predicate witness application = some right) :
    left = right := by
  unfold admitTypeInTheoryFromApplication at one two
  cases admitted : admitType context.names request with
  | none =>
    simp only [admitted] at one two
    split_ifs at one two
  | some result =>
    simp only [admitted] at one two
    split_ifs at one two; simp_all

theorem admitSourceTypeInTheory_unique (context : TheoryContext) (first second : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (left right : SourceTypeDefinitionResult)
    (one : admitSourceTypeInTheory context first request = some left)
    (two : admitSourceTypeInTheory context second request = some right) :
    left = right := by
  unfold admitSourceTypeInTheory at one two
  cases viewChecked : request.existence.sequent.concl.applicationView? with
  | none => simp [viewChecked] at one
  | some view =>
    simp only [viewChecked] at one two
    cases firstCore : admitTypeInTheoryFromApplication context first request
        view.function view.argument view.semantics with
    | none => simp [firstCore] at one
    | some firstResult =>
      cases secondCore : admitTypeInTheoryFromApplication context second request
          view.function view.argument view.semantics with
      | none => simp [secondCore] at two
      | some secondResult =>
        have equal := admitTypeInTheoryFromApplication_unique context first second request view.function view.argument
          view.semantics firstResult secondResult firstCore secondCore
        cases equal
        simp only [firstCore] at one
        simp only [secondCore] at two
        exact Option.some.inj (one.symm.trans two)

/-! ## Registered theory judgments

Inference, declaration formation, and definition extension are separate
obligations. The judgment below joins them while retaining the source's
existence proof as a premise of a type definition. Its definition constructors
do not reinterpret defining equations as new primitive axioms.
-/

def SequentFormed (signature : Signature) (sequent : Sequent) : Prop :=
  AnnotationsFormed signature sequent.concl.term ∧
    ∀ hypothesis ∈ sequent.hyp, AnnotationsFormed signature hypothesis.term

def TheoremFormed (signature : Signature) (fact : Theorem) : Prop :=
  SequentFormed signature fact.sequent ∧
    ∀ commitment ∈ fact.axioms, SequentFormed signature commitment

theorem SequentFormed.mono {before after : Signature} (included : before.Includes after)
    {sequent : Sequent} (formed : SequentFormed before sequent) :
    SequentFormed after sequent :=
  ⟨formed.1.mono included, fun hypothesis member => (formed.2 hypothesis member).mono included⟩

theorem TheoremFormed.mono {before after : Signature} (included : before.Includes after)
    {fact : Theorem} (formed : TheoremFormed before fact) :
    TheoremFormed after fact :=
  ⟨formed.1.mono included, fun commitment member => (formed.2 commitment member).mono included⟩

def sequentFormedB (signature : Signature) (witnesses : InstanceWitnesses)
    (sequent : Sequent) : Bool :=
  annotationsFormedB signature witnesses sequent.concl.term &&
    Finset.fold Bool.and true (fun hypothesis =>
      annotationsFormedB signature witnesses hypothesis.term) sequent.hyp

def theoremFormedB (signature : Signature) (witnesses : InstanceWitnesses)
    (fact : Theorem) : Bool :=
  sequentFormedB signature witnesses fact.sequent &&
    Finset.fold Bool.and true (sequentFormedB signature witnesses) fact.axioms

private theorem fold_and_true_iff {A : Type} (values : Finset A) (check : A → Bool) :
    Finset.fold Bool.and true check values = true ↔ ∀ value ∈ values, check value = true := by
  have expanded := Finset.fold_op_rel_iff_and (s := values) (op := Bool.and)
    (b := true) (f := check) (r := fun (_ : Bool) value => value = true) (c := true)
    (fun {x y z} => by simp only [Bool.and_eq_true])
  simpa using expanded

/-- Formation certificates establish declarations, independently of theorem
validity or the selected source axiom policy. -/
theorem sequentFormedB_sound (signature : Signature) (witnesses : InstanceWitnesses)
    {sequent : Sequent} (accepted : sequentFormedB signature witnesses sequent = true) :
    SequentFormed signature sequent := by
  rw [sequentFormedB, Bool.and_eq_true, fold_and_true_iff] at accepted
  exact ⟨annotationsFormedB_sound signature witnesses accepted.1,
    fun hypothesis member => annotationsFormedB_sound signature witnesses (accepted.2 hypothesis member)⟩

theorem theoremFormedB_sound (signature : Signature) (witnesses : InstanceWitnesses)
    {fact : Theorem} (accepted : theoremFormedB signature witnesses fact = true) :
    TheoremFormed signature fact := by
  rw [theoremFormedB, Bool.and_eq_true, fold_and_true_iff] at accepted
  exact ⟨sequentFormedB_sound signature witnesses accepted.1,
    fun commitment member => sequentFormedB_sound signature witnesses (accepted.2 commitment member)⟩

/-- One certificate family realizes all theorem occurrences in a declaration
context. This is logical completeness, without a claim about a native
certificate-selection procedure. -/
theorem sequentFormedB_complete (signature : Signature) (witnesses : InstanceWitnesses)
    (realizes : ∀ constant annotation, ConstantInstance signature constant annotation →
      constantInstanceB signature witnesses constant annotation = true)
    {sequent : Sequent} (formed : SequentFormed signature sequent) :
    sequentFormedB signature witnesses sequent = true := by
  rw [sequentFormedB, Bool.and_eq_true, fold_and_true_iff]
  exact ⟨annotationsFormedB_complete signature witnesses realizes formed.1,
    fun hypothesis member => annotationsFormedB_complete signature witnesses realizes
      (formed.2 hypothesis member)⟩

theorem theoremFormedB_complete (signature : Signature) (witnesses : InstanceWitnesses)
    (realizes : ∀ constant annotation, ConstantInstance signature constant annotation →
      constantInstanceB signature witnesses constant annotation = true)
    {fact : Theorem} (formed : TheoremFormed signature fact) :
    theoremFormedB signature witnesses fact = true := by
  rw [theoremFormedB, Bool.and_eq_true, fold_and_true_iff]
  exact ⟨sequentFormedB_complete signature witnesses realizes formed.1,
    fun commitment member => sequentFormedB_complete signature witnesses realizes
      (formed.2 commitment member)⟩

namespace InferenceFormation

/-- Non-premise type data supplied to a source operation. Both halves of
every type maplet are formed, even when its key will not match. -/
def types : InferenceRequest → List Ty
  | .abs binder _ => [binder.ty]
  | .instType entries _ => entries.flatMap fun entry => [entry.1, entry.2]
  | _ => []

/-- All supplied terms are checked for declarations, including unused and
shadowed term maplets. Ordered theorem premises are checked in the cache. -/
def terms : InferenceRequest → List DBTerm
  | .refl term | .assume term => [term.term]
  | .beta term => [term.canonical.term]
  | .inst entries _ => entries.flatMap fun entry =>
      [entry.1.canonical.term, entry.2.toDB []]
  | _ => []

def Formed (signature : Signature) (request : InferenceRequest) : Prop :=
  (∀ type ∈ types request, TypeFormed signature type) ∧
    ∀ term ∈ terms request, AnnotationsFormed signature term

def check (signature : Signature) (witnesses : InstanceWitnesses)
    (request : InferenceRequest) : Bool :=
  (types request).all (typeFormedB signature) &&
    (terms request).all (annotationsFormedB signature witnesses)

theorem check_sound (signature : Signature) (witnesses : InstanceWitnesses)
    (request : InferenceRequest) (accepted : check signature witnesses request = true) :
    Formed signature request := by
  rw [check, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at accepted
  exact ⟨fun type member => (typeFormedB_eq_true_iff _ _).mp (accepted.1 type member),
    fun term member => annotationsFormedB_sound signature witnesses (accepted.2 term member)⟩

theorem check_complete (signature : Signature) (witnesses : InstanceWitnesses)
    (realizes : ∀ constant annotation, ConstantInstance signature constant annotation →
      constantInstanceB signature witnesses constant annotation = true)
    {request : InferenceRequest} (formed : Formed signature request) :
    check signature witnesses request = true := by
  rw [check, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  exact ⟨fun type member => (typeFormedB_eq_true_iff _ _).mpr (formed.1 type member),
    fun term member => annotationsFormedB_complete signature witnesses realizes
      (formed.2 term member)⟩

end InferenceFormation

/-- Source derivability in an actual declaration context. Definition premises
and provenance are part of the calculus, rather than an admission oracle. -/
inductive TheoryDerives (policy : AxiomPolicy) : TheoryContext → Theorem → Prop where
  | inference {context : TheoryContext} {request : InferenceRequest} {out : Theorem}
      (step : request.Semantics out)
      (argumentsFormed : InferenceFormation.Formed context.signature request)
      (premises : ∀ premise ∈ request.premises, TheoryDerives policy context premise)
      (outputFormed : TheoremFormed context.signature out) :
      TheoryDerives policy context out
  | axiom {context : TheoryContext} {sequent : Sequent} {out : Theorem}
      (hypothesesEmpty : sequent.hyp = ∅) (authorized : policy sequent)
      (step : AxiomSemantics sequent out) (formed : TheoremFormed context.signature out) :
      TheoryDerives policy context out
  | weaken {before after : TheoryContext} {out : Theorem}
      (included : before.signature.Includes after.signature)
      (proof : TheoryDerives policy before out) : TheoryDerives policy after out
  | constantDefinition {context : TheoryContext} {witnesses : InstanceWitnesses}
      {name : Name} {body : SourceTerm} {result : ContextConstantDefinitionResult}
      (accepted : admitConstantInTheory context witnesses name body = some result)
      (formed : TheoremFormed result.context.signature result.output.definitionTheorem) :
      TheoryDerives policy result.context result.output.definitionTheorem
  | typeAbstractionDefinition {context : TheoryContext} {witnesses : InstanceWitnesses}
      {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
      (accepted : admitSourceTypeInTheory context witnesses request = some result)
      (existence : TheoryDerives policy context request.existence)
      (formed : TheoremFormed result.context.signature result.output.abstractionRepresentationTheorem) :
      TheoryDerives policy result.context result.output.abstractionRepresentationTheorem
  | typeRepresentationDefinition {context : TheoryContext} {witnesses : InstanceWitnesses}
      {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
      (accepted : admitSourceTypeInTheory context witnesses request = some result)
      (existence : TheoryDerives policy context request.existence)
      (formed : TheoremFormed result.context.signature result.output.representationAbstractionTheorem) :
      TheoryDerives policy result.context result.output.representationAbstractionTheorem

/-- Enlarging the declared axiom policy preserves the original derivation,
including its admitted definitions and their existence premises. -/
theorem TheoryDerives.mono_policy {first second : AxiomPolicy}
    (included : ∀ sequent, first sequent → second sequent)
    {context : TheoryContext} {out : Theorem} (proof : TheoryDerives first context out) :
    TheoryDerives second context out := by
  induction proof with
  | inference step formed _ output prior => exact .inference step formed prior output
  | «axiom» empty authorized step formed => exact .axiom empty (included _ authorized) step formed
  | weaken included _ prior => exact .weaken included prior
  | constantDefinition accepted formed => exact .constantDefinition accepted formed
  | typeAbstractionDefinition accepted _ formed prior => exact .typeAbstractionDefinition accepted prior formed
  | typeRepresentationDefinition accepted _ formed prior => exact .typeRepresentationDefinition accepted prior formed

theorem TheoryDerives.wellFormed {policy : AxiomPolicy} {context : TheoryContext} {out : Theorem}
    (proof : TheoryDerives policy context out) : TheoremFormed context.signature out := by
  induction proof with
  | inference _ _ _ formed => exact formed
  | «axiom» _ _ _ formed => exact formed
  | weaken included _ prior => exact prior.mono included
  | constantDefinition _ formed => exact formed
  | typeAbstractionDefinition _ _ formed => exact formed
  | typeRepresentationDefinition _ _ formed => exact formed

/-- Adding definitions never authorizes a new source axiom. Type definitions
retain exactly the dependencies of their checked existence derivation. -/
theorem TheoryDerives.authorizedAxioms {policy : AxiomPolicy} {context : TheoryContext} {out : Theorem}
    (proof : TheoryDerives policy context out) : policy.AllowsTheorem out := by
  induction proof with
  | inference step _ _ _ premises => exact step.outputAxiomsAllowed policy premises
  | «axiom» _ authorized step _ =>
      exact policy.allows_of_axioms_eq_singleton _ _ step.2.1 authorized
  | weaken _ _ prior => exact prior
  | constantDefinition accepted _ =>
      exact policy.allows_of_axioms_eq_empty _ (admitConstantInTheory_result accepted).2.2.2.2.2.2.1
  | typeAbstractionDefinition accepted _ _ earlier =>
      exact policy.allows_of_axioms_eq _ _ (admitSourceTypeInTheory_result accepted).2.2.1 earlier
  | typeRepresentationDefinition accepted _ _ earlier =>
      exact policy.allows_of_axioms_eq _ _ (admitSourceTypeInTheory_result accepted).2.2.2.1 earlier

namespace ContextControls

def booleanContext : TheoryContext :=
  TheoryContext.empty.addTypeOperator TypeOp.bool 0 (by simp [TheoryContext.empty])

def baseContext : TheoryContext :=
  booleanContext.addTypeOperator TypeOp.function 2 (by
    simp [booleanContext, TheoryContext.addTypeOperator, TheoryContext.empty,
      operatorName, TypeOp.bool, TypeOp.function, Name.global])

theorem boolean_registered : baseContext.signature.typeOperators TypeOp.bool = some 0 := by
  have first := TheoryContext.empty.addTypeOperator_registered TypeOp.bool 0
    (by simp [TheoryContext.empty])
  exact (booleanContext.addTypeOperator_includes TypeOp.function 2 _).1 TypeOp.bool 0 first

theorem function_registered : baseContext.signature.typeOperators TypeOp.function = some 2 :=
  booleanContext.addTypeOperator_registered TypeOp.function 2 _

theorem boolean_formed : TypeFormed baseContext.signature Ty.bool := by
  simp only [Ty.bool, TypeFormed, List.length_nil]
  exact ⟨boolean_registered, by simp⟩

def certificates : InstanceWitnesses := fun _ _ => TypeSubst.empty

theorem identity_source_admitted :
    checkSource baseContext.signature certificates Controls.identitySource = some Controls.identityTerm := by
  simp only [checkSource, Controls.identitySource_checked, bind, Option.bind,
    Controls.identityTerm, annotationsFormedB, typeFormedB, Ty.bool,
    boolean_registered, List.attach_nil, List.all_nil]
  rfl

theorem identity_definition_admitted :
    (admitConstantInTheory baseContext certificates (Name.global "identity") Controls.identitySource).isSome = true := by
  rw [admitConstantInTheory_isSome_iff]
  refine ⟨Controls.identityTerm, identity_source_admitted,
    TypeFormed.function _ function_registered boolean_formed boolean_formed, ?_⟩
  have original := (admitConstant_isSome_iff ∅ (Name.global "identity") Controls.identitySource).mp
    Controls.identity_definition_admitted
  refine ⟨?_, original.2⟩
  simp [baseContext, booleanContext, TheoryContext.addTypeOperator, TheoryContext.empty]

def registeredIdentity : Const := .mk (Name.global "identity") (.defined Controls.identitySource)

def identityContext : TheoryContext :=
  baseContext.addConstant registeredIdentity Controls.identityTerm.ty
    (TypeFormed.function _ function_registered boolean_formed boolean_formed)
    (by simp [baseContext, booleanContext, TheoryContext.addTypeOperator, TheoryContext.empty,
      constantName, registeredIdentity])

/-- A same-name symbol carrying another body is not the admitted definition. -/
theorem mismatched_definition_refused :
    identityContext.signature.constants
      (.mk (Name.global "identity") (.defined (.var (Name.global "x") Ty.bool))) = none := by
  simp [identityContext, baseContext, booleanContext, TheoryContext.addConstant,
    TheoryContext.addTypeOperator, TheoryContext.empty, Signature.addConstant, Signature.addTypeOperator,
    registeredIdentity, Controls.identitySource, Const.same, ConstProvenance.same, SourceTerm.same]

theorem duplicate_definition_refused :
    admitConstantInTheory identityContext certificates (Name.global "identity") Controls.identitySource = none := by
  apply admitConstantInTheory_repeated_refused
  simp [identityContext, TheoryContext.addConstant, constantName, registeredIdentity]

def equalityParameter : Name := Name.global "A"

theorem equality_schema_formed :
    TypeFormed baseContext.signature (Ty.equality (.var equalityParameter)) := by
  apply TypeFormed.function _ function_registered
  · simp [TypeFormed]
  · apply TypeFormed.function _ function_registered
    · simp [TypeFormed]
    · exact boolean_formed

def coreContext : TheoryContext :=
  baseContext.addConstant Const.equality (Ty.equality (.var equalityParameter)) equality_schema_formed
    (by simp [baseContext, booleanContext, TheoryContext.addTypeOperator, TheoryContext.empty,
      constantName, Const.equality])

theorem core_includes : baseContext.signature.Includes coreContext.signature :=
  baseContext.addConstant_includes _ _ equality_schema_formed _

def equalityCertificates : InstanceWitnesses := fun _ _ =>
  ⟨[(equalityParameter, Controls.identityTerm.ty)]⟩

/-- A closed predicate selecting exactly the Boolean identity function. -/
def identityPredicateSource : SourceTerm :=
  .app (.const Const.equality (Ty.equality Controls.identityTerm.ty)) Controls.identitySource

def identityPredicate : CanonicalTerm :=
  CanonicalTerm.applicationOfFunction
    (CanonicalTerm.constant Const.equality (Ty.equality Controls.identityTerm.ty))
    Controls.identityTerm (.function Controls.identityTerm.ty Ty.bool)
    (Ty.destFunction?_function _ _)

theorem identityPredicateSource_checked :
    identityPredicateSource.check = some identityPredicate := by
  rw [SourceTerm.check_eq_some_iff]
  have body := (SourceTerm.check_eq_some_iff _ _).mp Controls.identitySource_checked
  simp only [identityPredicateSource, SourceTerm.toDB, body,
    identityPredicate, CanonicalTerm.applicationOfFunction, CanonicalTerm.constant]

def identityExistence : Theorem :=
  Theorem.emptyResult ∅
    (CanonicalTerm.equalityOfSameType Controls.identityTerm Controls.identityTerm rfl)

/-- The type-definition premise is actually derivable, not a fabricated
hypothesis-free theorem record. -/
theorem identityExistence_derivable (policy : AxiomPolicy) :
    Mettapedia.Logic.Derives (HOLLight.Rule policy) identityExistence := by
  refine Mettapedia.Logic.Derives.node [] identityExistence ?_ ?_
  · refine Or.inl ⟨.refl Controls.identityTerm, rfl, ?_⟩
    exact ⟨_, CanonicalTerm.equalityOfSameType_semantics _ _ rfl, rfl, rfl, rfl⟩
  · intro premise member
    cases member

def identityTypeRequest : TypeOperatorDefinitionRequest :=
  { typeName := Name.global "identityFunction"
    abstractionName := Name.global "absIdentityFunction"
    representationName := Name.global "repIdentityFunction"
    typeVariables := []
    predicateSource := identityPredicateSource
    existence := identityExistence }

theorem identityType_application :
    CanonicalTerm.ApplicationSemantics identityPredicate Controls.identityTerm
      identityTypeRequest.existence.sequent.concl := by
  refine ⟨Controls.identityTerm.ty, Ty.bool, Ty.destFunction?_function _ _, rfl, ?_⟩
  rfl

theorem identityType_admissible : TypeAdmissible coreContext.names identityTypeRequest := by
  refine ⟨?_, ⟨identityPredicate, Controls.identityTerm, identityType_application,
    identityPredicateSource_checked, rfl, rfl, ?_, List.nodup_nil, ?_⟩, ?_⟩
  · simp [TypeNamesFresh, identityTypeRequest, coreContext, baseContext, booleanContext,
      TheoryContext.addConstant, TheoryContext.addTypeOperator, TheoryContext.empty,
      constantName, operatorName, Const.equality, TypeOp.bool, TypeOp.function, Name.global]
  · exact .app .const (.abs .bound)
  · simp [identityTypeRequest, identityPredicate, Controls.identityTerm,
      CanonicalTerm.applicationOfFunction, CanonicalTerm.constant, DBTerm.typeVariables,
      Ty.equality, Ty.function, Ty.bool, Ty.typeVariables, Ty.typeVariablesList]
  · simp [identityTypeRequest, sortedParameters, identityPredicateSource, Controls.identitySource,
      Controls.identityTerm, SourceTerm.toDB, boundIndex, DBTerm.typeVariables,
      Ty.equality, Ty.function, Ty.bool, Ty.typeVariables, Ty.typeVariablesList]

theorem identityType_registered_inputs :
    annotationsFormedB coreContext.signature equalityCertificates identityPredicate.term = true ∧
      annotationsFormedB coreContext.signature equalityCertificates Controls.identityTerm.term = true := by
  simp [annotationsFormedB, identityPredicate, Controls.identityTerm,
    CanonicalTerm.applicationOfFunction, CanonicalTerm.constant, typeFormedB,
    constantInstanceB, coreContext, baseContext, booleanContext, TheoryContext.addConstant,
    TheoryContext.addTypeOperator, TheoryContext.empty, Signature.addConstant,
    Signature.addTypeOperator, equalityCertificates, equalityParameter,
    Const.equality, TypeOp.bool, TypeOp.function, Ty.equality, Ty.function, Ty.bool,
    Const.same, TypeOp.same, TypeSubst.lookup, Name.global]

theorem identityType_admitted :
    (admitTypeInTheoryFromApplication coreContext equalityCertificates identityTypeRequest
      identityPredicate Controls.identityTerm identityType_application).isSome = true := by
  rw [admitTypeInTheoryFromApplication_isSome_iff]
  exact ⟨identityType_registered_inputs.1, identityType_registered_inputs.2,
    (TypeFormed.function _ function_registered boolean_formed boolean_formed).mono core_includes,
    core_includes.1 TypeOp.function 2 function_registered, identityType_admissible⟩

end ContextControls

end Mettapedia.Languages.HOLLight.DefinitionAdapters
