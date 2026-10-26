import Mettapedia.Languages.HOLLight.DefinitionHistoryModels

/-!
# Assignment support of constructed source interpretations

Agreement on a source type's actual parameters preserves its evaluated domain.
The initial pointed interpretation and the original source selection operation
also preserve their values under that agreement. Original polymorphic constant
admission preserves this support through the complete chronological history,
and actual translated source sentences retain truth. These are properties of
the constructed meanings, rather than assumptions imposed on arbitrary
meanings. Operator-family extension and mixed type-definition histories remain
separate transport obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ModelAssignmentSupport

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInterpretation SignatureFormation

universe w

/-- The actual HOL carrier at a source annotation depends only on parameters
occurring in that annotation. Equality includes the complete carrier data. -/
theorem carrier_parameter_agreement (other : OperatorFamilies.{w})
    (first second : Assignment.{w}) (type : Ty)
    (agree : ∀ name ∈ type.typeVariables, first name = second name) :
    HOL.Ty.denote.{0, w + 1} (atomicCarrier other first) type.toHOL =
      HOL.Ty.denote.{0, w + 1} (atomicCarrier other second) type.toHOL :=
  (evaluate_toHOL other first type).symm.trans
    ((congrArg Domain.Carrier (evaluate_parameter_agreement
      (primitiveFamilies other) first second type agree)).trans
      (evaluate_toHOL other second type))

/-- The same comparison at the original typed HOL carrier. -/
theorem carrier_parameter_agreement_hol (other : OperatorFamilies.{w})
    (first second : Assignment.{w}) (type : HOL.Ty AtomicTy)
    (agree : ∀ name ∈ (Ty.fromHOL type).typeVariables, first name = second name) :
    HOL.Ty.denote.{0, w + 1} (atomicCarrier other first) type =
      HOL.Ty.denote.{0, w + 1} (atomicCarrier other second) type := by
  simpa only [Ty.toHOL_fromHOL] using carrier_parameter_agreement other first second
    (Ty.fromHOL type) agree

private theorem function_support (domain codomain : Ty) :
    (Ty.function domain codomain).typeVariables = domain.typeVariables ∪ codomain.typeVariables := by
  simp [Ty.function, Ty.typeVariables, Ty.typeVariablesList]

/-- The ambient default value follows the same finite type support. In
particular, no unused assignment slot can change an ordinary source symbol. -/
theorem defaultValue_parameter_agreement (other : OperatorFamilies.{w})
    (first second : Assignment.{w}) (type : HOL.Ty AtomicTy)
    (agree : ∀ name ∈ (Ty.fromHOL type).typeVariables, first name = second name) :
    HEq ((standardModel other first).defaultValue
      (fun atomic => (evaluate (primitiveFamilies other) first atomic.val).inhabitant) type)
      ((standardModel other second).defaultValue
        (fun atomic => (evaluate (primitiveFamilies other) second atomic.val).inhabitant) type) := by
  induction type with
  | prop => rfl
  | base atomic =>
      change HEq (evaluate (primitiveFamilies other) first atomic.val).inhabitant
        (evaluate (primitiveFamilies other) second atomic.val).inhabitant
      rw [evaluate_parameter_agreement (primitiveFamilies other) first second atomic.val agree]
  | arr domain codomain domainIH codomainIH =>
      have domainAgreement : ∀ name ∈ (Ty.fromHOL domain).typeVariables,
          first name = second name := by
        intro name member
        exact agree name (by
          simp only [Ty.fromHOL, function_support, Finset.mem_union]
          exact Or.inl member)
      have codomainAgreement : ∀ name ∈ (Ty.fromHOL codomain).typeVariables,
          first name = second name := by
        intro name member
        exact agree name (by
          simp only [Ty.fromHOL, function_support, Finset.mem_union]
          exact Or.inr member)
      apply Function.hfunext (carrier_parameter_agreement_hol other first second domain domainAgreement)
      intro value otherValue same
      exact codomainIH codomainAgreement

/-- The ordinary source meanings are the original pointed construction and
retain values across assignments agreeing on the symbol's actual type. -/
theorem pointedMeanings_parameter_agreement (other : OperatorFamilies.{w})
    (first second : Assignment.{w}) {type : HOL.Ty AtomicTy} (symbol : Symbol type)
    (agree : ∀ name ∈ (Ty.fromHOL type).typeVariables, first name = second name) :
    HEq (pointedMeanings other first symbol) (pointedMeanings other second symbol) :=
  defaultValue_parameter_agreement other first second type agree

private theorem transportedSelector_heq {first second : Domain.{w}}
    {A B : Type (w + 1)} (firstCarrier : first.Carrier = A)
    (secondCarrier : second.Carrier = B) (sameDomain : first = second) (sameTarget : A = B) :
    HEq (fun predicate : A → ULift.{w + 1, 0} Prop =>
      Equiv.cast firstCarrier (first.select
        (fun value => predicate (Equiv.cast firstCarrier value))))
      (fun predicate : B → ULift.{w + 1, 0} Prop =>
        Equiv.cast secondCarrier (second.select
          (fun value => predicate (Equiv.cast secondCarrier value)))) := by
  cases sameDomain
  cases sameTarget
  rfl

/-- The actual source selector depends on the evaluated domain, including its
inhabitant. This comparison permits both an operator-table extension and an
actual source type instance; neither carrier nor selection equality is assumed
separately from equality of the complete evaluated domains. -/
theorem sourceSelection_domain_eq (firstOther secondOther : OperatorFamilies.{w})
    (first second : Assignment.{w}) (firstOperand secondOperand : Ty)
    (sameDomain : evaluate (primitiveFamilies firstOther) first firstOperand =
      evaluate (primitiveFamilies secondOther) second secondOperand) :
    HEq (sourceSelection firstOther first firstOperand)
      (sourceSelection secondOther second secondOperand) :=
  transportedSelector_heq (evaluate_toHOL firstOther first firstOperand)
    (evaluate_toHOL secondOther second secondOperand) sameDomain
    ((evaluate_toHOL firstOther first firstOperand).symm.trans
      ((congrArg Domain.Carrier sameDomain).trans
        (evaluate_toHOL secondOther second secondOperand)))

/-- The actual source selector depends on the evaluated domain, including its
inhabitant, and hence only on the operand's actual source parameters. -/
theorem sourceSelection_parameter_agreement (other : OperatorFamilies.{w})
    (first second : Assignment.{w}) (operand : Ty)
    (agree : ∀ name ∈ operand.typeVariables, first name = second name) :
    HEq (sourceSelection other first operand) (sourceSelection other second operand) :=
  sourceSelection_domain_eq other other first second operand operand
    (evaluate_parameter_agreement (primitiveFamilies other) first second operand agree)

/-- The constructed initial interpretation, including source selection,
retains actual symbol values under agreement on their type parameters. -/
theorem initial_symbol_parameter_agreement (other : OperatorFamilies.{w})
    (first second : Assignment.{w}) {type : HOL.Ty AtomicTy} (symbol : Symbol type)
    (agree : ∀ name ∈ (Ty.fromHOL type).typeVariables, first name = second name) :
    HEq ((ModelInterpretation.model other first (pointedMeanings other first)).constDen symbol)
      ((ModelInterpretation.model other second (pointedMeanings other second)).constDen symbol) := by
  change HEq (interpretation other first (pointedMeanings other first) symbol)
    (interpretation other second (pointedMeanings other second) symbol)
  cases symbol with
  | «variable» sourceVar typed =>
      exact pointedMeanings_parameter_agreement other first second (.variable sourceVar typed) agree
  | constant constant annotation typed =>
      cases typed
      simp only [interpretation]
      split
      · exact pointedMeanings_parameter_agreement other first second
          (.constant constant annotation rfl) agree
      · rename_i operand recognized
        have operandType : (selectionType operand).toHOL = annotation.toHOL :=
          congrArg Ty.toHOL (selectionOperand?_eq_some_iff _ _ _ |>.mp recognized).2.symm
        have operandAgreement : ∀ name ∈ operand.typeVariables, first name = second name := by
          intro name member
          apply agree name
          rw [← operandType, selectionType_toHOL]
          simp only [Ty.fromHOL, Ty.fromHOL_toHOL, function_support]
          exact Finset.mem_union_left _ (Finset.mem_union_left _ member)
        exact (eqRec_heq _ _).trans ((sourceSelection_parameter_agreement other first second
          operand operandAgreement).trans (eqRec_heq _ _).symm)

/-- The original bound context contributes only the parameters of its types. -/
def contextSupport (context : HOL.Ctx AtomicTy) : Finset Name :=
  Ty.typeVariablesList (context.map Ty.fromHOL)

private theorem bound_type_support {context : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (index : HOL.Var context type) : (Ty.fromHOL type).typeVariables ⊆ contextSupport context := by
  induction index with
  | vz =>
      intro name member
      exact Finset.mem_union_left _ member
  | vs index ih =>
      intro name member
      exact Finset.mem_union_right _ (ih member)

/-- Type dependencies inferred by the compositional source translation are
already present in the original annotations or original bound context. -/
theorem translation_type_support {context : HOL.Ctx AtomicTy} {term : DBTerm}
    {type : HOL.Ty AtomicTy} {target : HOL.Term Symbol context type}
    (translation : TranslatesCompositionally context term type target) :
    (Ty.fromHOL type).typeVariables ⊆ term.typeVariables ∪ contextSupport context := by
  induction translation with
  | @equality context constant annotation operand type recognized typed =>
      obtain ⟨rfl, rfl⟩ := (equalityOperand?_eq_some_iff _ _ _).mp recognized
      cases typed
      intro name member
      simp only [Ty.fromHOL, Ty.fromHOL_toHOL, function_support] at member
      exact Finset.mem_union_left _ (by
        simpa only [DBTerm.typeVariables, Ty.equality, function_support, Ty.typeVariables,
          Ty.typeVariablesList, Finset.union_empty] using member)
  | constant unrecognized typed =>
      cases typed
      intro name member
      exact Finset.mem_union_left _ (by simpa only [Ty.fromHOL_toHOL, DBTerm.typeVariables] using member)
  | free typed =>
      cases typed
      intro name member
      exact Finset.mem_union_left _ (by simpa only [Ty.fromHOL_toHOL, DBTerm.typeVariables] using member)
  | bound index =>
      intro name member
      exact Finset.mem_union_right _ (bound_type_support index member)
  | @app context function argument domain codomain functionTarget argumentTarget
      functionTranslation argumentTranslation functionIH argumentIH =>
      intro name member
      simp only [DBTerm.typeVariables]
      have functionMember := functionIH (by
        simp only [Ty.fromHOL, function_support]
        exact Finset.mem_union_right _ member)
      rcases Finset.mem_union.mp functionMember with inFunction | inContext
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ inFunction)
      · exact Finset.mem_union_right _ inContext
  | @abs context domain body type codomain bodyTarget typed bodyTranslation bodyIH =>
      intro name member
      simp only [DBTerm.typeVariables]
      simp only [Ty.fromHOL, function_support] at member
      rcases Finset.mem_union.mp member with inDomain | inCodomain
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by
          simpa only [← typed, Ty.fromHOL_toHOL] using inDomain))
      · rcases Finset.mem_union.mp (bodyIH inCodomain) with inBody | inContext
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ inBody)
        · simp only [contextSupport, List.map_cons, Ty.typeVariablesList,
            Finset.mem_union] at inContext
          rcases inContext with inDomain | inContext
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by
              simpa only [← typed, Ty.fromHOL_toHOL] using inDomain))
          · exact Finset.mem_union_right _ inContext

/-- Assignment support is a property of the complete actual symbol meanings.
It is proved for the constructed initial family and preserved by definitions. -/
def SymbolLocal (family : Assignment.{w} → HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) : Prop :=
  ∀ first second {type} (symbol : Symbol type),
    (∀ name ∈ (Ty.fromHOL type).typeVariables, first name = second name) →
    HEq ((family first).constDen symbol) ((family second).constDen symbol)

private theorem family_carrier_agreement (other : OperatorFamilies.{w})
    (family : Assignment.{w} → HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (carriers : ∀ assignment, (family assignment).Carrier = atomicCarrier other assignment)
    (first second : Assignment.{w}) (type : HOL.Ty AtomicTy)
    (agree : ∀ name ∈ (Ty.fromHOL type).typeVariables, first name = second name) :
    HOL.Ty.denote.{0, w + 1} (family first).Carrier type =
      HOL.Ty.denote.{0, w + 1} (family second).Carrier type := by
  rw [carriers first, carriers second]
  exact carrier_parameter_agreement_hol other first second type agree

private theorem translation_carrier_agreement (other : OperatorFamilies.{w})
    (family : Assignment.{w} → HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (carriers : ∀ assignment, (family assignment).Carrier = atomicCarrier other assignment)
    (first second : Assignment.{w}) {context : HOL.Ctx AtomicTy} {term : DBTerm}
    {type : HOL.Ty AtomicTy} {target : HOL.Term Symbol context type}
    (translation : TranslatesCompositionally context term type target)
    (termAgreement : ∀ name ∈ term.typeVariables, first name = second name)
    (contextAgreement : ∀ name ∈ contextSupport context, first name = second name) :
    HOL.Ty.denote.{0, w + 1} (family first).Carrier type =
      HOL.Ty.denote.{0, w + 1} (family second).Carrier type := by
  apply family_carrier_agreement other family carriers first second type
  intro name member
  rcases Finset.mem_union.mp (translation_type_support translation member) with inTerm | inContext
  · exact termAgreement name inTerm
  · exact contextAgreement name inContext

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
/-- Actual compositional term denotation has finite assignment support when
its underlying constructed symbol meanings do. Bound valuations are retained
pointwise across the actual carrier equalities. -/
theorem denote_parameter_agreement (other : OperatorFamilies.{w})
    (family : Assignment.{w} → HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (carriers : ∀ assignment, (family assignment).Carrier = atomicCarrier other assignment)
    (full : ∀ assignment, (family assignment).FullDomains) (localSymbols : SymbolLocal family)
    (first second : Assignment.{w}) {context : HOL.Ctx AtomicTy} {term : DBTerm}
    {type : HOL.Ty AtomicTy} {target : HOL.Term Symbol context type}
    (translation : TranslatesCompositionally context term type target) :
    (∀ name ∈ term.typeVariables, first name = second name) →
    (∀ name ∈ contextSupport context, first name = second name) →
    ∀ (firstValuation : HOL.HenkinModel.Valuation.{0, 0, w + 1} (family first) context)
      (secondValuation : HOL.HenkinModel.Valuation.{0, 0, w + 1} (family second) context),
      (∀ type (index : HOL.Var context type), HEq (firstValuation index) (secondValuation index)) →
      HEq (HOL.HenkinModel.denote.{0, 0, w + 1} (family first) target firstValuation)
        (HOL.HenkinModel.denote.{0, 0, w + 1} (family second) target secondValuation) := by
  induction translation with
  | @equality context constant annotation operand type recognized typed =>
      intro termAgreement contextAgreement firstValuation secondValuation same
      obtain ⟨rfl, rfl⟩ := (equalityOperand?_eq_some_iff _ _ _).mp recognized
      have operandAgreement : ∀ name ∈ (Ty.fromHOL type).typeVariables,
          first name = second name := by
        intro name member
        apply termAgreement name
        simpa only [DBTerm.typeVariables, Ty.equality, function_support,
          Ty.typeVariables, Ty.typeVariablesList, Finset.union_empty, ← typed,
          Ty.fromHOL_toHOL] using (Finset.mem_union_left _ member)
      have domain := family_carrier_agreement other family carriers first second type operandAgreement
      change HEq (fun left right => ULift.up ((family first).Eqv type left right))
        (fun left right => ULift.up ((family second).Eqv type left right))
      apply Function.hfunext domain
      intro left otherLeft lefts
      apply Function.hfunext domain
      intro right otherRight rights
      apply heq_of_eq
      apply ULift.ext
      apply propext
      exact (eqv_iff_eq _ (full first) type left right).trans
        ((equality_heq domain lefts rights).trans (eqv_iff_eq _ (full second) type otherLeft otherRight).symm)
  | constant unrecognized typed =>
      intro termAgreement contextAgreement firstValuation secondValuation same
      apply localSymbols first second
      simpa only [← typed, Ty.fromHOL_toHOL, DBTerm.typeVariables] using termAgreement
  | free typed =>
      intro termAgreement contextAgreement firstValuation secondValuation same
      apply localSymbols first second
      simpa only [← typed, Ty.fromHOL_toHOL, DBTerm.typeVariables] using termAgreement
  | bound index =>
      intro termAgreement contextAgreement firstValuation secondValuation same
      exact same _ index
  | @app context function argument domain codomain functionTarget argumentTarget
      functionTranslation argumentTranslation functionIH argumentIH =>
      intro termAgreement contextAgreement firstValuation secondValuation same
      have functionAgreement : ∀ name ∈ function.typeVariables, first name = second name :=
        fun name member => termAgreement name (by
          simp only [DBTerm.typeVariables]
          exact Finset.mem_union_left _ member)
      have argumentAgreement : ∀ name ∈ argument.typeVariables, first name = second name :=
        fun name member => termAgreement name (by
          simp only [DBTerm.typeVariables]
          exact Finset.mem_union_right _ member)
      exact apply_heq
        (translation_carrier_agreement other family carriers first second argumentTranslation
          argumentAgreement contextAgreement)
        (translation_carrier_agreement other family carriers first second
          (.app functionTranslation argumentTranslation) termAgreement contextAgreement)
        (functionIH functionAgreement contextAgreement firstValuation secondValuation same)
        (argumentIH argumentAgreement contextAgreement firstValuation secondValuation same)
  | @abs context domain body type codomain bodyTarget typed bodyTranslation bodyIH =>
      intro termAgreement contextAgreement firstValuation secondValuation same
      have domainAgreement : ∀ name ∈ (Ty.fromHOL type).typeVariables,
          first name = second name := by
        intro name member
        apply termAgreement name
        simp only [DBTerm.typeVariables]
        exact Finset.mem_union_left _ (by simpa only [← typed, Ty.fromHOL_toHOL] using member)
      apply Function.hfunext (family_carrier_agreement other family carriers first second type domainAgreement)
      intro value otherValue values
      apply bodyIH
      · intro name member
        apply termAgreement name
        simp only [DBTerm.typeVariables]
        exact Finset.mem_union_right _ member
      · intro name member
        simp only [contextSupport, List.map_cons, Ty.typeVariablesList, Finset.mem_union] at member
        rcases member with inDomain | inContext
        · exact domainAgreement name inDomain
        · exact contextAgreement name inContext
      · intro boundType index
        cases index with
        | vz => exact values
        | vs index => exact same _ index

/-- An instantiated schema retains every dependency introduced by the
replacement of a parameter which actually occurs in that schema. -/
theorem parameter_substitution_support (substitution : TypeSubst) (type : Ty)
    (parameter : Name) (occurs : parameter ∈ type.typeVariables) :
    (substitution.apply (.var parameter)).typeVariables ⊆
      (substitution.apply type).typeVariables := by
  cases type with
  | var name =>
      have equal : parameter = name := by simpa only [Ty.typeVariables, Finset.mem_singleton] using occurs
      subst parameter
      exact Finset.Subset.refl _
  | op operator arguments =>
      obtain ⟨argument, member, occurs⟩ := (SignatureFormation.mem_typeVariablesList parameter arguments).mp occurs
      intro name dependency
      simp only [TypeSubst.apply_op, Ty.typeVariables]
      apply (SignatureFormation.mem_typeVariablesList name (arguments.map substitution.apply)).mpr
      exact ⟨substitution.apply argument, List.mem_map.mpr ⟨argument, member, rfl⟩,
        parameter_substitution_support substitution argument parameter occurs dependency⟩
termination_by sizeOf type

/-- Actual source type substitution adds only the dependencies of the
replacement values of parameters already present in the original type. -/
theorem type_substitution_support (substitution : TypeSubst) (type : Ty) (support : Finset Name)
    (bounded : ∀ parameter ∈ type.typeVariables,
      (substitution.apply (.var parameter)).typeVariables ⊆ support) :
    (substitution.apply type).typeVariables ⊆ support := by
  cases type with
  | var name => exact bounded name (by simp only [Ty.typeVariables, Finset.mem_singleton])
  | op operator arguments =>
      intro name member
      simp only [TypeSubst.apply_op, Ty.typeVariables] at member
      obtain ⟨argument, argumentMember, parameterMember⟩ :=
        (SignatureFormation.mem_typeVariablesList name (arguments.map substitution.apply)).mp member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp argumentMember
      exact type_substitution_support substitution original support
        (fun parameter occurs => bounded parameter
          (SignatureFormation.mem_typeVariablesList parameter arguments |>.mpr
            ⟨original, originalMember, occurs⟩)) parameterMember
termination_by sizeOf type

/-- Type-only substitution uses the original displayed term annotations and
preserves bound positions; its dependencies have no hidden assignment slots. -/
theorem term_substitution_support (substitution : TypeSubst) (term : DBTerm) (support : Finset Name)
    (bounded : ∀ parameter ∈ term.typeVariables,
      (substitution.apply (.var parameter)).typeVariables ⊆ support) :
    ((TermSubst.mk substitution []).applyDB term).typeVariables ⊆ support := by
  induction term with
  | const constant annotation =>
      simp only [DBTerm.typeVariables] at bounded
      simpa only [TermSubst.applyDB_const, DBTerm.typeVariables] using
        type_substitution_support substitution annotation support bounded
  | free sourceVar =>
      simp only [DBTerm.typeVariables] at bounded
      simpa only [TermSubst.applyDB, TermSubst.lookup, List.find?_nil, Option.map_none,
        DBTerm.typeVariables, TypeSubst.applyVar] using
        type_substitution_support substitution sourceVar.ty support bounded
  | bound index =>
      simp only [TermSubst.applyDB_bound, DBTerm.typeVariables, Finset.empty_subset]
  | app function argument functionIH argumentIH =>
      simp only [TermSubst.applyDB_app, DBTerm.typeVariables, Finset.union_subset_iff]
      exact ⟨functionIH (fun parameter member => bounded parameter
        (by simp only [DBTerm.typeVariables]; exact Finset.mem_union_left _ member)),
        argumentIH (fun parameter member => bounded parameter
          (by simp only [DBTerm.typeVariables]; exact Finset.mem_union_right _ member))⟩
  | abs domain body bodyIH =>
      simp only [TermSubst.applyDB_abs, DBTerm.typeVariables, Finset.union_subset_iff]
      exact ⟨type_substitution_support substitution domain support
        (fun parameter member => bounded parameter
          (by simp only [DBTerm.typeVariables]; exact Finset.mem_union_left _ member)),
        bodyIH (fun parameter member => bounded parameter
          (by simp only [DBTerm.typeVariables]; exact Finset.mem_union_right _ member))⟩

/-- The original no-hidden-parameter guard survives every actual type
instance: the instantiated body depends only on its public annotation. -/
theorem instanceBody_support (result : DefinitionAdapters.ContextConstantDefinitionResult)
    (bounded : result.definition.term.typeVariables ⊆ result.definition.ty.typeVariables)
    (substitution : TypeSubst) :
    (ConstantAdmission.instanceTerm result substitution).term.typeVariables ⊆
      (substitution.apply result.definition.ty).typeVariables :=
  term_substitution_support substitution result.definition.term _
    (fun parameter occurs => parameter_substitution_support substitution result.definition.ty
      parameter (bounded occurs))

set_option backward.isDefEq.respectTransparency false in
/-- Locality is preserved by the original polymorphic source extension. The
new symbol's actual instantiated body is evaluated in the preceding model;
other identities and unlicensed annotations keep their preceding meaning. -/
theorem sourceExtension_symbol_local {context : DefinitionAdapters.TheoryContext}
    {instances : InstanceWitnesses} {name : Name} {body : SourceTerm}
    {result : DefinitionAdapters.ContextConstantDefinitionResult}
    (accepted : DefinitionAdapters.admitConstantInTheory context instances name body = some result)
    (other : OperatorFamilies.{w})
    (family : Assignment.{w} → HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (carriers : ∀ assignment, (family assignment).Carrier = atomicCarrier other assignment)
    (full : ∀ assignment, (family assignment).FullDomains) (localSymbols : SymbolLocal family) :
    SymbolLocal (fun assignment => ConstantAdmission.sourceExtension result (family assignment)) := by
  classical
  intro first second type symbol agree
  dsimp only
  cases symbol with
  | «variable» sourceVar typed =>
      rw [ConstantAdmission.sourceExtension_eq_reduct result (family first),
        ConstantAdmission.sourceExtension_eq_reduct result (family second)]
      change HEq ((family first).denote (ConstantAdmission.sourceExpansion result (.variable sourceVar typed)) (fun index => nomatch index))
        ((family second).denote (ConstantAdmission.sourceExpansion result (.variable sourceVar typed)) (fun index => nomatch index))
      rw [ConstantAdmission.sourceExpansion_variable]
      exact localSymbols first second (.variable sourceVar typed) agree
  | constant constant annotation typed =>
      by_cases sameConstant : constant = result.output.constant
      · subst constant
        by_cases instanceExists : ∃ substitution : TypeSubst,
            substitution.apply result.definition.ty = annotation
        · obtain ⟨substitution, rfl⟩ := instanceExists
          cases typed
          rw [ConstantAdmission.sourceExtension_constant_instance result
              (ConstantAdmission.admitted_parameters_bounded accepted),
            ConstantAdmission.sourceExtension_constant_instance result
              (ConstantAdmission.admitted_parameters_bounded accepted)]
          apply denote_parameter_agreement other family carriers full localSymbols first second
            (ConstantAdmission.instanceBody_translated result substitution)
          · intro parameter member
            apply agree parameter
            simpa only [Ty.fromHOL_toHOL] using
              (instanceBody_support result (ConstantAdmission.admitted_parameters_bounded accepted)
                substitution member)
          · intro parameter member
            simp [contextSupport, Ty.typeVariablesList] at member
          · intro boundType index
            nomatch index
        · rw [ConstantAdmission.sourceExtension_eq_reduct result (family first),
            ConstantAdmission.sourceExtension_eq_reduct result (family second)]
          simp only [HOL.HenkinModel.constantSubstitutionReduct,
            HOL.HenkinModel.constantSubstitutionPreModel]
          rw [ConstantAdmission.sourceExpansion_noninstance result annotation typed instanceExists]
          exact localSymbols first second (.constant result.output.constant annotation typed) agree
      · rw [ConstantAdmission.sourceExtension_constant_other result _ constant annotation typed sameConstant,
          ConstantAdmission.sourceExtension_constant_other result _ constant annotation typed sameConstant]
        exact localSymbols first second (.constant constant annotation typed) agree

/-- Every chronological constant extension inherits symbol support from its
constructed predecessor, using each original admission receipt. -/
theorem history_symbol_local {initial final : DefinitionAdapters.TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final) (other : OperatorFamilies.{w})
    (family : Assignment.{w} → HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (carriers : ∀ assignment, (family assignment).Carrier = atomicCarrier other assignment)
    (full : ∀ assignment, (family assignment).FullDomains) (localSymbols : SymbolLocal family) :
    SymbolLocal (fun assignment => history.extendModel (family assignment)) := by
  induction history with
  | nil => exact localSymbols
  | snoc prior instances name body result accepted ih =>
      exact sourceExtension_symbol_local accepted other _
        (fun assignment => (prior.carrier (family assignment)).trans (carriers assignment))
        (fun assignment => prior.fullDomains _ (full assignment)) ih

/-- The original constructed initial interpretation supplies the symbol
support needed by every admitted constant history. -/
theorem initial_symbol_local (other : OperatorFamilies.{w}) :
    SymbolLocal (fun assignment => ModelInterpretation.model other assignment
      (pointedMeanings other assignment)) :=
  initial_symbol_parameter_agreement other

/-- Complete actual constant histories from the original initial
interpretation do not acquire dependencies on unused assignment slots. -/
theorem history_initial_symbol_parameter_agreement {initial final : DefinitionAdapters.TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final) (other : OperatorFamilies.{w})
    (first second : Assignment.{w}) {type : HOL.Ty AtomicTy} (symbol : Symbol type)
    (agree : ∀ name ∈ (Ty.fromHOL type).typeVariables, first name = second name) :
    HEq ((history.extendModel (ModelInterpretation.model other first
      (pointedMeanings other first))).constDen symbol)
      ((history.extendModel (ModelInterpretation.model other second
        (pointedMeanings other second))).constDen symbol) :=
  history_symbol_local history other _ (fun _ => rfl)
    (fun _ => ModelInterpretation.model_fullDomains _ _ _) (initial_symbol_local other) first second symbol agree

/-- Finite parameter agreement preserves the actual truth of source sentences
through the complete constructed constant history. -/
theorem history_initial_models_parameter_agreement {initial final : DefinitionAdapters.TheoryContext}
    (history : DefinitionHistoryModels.ConstantHistory initial final) (other : OperatorFamilies.{w})
    (first second : Assignment.{w}) {term : DBTerm} {formula : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term .prop formula)
    (agree : ∀ name ∈ term.typeVariables, first name = second name) :
    (history.extendModel (ModelInterpretation.model other first
      (pointedMeanings other first))).models formula ↔
      (history.extendModel (ModelInterpretation.model other second
        (pointedMeanings other second))).models formula := by
  let family := fun assignment => history.extendModel
    (ModelInterpretation.model other assignment (pointedMeanings other assignment))
  have carriers : ∀ assignment, (family assignment).Carrier = atomicCarrier other assignment :=
    fun assignment => history.carrier _
  have full : ∀ assignment, (family assignment).FullDomains :=
    fun assignment => history.fullDomains _ (ModelInterpretation.model_fullDomains _ _ _)
  have localSymbols : SymbolLocal family := history_symbol_local history other _
    (fun _ => rfl) (fun _ => ModelInterpretation.model_fullDomains _ _ _) (initial_symbol_local other)
  change ((family first).denote formula _).down ↔ ((family second).denote formula _).down
  apply iff_of_eq
  apply congrArg (fun value : ULift.{w + 1, 0} Prop => value.down)
  apply eq_of_heq
  apply denote_parameter_agreement other family carriers full localSymbols first second translation agree
  · intro name member
    simp [contextSupport, Ty.typeVariablesList] at member
  · intro type index
    nomatch index

namespace Controls

/-- The original source selector at Boolean type is independent of every
assignment slot, even when the assignments have different inhabitants. -/
theorem boolean_selector_ignores_assignments (other : OperatorFamilies.{w})
    (first second : Assignment.{w}) :
    HEq ((ModelInterpretation.model other first (pointedMeanings other first)).constDen
      (.constant selectionConstant (selectionType Ty.bool) (selectionType_toHOL _)))
      ((ModelInterpretation.model other second (pointedMeanings other second)).constDen
        (.constant selectionConstant (selectionType Ty.bool) (selectionType_toHOL _))) := by
  apply initial_symbol_parameter_agreement other first second
  intro name member
  simp [Ty.fromHOL, Ty.typeVariables, Ty.typeVariablesList, Ty.function, Ty.bool] at member

/-- A genuine two-declaration polymorphic history retains its alias at an
admitted closed function instance under all assignment changes. -/
theorem polymorphic_alias_closed_instance_ignores_assignments (other : OperatorFamilies.{w})
    (first second : Assignment.{w}) :
    HEq ((DefinitionHistoryModels.Controls.polymorphicDefinitions.extendModel
      (ModelInterpretation.model other first (pointedMeanings other first))).constDen
      (.constant DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant
        (ModelInterpretation.Controls.functionInstance.apply
          DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty) rfl))
      ((DefinitionHistoryModels.Controls.polymorphicDefinitions.extendModel
        (ModelInterpretation.model other second (pointedMeanings other second))).constDen
        (.constant DefinitionHistoryModels.Controls.polymorphicAliasResult.output.constant
          (ModelInterpretation.Controls.functionInstance.apply
            DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty) rfl)) := by
  have noParameters : (ModelInterpretation.Controls.functionInstance.apply
      DefinitionHistoryModels.Controls.polymorphicAliasResult.definition.ty).typeVariables = ∅ := by
    decide +kernel
  apply history_initial_symbol_parameter_agreement
    DefinitionHistoryModels.Controls.polymorphicDefinitions other first second
  intro name member
  simp [Ty.fromHOL_toHOL, noParameters] at member

/-- This intentionally supplied meaning reads a slot absent from a Boolean
symbol's public type. It demonstrates why arbitrary meanings are excluded
from the constructed-locality theorem. -/
noncomputable def nonlocalMeanings (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    Meanings other assignment := by
  intro type symbol
  cases type with
  | prop => exact ULift.up (assignment (Name.global "unused") = proposition)
  | base atomic => exact pointedMeanings other assignment symbol
  | arr domain codomain => exact pointedMeanings other assignment symbol

private def marked : Domain.{w} := ⟨ULift.{w + 1, 0} Prop, .up True⟩

private theorem marked_ne_proposition : marked.{w} ≠ proposition := by
  intro equal
  have same : (True : Prop) = False :=
    congrArg (fun value : ULift.{w + 1, 0} Prop => value.down) (eq_of_heq (Domain.mk.inj equal).2)
  exact Eq.mp same True.intro

/-- Source model formation alone does not establish assignment locality: the
supplied fallback can distinguish an assignment slot absent from the type. -/
theorem arbitrary_meanings_need_not_be_local (other : OperatorFamilies.{w}) :
    ¬ SymbolLocal (fun assignment => ModelInterpretation.model other assignment
      (nonlocalMeanings other assignment)) := by
  intro localSymbols
  let first : Assignment.{w} := fun _ => proposition
  let second : Assignment.{w} := fun name => if name = Name.global "unused" then marked else proposition
  have values := localSymbols first second
    (.constant (.mk (Name.global "ordinary") .undefined) Ty.bool Ty.toHOL_bool)
    (by intro name member; simp [Ty.fromHOL, Ty.typeVariables, Ty.typeVariablesList, Ty.bool] at member)
  have absent : selectionOperand? (.mk (Name.global "ordinary") .undefined) Ty.bool = none := by
    decide +kernel
  simp only [ModelInterpretation.model, TypeFamilySemantics.model, HOL.HenkinModel.standard,
    interpretation] at values
  split at values
  · have same : (first (Name.global "unused") = proposition) =
        (second (Name.global "unused") = proposition) :=
      congrArg (fun value : ULift.{w + 1, 0} Prop => value.down) (eq_of_heq values)
    apply marked_ne_proposition
    simpa only [second, if_pos rfl] using Eq.mp same (show first (Name.global "unused") = proposition from rfl)
  · rename_i operand recognized
    rw [absent] at recognized
    cases recognized

end Controls

theorem translation_symbols (signature : Signature)
    (allowed : ∀ {type}, Symbol type → Prop)
    (constants : ∀ constant annotation {type} (typed : annotation.toHOL = type),
      ConstantInstance signature constant annotation → allowed (.constant constant annotation typed))
    (free : ∀ sourceVar {type} (typed : sourceVar.ty.toHOL = type), allowed (.variable sourceVar typed))
    {context : HOL.Ctx AtomicTy} {source : DBTerm} {type : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol context type}
    (translated : TranslatesCompositionally context source type target)
    (formed : AnnotationsFormed signature source) : target.SymbolsSatisfy allowed := by
  induction translated with
  | equality => trivial
  | constant unrecognized typed =>
    cases formed with
    | constant _ declared => exact constants _ _ typed declared
  | free typed => exact free _ typed
  | bound => trivial
  | app first second ihf ihs =>
    cases formed with
    | app firstFormed secondFormed => exact ⟨ihf firstFormed,ihs secondFormed⟩
  | abs typed body ih =>
    cases formed with
    | abs _ bodyFormed => exact ih bodyFormed

end Mettapedia.Languages.HOLLight.ModelAssignmentSupport
