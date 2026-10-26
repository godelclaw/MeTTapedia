import Mettapedia.Languages.OpenTheory.ExtensionalHOLInterpretation
import Mettapedia.Languages.OpenTheory.SignatureFormation
import Mettapedia.Logic.HOL.TypeSubstitutionModelCoherence
import Mettapedia.Logic.HOL.Semantics.ModelProperties
import Mettapedia.Logic.HOL.TypeDefinitionSemantics
import Mettapedia.Logic.HOL.HOLLightStandardTheory

/-!
# Inhabited type-operator families and semantic type instantiation

Source type operators denote actual families of inhabited carriers. The
primitive Boolean and function operators keep the meanings of the shared HOL
interpretation. Other operators are supplied as carrier data, without an
assumed logical soundness or model-extension interface.

Simultaneous source type substitution acts by reindexing the variable
assignment. Its identity and composition laws hold for the complete carrier
data, including the retained inhabitant. Interpretation in the existing HOL
model uses the already constructed translation of source types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.TypeFamilySemantics

open Mettapedia.Logic

universe w

/-- An explicit inhabitant records the nonempty-carrier commitment of HOL. -/
structure Domain where
  Carrier : Type (w + 1)
  inhabitant : Carrier

def proposition : Domain.{w} := ⟨ULift.{w + 1, 0} Prop, .up False⟩

def function (domain codomain : Domain.{w}) : Domain.{w} :=
  ⟨domain.Carrier → codomain.Carrier, fun _ => codomain.inhabitant⟩

/-- A selector depends on the actual inhabited domain, rather than the
source syntax used to present that domain. The existing choice construction
is instantiated at this one carrier. -/
noncomputable def Domain.select (domain : Domain.{w}) :
    (domain.Carrier → ULift.{w + 1, 0} Prop) → domain.Carrier :=
  HOL.HOLLightStandardTheory.selectionOperation.{0, w + 1}
    (fun _ : Unit => domain.Carrier) (fun _ => domain.inhabitant) (.base ())

theorem Domain.select_specified (domain : Domain.{w})
    (predicate : domain.Carrier → ULift.{w + 1, 0} Prop)
    (existsValue : ∃ value, (predicate value).down) :
    (predicate (domain.select predicate)).down :=
  HOL.HOLLightStandardTheory.selectionOperation_specified _ _ _ _ existsValue

abbrev OperatorFamilies := TypeOp → List Domain.{w} → Domain.{w}
abbrev Assignment := Name → Domain.{w}

/-- The reserved operators are interpreted, including their provenance;
unrecognized operators are delegated to the supplied family. -/
def primitiveFamilies (other : OperatorFamilies.{w}) : OperatorFamilies.{w} :=
  fun operator arguments =>
    if TypeOp.same operator TypeOp.bool then proposition
    else if TypeOp.same operator TypeOp.function then
      match arguments with
      | [domain, codomain] => function domain codomain
      | _ => other operator arguments
    else other operator arguments

@[simp] theorem primitiveFamilies_bool (other : OperatorFamilies.{w}) :
    primitiveFamilies other TypeOp.bool [] = proposition := by
  simp [primitiveFamilies]

@[simp] theorem primitiveFamilies_function (other : OperatorFamilies.{w})
    (domain codomain : Domain.{w}) :
    primitiveFamilies other TypeOp.function [domain, codomain] =
      function domain codomain := by
  have different : TypeOp.function ≠ TypeOp.bool := by
    intro equal
    have names : ("->" : String) = "bool" :=
      congrArg (fun operator => match operator with | .mk name _ => name.component) equal
    exact (by decide : ("->" : String) ≠ "bool") names
  simp [primitiveFamilies, different]

/-- Interpret every parameter occurrence recursively before applying its
operator's carrier family. Provenance is not substituted by this operation. -/
def evaluate (operators : OperatorFamilies.{w}) (assignment : Assignment.{w}) : Ty → Domain.{w}
  | .var name => assignment name
  | .op operator arguments => operators operator (arguments.map (evaluate operators assignment))
termination_by type => sizeOf type

@[simp] theorem evaluate_var (operators : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (name : Name) :
    evaluate operators assignment (.var name) = assignment name := by
  simp [evaluate]

@[simp] theorem evaluate_op (operators : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (operator : TypeOp) (arguments : List Ty) :
    evaluate operators assignment (.op operator arguments) =
      operators operator (arguments.map (evaluate operators assignment)) := by
  simp [evaluate]

@[simp] theorem evaluate_bool (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    evaluate (primitiveFamilies other) assignment Ty.bool = proposition := by
  simp [Ty.bool]

@[simp] theorem evaluate_function (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (domain codomain : Ty) :
    evaluate (primitiveFamilies other) assignment (.function domain codomain) =
      function (evaluate (primitiveFamilies other) assignment domain)
        (evaluate (primitiveFamilies other) assignment codomain) := by
  simp [Ty.function]

/-- Reindexing supplies the evaluated simultaneous replacement to each slot. -/
def reindex (operators : OperatorFamilies.{w}) (substitution : TypeSubst)
    (assignment : Assignment.{w}) : Assignment.{w} :=
  fun name => evaluate operators assignment (substitution.apply (.var name))

/-- This law concerns actual carrier constructions, not just the result type
of a successful source checker. -/
theorem evaluate_apply (operators : OperatorFamilies.{w}) (substitution : TypeSubst)
    (assignment : Assignment.{w}) (type : Ty) :
    evaluate operators assignment (substitution.apply type) =
      evaluate operators (reindex operators substitution assignment) type := by
  cases type with
  | var name => simp only [evaluate_var, reindex]
  | op operator arguments =>
      simp only [TypeSubst.apply_op, evaluate_op, List.map_map]
      congr 1
      exact List.map_congr_left (fun argument _ =>
        evaluate_apply operators substitution assignment argument)
termination_by sizeOf type

@[simp] theorem reindex_identity (operators : OperatorFamilies.{w})
    (assignment : Assignment.{w}) :
    reindex operators TypeSubst.empty assignment = assignment := by
  funext name
  simp [reindex]

/-- Source composition applies first and then second; contravariant
reindexing acts on assignments in the opposite nesting order. -/
theorem reindex_composition (operators : OperatorFamilies.{w})
    (first second : TypeSubst) (assignment : Assignment.{w}) :
    reindex operators (first.compose second) assignment =
      reindex operators first (reindex operators second assignment) := by
  funext name
  simp only [reindex, TypeSubst.apply_compose]
  exact evaluate_apply operators second assignment (first.apply (.var name))

/-- Only parameters occurring in the type affect its evaluated carrier. -/
theorem evaluate_parameter_agreement (operators : OperatorFamilies.{w})
    (first second : Assignment.{w}) (type : Ty)
    (agree : ∀ name ∈ type.typeVariables, first name = second name) :
    evaluate operators first type = evaluate operators second type := by
  cases type with
  | var name => simpa only [evaluate_var] using agree name (by simp [Ty.typeVariables])
  | op operator arguments =>
      simp only [evaluate_op]
      congr 1
      apply List.map_congr_left
      intro argument member
      exact evaluate_parameter_agreement operators first second argument
        (fun name occurs => agree name
          (SignatureFormation.mem_typeVariablesList name arguments |>.mpr
            ⟨argument, member, occurs⟩))
termination_by sizeOf type

/-- Extend a family table at the full provenance-bearing operator identity. -/
def extend (operators : OperatorFamilies.{w}) (operator : TypeOp)
    (family : List Domain.{w} → Domain.{w}) : OperatorFamilies.{w} :=
  fun candidate arguments =>
    if TypeOp.same candidate operator then family arguments else operators candidate arguments

@[simp] theorem extend_new (operators : OperatorFamilies.{w}) (operator : TypeOp)
    (family : List Domain.{w} → Domain.{w}) (arguments : List Domain.{w}) :
    extend operators operator family operator arguments = family arguments := by
  simp [extend]

/-! Independent ambient operator installations commute. -/

theorem extend_commute (original : OperatorFamilies.{w}) (first second : TypeOp)
    (firstFamily secondFamily : List Domain.{w} → Domain.{w}) (different : first ≠ second) :
    extend (extend original first firstFamily) second secondFamily =
      extend (extend original second secondFamily) first firstFamily := by
  funext candidate arguments
  by_cases firstMatch : candidate = first
  · subst candidate
    simp [extend, different]
  · by_cases secondMatch : candidate = second
    · subst candidate
      simp [extend, Ne.symm different]
    · simp [extend, firstMatch, secondMatch]


/-- A fresh extension preserves every old, formed carrier construction.
Malformed or undeclared old types are not granted an interpretation licence. -/
theorem evaluate_extend_formed (signature : SignatureFormation.Signature)
    (operators : OperatorFamilies.{w}) (operator : TypeOp)
    (family : List Domain.{w} → Domain.{w}) (assignment : Assignment.{w})
    (fresh : signature.typeOperators operator = none) (type : Ty)
    (formed : SignatureFormation.TypeFormed signature type) :
    evaluate (extend operators operator family) assignment type =
      evaluate operators assignment type := by
  cases type with
  | var name => simp only [evaluate_var]
  | op candidate arguments =>
      simp only [SignatureFormation.TypeFormed] at formed
      have different : candidate ≠ operator := by
        intro equal
        subst candidate
        rw [fresh] at formed
        cases formed.1
      have miss : TypeOp.same candidate operator = false :=
        Bool.eq_false_iff.mpr (fun hit => different ((TypeOp.same_eq_true_iff _ _).mp hit))
      simp only [evaluate_op, extend, miss, Bool.false_eq_true, if_false]
      congr 1
      exact List.map_congr_left (fun argument member =>
        evaluate_extend_formed signature operators operator family assignment fresh
          argument (formed.2 argument member))
termination_by sizeOf type

/-- Use the existing atomic-source-type substrate, without adding another
simple-type language or another evaluator for terms. -/
def atomicCarrier (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (atomic : AtomicTy) : Type (w + 1) :=
  (evaluate (primitiveFamilies other) assignment atomic.val).Carrier

theorem evaluate_toHOL (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (type : Ty) :
    (evaluate (primitiveFamilies other) assignment type).Carrier =
      HOL.Ty.denote.{0, w + 1} (atomicCarrier other assignment) type.toHOL := by
  rcases Ty.function_or_bool_or_isAtomic type with
    ⟨domain, codomain, rfl⟩ | rfl | atomic
  · rw [evaluate_function, Ty.toHOL_function]
    change (_ → _) = (_ → _)
    exact congrArg₂ (fun A B : Type (w + 1) => A → B)
      (evaluate_toHOL other assignment domain) (evaluate_toHOL other assignment codomain)
  · rw [evaluate_bool, Ty.toHOL_bool]
    rfl
  · rw [Ty.toHOL_of_isAtomic atomic]
    rfl
termination_by sizeOf type
decreasing_by
  all_goals subst_vars
  · exact Ty.sizeOf_domain_lt _ _
  · exact Ty.sizeOf_codomain_lt _ _

/-- The atomic carrier of the reindexed family is exactly the carrier used
by the existing HOL type-substitution reduct. -/
theorem atomicCarrier_reindex (other : OperatorFamilies.{w}) (substitution : TypeSubst)
    (assignment : Assignment.{w}) :
    atomicCarrier other (reindex (primitiveFamilies other) substitution assignment) =
      fun atomic => HOL.Ty.denote.{0, w + 1} (atomicCarrier other assignment)
        (substitution.baseInstance atomic) := by
  funext atomic
  change (evaluate (primitiveFamilies other)
    (reindex (primitiveFamilies other) substitution assignment) atomic.val).Carrier = _
  rw [← evaluate_apply]
  exact evaluate_toHOL other assignment (substitution.apply atomic.val)

/-- Values move along the proved structural carrier equality. -/
def substitutionEquiv (operators : OperatorFamilies.{w}) (substitution : TypeSubst)
    (assignment : Assignment.{w}) (type : Ty) :
    (evaluate operators (reindex operators substitution assignment) type).Carrier ≃
      (evaluate operators assignment (substitution.apply type)).Carrier :=
  Equiv.cast (congrArg Domain.Carrier (evaluate_apply operators substitution assignment type).symm)

theorem substitutionEquiv_apply_heq (operators : OperatorFamilies.{w})
    (substitution : TypeSubst) (assignment : Assignment.{w}) (type : Ty)
    (value : (evaluate operators (reindex operators substitution assignment) type).Carrier) :
    HEq (substitutionEquiv operators substitution assignment type value) value :=
  cast_heq _ _

theorem Domain.cast_inhabitant {left right : Domain.{w}} (equal : left = right) :
    Equiv.cast (congrArg Domain.Carrier equal) left.inhabitant = right.inhabitant := by
  cases equal
  rfl

theorem substitutionEquiv_inhabitant (operators : OperatorFamilies.{w})
    (substitution : TypeSubst) (assignment : Assignment.{w}) (type : Ty) :
    substitutionEquiv operators substitution assignment type
        (evaluate operators (reindex operators substitution assignment) type).inhabitant =
      (evaluate operators assignment (substitution.apply type)).inhabitant := by
  exact Domain.cast_inhabitant (evaluate_apply operators substitution assignment type).symm

/-- Substitution preserves the actual selector as well as the carrier and
inhabitant. It compares the transported function, not just its axiom. -/
theorem select_reindex_heq (operators : OperatorFamilies.{w}) (substitution : TypeSubst)
    (assignment : Assignment.{w}) (type : Ty) :
    HEq (evaluate operators (reindex operators substitution assignment) type).select
      (evaluate operators assignment (substitution.apply type)).select := by
  rw [← evaluate_apply]


/-- Interpretation of source values in the shared HOL model uses the proved
structural equality of carriers. -/
def holValue (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (type : Ty) :
    (evaluate (primitiveFamilies other) assignment type).Carrier ≃
      HOL.Ty.denote.{0, w + 1} (atomicCarrier other assignment) type.toHOL :=
  Equiv.cast (evaluate_toHOL other assignment type)

/-- A complete typed interpretation is model data, not a soundness assumption. -/
noncomputable def model (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (constants : ∀ {type}, Symbol type →
      HOL.Ty.denote.{0, w + 1} (atomicCarrier other assignment) type) :
    HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard (atomicCarrier other assignment) constants

theorem model_fullDomains (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (constants : ∀ {type}, Symbol type →
      HOL.Ty.denote.{0, w + 1} (atomicCarrier other assignment) type) :
    (model other assignment constants).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

noncomputable def model_inhabitedDomains (other : OperatorFamilies.{w})
    (assignment : Assignment.{w})
    (constants : ∀ {type}, Symbol type →
      HOL.Ty.denote.{0, w + 1} (atomicCarrier other assignment) type) :
    (model other assignment constants).InhabitedDomains :=
  (model other assignment constants).inhabitedDomains_of_fullDomains
    (model_fullDomains other assignment constants)
    (fun atomic => (evaluate (primitiveFamilies other) assignment atomic.val).inhabitant)

/-- Every interpreted simple type supports an actual total Hilbert selector. -/
noncomputable def model_choice (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (constants : ∀ {type}, Symbol type →
      HOL.Ty.denote.{0, w + 1} (atomicCarrier other assignment) type) :
    (model other assignment constants).HilbertChoice :=
  HOL.HenkinModel.HilbertChoice.ofFullInhabitedDomains
    (model_fullDomains other assignment constants)
    (model_inhabitedDomains other assignment constants)

/-- Pull back the complete typed interpretation along the actual source
type-and-symbol substitution. This reuses the shared STT model reduct. -/
def reindexedModel (substitution : TypeSubst)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standardTypeReduct substitution.baseInstance substitution.symbolInstance M

theorem reindexedModel_fullDomains (substitution : TypeSubst)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (reindexedModel substitution M).FullDomains :=
  HOL.HenkinModel.standardTypeReduct_fullDomains _ _ _

theorem reindexedModel_models (substitution : TypeSubst)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains)
    (sentence : HOL.ClosedFormula Symbol) :
    (reindexedModel substitution M).models sentence ↔
      M.models (HOL.mapTypes substitution.baseInstance substitution.symbolInstance sentence) :=
  HOL.HenkinModel.models_mapTypes _ _ _ full sentence

/-- The model reduct has exactly the recursively reindexed source carriers. -/
theorem reindexedModel_carrier (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (constants : ∀ {type}, Symbol type →
      HOL.Ty.denote.{0, w + 1} (atomicCarrier other assignment) type)
    (substitution : TypeSubst) :
    (reindexedModel substitution (model other assignment constants)).Carrier =
      atomicCarrier other (reindex (primitiveFamilies other) substitution assignment) :=
  (atomicCarrier_reindex other substitution assignment).symm

theorem reindexedModel_identity
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    reindexedModel TypeSubst.empty M = M := by
  calc
    _ = HOL.HenkinModel.standard M.Carrier M.constDen := by
      apply HOL.HenkinModel.standard_ext
      · funext atomic
        simp only [TypeSubst.baseInstance_empty]
        rfl
      · intro type symbol
        refine (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).trans ?_
        congr 1
        · simp only [TypeSubst.baseInstance_empty, HOL.Ty.substitute_id]
        · exact TypeSubst.symbolInstance_empty_heq symbol
    _ = M := HOL.HenkinModel.standard_eq_of_fullDomains M full

/-- Source substitution composition acts coherently on all model data,
including the meanings of polymorphic constants and free variables. -/
theorem reindexedModel_composition (first second : TypeSubst)
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    reindexedModel first (reindexedModel second M) =
      reindexedModel (first.compose second) M := by
  apply HOL.HenkinModel.standard_ext
  · funext atomic
    exact (HOL.Ty.denote_substitute second.baseInstance M.Carrier
      (first.baseInstance atomic)).trans
        (congrArg (HOL.Ty.denote.{0, w + 1} M.Carrier)
          (congrFun (TypeSubst.baseInstance_compose first second) atomic).symm)
  · intro type symbol
    refine (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).trans ?_
    refine (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).trans ?_
    refine HEq.trans ?_ (HOL.Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).symm
    congr 1
    · simp only [HOL.Ty.substitute_comp, TypeSubst.baseInstance_compose]
    · exact (TypeSubst.symbolInstance_compose_heq first second symbol).symm

/-- The source carrier families instantiate the constructed standard model;
the selected constant has its constructed meaning at every compound type. -/
noncomputable def standardModel (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    HOL.HenkinModel.{0, 0, w + 1} AtomicTy (HOL.HOLLightStandardTheory.Symbol AtomicTy) :=
  HOL.HOLLightStandardTheory.selectionModel (atomicCarrier other assignment)
    (fun atomic => (evaluate (primitiveFamilies other) assignment atomic.val).inhabitant)

theorem standardModel_fullDomains (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) : (standardModel other assignment).FullDomains :=
  HOL.HOLLightStandardTheory.selectionModel_fullDomains _ _

theorem standardModel_models_eta (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (domain codomain : Ty) :
    (standardModel other assignment).models
      (HOL.HOLLightStandardTheory.etaFormula domain.toHOL codomain.toHOL) :=
  HOL.HOLLightStandardTheory.selectionModel_models_eta _ _ _ _

theorem standardModel_models_selection (other : OperatorFamilies.{w})
    (assignment : Assignment.{w}) (type : Ty) :
    (standardModel other assignment).models
      (HOL.HOLLightStandardTheory.selectionFormula type.toHOL) :=
  HOL.HOLLightStandardTheory.selectionModel_models_selection _ _ _

/-- A type-definition family is the actual predicate subtype at each
parameter assignment. The supplied witness is retained as its inhabitant. -/
def subtypeFamily (represented : List Domain.{w} → Domain.{w})
    (predicate : ∀ parameters, (represented parameters).Carrier → Prop)
    (witness : ∀ parameters, (represented parameters).Carrier)
    (valid : ∀ parameters, predicate parameters (witness parameters)) :
    List Domain.{w} → Domain.{w} :=
  fun parameters =>
    ⟨HOL.WitnessedTypeDefinition.Carrier (predicate parameters),
      HOL.WitnessedTypeDefinition.inhabitant (predicate parameters)
        (witness parameters) (valid parameters)⟩

theorem subtypeFamily_abstraction_representation
    (represented : List Domain.{w} → Domain.{w})
    (predicate : ∀ parameters, (represented parameters).Carrier → Prop)
    (witness : ∀ parameters, (represented parameters).Carrier)
    (valid : ∀ parameters, predicate parameters (witness parameters))
    (parameters : List Domain.{w})
    (value : (subtypeFamily represented predicate witness valid parameters).Carrier) :
    HOL.WitnessedTypeDefinition.abstraction (predicate parameters)
        (witness parameters) (valid parameters)
        (HOL.WitnessedTypeDefinition.representation value) = value :=
  HOL.WitnessedTypeDefinition.abstraction_representation _ _ _ _

theorem subtypeFamily_predicate_iff_representation_abstraction
    (represented : List Domain.{w} → Domain.{w})
    (predicate : ∀ parameters, (represented parameters).Carrier → Prop)
    (witness : ∀ parameters, (represented parameters).Carrier)
    (valid : ∀ parameters, predicate parameters (witness parameters))
    (parameters : List Domain.{w}) (value : (represented parameters).Carrier) :
    predicate parameters value ↔
      HOL.WitnessedTypeDefinition.representation
        (HOL.WitnessedTypeDefinition.abstraction (predicate parameters)
          (witness parameters) (valid parameters) value) = value :=
  HOL.WitnessedTypeDefinition.predicate_iff_representation_abstraction _ _ _ _

namespace Controls

def natural : Domain.{w} := ⟨ULift.{w + 1, 0} Nat, .up 0⟩

def listOperator : TypeOp := .mk (Name.global "list") .undefined

def listFamily : List Domain.{w} → Domain.{w}
  | [element] => ⟨List element.Carrier, []⟩
  | _ => natural

def families : OperatorFamilies.{w} :=
  primitiveFamilies (extend (fun _ _ => natural) listOperator listFamily)

def alpha : Name := Name.global "A"

def listAlpha : Ty := .op listOperator [.var alpha]

/-- The same declared family has different, actual list carriers. -/
theorem list_natural : (evaluate families (fun _ => natural.{w}) listAlpha).Carrier =
    List (ULift.{w + 1, 0} Nat) := by
  simp [families, primitiveFamilies, extend, listAlpha, listOperator,
    listFamily, TypeOp.same, Name.global, TypeOp.bool, TypeOp.function, natural]

theorem list_proposition :
    (evaluate families (fun _ => proposition.{w}) listAlpha).Carrier =
      List (ULift.{w + 1, 0} Prop) := by
  simp [families, primitiveFamilies, extend, listAlpha, listOperator,
    listFamily, TypeOp.same, Name.global, TypeOp.bool, TypeOp.function, proposition]

theorem list_instantiation :
    evaluate families (fun _ => natural.{w})
        ((TypeSubst.ofList [(alpha, Ty.bool)]).apply listAlpha) =
      evaluate families
        (reindex families (TypeSubst.ofList [(alpha, Ty.bool)]) (fun _ => natural.{w}))
        listAlpha :=
  evaluate_apply _ _ _ _

def individual : AtomicTy :=
  ⟨.op (.mk (Name.global "ind") .undefined) [], by
    constructor
    · rfl
    · apply Bool.eq_false_iff.mpr
      intro bool
      have same := (Ty.isBool_eq_true_iff _).mp bool
      have operators := (Ty.op.inj same).1
      have names : ("ind" : String) = "bool" :=
        congrArg (fun operator => match operator with | .mk name _ => name.component) operators
      exact (by decide : ("ind" : String) ≠ "bool") names⟩

def initialOther : OperatorFamilies.{w} :=
  extend (fun _ _ => natural) listOperator listFamily

theorem individual_carrier :
    (standardModel initialOther (fun _ => natural.{w})).Carrier individual =
      ULift.{w + 1, 0} Nat := by
  simp [standardModel, HOL.HOLLightStandardTheory.selectionModel,
    HOL.HenkinModel.standard, atomicCarrier, individual, initialOther,
    primitiveFamilies, extend, listOperator, TypeOp.same, Name.global,
    TypeOp.bool, TypeOp.function, natural]

def individualValueEquiv :
    (standardModel initialOther (fun _ => natural.{w})).Carrier individual ≃
      ULift.{w + 1, 0} Nat := Equiv.cast individual_carrier

/-- The infinite base is retained alongside parameterized list carriers. -/
def infinityWitness :
    (standardModel initialOther (fun _ => natural.{w})).DedekindInfinityWitness individual where
  successor := fun value => individualValueEquiv.symm
    (ULift.up ((individualValueEquiv value).down + 1))
  successor_admissible := standardModel_fullDomains _ _ _ _
  successor_injective := by
    intro left right equal
    apply individualValueEquiv.injective
    apply ULift.ext
    have naturalEqual : (individualValueEquiv left).down + 1 =
        (individualValueEquiv right).down + 1 := by
      simpa using congrArg (fun value => (individualValueEquiv value).down) equal
    exact Nat.add_right_cancel naturalEqual
  omitted := individualValueEquiv.symm (ULift.up 0)
  omitted_not_image := by
    intro value equal
    have impossible : (individualValueEquiv value).down + 1 = 0 := by
      simpa using congrArg (fun value => (individualValueEquiv value).down) equal
    exact Nat.noConfusion impossible

theorem models_infinity :
    (standardModel initialOther (fun _ => natural.{w})).models
      (HOL.StandardAxiomProperties.infinityFormula individual) :=
  HOL.StandardAxiomProperties.models_infinityFormula _ _ infinityWitness

/-- No inhabited HOL family can realize an empty predicate subtype. -/
theorem empty_subtype_refused :
    ¬ ∃ domain : Domain.{w}, domain.Carrier =
      HOL.WitnessedTypeDefinition.Carrier (fun _ : ULift.{w + 1, 0} Nat => False) := by
  rintro ⟨domain, equal⟩
  have value : HOL.WitnessedTypeDefinition.Carrier
      (fun _ : ULift.{w + 1, 0} Nat => False) := equal ▸ domain.inhabitant
  exact value.property

end Controls

end Mettapedia.Languages.OpenTheory.TypeFamilySemantics
