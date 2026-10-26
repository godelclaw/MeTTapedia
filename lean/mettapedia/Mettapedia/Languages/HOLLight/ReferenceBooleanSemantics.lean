import Mettapedia.Languages.HOLLight.SourceProfileModels

/-!
# Boolean meanings retained by source-profile replay

The reference-schema invariant determines the meanings of the actual registered
Boolean symbols in every completed source-profile model. These meanings also
apply before a symbol is admitted; formation remains a separate checker judgment.
The term constructors below retain the source symbols and their definition
identities, rather than replacing them with primitive logical syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ReferenceBooleanSemantics

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open StandardTheoryInterpretation DefinitionHistorySchemas DefinitionSchemaSubstitution
open SourceProfileModels DefinitionModelFamily TypeFamilySemantics ModelInterpretation
open DefinitionAdapters

universe w

/-- The denotations of the registered source Boolean definitions. -/
structure Meanings (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) : Prop where
  truth : model.constDen Interpretation.Symbols.truth = ULift.up True
  conjunction : ∀ left right, model.constDen Interpretation.Symbols.conjunction left right =
    ULift.up (left.down ∧ right.down)
  implication : ∀ left right, model.constDen Interpretation.Symbols.implication left right =
    ULift.up (left.down → right.down)
  universal : ∀ operand predicate,
    model.constDen (Interpretation.Symbols.universal operand) predicate =
      ULift.up (∀ value, model.adm operand value → (predicate value).down)
  existential : ∀ operand predicate,
    model.constDen (Interpretation.Symbols.existential operand) predicate =
      ULift.up (∃ value, model.adm operand value ∧ (predicate value).down)
  falsity : model.constDen Interpretation.Symbols.falsity = ULift.up False
  negation : ∀ proposition, model.constDen Interpretation.Symbols.negation proposition =
    ULift.up (¬ proposition.down)

private theorem equality_at_truth : Source.truthContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.truthContext]
  exact (admitConstantInTheory_result Source.truthAdmitted).2.2.1.2 _ _ primitives.equalityRegistered

private theorem equality_at_conjunction : Source.conjunctionContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.conjunctionContext]
  exact (admitConstantInTheory_result Source.conjunctionAdmitted).2.2.1.2 _ _ equality_at_truth

private theorem equality_at_implication : Source.implicationContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.implicationContext]
  exact (admitConstantInTheory_result Source.implicationAdmitted).2.2.1.2 _ _ equality_at_conjunction

private theorem equality_at_universal : Source.universalContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.universalContext]
  exact (admitConstantInTheory_result Source.universalAdmitted).2.2.1.2 _ _ equality_at_implication

private theorem equality_at_existential : Source.existentialContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.existentialContext]
  exact (admitConstantInTheory_result Source.existentialAdmitted).2.2.1.2 _ _ equality_at_universal

private theorem equality_at_falsity : Source.falsityContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.falsityContext]
  exact (admitConstantInTheory_result Source.falsityAdmitted).2.2.1.2 _ _ equality_at_existential

/-- Recover all Boolean meanings from the preserved schemas, independently of
the order of subsequent proof and definition commands. -/
theorem meanings_of_invariant {initial context : TheoryContext}
    {theory : HOL.ClosedTheorySet Symbol} (family : Family.{w} initial context theory)
    (invariant : ReferenceInvariant family)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    Meanings (family.model other assignment) := by
  have definition (result : ContextConstantDefinitionResult)
      (known : result ∈ referenceHistory.records) (substitution : TypeSubst) :=
    invariant other assignment (constantSchema result)
      (List.mem_append_left _ (List.mem_map.mpr ⟨result,known,rfl⟩)) substitution
  have truth := Interpretation.truth_of_schema _ (family.fullDomains other assignment)
    primitives.equalityParameter primitives.equalityRegistered
    (definition Source.truthResult (by simp [referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
  have conjunction := Interpretation.conjunction_of_schema _ (family.fullDomains other assignment)
    primitives.equalityParameter equality_at_truth
    (definition Source.conjunctionResult (by simp [referenceHistory, DefinitionHistoryModels.ConstantHistory.records])) truth
  have implication := Interpretation.implication_of_schema _ (family.fullDomains other assignment)
    primitives.equalityParameter equality_at_conjunction
    (definition Source.implicationResult (by simp [referenceHistory, DefinitionHistoryModels.ConstantHistory.records])) conjunction
  have universal := Interpretation.universal_of_schema _ (family.fullDomains other assignment)
    primitives.equalityParameter equality_at_implication
    (definition Source.universalResult (by simp [referenceHistory, DefinitionHistoryModels.ConstantHistory.records])) truth
  have existential := Interpretation.existential_of_schema _ (family.fullDomains other assignment)
    primitives.equalityParameter equality_at_universal
    (definition Source.existentialResult (by simp [referenceHistory, DefinitionHistoryModels.ConstantHistory.records])) universal implication
  have falsity := Interpretation.falsity_of_schema _ (family.fullDomains other assignment)
    primitives.equalityParameter equality_at_existential
    (definition Source.falsityResult (by simp [referenceHistory, DefinitionHistoryModels.ConstantHistory.records])) universal
  have negation := Interpretation.negation_of_schema _ (family.fullDomains other assignment)
    primitives.equalityParameter equality_at_falsity
    (definition Source.negationResult (by simp [referenceHistory, DefinitionHistoryModels.ConstantHistory.records])) implication falsity
  exact ⟨truth,conjunction,implication,universal,existential,falsity,negation⟩

theorem replay_meanings (commands : List ProofExecution.Registered.Command)
    (after : ProofExecution.Registered.State)
    (accepted : ProofExecution.Registered.replayFrom policy
      (ProofExecution.Registered.empty SourceProfile.primitiveContext) commands = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    Meanings ((sourceReplayFrame commands after accepted).frame.model other assignment) :=
  meanings_of_invariant _ (sourceReplayFrame commands after accepted).invariant other assignment

set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.respectTransparency false in
theorem reference_extension_meanings (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) : Meanings (Interpretation.ontoModel model) := by
  refine ⟨Interpretation.ontoModel_truth model full,
    Interpretation.ontoModel_conjunction model full,
    Interpretation.ontoModel_implication model full,
    ?_, ?_,
    Interpretation.ontoModel_falsity model full,
    Interpretation.ontoModel_negation model full⟩
  · intro operand predicate
    rw [Interpretation.ontoModel_universal model full]
    apply ULift.ext
    apply propext
    constructor
    · intro valid value _
      exact valid value (full _ _)
    · intro valid value _
      exact valid value (Interpretation.ontoModel_fullDomains model full _ _)
  · intro operand predicate
    rw [Interpretation.ontoModel_existential model full]
    apply ULift.ext
    apply propext
    constructor
    · rintro ⟨value,_,holds⟩
      exact ⟨value,Interpretation.ontoModel_fullDomains model full _ _,holds⟩
    · rintro ⟨value,_,holds⟩
      exact ⟨value,full _ _,holds⟩

private theorem source_meanings_variable (result : ContextConstantDefinitionResult)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (source : SourceVar) {type : HOL.Ty AtomicTy} (typed : source.ty.toHOL = type) :
    ConstantAdmission.sourceMeanings result model (.variable source typed) =
      model.constDen (.variable source typed) := by
  unfold ConstantAdmission.sourceMeanings
  change model.denote (ConstantAdmission.sourceExpansion result (.variable source typed))
    (fun index => nomatch index) = _
  rw [ConstantAdmission.sourceExpansion_variable]
  rfl

private theorem standard_meanings_variable (result : ContextConstantDefinitionResult)
    (carrier : AtomicTy → Type (w+1))
    (meanings : ∀ {type}, Symbol type → HOL.Ty.denote.{0,w+1} carrier type)
    (source : SourceVar) {type : HOL.Ty AtomicTy} (typed : source.ty.toHOL = type) :
    ConstantAdmission.standardSourceMeanings result carrier meanings (.variable source typed) =
      meanings (.variable source typed) := by
  unfold ConstantAdmission.standardSourceMeanings
  exact source_meanings_variable _ _ _ _

theorem reference_extension_variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (source : SourceVar) {type : HOL.Ty AtomicTy} (typed : source.ty.toHOL = type) :
    (Interpretation.ontoModel model).constDen (.variable source typed) =
      model.constDen (.variable source typed) := by
  simp only [Interpretation.ontoModel, Interpretation.oneOneModel, Interpretation.negationModel,
    Interpretation.falsityModel, Interpretation.existentialModel, Interpretation.universalModel,
    Interpretation.implicationModel, Interpretation.conjunctionModel, Interpretation.truthModel,
    HOL.HenkinModel.standard, standard_meanings_variable, source_meanings_variable]

variable {context : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}

def conjunction (left right : HOL.Formula Symbol context) : HOL.Formula Symbol context :=
  .app (.app (.const Interpretation.Symbols.conjunction) left) right

def implication (left right : HOL.Formula Symbol context) : HOL.Formula Symbol context :=
  .app (.app (.const Interpretation.Symbols.implication) left) right

def universal (body : HOL.Formula Symbol (type :: context)) : HOL.Formula Symbol context :=
  .app (.const (Interpretation.Symbols.universal type)) (.lam body)

def existential (body : HOL.Formula Symbol (type :: context)) : HOL.Formula Symbol context :=
  .app (.const (Interpretation.Symbols.existential type)) (.lam body)

def negation (body : HOL.Formula Symbol context) : HOL.Formula Symbol context :=
  .app (.const Interpretation.Symbols.negation) body

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (meanings : Meanings model)
include meanings

theorem denote_conjunction (left right : HOL.Formula Symbol context) (valuation : model.Valuation context) :
    model.denote (conjunction left right) valuation =
      ULift.up ((model.denote left valuation).down ∧ (model.denote right valuation).down) :=
  meanings.conjunction _ _

theorem denote_implication (left right : HOL.Formula Symbol context) (valuation : model.Valuation context) :
    model.denote (implication left right) valuation =
      ULift.up ((model.denote left valuation).down → (model.denote right valuation).down) :=
  meanings.implication _ _

theorem denote_universal (body : HOL.Formula Symbol (type :: context)) (valuation : model.Valuation context) :
    model.denote (universal body) valuation = ULift.up
      (∀ value, model.adm type value → (model.denote body (model.extend valuation value)).down) :=
  meanings.universal _ _

theorem denote_existential (body : HOL.Formula Symbol (type :: context)) (valuation : model.Valuation context) :
    model.denote (existential body) valuation = ULift.up
      (∃ value, model.adm type value ∧ (model.denote body (model.extend valuation value)).down) :=
  meanings.existential _ _

theorem denote_negation (body : HOL.Formula Symbol context) (valuation : model.Valuation context) :
    model.denote (negation body) valuation = ULift.up (¬ (model.denote body valuation).down) :=
  meanings.negation _

#print axioms meanings_of_invariant

end Mettapedia.Languages.HOLLight.ReferenceBooleanSemantics
