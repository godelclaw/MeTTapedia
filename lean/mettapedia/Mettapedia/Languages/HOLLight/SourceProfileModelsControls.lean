import Mettapedia.Languages.HOLLight.SourceProfileModels
import Mettapedia.Languages.HOLLight.PrimitiveTransport

/-!
# Source-profile model controls

The registered reference prefix retains its nine equations and receipts.
Three further source axiom commands use exactly the selected commitments.
The constructed model validates their resulting cache; an unlisted sentence
and a changed axiom conclusion are refused. A finite individual carrier
cannot supply the concrete infinity witness used by the reference model.
All nine Boolean meanings are also recovered from their admitted schemas;
the pre-admission interpretation of truth separates the schema premise.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.SourceProfileModels.Controls
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics DefinitionAdapters ProofExecution Registered StandardTheoryInterpretation
open DefinitionHistorySchemas DefinitionSchemaSubstitution ModelInterpretation
universe w

def selected (index : Fin 3) : Sequent :=
  commitments.get ⟨index.val, by simp [commitments]⟩

private theorem axiom_available (index : Fin 3) :
    (checkAxiom (selected index)).isSome = true := by
  fin_cases index <;> decide +kernel

def axiomFact (index : Fin 3) : Theorem :=
  (checkAxiom (selected index)).get (axiom_available index)

def axiomCommand (index : Fin 3) : Command :=
  .proof ⟨axiomFact index, .axiom (selected index),
    [], ("profile-followup", index.val)⟩
    (ExportReplay.instanceCertificates referenceState.context.signature)

theorem reference_path : (Registered.gslt emptyAxiomPolicy).MultiStep
    (Registered.empty SourceProfile.primitiveContext) referenceState :=
  Registered.replayFrom_reachable emptyAxiomPolicy _ _ _ reference_replayed

def commands : List Command := [axiomCommand 0, axiomCommand 1, axiomCommand 2]

theorem commands_available : (replayFrom policy referenceState commands).isSome = true := by
  decide +kernel

def after : Registered.State := (replayFrom policy referenceState commands).get commands_available

theorem commands_replayed : replayFrom policy referenceState commands = some after :=
  (Option.some_get commands_available).symm

theorem retained_counts : referenceState.cache.size = 9 ∧ referenceState.receipts.size = 9 ∧
    after.cache.size = 12 ∧ after.receipts.size = 12 := by decide +kernel

theorem received_models (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    ∃ model : HOL.HenkinModel.{0,0,1} AtomicTy Symbol,
      model.FullDomains ∧ ∀ fact ∈ after.cache,
        ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
          ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, model.models hypothesis) → model.models formula) :=
  SourceProfileModels.replay_models commands after commands_replayed other assignment

def unlisted : Sequent := ⟨∅, Mettapedia.Languages.OpenTheory.falsity⟩

theorem unlisted_refused : (RuleRequest.axiom unlisted).check policy = none := by decide +kernel

def forgedFact : Theorem := { axiomFact 0 with sequent := unlisted }
def forgedCommand : Command :=
  .proof ⟨forgedFact, .axiom commitments[0], [], ("profile-forged", 0)⟩
    (ExportReplay.instanceCertificates referenceState.context.signature)

theorem changed_conclusion_refused : Registered.apply policy referenceState forgedCommand = none := by
  decide +kernel

def falseFact : Theorem := Theorem.emptyResult ∅ Mettapedia.Languages.OpenTheory.falsity

theorem reference_falsity_refused (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    falseFact ∉ referenceCache :=
  (referenceFrame.{0}).cached_falsity_refused other assignment falseFact rfl PrimitiveSentences.falsityDB_translates

def finiteDomain : Domain.{0} := ⟨ULift.{1,0} Unit, .up ()⟩
noncomputable def finiteModel : HOL.HenkinModel.{0,0,1} AtomicTy Symbol :=
  ModelInstanceCoherence.initialModel (fun _ _ => finiteDomain) (fun _ => finiteDomain)

theorem finite_carrier : finiteModel.Carrier SourceProfile.individualBase = ULift.{1,0} Unit := by
  simp [finiteModel, ModelInstanceCoherence.initialModel, ModelInterpretation.model,
    TypeFamilySemantics.model, HOL.HenkinModel.standard, atomicCarrier,
    SourceProfile.individualBase, SourceProfile.individualOperator, primitiveFamilies,
    TypeOp.bool, TypeOp.function, TypeOp.same, Name.global, finiteDomain]

theorem finite_infinity_refused : ¬ finiteModel.HasDedekindInfiniteBase SourceProfile.individualBase := by
  let _ : Finite (finiteModel.Carrier SourceProfile.individualBase) :=
    Finite.of_equiv (ULift.{1,0} Unit) (Equiv.cast finite_carrier).symm
  exact HOL.HenkinModel.not_hasDedekindInfiniteBase_of_finite _ _

theorem chronological_reference_model :
    referenceHistory.extendModel (initialFamily.model TypeFamilySemantics.Controls.initialOther
      (fun _ => TypeFamilySemantics.Controls.natural.{0})) =
      Interpretation.ontoModel (initialFamily.model TypeFamilySemantics.Controls.initialOther
        (fun _ => TypeFamilySemantics.Controls.natural.{0})) :=
  referenceHistory_model _ (initialFamily.fullDomains TypeFamilySemantics.Controls.initialOther
    (fun _ => TypeFamilySemantics.Controls.natural.{0}))

theorem reference_eta_model (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    (referenceCore.model other assignment).models (Raw.etaAxiom .prop .prop) :=
  reference_models_eta other assignment _ _

theorem reference_selection_model (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    (referenceCore.model other assignment).models (Raw.selectionAxiom .prop) := by
  simpa only [Ty.toHOL_bool] using reference_models_selection other assignment Ty.bool

theorem reference_infinity_model (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    (referenceCore.model other assignment).models Raw.infinityAxiom :=
  reference_models_infinity other assignment

private theorem reference_instance (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {before : TheoryContext} {instances : SignatureFormation.InstanceWitnesses} {name : Name}
    {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory before instances name source = some result)
    (known : result.output.definitionTheorem ∈ referenceCache) (substitution : TypeSubst) :
    (referenceCore.model other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (constantSchema result)) :=
  referenceBaseFrame.cached_constant_schema_instance primitives accepted known other assignment substitution

private theorem equality_at_truth : Source.truthContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.truthContext]
  exact (admitConstantInTheory_result Source.truthAdmitted).2.2.1.2 _ _ primitives.equalityRegistered

private theorem equality_at_conjunction : Source.conjunctionContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.conjunctionContext]
  exact (admitConstantInTheory_result Source.conjunctionAdmitted).2.2.1.2 _ _ (by
    simpa only [Source.truthContext] using equality_at_truth)

private theorem equality_at_implication : Source.implicationContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.implicationContext]
  exact (admitConstantInTheory_result Source.implicationAdmitted).2.2.1.2 _ _ (by
    simpa only [Source.conjunctionContext] using equality_at_conjunction)

private theorem equality_at_universal : Source.universalContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.universalContext]
  exact (admitConstantInTheory_result Source.universalAdmitted).2.2.1.2 _ _ (by
    simpa only [Source.implicationContext] using equality_at_implication)

private theorem equality_at_existential : Source.existentialContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.existentialContext]
  exact (admitConstantInTheory_result Source.existentialAdmitted).2.2.1.2 _ _ (by
    simpa only [Source.universalContext] using equality_at_universal)

private theorem equality_at_falsity : Source.falsityContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.falsityContext]
  exact (admitConstantInTheory_result Source.falsityAdmitted).2.2.1.2 _ _ (by
    simpa only [Source.existentialContext] using equality_at_existential)

private theorem equality_at_negation : Source.negationContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.negationContext]
  exact (admitConstantInTheory_result Source.negationAdmitted).2.2.1.2 _ _ (by
    simpa only [Source.falsityContext] using equality_at_falsity)

private theorem equality_at_oneOne : Source.oneOneContext.signature.constants Const.equality =
    some (Ty.equality (.var primitives.equalityParameter)) := by
  rw [Source.oneOneContext]
  exact (admitConstantInTheory_result Source.oneOneAdmitted).2.2.1.2 _ _ (by
    simpa only [Source.negationContext] using equality_at_negation)

theorem reference_truth_from_schema (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    : (referenceCore.model other assignment).constDen Interpretation.Symbols.truth = ULift.up True := by
  apply Interpretation.truth_of_schema _ (referenceCore.fullDomains other assignment)
    primitives.equalityParameter primitives.equalityRegistered
    (reference_instance other assignment Source.truthAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))

theorem reference_conjunction_from_schema (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (left right : HOL.Ty.denote.{0,w+1} (referenceCore.model other assignment).Carrier .prop)
    : (referenceCore.model other assignment).constDen Interpretation.Symbols.conjunction left right = ULift.up (left.down ∧ right.down) := by
  apply Interpretation.conjunction_of_schema _ (referenceCore.fullDomains other assignment)
    primitives.equalityParameter equality_at_truth
    (reference_instance other assignment Source.conjunctionAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_truth_from_schema other assignment)

theorem reference_implication_from_schema (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (left right : HOL.Ty.denote.{0,w+1} (referenceCore.model other assignment).Carrier .prop)
    : (referenceCore.model other assignment).constDen Interpretation.Symbols.implication left right = ULift.up (left.down → right.down) := by
  apply Interpretation.implication_of_schema _ (referenceCore.fullDomains other assignment)
    primitives.equalityParameter equality_at_conjunction
    (reference_instance other assignment Source.implicationAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_conjunction_from_schema other assignment)

theorem reference_universal_from_schema (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (operand : HOL.Ty AtomicTy)
    (predicate : HOL.Ty.denote.{0,w+1} (referenceCore.model other assignment).Carrier (operand.arr .prop))
    : (referenceCore.model other assignment).constDen (Interpretation.Symbols.universal operand) predicate =
      ULift.up (∀ value, (referenceCore.model other assignment).adm operand value → (predicate value).down) := by
  apply Interpretation.universal_of_schema _ (referenceCore.fullDomains other assignment)
    primitives.equalityParameter equality_at_implication
    (reference_instance other assignment Source.universalAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_truth_from_schema other assignment)

theorem reference_existential_from_schema (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (operand : HOL.Ty AtomicTy)
    (predicate : HOL.Ty.denote.{0,w+1} (referenceCore.model other assignment).Carrier (operand.arr .prop))
    : (referenceCore.model other assignment).constDen (Interpretation.Symbols.existential operand) predicate =
      ULift.up (∃ value, (referenceCore.model other assignment).adm operand value ∧ (predicate value).down) := by
  apply Interpretation.existential_of_schema _ (referenceCore.fullDomains other assignment)
    primitives.equalityParameter equality_at_universal
    (reference_instance other assignment Source.existentialAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_universal_from_schema other assignment)
    (reference_implication_from_schema other assignment)

theorem reference_falsity_from_schema (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    : (referenceCore.model other assignment).constDen Interpretation.Symbols.falsity = ULift.up False := by
  apply Interpretation.falsity_of_schema _ (referenceCore.fullDomains other assignment)
    primitives.equalityParameter equality_at_existential
    (reference_instance other assignment Source.falsityAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_universal_from_schema other assignment)

theorem reference_negation_from_schema (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (proposition : HOL.Ty.denote.{0,w+1} (referenceCore.model other assignment).Carrier .prop)
    : (referenceCore.model other assignment).constDen Interpretation.Symbols.negation proposition = ULift.up (¬ proposition.down) := by
  apply Interpretation.negation_of_schema _ (referenceCore.fullDomains other assignment)
    primitives.equalityParameter equality_at_falsity
    (reference_instance other assignment Source.negationAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_implication_from_schema other assignment)
    (reference_falsity_from_schema other assignment)

theorem reference_oneOne_from_schema (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (domain codomain : HOL.Ty AtomicTy)
    (function : HOL.Ty.denote.{0,w+1} (referenceCore.model other assignment).Carrier (domain.arr codomain))
    : (referenceCore.model other assignment).constDen (Interpretation.Symbols.oneOne domain codomain) function =
      ULift.up (Function.Injective function) := by
  apply Interpretation.oneOne_of_schema _ (referenceCore.fullDomains other assignment)
    primitives.equalityParameter equality_at_negation
    (reference_instance other assignment Source.oneOneAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_universal_from_schema other assignment)
    (reference_implication_from_schema other assignment)

theorem reference_onto_from_schema (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (domain codomain : HOL.Ty AtomicTy)
    (function : HOL.Ty.denote.{0,w+1} (referenceCore.model other assignment).Carrier (domain.arr codomain))
    : (referenceCore.model other assignment).constDen (Interpretation.Symbols.onto domain codomain) function =
      ULift.up (Function.Surjective function) := by
  apply Interpretation.onto_of_schema _ (referenceCore.fullDomains other assignment)
    primitives.equalityParameter equality_at_oneOne
    (reference_instance other assignment Source.ontoAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_universal_from_schema other assignment)
    (reference_existential_from_schema other assignment)

theorem uninstalled_truth_false (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (initialFamily.model other assignment).constDen Interpretation.Symbols.truth = ULift.up False := by
  have different : Source.truthConstant ≠ ModelInterpretation.selectionConstant := by
    intro equal
    cases (Const.mk.inj equal).2
  change ModelInterpretation.interpretation
    (extend other SourceProfile.individualOperator (fun _ => individualDomain)) assignment
    (ModelInstanceCoherence.domainMeanings _ _) Interpretation.Symbols.truth = _
  simp only [Interpretation.Symbols.truth, ModelInterpretation.interpretation]
  split
  · have value := ModelInstanceCoherence.sourceDefault_inhabitant
      (extend other SourceProfile.individualOperator (fun _ => individualDomain)) assignment .prop
    rw [show Ty.fromHOL .prop = Ty.bool from rfl, evaluate_bool] at value
    exact eq_of_heq value
  · rename_i operand recognized
    exact False.elim (different ((ModelInterpretation.selectionOperand?_eq_some_iff _ _ _).mp recognized).1)

theorem uninstalled_truth_schema_refused (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ¬ (∀ substitution : TypeSubst, (initialFamily.model other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (constantSchema Source.truthResult))) := by
  intro holds
  have meaning := Interpretation.truth_of_schema _ (initialFamily.fullDomains other assignment)
    primitives.equalityParameter primitives.equalityRegistered holds
  rw [uninstalled_truth_false] at meaning
  have impossible : False = True := congrArg ULift.down meaning
  exact impossible.symm ▸ True.intro

theorem closed_truth_from_schema
    : (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).constDen Interpretation.Symbols.truth = ULift.up True := by
  apply Interpretation.truth_of_schema _ (referenceCore.fullDomains TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    primitives.equalityParameter primitives.equalityRegistered
    (reference_instance TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}) Source.truthAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))

theorem closed_conjunction_from_schema
    (left right : HOL.Ty.denote.{0,1} (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).Carrier .prop)
    : (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).constDen Interpretation.Symbols.conjunction left right = ULift.up (left.down ∧ right.down) := by
  apply Interpretation.conjunction_of_schema _ (referenceCore.fullDomains TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    primitives.equalityParameter equality_at_truth
    (reference_instance TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}) Source.conjunctionAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_truth_from_schema TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))

theorem closed_implication_from_schema
    (left right : HOL.Ty.denote.{0,1} (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).Carrier .prop)
    : (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).constDen Interpretation.Symbols.implication left right = ULift.up (left.down → right.down) := by
  apply Interpretation.implication_of_schema _ (referenceCore.fullDomains TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    primitives.equalityParameter equality_at_conjunction
    (reference_instance TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}) Source.implicationAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_conjunction_from_schema TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))

theorem closed_universal_from_schema
    (operand : HOL.Ty AtomicTy)
    (predicate : HOL.Ty.denote.{0,1} (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).Carrier (operand.arr .prop))
    : (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).constDen (Interpretation.Symbols.universal operand) predicate =
      ULift.up (∀ value, (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).adm operand value → (predicate value).down) := by
  apply Interpretation.universal_of_schema _ (referenceCore.fullDomains TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    primitives.equalityParameter equality_at_implication
    (reference_instance TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}) Source.universalAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_truth_from_schema TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))

theorem closed_existential_from_schema
    (operand : HOL.Ty AtomicTy)
    (predicate : HOL.Ty.denote.{0,1} (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).Carrier (operand.arr .prop))
    : (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).constDen (Interpretation.Symbols.existential operand) predicate =
      ULift.up (∃ value, (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).adm operand value ∧ (predicate value).down) := by
  apply Interpretation.existential_of_schema _ (referenceCore.fullDomains TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    primitives.equalityParameter equality_at_universal
    (reference_instance TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}) Source.existentialAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_universal_from_schema TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    (reference_implication_from_schema TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))

theorem closed_falsity_from_schema
    : (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).constDen Interpretation.Symbols.falsity = ULift.up False := by
  apply Interpretation.falsity_of_schema _ (referenceCore.fullDomains TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    primitives.equalityParameter equality_at_existential
    (reference_instance TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}) Source.falsityAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_universal_from_schema TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))

theorem closed_negation_from_schema
    (proposition : HOL.Ty.denote.{0,1} (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).Carrier .prop)
    : (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).constDen Interpretation.Symbols.negation proposition = ULift.up (¬ proposition.down) := by
  apply Interpretation.negation_of_schema _ (referenceCore.fullDomains TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    primitives.equalityParameter equality_at_falsity
    (reference_instance TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}) Source.negationAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_implication_from_schema TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    (reference_falsity_from_schema TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))

theorem closed_oneOne_from_schema
    (domain codomain : HOL.Ty AtomicTy)
    (function : HOL.Ty.denote.{0,1} (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).Carrier (domain.arr codomain))
    : (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).constDen (Interpretation.Symbols.oneOne domain codomain) function =
      ULift.up (Function.Injective function) := by
  apply Interpretation.oneOne_of_schema _ (referenceCore.fullDomains TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    primitives.equalityParameter equality_at_negation
    (reference_instance TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}) Source.oneOneAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_universal_from_schema TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    (reference_implication_from_schema TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))

theorem closed_onto_from_schema
    (domain codomain : HOL.Ty AtomicTy)
    (function : HOL.Ty.denote.{0,1} (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).Carrier (domain.arr codomain))
    : (referenceCore.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).constDen (Interpretation.Symbols.onto domain codomain) function =
      ULift.up (Function.Surjective function) := by
  apply Interpretation.onto_of_schema _ (referenceCore.fullDomains TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    primitives.equalityParameter equality_at_oneOne
    (reference_instance TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}) Source.ontoAdmitted (by
      simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]))
    (reference_universal_from_schema TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    (reference_existential_from_schema TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))

theorem closed_eta_via_meanings :
    (Interpretation.ontoModel (initialFamily.model TypeFamilySemantics.Controls.initialOther
      (fun _ => TypeFamilySemantics.Controls.natural.{0}))).models (Raw.etaAxiom .prop .prop) :=
  Interpretation.ontoModel_models_eta _ (initialFamily.fullDomains _ _) _ _

theorem closed_selection_via_meanings :
    (Interpretation.ontoModel (initialFamily.model TypeFamilySemantics.Controls.initialOther
      (fun _ => TypeFamilySemantics.Controls.natural.{0}))).models (Raw.selectionAxiom .prop) := by
  simpa only [Ty.toHOL_bool] using Interpretation.ontoModel_models_selection
    (initialFamily.model TypeFamilySemantics.Controls.initialOther
      (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    (initialFamily.fullDomains _ _) Ty.bool
    (ModelInstanceCoherence.initialModel_models_selection _ _ _)

theorem closed_infinity_via_meanings :
    (Interpretation.ontoModel (initialFamily.model TypeFamilySemantics.Controls.initialOther
      (fun _ => TypeFamilySemantics.Controls.natural.{0}))).models Raw.infinityAxiom :=
  Interpretation.ontoModel_models_infinity _ (initialFamily.fullDomains _ _) (initialInfinity _ _)

theorem closed_truth_instance_image :
    HOL.mapTypes TypeSubst.empty.baseInstance TypeSubst.empty.symbolInstance
      (constantSchema Source.truthResult) = constantInstanceSchema Source.truthResult TypeSubst.empty :=
  constantSchema_type_image Source.truthAdmitted primitives.equalityParameter
    primitives.equalityRegistered TypeSubst.empty

theorem closed_truth_instance_value :
    (referenceCore.model TypeFamilySemantics.Controls.initialOther
      (fun _ => TypeFamilySemantics.Controls.natural.{0})).constDen
        (.constant Source.truthResult.output.constant (TypeSubst.empty.apply Source.truthResult.definition.ty) rfl) =
      (referenceCore.model TypeFamilySemantics.Controls.initialOther
        (fun _ => TypeFamilySemantics.Controls.natural.{0})).denote
        (ModelInterpretation.ConstantAdmission.instanceBody Source.truthResult TypeSubst.empty) (fun v => nomatch v) := by
  exact constant_value_of_schema Source.truthAdmitted primitives.equalityParameter primitives.equalityRegistered
    _ (referenceCore.fullDomains _ _) TypeSubst.empty
    (reference_instance TypeFamilySemantics.Controls.initialOther
      (fun _ => TypeFamilySemantics.Controls.natural.{0}) Source.truthAdmitted
      (by simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]) TypeSubst.empty)

theorem closed_truth_source_meaning :
    (referenceCore.model TypeFamilySemantics.Controls.initialOther
      (fun _ => TypeFamilySemantics.Controls.natural.{0})).constDen Interpretation.Symbols.truth =
      (referenceCore.model TypeFamilySemantics.Controls.initialOther
        (fun _ => TypeFamilySemantics.Controls.natural.{0})).denote Raw.truth (fun v => nomatch v) := by
  unfold Interpretation.Symbols.truth
  rw [← Source.truthIdentity]
  exact constant_meaning_of_source Source.truthAdmitted primitives.equalityParameter primitives.equalityRegistered
    _ (referenceCore.fullDomains _ _) TypeSubst.empty
    (reference_instance TypeFamilySemantics.Controls.initialOther
      (fun _ => TypeFamilySemantics.Controls.natural.{0}) Source.truthAdmitted
      (by simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]) TypeSubst.empty)
    Ty.bool (by simp) (by simp [Source.truthType, Source.truthSchema]) (Raw.truth_translated TypeSubst.empty)

theorem installed_truth_unchanged (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ModelInterpretation.ConstantAdmission.sourceExtension Source.truthResult (referenceCore.model other assignment) =
      referenceCore.model other assignment := by
  apply constant_extension_eq_of_schema Source.truthAdmitted primitives.equalityParameter
    primitives.equalityRegistered _ (referenceCore.fullDomains other assignment)
  exact referenceBaseFrame.cached_constant_schema_instance primitives Source.truthAdmitted
    (by simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]) other assignment

theorem closed_installed_truth_unchanged :
    ModelInterpretation.ConstantAdmission.sourceExtension Source.truthResult
      (referenceCore.model TypeFamilySemantics.Controls.initialOther
        (fun _ => TypeFamilySemantics.Controls.natural.{0})) =
      referenceCore.model TypeFamilySemantics.Controls.initialOther
        (fun _ => TypeFamilySemantics.Controls.natural.{0}) := by
  apply constant_extension_eq_of_schema Source.truthAdmitted primitives.equalityParameter
    primitives.equalityRegistered _ (referenceCore.fullDomains _ _)
  exact referenceBaseFrame.cached_constant_schema_instance primitives Source.truthAdmitted
    (by simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]) _ _

theorem closed_polymorphic_repeat :
    ModelInterpretation.ConstantAdmission.sourceExtension Source.universalResult
      (ModelInterpretation.ConstantAdmission.sourceExtension Source.universalResult
        (initialFamily.model TypeFamilySemantics.Controls.initialOther
          (fun _ => TypeFamilySemantics.Controls.natural.{0}))) =
      ModelInterpretation.ConstantAdmission.sourceExtension Source.universalResult
        (initialFamily.model TypeFamilySemantics.Controls.initialOther
          (fun _ => TypeFamilySemantics.Controls.natural.{0})) :=
  constant_extension_idempotent Source.universalAdmitted _

theorem uninstalled_truth_changes_model (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ModelInterpretation.ConstantAdmission.sourceExtension Source.truthResult (initialFamily.model other assignment) ≠
      initialFamily.model other assignment := by
  intro same
  have installed := Interpretation.truth_extension _ (initialFamily.fullDomains other assignment)
  rw [same, uninstalled_truth_false, Interpretation.raw_truth_denote] at installed
  have impossible : False = True := congrArg ULift.down installed
  exact impossible.symm ▸ True.intro

theorem earlier_identity_unchanged_after_alias :
    DefinitionHistoryModels.Controls.identityHistory.extendModel
      (DefinitionHistoryModels.Controls.twoDefinitions.extendModel ModelInterpretation.Controls.initialModel.{0}) =
      DefinitionHistoryModels.Controls.twoDefinitions.extendModel ModelInterpretation.Controls.initialModel.{0} := by
  apply constant_history_absorbs _ _ _ _ ModelInterpretation.Controls.initialModel_fullDomains
  intro result member
  simpa only [DefinitionHistoryModels.ConstantHistory.records,
    DefinitionHistoryModels.Controls.identityHistory,
    DefinitionHistoryModels.Controls.twoDefinitions] using List.mem_append_left
      [DefinitionHistoryModels.Controls.aliasResult] member

theorem truth_identity_extensions_commute :
    ConstantAdmission.sourceExtension Source.truthResult
      (ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.identityResult ModelInterpretation.Controls.initialModel.{0}) =
    ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.identityResult
      (ConstantAdmission.sourceExtension Source.truthResult ModelInterpretation.Controls.initialModel.{0}) := by
  apply independent_constant_extensions_commute Source.truthAdmitted DefinitionHistoryModels.Controls.identity_admitted
  · intro same
    have test := (Const.same_eq_true_iff _ _).mpr same
    have unequal : Source.truthResult.output.constant.same DefinitionHistoryModels.Controls.identityResult.output.constant = false := by
      decide +kernel
    rw [unequal] at test
    cases test
  · exact (SignatureFormation.AnnotationsFormed.omits_unregistered
      (Option.isNone_iff_eq_none.mp (by decide +kernel :
        (SourceProfile.primitiveContext.signature.constants DefinitionHistoryModels.Controls.identityResult.output.constant).isNone = true)))
      (SignatureFormation.checkSource_sound _ _ (admitConstantInTheory_result Source.truthAdmitted).1).2
  · exact (SignatureFormation.AnnotationsFormed.omits_unregistered
      (Option.isNone_iff_eq_none.mp (by decide +kernel :
        (ContextControls.baseContext.signature.constants Source.truthResult.output.constant).isNone = true)))
      (SignatureFormation.checkSource_sound _ _ (admitConstantInTheory_result DefinitionHistoryModels.Controls.identity_admitted).1).2

theorem dependent_alias_not_independent :
    ¬ DefinitionHistoryModels.Controls.aliasResult.definition.term.OmitsConstant
      DefinitionHistoryModels.Controls.identityResult.output.constant := by
  have sourceChecked := (SignatureFormation.checkSource_sound _ _
    (admitConstantInTheory_result DefinitionHistoryModels.Controls.alias_admitted).1).1
  have shape := (SourceTerm.check_eq_some_iff _ _).mp sourceChecked
  rw [← shape]
  simp only [DefinitionHistoryModels.Controls.aliasBody, SourceTerm.toDB, DBTerm.OmitsConstant]
  exact fun different => different rfl

def identityBoolean : Symbol (.arr .prop .prop) :=
  .constant DefinitionHistoryModels.Controls.identityResult.output.constant (.function Ty.bool Ty.bool) (by simp)
def aliasBoolean : Symbol (.arr .prop .prop) :=
  .constant DefinitionHistoryModels.Controls.aliasResult.output.constant (.function Ty.bool Ty.bool) (by simp)

private theorem identity_definition_type : DefinitionHistoryModels.Controls.identityResult.definition.ty =
    Ty.function Ty.bool Ty.bool := by
  have checked := (SignatureFormation.checkSource_sound _ _
    (admitConstantInTheory_result DefinitionHistoryModels.Controls.identity_admitted).1).1
  have same := Option.some.inj (checked.symm.trans DefinitionAdapters.Controls.identitySource_checked)
  exact congrArg CanonicalTerm.ty same

private theorem alias_definition_type : DefinitionHistoryModels.Controls.aliasResult.definition.ty =
    Ty.function Ty.bool Ty.bool := by
  have checked := (SignatureFormation.checkSource_sound _ _
    (admitConstantInTheory_result DefinitionHistoryModels.Controls.alias_admitted).1).1
  have shape := (SourceTerm.check_eq_some_iff _ _).mp checked
  have inferred := DefinitionHistoryModels.Controls.aliasResult.definition.checked
  rw [← shape] at inferred
  simp only [DefinitionHistoryModels.Controls.aliasBody, SourceTerm.toDB, DBTerm.inferType] at inferred
  exact (Option.some.inj inferred).symm.trans identity_definition_type

private theorem identity_not_equality :
    DefinitionHistoryModels.Controls.identityResult.output.constant ≠ Const.equality := by
  rw [(ConstantAdmission.source_equation DefinitionHistoryModels.Controls.identity_admitted).1]
  intro same
  cases (Const.mk.inj same).2

theorem alias_extension_value (model : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) (full : model.FullDomains) :
    (ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.aliasResult model).constDen aliasBoolean =
      model.constDen identityBoolean := by
  exact ConstantAdmission.sourceExtension_constant_translates
    (type := .arr .prop .prop) (target := .const identityBoolean) DefinitionHistoryModels.Controls.alias_admitted
    model full TypeSubst.empty (.function Ty.bool Ty.bool) (by simp) (by rw [TypeSubst.apply_empty, alias_definition_type]) (by
      simp only [DefinitionHistoryModels.Controls.aliasBody, SourceTerm.toDB,
        TermSubst.applyDB_const, TypeSubst.apply_empty,
        identity_definition_type]
      exact Translates.constant (by simp [equalityOperand?, Const.same_eq_true_iff, identity_not_equality]) (by simp))

theorem identity_extension_false (model : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) (full : model.FullDomains) :
    (ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.identityResult model).constDen identityBoolean
      (ULift.up False) = ULift.up False := by
  have expanded :
      (ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.identityResult model).constDen identityBoolean =
        model.denote (.lam (.var .vz) : HOL.ClosedTerm Symbol (.arr .prop .prop)) (fun v => nomatch v) := by
    exact ConstantAdmission.sourceExtension_constant_translates DefinitionHistoryModels.Controls.identity_admitted
      model full TypeSubst.empty (.function Ty.bool Ty.bool) (by simp) (by rw [TypeSubst.apply_empty, identity_definition_type]) (by
        rw [(SourceTerm.check_eq_some_iff _ _).mp DefinitionAdapters.Controls.identitySource_checked]
        simp only [DefinitionAdapters.Controls.identityTerm, TermSubst.typeInstance_identity]
        exact Translates.abs (by simp) (Translates.bound .vz))
  exact congrFun expanded (ULift.up False)

private theorem initial_identity_false :
    ModelInterpretation.Controls.initialModel.{0}.constDen identityBoolean (ULift.up False) = ULift.up True := by
  have different : DefinitionHistoryModels.Controls.identityResult.output.constant ≠ selectionConstant := by
    rw [(ConstantAdmission.source_equation DefinitionHistoryModels.Controls.identity_admitted).1]
    intro same
    cases (Const.mk.inj same).2
  have ordinary : ModelInterpretation.Controls.initialModel.{0}.constDen identityBoolean =
      (fun _ : ULift.{1,0} Prop => ULift.up True) := by
    change interpretation TypeFamilySemantics.Controls.initialOther
      (fun _ => TypeFamilySemantics.Controls.natural.{0}) (pointedMeanings _ _) identityBoolean = _
    simp only [identityBoolean, interpretation]
    split
    · simp only [pointedMeanings, HOL.HenkinModel.defaultValue]
      funext value
      rfl
    · rename_i operand recognized
      exact False.elim (different ((selectionOperand?_eq_some_iff _ _ _).mp recognized).1)
  exact congrFun ordinary (ULift.up False)

theorem dependent_extensions_do_not_commute :
    ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.identityResult
      (ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.aliasResult ModelInterpretation.Controls.initialModel.{0}) ≠
    ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.aliasResult
      (ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.identityResult ModelInterpretation.Controls.initialModel.{0}) := by
  have different : DefinitionHistoryModels.Controls.aliasResult.output.constant ≠
      DefinitionHistoryModels.Controls.identityResult.output.constant := by
    intro same
    have test := (Const.same_eq_true_iff _ _).mpr same
    have unequal : DefinitionHistoryModels.Controls.aliasResult.output.constant.same
        DefinitionHistoryModels.Controls.identityResult.output.constant = false := by decide +kernel
    rw [unequal] at test
    cases test
  have left :
      (ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.identityResult
        (ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.aliasResult ModelInterpretation.Controls.initialModel.{0})).constDen
          aliasBoolean (ULift.up False) = ULift.up True := by
    have kept := ConstantAdmission.sourceExtension_constant_other DefinitionHistoryModels.Controls.identityResult
      (ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.aliasResult ModelInterpretation.Controls.initialModel.{0})
      _ (.function Ty.bool Ty.bool) (type := .arr .prop .prop) (by simp) different
    exact (congrFun kept (ULift.up False)).trans
      ((congrFun (alias_extension_value _ ModelInterpretation.Controls.initialModel_fullDomains) (ULift.up False)).trans initial_identity_false)
  have right :
      (ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.aliasResult
        (ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.identityResult ModelInterpretation.Controls.initialModel.{0})).constDen
          aliasBoolean (ULift.up False) = ULift.up False :=
    (congrFun (alias_extension_value _ (ConstantAdmission.sourceExtension_fullDomains _ _
      ModelInterpretation.Controls.initialModel_fullDomains)) (ULift.up False)).trans
      (identity_extension_false _ ModelInterpretation.Controls.initialModel_fullDomains)
  intro same
  have values := congrArg (fun candidate : HOL.HenkinModel.{0,0,1} AtomicTy Symbol =>
    candidate.constDen aliasBoolean (ULift.up False)) same
  rw [left, right] at values
  have impossible : True = False := congrArg ULift.down values
  exact impossible ▸ True.intro

theorem premature_alias_refused :
    admitConstantInTheory ContextControls.baseContext ContextControls.certificates (Name.global "alias")
      DefinitionHistoryModels.Controls.aliasBody = none := by decide +kernel

theorem closed_reference_history_repeat :
    StandardTheoryInterpretation.referenceHistory.extendModel
      (StandardTheoryInterpretation.referenceHistory.extendModel
        (initialFamily.model TypeFamilySemantics.Controls.initialOther
          (fun _ => TypeFamilySemantics.Controls.natural.{0}))) =
      StandardTheoryInterpretation.referenceHistory.extendModel
        (initialFamily.model TypeFamilySemantics.Controls.initialOther
          (fun _ => TypeFamilySemantics.Controls.natural.{0})) :=
  constant_history_idempotent _ _ (initialFamily.fullDomains _ _)

theorem expanded_identity_available :
    (admitConstantInTheory SourceProfile.primitiveContext
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature) (Name.global "identity")
      DefinitionAdapters.Controls.identitySource).isSome = true := by decide +kernel

def expandedIdentity : ContextConstantDefinitionResult :=
  (admitConstantInTheory SourceProfile.primitiveContext
    (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature) (Name.global "identity")
    DefinitionAdapters.Controls.identitySource).get expanded_identity_available

theorem expanded_identity_admitted :
    admitConstantInTheory SourceProfile.primitiveContext
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature) (Name.global "identity")
      DefinitionAdapters.Controls.identitySource = some expandedIdentity :=
  (Option.some_get expanded_identity_available).symm

theorem expanded_truth_available :
    (admitConstantInTheory expandedIdentity.context
      (ExportReplay.instanceCertificates expandedIdentity.context.signature) (Name.global "T") Source.truthBody).isSome = true := by
  decide +kernel

def expandedTruth : ContextConstantDefinitionResult :=
  (admitConstantInTheory expandedIdentity.context
    (ExportReplay.instanceCertificates expandedIdentity.context.signature) (Name.global "T") Source.truthBody).get expanded_truth_available

theorem expanded_truth_admitted :
    admitConstantInTheory expandedIdentity.context
      (ExportReplay.instanceCertificates expandedIdentity.context.signature) (Name.global "T") Source.truthBody = some expandedTruth :=
  (Option.some_get expanded_truth_available).symm

theorem different_initial_contexts : ContextControls.baseContext ≠ SourceProfile.primitiveContext := by
  intro same
  have absent : ContextControls.baseContext.signature.typeOperators SourceProfile.individualOperator = none := by decide +kernel
  have registered := individual_registered
  have compared := congrArg (fun context : TheoryContext => context.signature.typeOperators SourceProfile.individualOperator) same
  rw [absent, registered] at compared
  cases compared

theorem identity_payload_across_contexts :
    DefinitionHistoryModels.Controls.identityResult.definition = expandedIdentity.definition ∧
      DefinitionHistoryModels.Controls.identityResult.output = expandedIdentity.output :=
  admitConstantInTheory_payload_eq DefinitionHistoryModels.Controls.identity_admitted expanded_identity_admitted

theorem expanded_truth_schema_from_cached_source (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (substitution : TypeSubst) : (referenceCore.model other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (constantSchema expandedTruth)) := by
  exact referenceBaseFrame.cached_source_definition_instance primitives expanded_truth_admitted Source.truthAdmitted
    (by simp [referenceCache, referenceHistory, DefinitionHistoryModels.ConstantHistory.records]) other assignment substitution

theorem alternate_truth_available :
    (admitConstantInTheory SourceProfile.primitiveContext
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature) (Name.global "T")
      DefinitionAdapters.Controls.identitySource).isSome = true := by decide +kernel

def alternateTruth : ContextConstantDefinitionResult :=
  (admitConstantInTheory SourceProfile.primitiveContext
    (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature) (Name.global "T")
    DefinitionAdapters.Controls.identitySource).get alternate_truth_available

theorem alternate_truth_admitted :
    admitConstantInTheory SourceProfile.primitiveContext
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature) (Name.global "T")
      DefinitionAdapters.Controls.identitySource = some alternateTruth :=
  (Option.some_get alternate_truth_available).symm

theorem alternate_truth_same_name :
    constantName Source.truthResult.output.constant = constantName alternateTruth.output.constant := by
  rw [(ModelInterpretation.ConstantAdmission.source_equation Source.truthAdmitted).1,
    (ModelInterpretation.ConstantAdmission.source_equation alternate_truth_admitted).1]
  rfl

theorem alternate_truth_different_payload : Source.truthResult.output ≠ alternateTruth.output := by
  intro same
  have named := congrArg ConstantDefinitionResult.constant same
  have recognized := (Const.same_eq_true_iff _ _).mpr named
  have different : Source.truthResult.output.constant.same alternateTruth.output.constant = false := by decide +kernel
  rw [different] at recognized
  cases recognized

theorem identity_schema_across_contexts :
    constantSchema DefinitionHistoryModels.Controls.identityResult = constantSchema expandedIdentity :=
  constantSchema_payload_eq identity_payload_across_contexts.1 identity_payload_across_contexts.2

theorem identity_extension_across_contexts (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.identityResult model =
      ConstantAdmission.sourceExtension expandedIdentity model :=
  constantExtension_payload_eq identity_payload_across_contexts.1 identity_payload_across_contexts.2 model

namespace PrimitivePreservation

open DefinitionModelFamily SignatureFormation

def instances : InstanceWitnesses := ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature

theorem type_available :
    (admitSourceTypeInTheory SourceProfile.primitiveContext instances ContextControls.identityTypeRequest).isSome = true := by
  decide +kernel

def typeResult : SourceTypeDefinitionResult :=
  (admitSourceTypeInTheory SourceProfile.primitiveContext instances ContextControls.identityTypeRequest).get type_available

theorem type_admitted : admitSourceTypeInTheory SourceProfile.primitiveContext instances
    ContextControls.identityTypeRequest = some typeResult := (Option.some_get type_available).symm

theorem existenceProof : HOL.ClosedTheorySet.Provable (∅ : HOL.ClosedTheorySet Symbol)
    (TypeAdmission.admittedImage type_admitted).formula := by
  obtain ⟨formula, translated, proven⟩ :=
    (translatedProvable_iff_compositionallyProvable _ _).mp
      (derives_translatedProvable_of_emptyAxiomPolicy
        (Mettapedia.Languages.HOLLight.derives_shared emptyAxiomPolicy (ContextControls.identityExistence_derivable emptyAxiomPolicy)))
  have same := translated.unique_eq (TypeAdmission.admittedImage type_admitted).conclusionTranslated
  cases same
  apply HOL.ClosedTheorySet.provable_mono _ proven
  intro sentence member
  rcases member with impossible | hypothesis
  · exact impossible
  · obtain ⟨term, present, _⟩ := hypothesis
    change term ∈ (∅ : Finset CanonicalTerm) at present
    exact absurd present (Finset.notMem_empty _)

theorem initial_selector (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) (operand : Ty) :
    (initialFamily.model other assignment).models (selectionFormula operand) :=
  ModelInstanceCoherence.initialModel_models_selection _ _ operand

theorem type_selector (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) (operand : Ty) :
    (TypeDefinitionModels.model initialFamily type_admitted existenceProof other assignment).models
      (selectionFormula operand) :=
  TypeDefinitionModels.selection_preserved initialFamily type_admitted existenceProof
    primitives.selectionParameter SourceProfile.selector_registered initial_selector other assignment operand

noncomputable def type_infinity (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    (TypeDefinitionModels.model initialFamily type_admitted existenceProof other assignment).DedekindInfinityWitness
      SourceProfile.individualBase :=
  TypeDefinitionModels.infinity_preserved initialFamily type_admitted existenceProof other assignment
    SourceProfile.individualBase (by
      simp [TypeFormed, SourceProfile.individualBase, individual_registered]) (initialInfinity other assignment)

theorem identity_selector (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) (operand : Ty) :
    (ConstantAdmission.sourceExtension expandedIdentity (initialFamily.model other assignment)).models
      (selectionFormula operand) :=
  ConstantAdmission.selection_preserved expanded_identity_admitted SourceProfile.selector_registered
    (initialFamily.model other assignment) operand (initial_selector other assignment operand)

noncomputable def identity_infinity (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    (ConstantAdmission.sourceExtension expandedIdentity (initialFamily.model other assignment)).DedekindInfinityWitness
      SourceProfile.individualBase :=
  ConstantAdmission.infinity_preserved expandedIdentity (initialFamily.model other assignment)
    SourceProfile.individualBase (initialInfinity other assignment)

theorem type_individual_carrier (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    (TypeDefinitionModels.model initialFamily type_admitted existenceProof other assignment).Carrier
      SourceProfile.individualBase = (initialFamily.model other assignment).Carrier SourceProfile.individualBase :=
  TypeDefinitionModels.old_base_carrier_preserved initialFamily type_admitted existenceProof other assignment
    SourceProfile.individualBase (by
      simp [TypeFormed, SourceProfile.individualBase, individual_registered])

end PrimitivePreservation

theorem closed_identity_extension_across_contexts :
    ConstantAdmission.sourceExtension DefinitionHistoryModels.Controls.identityResult ModelInterpretation.Controls.initialModel.{0} =
      ConstantAdmission.sourceExtension expandedIdentity ModelInterpretation.Controls.initialModel.{0} :=
  constantExtension_payload_eq identity_payload_across_contexts.1 identity_payload_across_contexts.2
    ModelInterpretation.Controls.initialModel.{0}

namespace PrimitivePreservation

noncomputable def closed_type_infinity :
    (TypeDefinitionModels.model initialFamily type_admitted existenceProof
      TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).DedekindInfinityWitness
      SourceProfile.individualBase :=
  TypeDefinitionModels.infinity_preserved initialFamily type_admitted existenceProof
    TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})
    SourceProfile.individualBase (by simp [SignatureFormation.TypeFormed,SourceProfile.individualBase,individual_registered])
    (initialInfinity TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))

theorem closed_identity_selector :
    (ConstantAdmission.sourceExtension expandedIdentity
      (initialFamily.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))).models
      (selectionFormula Ty.bool) :=
  ConstantAdmission.selection_preserved expanded_identity_admitted SourceProfile.selector_registered
    (initialFamily.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    Ty.bool (initial_selector TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}) Ty.bool)

noncomputable def closed_identity_infinity :
    (ConstantAdmission.sourceExtension expandedIdentity
      (initialFamily.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))).DedekindInfinityWitness
      SourceProfile.individualBase :=
  ConstantAdmission.infinity_preserved expandedIdentity
    (initialFamily.model TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
    SourceProfile.individualBase
    (initialInfinity TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0}))
end PrimitivePreservation

def falseTruthBody : SourceTerm :=
  .app (.app (.const Const.equality
    (Ty.equality (Ty.function Ty.bool Ty.bool)))
    (.abs (Name.global "p") Ty.bool (.var (Name.global "p") Ty.bool)))
    (.abs (Name.global "p") Ty.bool
      (.app (.app (.const Const.equality (Ty.equality Ty.bool))
        (.var (Name.global "p") Ty.bool)) (.var (Name.global "p") Ty.bool)))

theorem false_truth_available :
    (admitConstantInTheory SourceProfile.primitiveContext
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature)
      (Name.global "T") falseTruthBody).isSome = true := by decide +kernel

def falseTruth : ContextConstantDefinitionResult :=
  (admitConstantInTheory SourceProfile.primitiveContext
    (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature)
    (Name.global "T") falseTruthBody).get false_truth_available

theorem false_truth_admitted :
    admitConstantInTheory SourceProfile.primitiveContext
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature)
      (Name.global "T") falseTruthBody = some falseTruth :=
  (Option.some_get false_truth_available).symm

theorem false_truth_same_type : Source.truthResult.definition.ty = falseTruth.definition.ty :=
  (Ty.same_eq_true_iff _ _).mp (by decide +kernel)

theorem false_truth_same_name : constantName Source.truthResult.output.constant = constantName falseTruth.output.constant := by
  rw [(ConstantAdmission.source_equation Source.truthAdmitted).1,
    (ConstantAdmission.source_equation false_truth_admitted).1]
  rfl

theorem false_truth_different_payload : Source.truthResult.output ≠ falseTruth.output := by
  intro same
  have named := congrArg ConstantDefinitionResult.constant same
  have compared := (Const.same_eq_true_iff _ _).mpr named
  revert compared
  decide +kernel

def falseTruthFormula : HOL.ClosedFormula Symbol :=
  .eq (.lam (.var .vz)) (.lam (.eq (.var .vz) (.var .vz)))

theorem false_truth_translated : Translates [] (falseTruthBody.toDB []) .prop falseTruthFormula := by
  have checked : falseTruthBody.toDB [] =
    (.app (.app (.const Const.equality (Ty.equality (Ty.function Ty.bool Ty.bool)))
      (.abs Ty.bool (.bound 0)))
      (.abs Ty.bool (.app (.app (.const Const.equality (Ty.equality Ty.bool)) (.bound 0)) (.bound 0)))) :=
    (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
  rw [checked]
  exact .equalityApp (equalityOperand?_equality _) (by simp)
    (.abs (by simp) (.bound .vz))
    (.abs (by simp) (.equalityApp (equalityOperand?_equality _) (by simp) (.bound .vz) (.bound .vz)))

theorem false_definition_not_truth
    (model : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) (full : model.FullDomains) :
    ¬ ((ConstantAdmission.sourceExtension falseTruth model).constDen
      (.constant falseTruth.output.constant Ty.bool (τ := .prop) (by simp))).down := by
  have value : (ConstantAdmission.sourceExtension falseTruth model).constDen
      (.constant falseTruth.output.constant Ty.bool (τ := .prop) (by simp)) =
      model.denote falseTruthFormula (fun index => nomatch index) := by
    apply ConstantAdmission.sourceExtension_constant_translates false_truth_admitted
      model full TypeSubst.empty Ty.bool (by simp)
    · rw [TypeSubst.apply_empty,← false_truth_same_type,Source.truthType]
      rfl
    · simpa only [TypeCorrectTermSubstitution.ofTypes,TermSubst.typeInstance_identity] using false_truth_translated
  rw [value]
  change ¬ (∀ p, model.adm .prop p → (p.down ↔ (p.down ↔ p.down)))
  intro valid
  exact (valid (ULift.up False) (model.prop_mem (ULift.up False))).mpr Iff.rfl


theorem closed_constant_reference_invariant :
    ReferenceInvariant (DefinitionModelFamily.Family.constantCore primitives referenceReduct.{0}
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature)
      (Name.global "identity") DefinitionAdapters.Controls.identitySource expandedIdentity expanded_identity_admitted) :=
  constant_definition_invariant primitives referenceReduct referenceReduct_invariant
    (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature)
    (Name.global "identity") DefinitionAdapters.Controls.identitySource expandedIdentity expanded_identity_admitted

theorem closed_type_reference_invariant :
    ReferenceInvariant (DefinitionModelFamily.Family.typeDefinitionCore primitives referenceReduct.{0}
      PrimitivePreservation.instances ContextControls.identityTypeRequest PrimitivePreservation.typeResult
      PrimitivePreservation.type_admitted PrimitivePreservation.existenceProof) :=
  type_definition_invariant primitives referenceReduct referenceReduct_invariant
    PrimitivePreservation.type_admitted PrimitivePreservation.existenceProof

namespace Interleaved

open RegisteredReplayModels SignatureFormation

def instances : InstanceWitnesses := ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature

def proofCommand : Command := .proof
  ⟨ContextControls.identityExistence,.inference (.refl DefinitionAdapters.Controls.identityTerm),[],("original-order",0)⟩ instances

def typeCommand : Command := .typeDefinition ("original-order",1) ContextControls.identityTypeRequest 0 instances

def constantCommand : Command := .constant ("original-order",2) (Name.global "identityAfterType")
  DefinitionAdapters.Controls.identitySource instances

def commands : List Command := [proofCommand,typeCommand,constantCommand]

theorem available : (Registered.replayFrom emptyAxiomPolicy (Registered.empty SourceProfile.primitiveContext) commands).isSome = true := by
  decide +kernel

def after : Registered.State :=
  (Registered.replayFrom emptyAxiomPolicy (Registered.empty SourceProfile.primitiveContext) commands).get available

theorem replayed : Registered.replayFrom emptyAxiomPolicy (Registered.empty SourceProfile.primitiveContext) commands = some after :=
  (Option.some_get available).symm

@[irreducible] noncomputable def frame : Frame.{0} SourceProfile.primitiveContext emptyAxiomPolicy after.context after.cache :=
  Frame.replay primitives (Registered.empty SourceProfile.primitiveContext) after initialReferenceFrame commands replayed

theorem invariant : ReferenceInvariant frame.family := by
  unfold frame
  exact ReferenceInvariant.replay primitives (Registered.empty SourceProfile.primitiveContext) after
    initialReferenceFrame initialReferenceFrame_invariant commands replayed

theorem counts : after.cache.size = 4 ∧ after.receipts.size = 3 := by decide +kernel

theorem type_before_witness_refused :
    (Registered.apply emptyAxiomPolicy (Registered.empty SourceProfile.primitiveContext) typeCommand).isNone = true := by
  decide +kernel

end Interleaved

namespace Phases

def commands : List Command :=
  referenceCommands.take 7 ++ [axiomCommand 0,axiomCommand 1] ++
    referenceCommands.drop 7 ++ [axiomCommand 2]

theorem available : (Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) commands).isSome = true := by
  decide +kernel

def after : Registered.State :=
  (Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) commands).get available

theorem replayed : Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) commands = some after :=
  (Option.some_get available).symm

theorem counts : after.cache.size = 12 ∧ after.receipts.size = 12 := by decide +kernel

def prematureInfinity : List Command := referenceCommands.take 7 ++ [axiomCommand 2]

theorem infinity_before_definitions_refused :
    (Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) prematureInfinity).isNone = true := by
  decide +kernel

theorem received_models (other : OperatorFamilies.{0}) (assignment : Assignment.{0})
    (fact : Theorem) (known : fact ∈ after.cache) :
    ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
      ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp,
        ((sourceReplayFrame commands after replayed).frame.model other assignment).models hypothesis) →
        ((sourceReplayFrame commands after replayed).frame.model other assignment).models formula) :=
  source_replay_models commands after replayed other assignment fact known

theorem closed_model_exists :
    ∃ model : HOL.HenkinModel.{0,0,1} AtomicTy Symbol, model.FullDomains ∧
      ∀ fact ∈ after.cache, ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
        ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, model.models hypothesis) → model.models formula) :=
  source_replay_model commands after replayed TypeFamilySemantics.Controls.initialOther
    (fun _ => TypeFamilySemantics.Controls.natural.{0})

def truthEvent : ExportReplay.Event :=
  ⟨[0],[],.constant ("model-export",0) (Name.global "T") Source.truthBody
    (ExportReplay.instanceCertificates Source.truthResult.context.signature),
    [Source.truthResult.output.definitionTheorem.sequent]⟩

theorem export_available :
    (ExportReplay.replayFrom policy (ExportReplay.empty SourceProfile.primitiveContext) [truthEvent]).isSome = true := by
  decide +kernel

def exportAfter : ExportReplay.State :=
  (ExportReplay.replayFrom policy (ExportReplay.empty SourceProfile.primitiveContext) [truthEvent]).get export_available

theorem export_replayed :
    ExportReplay.replayFrom policy (ExportReplay.empty SourceProfile.primitiveContext) [truthEvent] = some exportAfter :=
  (Option.some_get export_available).symm

theorem closed_export_model_exists :
    ∃ model : HOL.HenkinModel.{0,0,1} AtomicTy Symbol, model.FullDomains ∧
      ∀ fact ∈ exportAfter.registered.cache, ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
        ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, model.models hypothesis) → model.models formula) :=
  source_export_model [truthEvent] exportAfter export_replayed TypeFamilySemantics.Controls.initialOther
    (fun _ => TypeFamilySemantics.Controls.natural.{0})

end Phases

def verdicts : List (String × Bool) :=
  [("source-profile/original-phase-order-accepted", (Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) Phases.commands).isSome),
   ("source-profile/original-phase-counts", decide (Phases.after.cache.size = 12 ∧ Phases.after.receipts.size = 12)),
   ("source-profile/infinity-before-definitions-refused", (Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) Phases.prematureInfinity).isNone),
   ("source-profile/interleaved-accepted", (Registered.replayFrom emptyAxiomPolicy (Registered.empty SourceProfile.primitiveContext) Interleaved.commands).isSome),
   ("source-profile/interleaved-cache-four", decide (Interleaved.after.cache.size = 4)),
   ("source-profile/interleaved-receipts-three", decide (Interleaved.after.receipts.size = 3)),
   ("source-profile/type-before-witness-refused", (Registered.apply emptyAxiomPolicy (Registered.empty SourceProfile.primitiveContext) Interleaved.typeCommand).isNone),
   ("source-profile/reference-cache-nine", decide (referenceState.cache.size = 9)),
   ("source-profile/reference-receipts-nine", decide (referenceState.receipts.size = 9)),
   ("source-profile/three-commitments-received", (replayFrom policy referenceState commands).isSome),
   ("source-profile/received-cache-twelve", decide (after.cache.size = 12)),
   ("source-profile/received-receipts-twelve", decide (after.receipts.size = 12)),
   ("source-profile/unlisted-axiom-refused", decide ((RuleRequest.axiom unlisted).check policy = none)),
   ("source-profile/changed-conclusion-refused", (Registered.apply policy referenceState forgedCommand).isNone)]

#print axioms received_models
#print axioms retained_counts
#print axioms reference_falsity_refused
#print axioms finite_infinity_refused
#print axioms reference_eta_model
#print axioms reference_selection_model
#print axioms reference_infinity_model
end Mettapedia.Languages.HOLLight.SourceProfileModels.Controls
