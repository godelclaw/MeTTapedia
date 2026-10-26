import Mettapedia.Languages.HOLLight.RegisteredReplayModels
import Mettapedia.Languages.HOLLight.StandardTheoryInterpretation
/-!
# Constructed model of the retained three-axiom source profile

The original nine admitted Boolean definitions are interpreted over a coherent
primitive family with a concrete natural-number individual carrier. Their
chronological extension validates the actual quantified source commitments.
The nine registered reference commands construct their exact cache and receipt
state. Accepted proof, constant and type-definition replay after that state has
a constructed full-domain model under the selected three-axiom policy. This
reference-prefix route is separate from a model correspondence for the complete
interleaved receiving history and from native implementation refinement.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.SourceProfileModels
open DefinitionHistoryModels ModelInterpretation RegisteredReplayModels
open ProofExecution Registered UniversalDefinitionHistory
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics ModelInstanceCoherence DefinitionAdapters DefinitionModelFamily
open StandardTheoryInterpretation SignatureFormation DefinitionHistorySchemas DefinitionSchemaSubstitution
universe w

def primitives : Primitives SourceProfile.primitiveContext where
  functionArity :=
    (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes).1 _ _
      (ContextControls.core_includes.1 _ _ ContextControls.function_registered)
  equalityParameter := ContextControls.equalityParameter
  equalityRegistered :=
    (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes).2 _ _ (by
      unfold ContextControls.coreContext
      exact ContextControls.baseContext.addConstant_registered _ _ _ _)
  selectionParameter := ContextControls.equalityParameter
  selectionDeclaration := Or.inr SourceProfile.selector_registered

def individualDomain : Domain.{w} := ⟨ULift.{w+1,0} Nat, .up 0⟩

theorem individual_registered : SourceProfile.primitiveContext.signature.typeOperators
    SourceProfile.individualOperator = some 0 := by
  apply SourceProfile.individual_includes.1
  exact ContextControls.coreContext.addTypeOperator_registered _ _ _

noncomputable def initialFamily : Family.{w} SourceProfile.primitiveContext SourceProfile.primitiveContext ∅ :=
  (Family.nil primitives).fixAmbientOperator SourceProfile.individualOperator 0 individual_registered
    (fun _ => individualDomain)

noncomputable def referenceCore : Family.{w} SourceProfile.primitiveContext
    StandardTheoryInterpretation.Source.ontoResult.context ∅ :=
  Family.constantHistoryCore primitives initialFamily StandardTheoryInterpretation.referenceHistory

theorem referenceCore_model (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    referenceCore.model other assignment =
      StandardTheoryInterpretation.Interpretation.ontoModel
        (ModelInstanceCoherence.initialModel
          (extend other SourceProfile.individualOperator (fun _ => individualDomain)) assignment) := by
  exact (Family.constantHistoryCore_model primitives initialFamily
    StandardTheoryInterpretation.referenceHistory other assignment).trans
    (StandardTheoryInterpretation.referenceHistory_model _ (initialFamily.fullDomains other assignment))

theorem initial_individual_carrier (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (initialFamily.model other assignment).Carrier SourceProfile.individualBase = ULift.{w+1,0} Nat := by
  simp [initialFamily, Family.fixAmbientOperator, Family.nil, ModelInstanceCoherence.initialModel,
    ModelInterpretation.model, TypeFamilySemantics.model, HOL.HenkinModel.standard,
    atomicCarrier, SourceProfile.individualBase, SourceProfile.individualOperator,
    primitiveFamilies, extend, TypeOp.bool, TypeOp.function, TypeOp.same, Name.global,
    individualDomain]

noncomputable def initialInfinity (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (initialFamily.model other assignment).DedekindInfinityWitness SourceProfile.individualBase :=
  HOL.HenkinModel.DedekindInfinityWitness.ofNatEquiv
    (initialFamily.fullDomains other assignment)
    ((Equiv.cast (initial_individual_carrier other assignment)).trans Equiv.ulift)

theorem reference_models_eta (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (domain codomain : HOL.Ty AtomicTy) :
    (referenceCore.model other assignment).models
      (StandardTheoryInterpretation.Raw.etaAxiom domain codomain) := by
  rw [referenceCore_model]
  exact StandardTheoryInterpretation.Interpretation.ontoModel_models_eta _
    (initialFamily.fullDomains other assignment) domain codomain

theorem reference_models_infinity (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (referenceCore.model other assignment).models StandardTheoryInterpretation.Raw.infinityAxiom := by
  rw [referenceCore_model]
  exact StandardTheoryInterpretation.Interpretation.ontoModel_models_infinity _
    (initialFamily.fullDomains other assignment) (initialInfinity other assignment)

theorem reference_models_selection (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (operand : Ty) :
    (referenceCore.model other assignment).models
      (StandardTheoryInterpretation.Raw.selectionAxiom operand.toHOL) := by
  rw [referenceCore_model]
  exact StandardTheoryInterpretation.Interpretation.ontoModel_models_selection _
    (initialFamily.fullDomains other assignment) operand
    (ModelInstanceCoherence.initialModel_models_selection _ _ operand)


/-- The actual source syntax, its canonical checked term and its compositional
reading. This record supplies no semantic validity assumption. -/
structure SourceSentence where
  source : SourceTerm
  canonical : CanonicalTerm
  boolean : canonical.IsBool
  same : canonical.term = source.toDB []
  formula : HOL.ClosedFormula Symbol
  translated : TranslatesCompositionally [] canonical.term .prop formula

noncomputable def SourceSentence.ofTranslation (source : SourceTerm)
    (direct : HOL.ClosedFormula Symbol)
    (translation : Translates [] (source.toDB []) .prop direct) : SourceSentence where
  source := source
  canonical := CanonicalTerm.ofFormulaTranslation _ translation
  boolean := rfl
  same := rfl
  formula := closedTranslation _ translation.exists_compositional
  translated := closedTranslation_spec _ translation.exists_compositional

private theorem etaTranslated : Translates [] (Source.etaAxiom.toDB []) .prop
    (Raw.etaAxiom ((Ty.var (Name.global "A")).toHOL) ((Ty.var (Name.global "B")).toHOL)) := by
  simpa only [TypeCorrectTermSubstitution.ofTypes, TermSubst.typeInstance_identity,
    TypeSubst.apply_empty] using Raw.etaAxiom_translated TypeSubst.empty

private theorem selectionTranslated : Translates [] (Source.selectionAxiom.toDB []) .prop
    (Raw.selectionAxiom ((Ty.var (Name.global "A")).toHOL)) := by
  simpa only [TypeCorrectTermSubstitution.ofTypes, TermSubst.typeInstance_identity,
    TypeSubst.apply_empty] using Raw.selectionAxiom_translated TypeSubst.empty

private theorem infinityTranslated : Translates [] (Source.infinityAxiom.toDB []) .prop
    Raw.infinityAxiom := by
  simpa only [TypeCorrectTermSubstitution.ofTypes, TermSubst.typeInstance_identity]
    using Raw.infinityAxiom_translated TypeSubst.empty

noncomputable def etaSourceSentence : SourceSentence := SourceSentence.ofTranslation Source.etaAxiom _ etaTranslated
noncomputable def selectionSourceSentence : SourceSentence := SourceSentence.ofTranslation Source.selectionAxiom _ selectionTranslated
noncomputable def infinitySourceSentence : SourceSentence := SourceSentence.ofTranslation Source.infinityAxiom _ infinityTranslated

theorem eta_formed : AnnotationsFormed Source.ontoResult.context.signature etaSourceSentence.canonical.term := by
  apply (checkSource_sound _ _ (show checkSource Source.ontoResult.context.signature
    (ExportReplay.instanceCertificates Source.ontoResult.context.signature)
    Source.etaAxiom = some etaSourceSentence.canonical by decide +kernel)).2

theorem eta_closed : etaSourceSentence.canonical.term.HasNoFreeVariables :=
  (DBTerm.hasNoFreeVariables_eq_true_iff _).mp (by decide +kernel)

theorem selection_formed : AnnotationsFormed Source.ontoResult.context.signature selectionSourceSentence.canonical.term := by
  apply (checkSource_sound _ _ (show checkSource Source.ontoResult.context.signature
    (ExportReplay.instanceCertificates Source.ontoResult.context.signature)
    Source.selectionAxiom = some selectionSourceSentence.canonical by decide +kernel)).2

theorem selection_closed : selectionSourceSentence.canonical.term.HasNoFreeVariables :=
  (DBTerm.hasNoFreeVariables_eq_true_iff _).mp (by decide +kernel)

theorem infinity_formed : AnnotationsFormed Source.ontoResult.context.signature infinitySourceSentence.canonical.term := by
  apply (checkSource_sound _ _ (show checkSource Source.ontoResult.context.signature
    (ExportReplay.instanceCertificates Source.ontoResult.context.signature)
    Source.infinityAxiom = some infinitySourceSentence.canonical by decide +kernel)).2

theorem infinity_closed : infinitySourceSentence.canonical.term.HasNoFreeVariables :=
  (DBTerm.hasNoFreeVariables_eq_true_iff _).mp (by decide +kernel)

theorem SourceSentence.models_of_direct (sentence : SourceSentence) (direct : HOL.ClosedFormula Symbol)
    (translation : Translates [] sentence.canonical.term .prop direct)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
    (holds : model.models direct) : model.models sentence.formula := by
  let empty : model.Valuation [] := fun v => nomatch v
  have atEmpty (formula : HOL.ClosedFormula Symbol) :
      model.models formula = (model.denote formula empty).down := by
    unfold HOL.HenkinModel.models HOL.PreModel.models
    exact congrArg ULift.down (model.denote_closed_valuation_eq _ _ _)
  have same := translation.denote_eq_compositional sentence.translated model full empty
  exact (atEmpty sentence.formula).mpr
    ((congrArg ULift.down same).mp ((atEmpty direct).mp holds))

theorem eta_models (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (referenceCore.model other assignment).models etaSourceSentence.formula :=
  etaSourceSentence.models_of_direct _ etaTranslated _ (referenceCore.fullDomains other assignment)
    (reference_models_eta other assignment (Ty.var (Name.global "A")).toHOL (Ty.var (Name.global "B")).toHOL)

theorem selection_models (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (referenceCore.model other assignment).models selectionSourceSentence.formula :=
  selectionSourceSentence.models_of_direct _ selectionTranslated _ (referenceCore.fullDomains other assignment)
    (reference_models_selection other assignment (Ty.var (Name.global "A")))

theorem infinity_models (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (referenceCore.model other assignment).models infinitySourceSentence.formula :=
  infinitySourceSentence.models_of_direct _ infinityTranslated _ (referenceCore.fullDomains other assignment)
    (reference_models_infinity other assignment)

def SourceSentence.sequent (sentence : SourceSentence) : Sequent := ⟨∅, sentence.canonical⟩

theorem SourceSentence.licensed (sentence : SourceSentence)
    (formed : AnnotationsFormed Source.ontoResult.context.signature sentence.canonical.term) :
    LicensedSchema Source.ontoResult.context.signature sentence.formula :=
  ⟨[], _, _, sentence.translated, formed, ContextFormed.nil _, rfl⟩

theorem SourceSentence.ordinary (sentence : SourceSentence)
    (formed : AnnotationsFormed Source.ontoResult.context.signature sentence.canonical.term)
    (closed : sentence.canonical.term.HasNoFreeVariables) : OrdinarySymbols sentence.formula := by
  exact ordinary_of_closed_translation _ primitives.equalityParameter
    (referenceHistory.includes.2 _ _ primitives.equalityRegistered) sentence.translated formed closed

noncomputable def sentences : List SourceSentence := [etaSourceSentence, selectionSourceSentence, infinitySourceSentence]
noncomputable def commitmentSchemas : List (HOL.ClosedFormula Symbol) := sentences.map SourceSentence.formula
noncomputable def definitionSchemas : List (HOL.ClosedFormula Symbol) :=
  referenceHistory.records.map DefinitionHistorySchemas.constantSchema
noncomputable def referenceSchemas : List (HOL.ClosedFormula Symbol) := definitionSchemas ++ commitmentSchemas

theorem commitment_licensed {formula : HOL.ClosedFormula Symbol} (member : formula ∈ commitmentSchemas) :
    LicensedSchema Source.ontoResult.context.signature formula := by
  simp only [commitmentSchemas, sentences, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact etaSourceSentence.licensed eta_formed
  · exact selectionSourceSentence.licensed selection_formed
  · exact infinitySourceSentence.licensed infinity_formed

theorem commitment_ordinary {formula : HOL.ClosedFormula Symbol} (member : formula ∈ commitmentSchemas) :
    OrdinarySymbols formula := by
  simp only [commitmentSchemas, sentences, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact etaSourceSentence.ordinary eta_formed eta_closed
  · exact selectionSourceSentence.ordinary selection_formed selection_closed
  · exact infinitySourceSentence.ordinary infinity_formed infinity_closed

theorem commitment_models (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {formula : HOL.ClosedFormula Symbol} (member : formula ∈ commitmentSchemas) :
    (referenceCore.model other assignment).models formula := by
  simp only [commitmentSchemas, sentences, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact eta_models other assignment
  · exact selection_models other assignment
  · exact infinity_models other assignment

theorem reference_licensed {formula : HOL.ClosedFormula Symbol} (member : formula ∈ referenceSchemas) :
    LicensedSchema Source.ontoResult.context.signature formula := by
  rcases List.mem_append.mp member with earlier | commitment
  · obtain ⟨result, present, rfl⟩ := List.mem_map.mp earlier
    exact DefinitionHistorySchemas.ConstantHistory.record_licensed referenceHistory primitives present
  · exact commitment_licensed commitment

theorem reference_ordinary {formula : HOL.ClosedFormula Symbol} (member : formula ∈ referenceSchemas) :
    OrdinarySymbols formula := by
  rcases List.mem_append.mp member with earlier | commitment
  · obtain ⟨result, present, rfl⟩ := List.mem_map.mp earlier
    exact DefinitionHistorySchemas.ConstantHistory.record_ordinary referenceHistory primitives present
  · exact commitment_ordinary commitment

theorem reference_models (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {formula : HOL.ClosedFormula Symbol} (member : formula ∈ referenceSchemas) :
    (referenceCore.model other assignment).models formula := by
  rcases List.mem_append.mp member with earlier | commitment
  · obtain ⟨result, present, rfl⟩ := List.mem_map.mp earlier
    rw [show referenceCore.model other assignment = referenceHistory.extendModel (initialFamily.model other assignment)
      from DefinitionModelFamily.Family.constantHistoryCore_model primitives initialFamily referenceHistory other assignment]
    exact DefinitionHistorySchemas.ConstantHistory.record_models referenceHistory _ present
  · exact commitment_models other assignment commitment

def etaCanonical : CanonicalTerm := CanonicalTerm.ofFormulaTranslation _ etaTranslated
def selectionCanonical : CanonicalTerm := CanonicalTerm.ofFormulaTranslation _ selectionTranslated
def infinityCanonical : CanonicalTerm := CanonicalTerm.ofFormulaTranslation _ infinityTranslated

def commitments : List Sequent :=
  [⟨∅, etaCanonical⟩, ⟨∅, selectionCanonical⟩, ⟨∅, infinityCanonical⟩]

def policy : AxiomPolicy := fun sequent => sequent ∈ commitments
instance : DecidablePred policy := fun _ => inferInstanceAs (Decidable (_ ∈ commitments))

def referenceCache : Array Theorem :=
  (referenceHistory.records.map (fun result => result.output.definitionTheorem)).toArray

/-- The original nine checked equations carry their axiom-free source
derivations and their chronological full-domain interpretation. -/
noncomputable def referenceBaseFrame : RegisteredReplayModels.Frame.{w}
    SourceProfile.primitiveContext emptyAxiomPolicy Source.ontoResult.context referenceCache where
  schemas := definitionSchemas
  ordinary := fun _ member => reference_ordinary (List.mem_append_left _ member)
  licensed := fun _ member => reference_licensed (List.mem_append_left _ member)
  family := referenceCore.retheorize _
    (UniversalDefinitionModels.background_models_of_schemas referenceCore primitives definitionSchemas
      (fun _ member => reference_licensed (List.mem_append_left _ member))
      (fun other assignment _ member => reference_models other assignment (List.mem_append_left _ member)))
  authorized := fun _ unauthorized => False.elim unauthorized
  cacheProvable := by
    intro fact present
    obtain ⟨result, member, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp present)
    apply (translatedProvable_iff_compositionallyProvable _ _).mpr
    refine ⟨DefinitionHistorySchemas.constantSchema result,
      DefinitionHistorySchemas.ConstantHistory.record_translated referenceHistory member,
      HOL.ClosedTheorySet.provable_of_mem (Or.inl ?_)⟩
    exact ⟨_, List.mem_map.mpr ⟨result, member, rfl⟩,
      DefinitionSchemaSubstitution.TypeImageOrbit.original⟩
  valid := by
    intro fact present
    exact MixedDefinitionHistory.constant_record_derives referenceHistory primitives emptyAxiomPolicy
      (List.mem_toArray.mp present)

/-- The three formed, interpreted commitments enlarge the same reference
frame through the generic schema/policy extension, retaining its cache. -/
noncomputable def referenceFrame : RegisteredReplayModels.Frame.{w} SourceProfile.primitiveContext policy
    Source.ontoResult.context referenceCache :=
  referenceBaseFrame.adjoinSchemas primitives commitmentSchemas
    (fun _ member => commitment_ordinary member)
    (fun _ member => commitment_licensed member)
    (fun other assignment _ member => commitment_models other assignment member)
    policy (fun _ unauthorized => False.elim unauthorized)
    (by
    intro sequent present
    change sequent ∈ sentences.map SourceSentence.sequent at present
    obtain ⟨sentence, member, rfl⟩ := List.mem_map.mp present
    apply (translatedProvable_iff_compositionallyProvable _ _).mpr
    refine ⟨sentence.formula, sentence.translated, HOL.ClosedTheorySet.provable_of_mem (Or.inl ?_)⟩
    exact ⟨sentence.formula, List.mem_append_right _ (List.mem_map.mpr ⟨sentence, member, rfl⟩),
      DefinitionSchemaSubstitution.TypeImageOrbit.original⟩)

def referenceCommands : List ProofExecution.Registered.Command :=
  [.constant ("hol-light-export", 0) (Name.global "T") Source.truthBody (ExportReplay.instanceCertificates Source.truthResult.context.signature),
   .constant ("hol-light-export", 18) (Name.global "/\\") Source.conjunctionBody (ExportReplay.instanceCertificates Source.conjunctionResult.context.signature),
   .constant ("hol-light-export", 188) (Name.global "==>") Source.implicationBody (ExportReplay.instanceCertificates Source.implicationResult.context.signature),
   .constant ("hol-light-export", 421) (Name.global "!") Source.universalBody (ExportReplay.instanceCertificates Source.universalResult.context.signature),
   .constant ("hol-light-export", 463) (Name.global "?") Source.existentialBody (ExportReplay.instanceCertificates Source.existentialResult.context.signature),
   .constant ("hol-light-export", 715) (Name.global "F") Source.falsityBody (ExportReplay.instanceCertificates Source.falsityResult.context.signature),
   .constant ("hol-light-export", 716) (Name.global "~") Source.negationBody (ExportReplay.instanceCertificates Source.negationResult.context.signature),
   .constant ("hol-light-export", 131635) (Name.global "ONE_ONE") Source.oneOneBody (ExportReplay.instanceCertificates Source.oneOneResult.context.signature),
   .constant ("hol-light-export", 132024) (Name.global "ONTO") Source.ontoBody (ExportReplay.instanceCertificates Source.ontoResult.context.signature)]

def referenceState : ProofExecution.Registered.State :=
  ⟨Source.ontoResult.context, referenceCache,
    ((referenceCommands.zip (referenceCache.toList)).map
      (fun (command, fact) => (⟨command, [fact]⟩ : ProofExecution.Registered.CommandReceipt))).toArray⟩

private theorem reference_constant_checked {context : TheoryContext}
    {oldWitnesses : InstanceWitnesses} {name : Name} {body : SourceTerm}
    {result : ContextConstantDefinitionResult}
    (admitted : admitConstantInTheory context oldWitnesses name body = some result)
    (available : (admitConstantInTheory context
      (ExportReplay.instanceCertificates result.context.signature) name body).isSome = true)
    (formed : theoremFormedB result.context.signature
      (ExportReplay.instanceCertificates result.context.signature) result.output.definitionTheorem = true)
    (origin : ProofExecution.Origin) (cache : Array Theorem) :
    (ProofExecution.Registered.Command.constant origin name body
      (ExportReplay.instanceCertificates result.context.signature)).check emptyAxiomPolicy context cache =
      some ⟨result.context, [result.output.definitionTheorem]⟩ := by
  obtain ⟨actual, received⟩ := Option.isSome_iff_exists.mp available
  have same := admitConstantInTheory_unique admitted received
  rw [← same] at received
  change (do
    let defined ← admitConstantInTheory context
      (ExportReplay.instanceCertificates result.context.signature) name body
    if theoremFormedB defined.context.signature
      (ExportReplay.instanceCertificates result.context.signature) defined.output.definitionTheorem then
      pure (⟨defined.context, [defined.output.definitionTheorem]⟩ : ProofExecution.Registered.Output)
    else none) = _
  rw [received]
  change (if theoremFormedB result.context.signature
      (ExportReplay.instanceCertificates result.context.signature) result.output.definitionTheorem then
    some (⟨result.context, [result.output.definitionTheorem]⟩ : ProofExecution.Registered.Output) else none) = _
  rw [if_pos formed]

private theorem truthCommand_checked (cache : Array Theorem) :
    (ProofExecution.Registered.Command.constant ("hol-light-export", 0) (Name.global "T")
      Source.truthBody (ExportReplay.instanceCertificates Source.truthResult.context.signature)).check
      emptyAxiomPolicy SourceProfile.primitiveContext cache =
      some ⟨Source.truthResult.context, [Source.truthResult.output.definitionTheorem]⟩ :=
  reference_constant_checked Source.truthAdmitted (by decide +kernel) (by decide +kernel) _ cache

private theorem conjunctionCommand_checked (cache : Array Theorem) :
    (ProofExecution.Registered.Command.constant ("hol-light-export", 18) (Name.global "/\\")
      Source.conjunctionBody (ExportReplay.instanceCertificates Source.conjunctionResult.context.signature)).check
      emptyAxiomPolicy Source.truthResult.context cache =
      some ⟨Source.conjunctionResult.context, [Source.conjunctionResult.output.definitionTheorem]⟩ :=
  reference_constant_checked (by simpa only [Source.truthContext] using Source.conjunctionAdmitted) (by decide +kernel) (by decide +kernel) _ cache

private theorem implicationCommand_checked (cache : Array Theorem) :
    (ProofExecution.Registered.Command.constant ("hol-light-export", 188) (Name.global "==>")
      Source.implicationBody (ExportReplay.instanceCertificates Source.implicationResult.context.signature)).check
      emptyAxiomPolicy Source.conjunctionResult.context cache =
      some ⟨Source.implicationResult.context, [Source.implicationResult.output.definitionTheorem]⟩ :=
  reference_constant_checked (by simpa only [Source.conjunctionContext] using Source.implicationAdmitted) (by decide +kernel) (by decide +kernel) _ cache

private theorem universalCommand_checked (cache : Array Theorem) :
    (ProofExecution.Registered.Command.constant ("hol-light-export", 421) (Name.global "!")
      Source.universalBody (ExportReplay.instanceCertificates Source.universalResult.context.signature)).check
      emptyAxiomPolicy Source.implicationResult.context cache =
      some ⟨Source.universalResult.context, [Source.universalResult.output.definitionTheorem]⟩ :=
  reference_constant_checked (by simpa only [Source.implicationContext] using Source.universalAdmitted) (by decide +kernel) (by decide +kernel) _ cache

private theorem existentialCommand_checked (cache : Array Theorem) :
    (ProofExecution.Registered.Command.constant ("hol-light-export", 463) (Name.global "?")
      Source.existentialBody (ExportReplay.instanceCertificates Source.existentialResult.context.signature)).check
      emptyAxiomPolicy Source.universalResult.context cache =
      some ⟨Source.existentialResult.context, [Source.existentialResult.output.definitionTheorem]⟩ :=
  reference_constant_checked (by simpa only [Source.universalContext] using Source.existentialAdmitted) (by decide +kernel) (by decide +kernel) _ cache

private theorem falsityCommand_checked (cache : Array Theorem) :
    (ProofExecution.Registered.Command.constant ("hol-light-export", 715) (Name.global "F")
      Source.falsityBody (ExportReplay.instanceCertificates Source.falsityResult.context.signature)).check
      emptyAxiomPolicy Source.existentialResult.context cache =
      some ⟨Source.falsityResult.context, [Source.falsityResult.output.definitionTheorem]⟩ :=
  reference_constant_checked (by simpa only [Source.existentialContext] using Source.falsityAdmitted) (by decide +kernel) (by decide +kernel) _ cache

private theorem negationCommand_checked (cache : Array Theorem) :
    (ProofExecution.Registered.Command.constant ("hol-light-export", 716) (Name.global "~")
      Source.negationBody (ExportReplay.instanceCertificates Source.negationResult.context.signature)).check
      emptyAxiomPolicy Source.falsityResult.context cache =
      some ⟨Source.negationResult.context, [Source.negationResult.output.definitionTheorem]⟩ :=
  reference_constant_checked (by simpa only [Source.falsityContext] using Source.negationAdmitted) (by decide +kernel) (by decide +kernel) _ cache

private theorem oneOneCommand_checked (cache : Array Theorem) :
    (ProofExecution.Registered.Command.constant ("hol-light-export", 131635) (Name.global "ONE_ONE")
      Source.oneOneBody (ExportReplay.instanceCertificates Source.oneOneResult.context.signature)).check
      emptyAxiomPolicy Source.negationResult.context cache =
      some ⟨Source.oneOneResult.context, [Source.oneOneResult.output.definitionTheorem]⟩ :=
  reference_constant_checked (by simpa only [Source.negationContext] using Source.oneOneAdmitted) (by decide +kernel) (by decide +kernel) _ cache

private theorem ontoCommand_checked (cache : Array Theorem) :
    (ProofExecution.Registered.Command.constant ("hol-light-export", 132024) (Name.global "ONTO")
      Source.ontoBody (ExportReplay.instanceCertificates Source.ontoResult.context.signature)).check
      emptyAxiomPolicy Source.oneOneResult.context cache =
      some ⟨Source.ontoResult.context, [Source.ontoResult.output.definitionTheorem]⟩ :=
  reference_constant_checked (by simpa only [Source.oneOneContext] using Source.ontoAdmitted) (by decide +kernel) (by decide +kernel) _ cache

theorem reference_available : (ProofExecution.Registered.replayFrom emptyAxiomPolicy
    (ProofExecution.Registered.empty SourceProfile.primitiveContext) referenceCommands).isSome = true := by
  decide +kernel

/-- The reference state retains the original nine declaration commands,
their source IDs, exact outputs and registered receipts. -/
theorem reference_replayed : ProofExecution.Registered.replayFrom emptyAxiomPolicy
    (ProofExecution.Registered.empty SourceProfile.primitiveContext) referenceCommands = some referenceState := by
  simp only [referenceCommands, ProofExecution.Registered.empty, ProofExecution.Registered.replayFrom,
    ProofExecution.Registered.apply, Bind.bind, Pure.pure, truthCommand_checked, conjunctionCommand_checked, implicationCommand_checked, universalCommand_checked, existentialCommand_checked, falsityCommand_checked, negationCommand_checked, oneOneCommand_checked, ontoCommand_checked, Option.bind_some]
  rfl

noncomputable def replayFrame (commands : List ProofExecution.Registered.Command)
    (after : ProofExecution.Registered.State)
    (accepted : ProofExecution.Registered.replayFrom policy referenceState commands = some after) :
    RegisteredReplayModels.Frame.{w} SourceProfile.primitiveContext policy after.context after.cache :=
  RegisteredReplayModels.Frame.replay primitives referenceState after referenceFrame commands accepted

/-- Accepted registered replay after the reference state preserves a
constructed full-domain model. The original interleaved whole-source trace
is not identified with this reference-prefix route by this theorem. -/
theorem replay_models (commands : List ProofExecution.Registered.Command)
    (after : ProofExecution.Registered.State)
    (accepted : ProofExecution.Registered.replayFrom policy referenceState commands = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∃ model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol,
      model.FullDomains ∧ ∀ fact ∈ after.cache,
        ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
          ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, model.models hypothesis) → model.models formula) := by
  let frame := replayFrame commands after accepted
  exact ⟨frame.model other assignment, frame.model_fullDomains other assignment,
    fun _ known => frame.cached_models other assignment known⟩


#print axioms referenceCore_model
#print axioms initialInfinity
#print axioms reference_models_eta
#print axioms reference_models_selection
#print axioms reference_models_infinity
#print axioms referenceFrame
#print axioms reference_replayed
#print axioms replay_models
/-- The reference interpretation restricted to the original primitive
declaration context. This interpretation grants no declaration authority. -/
noncomputable def referenceReduct : Family.{w} SourceProfile.primitiveContext SourceProfile.primitiveContext ∅ :=
  referenceCore.restrictConstants (Signature.Includes.refl _) referenceHistory.includes
    (ConstantHistoryExpandedTypes.history_typeOperators referenceHistory).symm

theorem referenceReduct_model (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    referenceReduct.model other assignment = referenceCore.model other assignment := rfl

/-- Every reference schema and its source type images hold in the restricted
model, before those constants or axioms enter the receiving declaration state. -/
theorem referenceReduct_models (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {formula : HOL.ClosedFormula Symbol} (member : formula ∈ referenceSchemas)
    (substitution : TypeSubst) :
    (referenceReduct.model other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance formula) := by
  exact referenceFrame.family.equations other assignment _
    ⟨formula, member, DefinitionSchemaSubstitution.TypeImageOrbit.image substitution
      DefinitionSchemaSubstitution.TypeImageOrbit.original⟩

theorem primitive_declared {constant : Const} {schema : Ty}
    (declared : SourceProfile.primitiveContext.signature.constants constant = some schema) :
    constant = Const.equality ∨ constant = selectionConstant := by
  classical
  by_cases selector : constant = selectionConstant
  · exact Or.inr selector
  by_cases equality : constant = Const.equality
  · exact Or.inl equality
  simp [SourceProfile.primitiveContext,SourceProfile.individualContext,
    ContextControls.coreContext,ContextControls.baseContext,ContextControls.booleanContext,
    TheoryContext.addConstant,TheoryContext.addTypeOperator,TheoryContext.empty,
    Signature.addConstant,Signature.addTypeOperator,
    Const.same_eq_true_iff,selector,equality] at declared


def PrimitiveOrDefined : Const → Prop
  | .mk _ .undefined | .mk _ (.defined _) => True
  | _ => False

theorem reference_constant_origin {constant : Const} {schema : Ty}
    (declared : Source.ontoResult.context.signature.constants constant = some schema) :
    PrimitiveOrDefined constant := by
  rcases ConstantHistoryExpandedTypes.history_declared_origin referenceHistory constant schema declared with primitive | ⟨result,member,rfl⟩
  · rcases primitive_declared primitive with rfl | rfl <;> trivial
  · obtain ⟨before,instances,name,source,accepted⟩ := referenceHistory.record_admitted member
    rw [(ConstantAdmission.source_equation accepted).1]
    trivial

theorem primitiveOrDefined_avoids_type_maps
    {context : TheoryContext} {instances : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    {constant : Const} (ordinary : PrimitiveOrDefined constant) :
    constant ≠ result.output.abstractionConstant ∧ constant ≠ result.output.representationConstant := by
  constructor
  · intro same
    rw [same,(admitSourceTypeInTheory_pointwise accepted).2.1] at ordinary
    exact ordinary
  · intro same
    rw [same,(admitSourceTypeInTheory_pointwise accepted).2.2.1] at ordinary
    exact ordinary

theorem reference_schema_supported
    {context : TheoryContext} {instances : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    {formula : HOL.ClosedFormula Symbol} (member : formula ∈ referenceSchemas) :
    formula.SymbolsSatisfy (TypeDefinitionModels.AvoidsTypeDefinitionMaps result) := by
  obtain ⟨scope,source,body,translated,formed,_,rfl⟩ := reference_licensed member
  apply HOL.Term.SymbolsSatisfy.closeAll
  apply ModelAssignmentSupport.translation_symbols Source.ontoResult.context.signature
    (TypeDefinitionModels.AvoidsTypeDefinitionMaps result) _ _ translated formed
  · intro constant annotation type typed declared
    obtain ⟨schema,substitution,registered,_⟩ := declared
    exact primitiveOrDefined_avoids_type_maps accepted (reference_constant_origin registered)
  · intro sourceVar type typed
    trivial

theorem reference_schema_type_image_supported
    {context : TheoryContext} {instances : InstanceWitnesses}
    {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    {formula : HOL.ClosedFormula Symbol} (member : formula ∈ referenceSchemas) (substitution : TypeSubst) :
    (HOL.mapTypes substitution.baseInstance substitution.symbolInstance formula).SymbolsSatisfy
      (TypeDefinitionModels.AvoidsTypeDefinitionMaps result) :=
  TypeDefinitionModels.avoids_type_maps_typeImage result substitution formula (reference_schema_supported accepted member)

def ReferenceInvariant {initial context : TheoryContext} {theory : HOL.ClosedTheorySet Symbol}
    (family : Family.{w} initial context theory) : Prop :=
  ∀ other assignment formula, formula ∈ referenceSchemas → ∀ substitution : TypeSubst,
    (family.model other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance formula)

theorem referenceReduct_invariant : ReferenceInvariant referenceReduct.{w} := by
  intro other assignment formula member substitution
  exact referenceReduct_models other assignment member substitution

theorem type_definition_invariant
    {initial context : TheoryContext} {theory : HOL.ClosedTheorySet Symbol}
    (primitives : Primitives initial) (prior : Family.{w} initial context theory)
    (invariant : ReferenceInvariant prior)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (proof : HOL.ClosedTheorySet.Provable theory (TypeAdmission.admittedImage accepted).formula) :
    ReferenceInvariant (Family.typeDefinitionCore primitives prior instances request result accepted proof) := by
  intro other assignment formula member substitution
  apply (TypeDefinitionModels.models_without_new_maps prior accepted proof other assignment
    (HOL.mapTypes substitution.baseInstance substitution.symbolInstance formula)
    (reference_schema_type_image_supported accepted member substitution)).mpr
  exact invariant _ assignment formula member substitution


def AvoidsConstant (changed : Const) : ∀ {type}, Symbol type → Prop
  | _, .constant constant _ _ => constant ≠ changed
  | _, .variable _ _ => True

theorem reference_schema_avoids_unregistered (changed : Const)
    (absent : Source.ontoResult.context.signature.constants changed = none)
    {formula : HOL.ClosedFormula Symbol} (member : formula ∈ referenceSchemas)
    (substitution : TypeSubst) :
    (HOL.mapTypes substitution.baseInstance substitution.symbolInstance formula).SymbolsSatisfy
      (AvoidsConstant changed) := by
  apply HOL.Term.SymbolsSatisfy.mapTypes substitution.baseInstance substitution.symbolInstance
    (AvoidsConstant changed) (AvoidsConstant changed)
  · intro type symbol allowed
    cases symbol with
    | constant => exact allowed
    | «variable» => trivial
  · obtain ⟨scope,source,body,translated,formed,_,rfl⟩ := reference_licensed member
    apply HOL.Term.SymbolsSatisfy.closeAll
    apply ModelAssignmentSupport.translation_symbols Source.ontoResult.context.signature
      (AvoidsConstant changed) _ _ translated formed
    · intro constant annotation type typed declared same
      obtain ⟨schema,sourceInstance,registered,_⟩ := declared
      rw [same,absent] at registered
      cases registered
    · intro sourceVar type typed
      trivial

theorem constant_models_of_avoidance (result : ContextConstantDefinitionResult)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (formula : HOL.ClosedFormula Symbol)
    (supported : formula.SymbolsSatisfy (AvoidsConstant result.output.constant)) :
    (ConstantAdmission.sourceExtension result model).models formula ↔ model.models formula := by
  rw [ConstantAdmission.sourceExtension_eq_reduct,← HOL.HenkinModel.models_substConst]
  have fixed : HOL.substConst (ConstantAdmission.sourceExpansion result) formula = formula := by
    apply HOL.Term.SymbolsSatisfy.substConst_eq (ConstantAdmission.sourceExpansion result)
      (AvoidsConstant result.output.constant) _ formula supported
    intro type symbol allowed
    cases symbol with
    | constant constant annotation typed => exact ConstantAdmission.sourceExpansion_other result constant annotation typed allowed
    | «variable» sourceVar typed => exact ConstantAdmission.sourceExpansion_variable result sourceVar typed
  rw [fixed]

theorem constant_definition_invariant
    {initial context : TheoryContext} {theory : HOL.ClosedTheorySet Symbol}
    (primitives : Primitives initial) (prior : Family.{w} initial context theory)
    (invariant : ReferenceInvariant prior)
    (instances : InstanceWitnesses) (name : Name) (source : SourceTerm)
    (result : ContextConstantDefinitionResult)
    (accepted : admitConstantInTheory context instances name source = some result) :
    ReferenceInvariant (Family.constantCore primitives prior instances name source result accepted) := by
  intro other assignment formula member substitution
  change (ConstantAdmission.sourceExtension result (prior.model other assignment)).models _
  cases registered : Source.ontoResult.context.signature.constants result.output.constant with
  | none =>
    apply (constant_models_of_avoidance result (prior.model other assignment) _
      (reference_schema_avoids_unregistered result.output.constant registered member substitution)).mpr
    exact invariant other assignment formula member substitution
  | some schema =>
    rcases ConstantHistoryExpandedTypes.history_declared_origin referenceHistory _ schema registered with primitive | ⟨reference,present,same⟩
    · rcases primitive_declared primitive with same | same
      · rw [(ConstantAdmission.source_equation accepted).1] at same
        cases (Const.mk.inj same).2
      · rw [(ConstantAdmission.source_equation accepted).1] at same
        cases (Const.mk.inj same).2
    · obtain ⟨before,witnesses,referenceName,referenceSource,referenceAccepted⟩ := referenceHistory.record_admitted present
      have payload := admitted_same_identity_payload accepted referenceAccepted same
      have schemaPresent : constantSchema result ∈ referenceSchemas := by
        rw [constantSchema_payload_eq payload.1 payload.2]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨reference,present,rfl⟩)
      rw [constant_extension_eq_of_schema accepted primitives.equalityParameter
        (prior.includes.2 _ _ primitives.equalityRegistered) (prior.model other assignment)
        (prior.fullDomains other assignment)
        (fun sourceInstance => invariant other assignment _ schemaPresent sourceInstance)]
      exact invariant other assignment formula member substitution

namespace ReferenceInvariant

theorem models {initial context : TheoryContext} {theory : HOL.ClosedTheorySet Symbol}
    (family : Family.{w} initial context theory) (invariant : ReferenceInvariant family)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {formula : HOL.ClosedFormula Symbol} (member : formula ∈ referenceSchemas) :
    (family.model other assignment).models formula := by
  have image := invariant other assignment formula member TypeSubst.empty
  have original := (reindexedModel_models TypeSubst.empty (family.model other assignment)
    (family.fullDomains other assignment) formula).mpr image
  rwa [reindexedModel_identity _ (family.fullDomains other assignment)] at original


theorem transfer {initial context otherContext : TheoryContext} {policy : AxiomPolicy}
    {cache nextCache : Array Theorem} (frame : Frame.{w} initial policy context cache)
    (sameContext : context = otherContext) (sameCache : cache = nextCache)
    (invariant : ReferenceInvariant frame.family) :
    ReferenceInvariant (frame.transfer sameContext sameCache).family := by
  intro other assignment formula member substitution
  rw [frame.transfer_model sameContext sameCache]
  exact invariant other assignment formula member substitution

theorem constantAdmitted {initial context : TheoryContext} {policy : AxiomPolicy} {cache : Array Theorem}
    (primitives : Primitives initial) (frame : Frame.{w} initial policy context cache)
    (invariant : ReferenceInvariant frame.family)
    (instances : InstanceWitnesses) (name : Name) (source : SourceTerm)
    (result : ContextConstantDefinitionResult)
    (admitted : admitConstantInTheory context instances name source = some result)
    (formed : TheoremFormed result.context.signature result.output.definitionTheorem) :
    ReferenceInvariant (frame.constantAdmitted primitives instances name source result admitted formed).family :=
  constant_definition_invariant primitives frame.family invariant instances name source result admitted

theorem constant {initial context : TheoryContext} {policy : AxiomPolicy} [DecidablePred policy]
    {cache : Array Theorem} (primitives : Primitives initial) (frame : Frame.{w} initial policy context cache)
    (invariant : ReferenceInvariant frame.family)
    (origin : ProofExecution.Origin) (name : Name) (source : SourceTerm) (instances : InstanceWitnesses)
    (output : ProofExecution.Registered.Output)
    (accepted : (ProofExecution.Registered.Command.constant origin name source instances).check policy context cache = some output) :
    ReferenceInvariant (frame.constant primitives origin name source instances output accepted).family := by
  unfold Frame.constant
  apply transfer
  apply constantAdmitted
  exact invariant

theorem typeAdmitted {initial context : TheoryContext} {policy : AxiomPolicy} {cache : Array Theorem}
    (primitives : Primitives initial) (frame : Frame.{w} initial policy context cache)
    (invariant : ReferenceInvariant frame.family)
    (instances : InstanceWitnesses) (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult)
    (admitted : admitSourceTypeInTheory context instances request = some result)
    (known : request.existence ∈ cache)
    (formed : TheoremFormed result.context.signature result.output.abstractionRepresentationTheorem ∧
      TheoremFormed result.context.signature result.output.representationAbstractionTheorem) :
    ReferenceInvariant (frame.typeAdmitted primitives instances request result admitted known formed).family :=
  type_definition_invariant primitives frame.family invariant admitted (frame.existence_provable admitted known)

theorem typeDefinition {initial context : TheoryContext} {policy : AxiomPolicy} [DecidablePred policy]
    {cache : Array Theorem} (primitives : Primitives initial) (frame : Frame.{w} initial policy context cache)
    (invariant : ReferenceInvariant frame.family)
    (origin : ProofExecution.Origin) (request : TypeOperatorDefinitionRequest)
    (index : Nat) (instances : InstanceWitnesses) (output : ProofExecution.Registered.Output)
    (accepted : (ProofExecution.Registered.Command.typeDefinition origin request index instances).check policy context cache = some output) :
    ReferenceInvariant (frame.typeDefinition primitives origin request index instances output accepted).family := by
  unfold Frame.typeDefinition
  apply transfer
  apply typeAdmitted
  exact invariant

theorem proof {initial context : TheoryContext} {policy : AxiomPolicy} [DecidablePred policy]
    {cache : Array Theorem} (frame : Frame.{w} initial policy context cache)
    (invariant : ReferenceInvariant frame.family)
    (node : ProofExecution.Receipt) (instances : InstanceWitnesses) (output : ProofExecution.Registered.Output)
    (accepted : (ProofExecution.Registered.Command.proof node instances).check policy context cache = some output) :
    ReferenceInvariant (frame.proof node instances output accepted).family := invariant

theorem command {initial context : TheoryContext} {policy : AxiomPolicy} [DecidablePred policy]
    {cache : Array Theorem} (primitives : Primitives initial) (frame : Frame.{w} initial policy context cache)
    (invariant : ReferenceInvariant frame.family) (next : ProofExecution.Registered.Command)
    (output : ProofExecution.Registered.Output) (accepted : next.check policy context cache = some output) :
    ReferenceInvariant (frame.command primitives next output accepted).family := by
  cases next with
  | proof node instances => exact proof frame invariant node instances output accepted
  | constant origin name source instances => exact constant primitives frame invariant origin name source instances output accepted
  | typeDefinition origin request index instances => exact typeDefinition primitives frame invariant origin request index instances output accepted
theorem apply {initial : TheoryContext} {policy : AxiomPolicy} [DecidablePred policy]
    (primitives : Primitives initial) (before after : ProofExecution.Registered.State)
    (frame : Frame.{w} initial policy before.context before.cache)
    (invariant : ReferenceInvariant frame.family) (next : ProofExecution.Registered.Command)
    (accepted : ProofExecution.Registered.apply policy before next = some after) :
    ReferenceInvariant (Frame.apply primitives before after frame next accepted).family := by
  unfold Frame.apply
  apply transfer
  apply command
  exact invariant

theorem replay {initial : TheoryContext} {policy : AxiomPolicy} [DecidablePred policy]
    (primitives : Primitives initial) (before after : ProofExecution.Registered.State)
    (frame : Frame.{w} initial policy before.context before.cache)
    (invariant : ReferenceInvariant frame.family) (commands : List ProofExecution.Registered.Command)
    (accepted : ProofExecution.Registered.replayFrom policy before commands = some after) :
    ReferenceInvariant (Frame.replay primitives before after frame commands accepted).family := by
  induction commands generalizing before with
  | nil =>
    rw [Frame.replay]
    apply transfer
    exact invariant
  | cons head tail ih =>
    rw [Frame.replay]
    apply ih
    apply ReferenceInvariant.apply
    exact invariant

end ReferenceInvariant

noncomputable def initialReferenceFrame :
    Frame.{w} SourceProfile.primitiveContext emptyAxiomPolicy SourceProfile.primitiveContext #[] :=
  Frame.emptyWithFamily referenceReduct (by intro sequent forbidden; cases forbidden)

theorem initialReferenceFrame_invariant : ReferenceInvariant initialReferenceFrame.{w}.family :=
  referenceReduct_invariant

@[irreducible] noncomputable def replayedReferenceFrame :
    Frame.{w} SourceProfile.primitiveContext emptyAxiomPolicy referenceState.context referenceState.cache :=
  Frame.replay primitives (ProofExecution.Registered.empty SourceProfile.primitiveContext)
    referenceState initialReferenceFrame referenceCommands reference_replayed

theorem replayedReferenceFrame_invariant : ReferenceInvariant replayedReferenceFrame.{w}.family := by
  unfold replayedReferenceFrame
  exact ReferenceInvariant.replay primitives (ProofExecution.Registered.empty SourceProfile.primitiveContext)
    referenceState initialReferenceFrame initialReferenceFrame_invariant referenceCommands reference_replayed

theorem initial_truth_undeclared :
    SourceProfile.primitiveContext.signature.constants StandardTheoryInterpretation.Source.truthResult.output.constant = none :=
  ConstantAdmission.admitted_identity_fresh StandardTheoryInterpretation.Source.truthAdmitted

theorem initial_truth_formation_refused :
    ¬ AnnotationsFormed SourceProfile.primitiveContext.signature
      (.const StandardTheoryInterpretation.Source.truthResult.output.constant Ty.bool) := by
  intro formed
  cases formed with
  | constant _ declared =>
    obtain ⟨schema,substitution,registered,_⟩ := declared
    rw [initial_truth_undeclared] at registered
    cases registered


def withSentence (current : AxiomPolicy) (sentence : SourceSentence) : AxiomPolicy :=
  fun sequent => current sequent ∨ sequent = sentence.sequent

instance {current : AxiomPolicy} [DecidablePred current] (sentence : SourceSentence) :
    DecidablePred (withSentence current sentence) := fun _ => inferInstanceAs (Decidable (_ ∨ _))

noncomputable def adjoinReference {initial context : TheoryContext} {current : AxiomPolicy}
    {cache : Array Theorem} (primitives : Primitives initial) (frame : Frame.{w} initial current context cache)
    (invariant : ReferenceInvariant frame.family) (sentence : SourceSentence) (member : sentence ∈ sentences)
    (formed : AnnotationsFormed context.signature sentence.canonical.term) :
    Frame.{w} initial (withSentence current sentence) context cache :=
  frame.adjoinSchemas primitives [sentence.formula]
    (by intro formula present; obtain rfl := List.mem_singleton.mp present
        exact commitment_ordinary (List.mem_map.mpr ⟨sentence,member,rfl⟩))
    (by intro formula present; obtain rfl := List.mem_singleton.mp present
        exact ⟨[],sentence.canonical.term,sentence.formula,sentence.translated,formed,ContextFormed.nil _,rfl⟩)
    (by intro other assignment formula present; obtain rfl := List.mem_singleton.mp present
        exact invariant.models frame.family other assignment
          (List.mem_append_right _ (List.mem_map.mpr ⟨sentence,member,rfl⟩)))
    (withSentence current sentence) (fun _ permitted => Or.inl permitted)
    (by
      intro sequent permitted
      rcases permitted with old | rfl
      · obtain ⟨formula,translated,proven⟩ := frame.authorized sequent old
        refine ⟨formula,translated,HOL.ClosedTheorySet.provable_mono ?_ proven⟩
        rintro proposition (earlier | hypothesis)
        · obtain ⟨schema,present,image⟩ := earlier
          exact Or.inl ⟨schema,List.mem_append_left _ present,image⟩
        · exact Or.inr hypothesis
      · apply (translatedProvable_iff_compositionallyProvable _ _).mpr
        exact ⟨sentence.formula,sentence.translated,HOL.ClosedTheorySet.provable_of_mem
          (Or.inl ⟨sentence.formula,List.mem_append_right _ List.mem_cons_self,TypeImageOrbit.original⟩)⟩)

theorem adjoinReference_invariant {initial context : TheoryContext} {current : AxiomPolicy}
    {cache : Array Theorem} (primitives : Primitives initial) (frame : Frame.{w} initial current context cache)
    (invariant : ReferenceInvariant frame.family) (sentence : SourceSentence) (member : sentence ∈ sentences)
    (formed : AnnotationsFormed context.signature sentence.canonical.term) :
    ReferenceInvariant (adjoinReference primitives frame invariant sentence member formed).family := invariant

theorem withSentence_subset {current : AxiomPolicy}
    (included : ∀ sequent, current sequent → policy sequent)
    (sentence : SourceSentence) (member : sentence ∈ sentences) :
    ∀ sequent, withSentence current sentence sequent → policy sequent := by
  rintro sequent (earlier | rfl)
  · exact included sequent earlier
  · change sentence.sequent ∈ sentences.map SourceSentence.sequent
    exact List.mem_map.mpr ⟨sentence,member,rfl⟩

structure ProfileFrame (state : Registered.State) : Type (w+2) where
  current : AxiomPolicy
  decision : DecidablePred current
  frame : Frame.{w} SourceProfile.primitiveContext current state.context state.cache
  included : ∀ sequent, current sequent → policy sequent
  invariant : ReferenceInvariant frame.family

noncomputable def initialProfileFrame : ProfileFrame.{w} (Registered.empty SourceProfile.primitiveContext) where
  current := emptyAxiomPolicy
  decision := inferInstance
  frame := initialReferenceFrame
  included := by intro sequent impossible; cases impossible
  invariant := initialReferenceFrame_invariant

noncomputable def ProfileFrame.receive {before after : Registered.State} (state : ProfileFrame.{w} before)
    (command : Command)
    (accepted : @Registered.apply state.current state.decision before command = some after) :
    ProfileFrame.{w} after where
  current := state.current
  decision := state.decision
  frame := @Frame.apply _ state.current state.decision primitives before after state.frame command accepted
  included := state.included
  invariant := @ReferenceInvariant.apply _ state.current state.decision primitives before after state.frame
    state.invariant command accepted

noncomputable def ProfileFrame.adjoin {before : Registered.State} (state : ProfileFrame.{w} before)
    (sentence : SourceSentence) (member : sentence ∈ sentences)
    (formed : AnnotationsFormed before.context.signature sentence.canonical.term) :
    ProfileFrame.{w} before := by
  letI := state.decision
  exact {
    current := withSentence state.current sentence
    decision := inferInstance
    frame := adjoinReference primitives state.frame state.invariant sentence member formed
    included := withSentence_subset state.included sentence member
    invariant := adjoinReference_invariant primitives state.frame state.invariant sentence member formed }

noncomputable def ProfileFrame.advance {before after : Registered.State} (state : ProfileFrame.{w} before)
    (command : Command) (accepted : Registered.apply policy before command = some after) :
    ProfileFrame.{w} after := by
  letI := state.decision
  cases requested : command.requestedAxiom with
  | none =>
    apply state.receive command
    rw [Registered.apply_policy_congr state.current policy before command]
    · exact accepted
    · intro sequent asked
      rw [requested] at asked
      cases asked
  | some sequent =>
    let output := (Registered.apply_check_exists accepted).choose
    have checked := (Registered.apply_check_exists accepted).choose_spec
    obtain ⟨allowed,formed⟩ := Registered.requested_axiom_formed requested checked
    change sequent ∈ sentences.map SourceSentence.sequent at allowed
    let sentence := (List.mem_map.mp allowed).choose
    have member := (List.mem_map.mp allowed).choose_spec.1
    have same := (List.mem_map.mp allowed).choose_spec.2
    have sentenceFormed : AnnotationsFormed before.context.signature sentence.canonical.term := by
      change AnnotationsFormed before.context.signature sentence.sequent.concl.term
      rw [same]
      exact formed
    let next := state.adjoin sentence member sentenceFormed
    letI := next.decision
    apply next.receive command
    rw [Registered.apply_policy_congr next.current policy before command]
    · exact accepted
    · intro candidate asked
      have targetEq : candidate = sentence.sequent :=
        (Option.some.inj (asked.symm.trans requested)).trans same.symm
      constructor
      · intro _
        change candidate ∈ sentences.map SourceSentence.sequent
        exact List.mem_map.mpr ⟨sentence,member,targetEq.symm⟩
      · intro _
        exact Or.inr targetEq

theorem ProfileFrame.replay_exists {before after : Registered.State} (state : ProfileFrame.{w} before)
    (commands : List Command) (accepted : Registered.replayFrom policy before commands = some after) :
    Nonempty (ProfileFrame.{w} after) := by
  induction commands generalizing before with
  | nil =>
    have same : before = after := Option.some.inj accepted
    exact ⟨same ▸ state⟩
  | cons head tail ih =>
    cases applied : Registered.apply policy before head with
    | none => simp [Registered.replayFrom,applied] at accepted
    | some middle =>
      have rest : Registered.replayFrom policy middle tail = some after := by
        simpa [Registered.replayFrom,applied] using accepted
      exact ih (state.advance head applied) rest

/-- Accepted replay in the original command order constructs a model frame.
Only the axioms actually requested are adjoined to the interpreted background. -/
noncomputable def sourceReplayFrame (commands : List Command) (after : Registered.State)
    (accepted : Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) commands = some after) :
    ProfileFrame.{w} after :=
  Classical.choice (ProfileFrame.replay_exists initialProfileFrame commands accepted)

theorem source_replay_models (commands : List Command) (after : Registered.State)
    (accepted : Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) commands = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (fact : Theorem) (known : fact ∈ after.cache) :
    ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
      ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp,
          ((sourceReplayFrame commands after accepted).frame.model other assignment).models hypothesis) →
        ((sourceReplayFrame commands after accepted).frame.model other assignment).models formula) :=
  (sourceReplayFrame commands after accepted).frame.cached_models other assignment known

theorem source_replay_refuses_falsity (commands : List Command) (after : Registered.State)
    (accepted : Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) commands = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (fact : Theorem) (empty : fact.sequent.hyp = ∅)
    (translated : Translates [] fact.sequent.concl.term .prop PrimitiveSentences.falsityFormula) :
    fact ∉ after.cache :=
  (sourceReplayFrame commands after accepted).frame.cached_falsity_refused other assignment fact empty translated

/-- One constructed full-domain model validates the complete received cache,
with each cached sequent retaining its own hypotheses. -/
theorem source_replay_model (commands : List Command) (after : Registered.State)
    (accepted : Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) commands = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∃ model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol, model.FullDomains ∧
      ∀ fact ∈ after.cache, ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
        ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, model.models hypothesis) → model.models formula) := by
  let completed := sourceReplayFrame commands after accepted
  refine ⟨completed.frame.model other assignment,completed.frame.model_fullDomains other assignment,?_⟩
  intro fact known
  exact completed.frame.cached_models other assignment known

theorem source_export_model (events : List ExportReplay.Event) (after : ExportReplay.State)
    (accepted : ExportReplay.replayFrom policy (ExportReplay.empty SourceProfile.primitiveContext) events = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∃ model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol, model.FullDomains ∧
      ∀ fact ∈ after.registered.cache, ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
        ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, model.models hypothesis) → model.models formula) :=
  source_replay_model (events.map ExportReplay.Event.command) after.registered
    (ExportReplay.replayFrom_registered policy _ events after accepted) other assignment

/-- Export reception preserves the exact registered command order, so its
accepted cache has the constructed source-profile model. -/
theorem source_export_models (events : List ExportReplay.Event) (after : ExportReplay.State)
    (accepted : ExportReplay.replayFrom policy (ExportReplay.empty SourceProfile.primitiveContext) events = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (fact : Theorem) (known : fact ∈ after.registered.cache) :
    ∃ model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol, model.FullDomains ∧
      ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
        ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, model.models hypothesis) → model.models formula) := by
  have checked := ExportReplay.replayFrom_registered policy _ events after accepted
  let completed := sourceReplayFrame (events.map ExportReplay.Event.command) after.registered checked
  refine ⟨completed.frame.model other assignment,completed.frame.model_fullDomains other assignment,?_⟩
  exact completed.frame.cached_models other assignment known

theorem source_export_root_models (events : List ExportReplay.Event) (after : ExportReplay.State)
    (accepted : ExportReplay.replayFrom policy (ExportReplay.empty SourceProfile.primitiveContext) events = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {id : Nat} {claim : Sequent} {fact : Theorem} (found : ExportReplay.root? after id claim = some fact) :
    ∃ model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol, model.FullDomains ∧
      ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
        ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, model.models hypothesis) → model.models formula) :=
  source_export_models events after accepted other assignment fact (ExportReplay.root_mem_cache found)

end Mettapedia.Languages.HOLLight.SourceProfileModels
