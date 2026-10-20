import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.SelectionEquivariance
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationPrincipalAlpha
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Exact finite-presentation simulation of the application type fold

The repaired runtime carries equality-class bindings, while exact spec type
packages carry a normal finite substitution.  The simulation state relates
the finite presentation to the already-sealed native spec binding theory,
and relates that theory to LeaTTa independently through `TypeBindingState`.

Each successful runtime type match is reconstructed as one presentation
step by semantic completeness.  The resulting finite presentation is not
identified with LeaTTa's binding list; their declared-return observations
are related only up to the alpha theorem for mutually principal models.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationFoldConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation
open Spec.Type.Presentation.Theory
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.Presentation.Completeness
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.PrincipalAlpha
open Spec.Type.Presentation.Exact
open Spec.Type.RuntimeRefinement
open LeaTTaBridge
open LeaTTaSpecConformance
open LeaTTaTypeConformance

/-- The exact presentation carried alongside the semantic spec/LeaTTa
binding state.  `specSolutions` is representation-independent equality of
native solution sets; it does not identify the finite substitution with the
spec binding record. -/
structure TypePresentationSimulationState
    (presentation : TypeSubst) (spec : Bindings)
    (lea : Metta.Bindings) : Prop where
  normal : presentation.Normal
  specSolutions : ∀ valuation,
    TypeSubstSatisfied valuation presentation ↔
      TypeBindingSatisfied valuation spec
  semantic : TypeBindingState spec lea

/-- Empty finite, spec, and runtime presentations establish the simulation
state used at every application-inference boundary. -/
theorem typePresentationSimulationState_empty :
    TypePresentationSimulationState [] Bindings.empty
      Metta.Bindings.empty := by
  refine ⟨TypeSubst.normal_empty, ?_, typeBindingState_empty⟩
  intro valuation
  simp [TypeSubstSatisfied, TypeBindingSatisfied, Bindings.empty]

/-- A finite presentation paired with a reachable runtime binding theory is
semantically supported by the variables occurring in that runtime theory.
The presentation may use different private spellings syntactically; only
its complete solution theory is asserted to be insensitive away from the
runtime support. -/
theorem TypePresentationSimulationState.satisfied_congr_on_runtimeVars
    {presentation : TypeSubst} {spec : Bindings}
    {runtime : Metta.Bindings}
    (state : TypePresentationSimulationState presentation spec runtime)
    {left right : String → Atom}
    (agrees : ∀ name, name ∈ runtime.vars → left name = right name) :
    TypeSubstSatisfied left presentation ↔
      TypeSubstSatisfied right presentation := by
  rw [state.specSolutions left, state.specSolutions right]
  exact state.semantic.specSatisfied_congr_on_runtimeVars agrees

/-- Full one-step presentation simulation.  Besides the finite-presentation
derivation, retain the native core-plus-R2 match consumed by type-service
relations; projecting it away would force later boundaries to reconstruct the
same match from solution semantics.  The resulting normal finite presentation
has exactly the same native specification solution theory. -/
theorem TypePresentationSimulationState.matchTypeFull
    {presentation : TypeSubst} {spec : Bindings}
    {lea leaOutput : Metta.Bindings}
    (state : TypePresentationSimulationState presentation spec lea)
    (expected actual : Atom)
    (success : Metta.Minimal.matchType lea
      (encodeModelAtom expected) (encodeModelAtom actual) = some leaOutput) :
    ∃ presentationOutput specOutput,
      CorePlusR2TypePresentationMatchRel
          presentation expected actual presentationOutput ∧
        CorePlusR2TypeMatchRel expected actual spec specOutput ∧
        TypePresentationSimulationState
          presentationOutput specOutput leaOutput := by
  obtain ⟨specOutput, specMatch, semanticOutput⟩ :=
    matchType_corePlusR2_sound state.semantic success
  obtain ⟨valuation, outputSatisfied⟩ :=
    semanticOutput.specSatisfiable
  have parts := (specMatch.solutions valuation).mp outputSatisfied
  have presentationSatisfied :
      TypeSubstSatisfied valuation presentation :=
    (state.specSolutions valuation).mpr parts.1
  obtain ⟨presentationOutput, presentationMatch,
      outputNormal, _outputSatisfied⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      state.normal presentationSatisfied expected actual parts.2
  refine ⟨presentationOutput, specOutput, presentationMatch, specMatch,
    ⟨outputNormal, ?_, semanticOutput⟩⟩
  intro otherValuation
  rw [Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
        presentationMatch state.normal otherValuation,
    state.specSolutions otherValuation,
    ← specMatch.solutions otherValuation]

/-- Present any satisfiable native core-plus-R2 match as one exact normal
finite substitution extending the incoming presentation.  Unlike
`matchTypeFull`, this theorem is executable-independent: it starts from the
specification match relation itself and retains exactly the finite evidence
needed by alpha-transport and evaluator completeness. -/
theorem TypePresentationSimulationState.presentCorePlusR2
    {presentation : TypeSubst} {spec specOutput : Bindings}
    {runtime : Metta.Bindings} {expected actual : Atom}
    (state : TypePresentationSimulationState presentation spec runtime)
    (derivation : CorePlusR2TypeMatchRel expected actual spec specOutput) :
    ∃ presentationOutput,
      CorePlusR2TypePresentationMatchRel
          presentation expected actual presentationOutput ∧
        presentationOutput.Normal ∧
        ∀ valuation,
          TypeSubstSatisfied valuation presentationOutput ↔
            TypeBindingSatisfied valuation specOutput := by
  obtain ⟨valuation, outputSatisfied⟩ := derivation.satisfiable
  obtain ⟨incomingSatisfied, consistent⟩ :=
    (derivation.solutions valuation).mp outputSatisfied
  have presentationSatisfied :
      TypeSubstSatisfied valuation presentation :=
    (state.specSolutions valuation).mpr incomingSatisfied
  obtain ⟨presentationOutput, presentationMatch,
      outputNormal, _outputSatisfied⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      state.normal presentationSatisfied expected actual consistent
  refine ⟨presentationOutput, presentationMatch, outputNormal, ?_⟩
  intro otherValuation
  rw [Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
        presentationMatch state.normal otherValuation,
    state.specSolutions otherValuation,
    ← derivation.solutions otherValuation]

/-- Compatibility projection for consumers that need only the finite
presentation derivation and the resulting simulation state. -/
theorem TypePresentationSimulationState.matchType
    {presentation : TypeSubst} {spec : Bindings}
    {lea leaOutput : Metta.Bindings}
    (state : TypePresentationSimulationState presentation spec lea)
    (expected actual : Atom)
    (success : Metta.Minimal.matchType lea
      (encodeModelAtom expected) (encodeModelAtom actual) = some leaOutput) :
    ∃ presentationOutput specOutput,
      CorePlusR2TypePresentationMatchRel
          presentation expected actual presentationOutput ∧
        TypePresentationSimulationState
          presentationOutput specOutput leaOutput := by
  obtain ⟨presentationOutput, specOutput, presentationMatch,
      _specMatch, outputState⟩ :=
    state.matchTypeFull expected actual success
  exact ⟨presentationOutput, specOutput, presentationMatch, outputState⟩

/-- The finite presentation and LeaTTa's canonical runtime resolver observe
any declared type up to alpha-renaming. -/
theorem TypePresentationSimulationState.returnAlpha
    {presentation : TypeSubst} {spec : Bindings}
    {lea : Metta.Bindings}
    (state : TypePresentationSimulationState presentation spec lea)
    (declared : Atom) :
    ObservedTypeAlphaRel
      (presentation.apply declared)
      (decodeModelAtom
        (Metta.instantiate lea (encodeModelAtom declared))) := by
  let leaModel := leaClassSolution lea
  let nativeModel : String → Atom :=
    fun name => decodeModelAtom (leaModel name)
  have nativeModelSatisfied :
      TypeSubstSatisfied nativeModel presentation := by
    have specModel : HEBindingSatisfied leaModel spec :=
      (state.semantic.theory leaModel).mpr state.semantic.runtime.canonical.1
    have nativeSpecModel :=
      specTypeBindingSatisfied_of_heBindingSatisfied specModel
    exact (state.specSolutions nativeModel).mpr nativeSpecModel
  have presentationRefinesModel :
      ∃ post : String → Atom, ∀ name,
        presentedValuation presentation name =
          applyTypeValuation post (nativeModel name) := by
    let presentationModel := presentedValuation presentation
    let leaPresentationModel : String → Metta.Atom :=
      fun name => encodeModelAtom (presentationModel name)
    have presentationSatisfied :
        TypeSubstSatisfied presentationModel presentation :=
      normal_presentedValuation_satisfied state.normal
    have specPresentationSatisfied :
        TypeBindingSatisfied presentationModel spec :=
      (state.specSolutions presentationModel).mp presentationSatisfied
    have heaPresentationSatisfied :
        HEBindingSatisfied leaPresentationModel spec :=
      heBindingSatisfied_of_specTypeBindingSatisfied
        specPresentationSatisfied
    have leaPresentationSatisfied :
        LeaBindingSatisfied leaPresentationModel lea :=
      (state.semantic.theory leaPresentationModel).mp
        heaPresentationSatisfied
    obtain ⟨leaPost, hleaPost⟩ :=
      state.semantic.runtime.canonical.2
        leaPresentationModel leaPresentationSatisfied
    refine ⟨fun name => decodeModelAtom (leaPost name), ?_⟩
    intro name
    have decoded := congrArg decodeModelAtom (hleaPost name)
    rw [decodeModelAtom_applyClassSolution_any] at decoded
    simpa [leaPresentationModel, presentationModel,
      nativeModel, leaModel] using decoded
  have alpha := observedTypeAlpha_of_mutuallyPrincipal state.normal
    nativeModelSatisfied presentationRefinesModel declared
  simpa [nativeModel, leaModel, ← decodeModelAtom_applyClassSolution,
    applyClassSolution_lea_eq_instantiate] using alpha

/-- Repaired LeaTTa's left-to-right argument-type fold is realized by the
executable-independent finite-presentation fold, preserving the complete
simulation state. -/
theorem matchApplicationTypeArguments_presentation_sound :
    ∀ (expectedTypes actualTypes : List Atom)
      {presentation : TypeSubst} {spec : Bindings}
      {lea leaOutput : Metta.Bindings},
      TypePresentationSimulationState presentation spec lea →
      Metta.Minimal.matchApplicationTypeArguments lea
        (encodeModelAtoms expectedTypes) (encodeModelAtoms actualTypes) =
          some leaOutput →
      ∃ presentationOutput specOutput,
        PresentationArgumentListMatchRel expectedTypes actualTypes
            presentation presentationOutput ∧
          TypePresentationSimulationState
            presentationOutput specOutput leaOutput := by
  intro expectedTypes
  induction expectedTypes with
  | nil =>
      intro actualTypes presentation spec lea leaOutput state success
      cases actualTypes with
      | nil =>
          have same : lea = leaOutput := by
            simpa [encodeModelAtoms,
              Metta.Minimal.matchApplicationTypeArguments] using success
          subst leaOutput
          exact ⟨presentation, spec,
            PresentationArgumentListMatchRel.nil presentation, state⟩
      | cons actual actualTypes =>
          simp [encodeModelAtoms,
            Metta.Minimal.matchApplicationTypeArguments] at success
  | cons expected expectedTypes inductionHypothesis =>
      intro actualTypes presentation spec lea leaOutput state success
      cases actualTypes with
      | nil =>
          simp [encodeModelAtoms,
            Metta.Minimal.matchApplicationTypeArguments] at success
      | cons actual actualTypes =>
          simp only [encodeModelAtoms,
            Metta.Minimal.matchApplicationTypeArguments] at success
          generalize nextEquation : Metta.Minimal.matchType lea
            (encodeModelAtom expected) (encodeModelAtom actual) = next at success
          cases next with
          | none => simp at success
          | some leaNext =>
              obtain ⟨presentationNext, specNext,
                  headMatch, nextState⟩ :=
                state.matchType expected actual nextEquation
              obtain ⟨presentationOutput, specOutput,
                  tailMatch, outputState⟩ :=
                inductionHypothesis actualTypes nextState success
              exact ⟨presentationOutput, specOutput,
                PresentationArgumentListMatchRel.cons headMatch tailMatch,
                outputState⟩

/-- End-to-end fold boundary from empty input: the exact spec argument
presentation exists, and its emitted return is alpha-exactly LeaTTa's
instantiated return. -/
theorem matchApplicationTypeArguments_exact_return
    {expectedTypes actualTypes : List Atom}
    {leaOutput : Metta.Bindings} {returnType : Atom}
    (success : Metta.Minimal.matchApplicationTypeArguments
      Metta.Bindings.empty (encodeModelAtoms expectedTypes)
        (encodeModelAtoms actualTypes) = some leaOutput) :
    ∃ presentation specOutput,
      PresentationArgumentListMatchRel
          expectedTypes actualTypes [] presentation ∧
        TypePresentationSimulationState
          presentation specOutput leaOutput ∧
        ObservedTypeAlphaRel
          (presentation.apply returnType)
          (decodeModelAtom
            (Metta.instantiate leaOutput (encodeModelAtom returnType))) := by
  obtain ⟨presentation, specOutput, fold, state⟩ :=
    matchApplicationTypeArguments_presentation_sound
      expectedTypes actualTypes typePresentationSimulationState_empty success
  exact ⟨presentation, specOutput, fold, state,
    state.returnAlpha returnType⟩

/-! ## Boundary examples -/

/-- Positive: the empty application fold produces the empty exact
presentation and preserves its simulation state. -/
theorem empty_application_fold_exact :
    ∃ presentation specOutput,
      PresentationArgumentListMatchRel [] [] [] presentation ∧
        TypePresentationSimulationState presentation specOutput
          Metta.Bindings.empty := by
  exact ⟨[], Bindings.empty,
    PresentationArgumentListMatchRel.nil [],
    typePresentationSimulationState_empty⟩

/-- Negative: unequal argument arities admit no presentation derivation. -/
theorem unequal_arity_has_no_presentation
    (expected : Atom) :
    ¬∃ output,
      PresentationArgumentListMatchRel [expected] [] [] output := by
  rintro ⟨output, derivation⟩
  cases derivation

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationFoldConformance

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationFoldConformance
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation Spec.Type.Presentation
open Spec.Type.Presentation.Alpha Spec.Type.Presentation.ApplicationEquivariance
open Spec.Type.Presentation.Exact Spec.Type.Presentation.ExactNormal
open Spec.Type.Presentation.MatchSolutionTheory Spec.Type.Presentation.PrincipalAlpha
open Spec.Type.Presentation.Theory Spec.Type.Presentation.ScopeObservation
open Spec.Type.Presentation.SelectionEquivariance Spec.Type.RuntimeRefinement
open LeaTTaBridge LeaTTaTypeConformance

/-! Runtime binding-list instances of the independent scoped-observation laws. -/
/-- Runtime-support variant of
`transport_model_across_presentations_of_target_fresh`.

The exact right presentation may use an independent private spelling, so
syntactic support inclusion is neither required nor generally true.
`TypePresentationSimulationState` proves that its complete solution theory
depends only on the variables occurring in the runtime binding list; the
runtime candidate is fresh from exactly that support. -/
theorem PrivateCandidateAlphaRel.transport_model_across_presentations_of_runtime_target_fresh
    {fixedScope theoryScope observationScope : List String}
    {leftIncoming rightIncoming : TypeSubst}
    {rightSpec : Bindings} {runtimeBindings : Metta.Bindings}
    {expected leftActual rightActual : Atom}
    (alpha : PrivateCandidateAlphaRel fixedScope leftActual rightActual)
    (incomingEquiv : TypePresentationTheoryEquivAt
      theoryScope leftIncoming rightIncoming)
    (rightState : TypePresentationSimulationState
      rightIncoming rightSpec runtimeBindings)
    (rightTargetFresh : ∀ name,
      name ∈ TypeSubst.typeVars rightActual →
        name ∉ runtimeBindings.vars)
    (theoryCovered : ∀ name, name ∈ theoryScope → name ∈ fixedScope)
    (expectedObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ theoryScope)
    (observationObserved : ∀ name,
      name ∈ observationScope → name ∈ theoryScope)
    (leftModel : String → Atom)
    (leftSatisfied : TypeSubstSatisfied leftModel leftIncoming)
    (leftConsistent : CorePlusR2TypeConsistent
      leftModel expected leftActual) :
    ∃ rightModel,
      TypeSubstSatisfied rightModel rightIncoming ∧
        CorePlusR2TypeConsistent rightModel expected rightActual ∧
        ValuationsAgreeOn observationScope leftModel rightModel := by
  obtain ⟨permutation, fixed, candidateEquation⟩ :=
    alpha.exists_public_fixed_permutation
  obtain ⟨rightBase, rightBaseSatisfied, baseAgrees⟩ :=
    incomingEquiv.leftToRight leftModel leftSatisfied
  let transported : String → Atom := leftModel ∘ permutation.symm
  let rightModel : String → Atom := fun name =>
    if name ∈ TypeSubst.typeVars rightActual then
      transported name
    else
      rightBase name
  have inverseFixed : ∀ name, name ∈ fixedScope →
      permutation.symm name = name := by
    intro name member
    apply permutation.injective
    simp [fixed name member]
  have rightModelAgreesBaseOnRuntime :
      ValuationsAgreeOn runtimeBindings.vars rightBase rightModel := by
    intro name member
    have notCandidate : name ∉ TypeSubst.typeVars rightActual := by
      intro candidateMember
      exact rightTargetFresh name candidateMember member
    simp [rightModel, notCandidate]
  have rightSatisfied : TypeSubstSatisfied rightModel rightIncoming :=
    (rightState.satisfied_congr_on_runtimeVars
      rightModelAgreesBaseOnRuntime).mp rightBaseSatisfied
  have rightActualAvoids : ∀ name,
      name ∈ TypeSubst.typeVars rightActual → name ∉ fixedScope :=
    alpha.vars_avoid_fixedScope.2
  have expectedFixed :
      renameTypeVars permutation expected = expected := by
    calc
      renameTypeVars permutation expected =
          renameTypeVars id expected := by
        apply renameTypeVars_congr_on_typeVars expected
        intro name member
        exact fixed name (theoryCovered name (expectedObserved name member))
      _ = expected := renameTypeVars_id expected
  have transportedConsistent : CorePlusR2TypeConsistent transported
      expected rightActual := by
    have renamedConsistent : CorePlusR2TypeConsistent transported
        (renameTypeVars permutation expected)
        (renameTypeVars permutation leftActual) := by
      apply (corePlusR2TypeConsistent_rename_iff
        transported permutation expected leftActual).mpr
      simpa [transported, Function.comp_def] using leftConsistent
    simpa [expectedFixed, candidateEquation] using renamedConsistent
  have constraintAgreement : ∀ name,
      name ∈ TypeSubst.typeVars expected ++
          TypeSubst.typeVars rightActual →
        transported name = rightModel name := by
    intro name member
    rcases List.mem_append.mp member with expectedMember | actualMember
    · have theoryMember := expectedObserved name expectedMember
      have fixedMember := theoryCovered name theoryMember
      have notCandidate : name ∉ TypeSubst.typeVars rightActual := by
        intro candidateMember
        exact rightActualAvoids name candidateMember fixedMember
      simp [rightModel, notCandidate, transported, Function.comp_apply,
        inverseFixed name fixedMember, baseAgrees name theoryMember]
    · simp [rightModel, actualMember]
  have rightConsistent : CorePlusR2TypeConsistent rightModel
      expected rightActual :=
    (corePlusR2TypeConsistent_congr_of_typeVars
      expected rightActual constraintAgreement).mp transportedConsistent
  refine ⟨rightModel, rightSatisfied, rightConsistent, ?_⟩
  intro name member
  have theoryMember := observationObserved name member
  have fixedMember := theoryCovered name theoryMember
  have notCandidate : name ∉ TypeSubst.typeVars rightActual := by
    intro candidateMember
    exact rightActualAvoids name candidateMember fixedMember
  simpa [rightModel, notCandidate] using baseAgrees name theoryMember


/-- Cross a scoped specification/runtime boundary without identifying the
runtime presentation's private syntactic support.  The left candidate is
fresh from the finite specification presentation; the right candidate is
fresh from the runtime binding list that semantically supports its exact
branch presentation. -/
theorem TypeConstraintTheoryEquivAt.of_scopedIncoming_privateCandidateAlpha_runtimeSupport
    {fixedScope theoryScope observationScope : List String}
    {leftIncoming rightIncoming : TypeSubst}
    {rightSpec : Bindings} {runtimeBindings : Metta.Bindings}
    {expected leftActual rightActual : Atom}
    (incomingEquiv : TypePresentationTheoryEquivAt
      theoryScope leftIncoming rightIncoming)
    (rightState : TypePresentationSimulationState
      rightIncoming rightSpec runtimeBindings)
    (alpha : PrivateCandidateAlphaRel fixedScope leftActual rightActual)
    (leftTargetFresh : ∀ name,
      name ∈ TypeSubst.typeVars leftActual →
        name ∉ specBindingVars ⟨leftIncoming, []⟩)
    (rightTargetFresh : ∀ name,
      name ∈ TypeSubst.typeVars rightActual →
        name ∉ runtimeBindings.vars)
    (theoryCovered : ∀ name, name ∈ theoryScope → name ∈ fixedScope)
    (expectedObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ theoryScope)
    (observationObserved : ∀ name,
      name ∈ observationScope → name ∈ theoryScope) :
    TypeConstraintTheoryEquivAt observationScope
      leftIncoming expected leftActual
      rightIncoming expected rightActual := by
  have reverseAlpha :
      PrivateCandidateAlphaRel fixedScope rightActual leftActual := by
    rcases alpha with ⟨source, leftVariant, rightVariant⟩
    exact ⟨source, rightVariant, leftVariant⟩
  constructor
  · exact PrivateCandidateAlphaRel.transport_model_across_presentations_of_runtime_target_fresh
      alpha incomingEquiv rightState rightTargetFresh theoryCovered
        expectedObserved observationObserved
  · intro rightModel rightSatisfied rightConsistent
    obtain ⟨leftModel, leftSatisfied, leftConsistent, agrees⟩ :=
      reverseAlpha.transport_model_across_presentations_of_target_fresh
        incomingEquiv.symm leftTargetFresh theoryCovered expectedObserved
          observationObserved rightModel rightSatisfied rightConsistent
    exact ⟨leftModel, leftSatisfied, leftConsistent,
      fun name member => (agrees name member).symm⟩


/-- A static specification presentation and one runtime binding state agree
through an exact branch-local presentation, with only the comparison between
the two finite presentations restricted to the declared public scope. -/
def ScopedTypePresentationSimulationState
    (scope : List String) (specPresentation : TypeSubst)
    (runtimeBindings : Metta.Bindings) : Prop :=
  specPresentation.Normal ∧
    ∃ branchPresentation specBindings,
      TypePresentationSimulationState
          branchPresentation specBindings runtimeBindings ∧
        TypePresentationTheoryEquivAt
          scope specPresentation branchPresentation

/-- Exact same-spelling simulation is the reflexive case of scoped
simulation. -/
theorem ScopedTypePresentationSimulationState.ofExact
    {scope : List String} {presentation : TypeSubst}
    {spec : Bindings} {runtime : Metta.Bindings}
    (state : TypePresentationSimulationState presentation spec runtime) :
    ScopedTypePresentationSimulationState scope presentation runtime :=
  ⟨state.normal, presentation, spec, state,
    TypePresentationTheoryEquivAt.refl scope presentation⟩

/-- Scoped simulation is contravariant in its observation scope: agreement
at a larger finite scope immediately gives agreement at every smaller scope.
This is the boundary used after a private signature scan, where the recursive
matcher may temporarily observe signature variables that the evaluator seal
does not expose. -/
theorem ScopedTypePresentationSimulationState.mono
    {large small : List String} {presentation : TypeSubst}
    {runtime : Metta.Bindings}
    (state : ScopedTypePresentationSimulationState
      large presentation runtime)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    ScopedTypePresentationSimulationState small presentation runtime := by
  rcases state with
    ⟨normal, branchPresentation, specBindings,
      branchState, theory⟩
  exact ⟨normal, branchPresentation, specBindings, branchState,
    theory.mono subset⟩

/-- A scoped presentation state observes any declared type whose variables
lie in the public scope exactly as the repaired runtime does, up to private
alpha-renaming.  This is the diagnostic/policy projection of the semantic
state; it does not identify the private finite presentations syntactically. -/
theorem ScopedTypePresentationSimulationState.returnAlpha
    {scope : List String} {presentation : TypeSubst}
    {runtime : Metta.Bindings}
    (state : ScopedTypePresentationSimulationState
      scope presentation runtime)
    (declared : Atom)
    (declaredCovered : ∀ name,
      name ∈ TypeSubst.typeVars declared → name ∈ scope) :
    ObservedTypeAlphaRel
      (presentation.apply declared)
      (decodeModelAtom
        (Metta.instantiate runtime (encodeModelAtom declared))) := by
  rcases state with
    ⟨presentationNormal, branchPresentation, specBindings,
      branchState, presentationEquiv⟩
  exact ObservedTypeAlphaRel.trans
    (presentationEquiv.observedTypeAlpha presentationNormal
      branchState.normal declared declaredCovered)
    (branchState.returnAlpha declared)

/-- Pointwise scoped simulation for an ordered branch list. -/
def ScopedTypePresentationSimulationStates
    (scope : List String) (presentations : List TypeSubst)
    (runtimeBindings : List Metta.Bindings) : Prop :=
  List.Forall₂
    (ScopedTypePresentationSimulationState scope)
    presentations runtimeBindings

/-- Pointwise scope weakening for an ordered branch list. -/
theorem scopedTypePresentationSimulationStates_mono
    {large small : List String} {presentations : List TypeSubst}
    {runtimeBindings : List Metta.Bindings}
    (states : ScopedTypePresentationSimulationStates
      large presentations runtimeBindings)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    ScopedTypePresentationSimulationStates
      small presentations runtimeBindings := by
  exact states.imp fun _ _ state => state.mono subset

/-! ## Boundary canaries -/

/-- Post-composing a raw-signature runtime simulation with a public-fixed
signature localization yields the corresponding localized simulation. -/
theorem TypePresentationPermutationState.composeScopedRuntime
    {permutation : Equiv.Perm String} {raw localized : TypeSubst}
    {scope : List String} {runtime : Metta.Bindings}
    (state : TypePresentationPermutationState permutation raw localized)
    (scopeFixed : ∀ name, name ∈ scope → permutation name = name)
    (runtimeState : ScopedTypePresentationSimulationState
      scope raw runtime) :
    ScopedTypePresentationSimulationState scope localized runtime := by
  rcases runtimeState with
    ⟨_rawNormal, branchPresentation, specBindings,
      branchState, rawBranchEquiv⟩
  exact ⟨state.rightNormal, branchPresentation, specBindings, branchState,
    (state.theoryEquivAt scope scopeFixed).symm.trans rawBranchEquiv⟩


end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationFoldConformance
