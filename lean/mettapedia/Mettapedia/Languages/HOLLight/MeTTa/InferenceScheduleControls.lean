import Mettapedia.Languages.HOLLight.MeTTa.InferenceSchedule

/-!
# A mixed source history starts empty and reuses earned evidence

Polymorphic reflexivity earns the first record. Transitivity retrieves it
twice, retaining both premise occurrences. Type instantiation then consumes
that returned record. The actual source replay loop executes the history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.InferenceScheduleControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters CacheAuthorization Eval InferenceSchedule
open Effects (State)

private theorem primitive_function : SourceProfile.primitiveContext.signature.typeOperators TypeOp.function = some 2 :=
  (ContextControls.core_includes.trans
    (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes)).1
    _ _ ContextControls.function_registered

private theorem primitive_boolean : TypeFormed SourceProfile.primitiveContext.signature Ty.bool :=
  ContextControls.boolean_formed.mono (ContextControls.core_includes.trans
    (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes))

private theorem primitive_equality : SourceProfile.primitiveContext.signature.constants Const.equality =
    some (Ty.equality (.var ContextControls.equalityParameter)) :=
  (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes).2 _ _
    (ContextControls.baseContext.addConstant_registered _ _ ContextControls.equality_schema_formed _)

def frame : InferenceSchedule.Frame :=
  { policy := emptyAxiomPolicy
    world := SourceProfile.primitiveContext
    table := DeclarationTable.sourcePrimitive
    origins := fun _ => .symbol "HOL:Primitive"
    constants := DeclarationTable.primitiveIdentity
    identified := DeclarationTable.primitiveIdentity_identifies _
    equalityIdentity := rfl
    functionArity := primitive_function
    equalityParameter := ContextControls.equalityParameter
    equalityRegistered := primitive_equality
    booleanFormed := primitive_boolean
    axioms := .symbol "HOL:Nil" }

def parameter : Name := Name.global "A"
def source : CheckedSourceTerm :=
  ⟨.var (Name.global "value") (.var parameter), .var parameter, by simp [SourceTerm.inferType]⟩

private theorem source_formed : AnnotationsFormed frame.world.signature source.canonical.term := by
  have formed : TypeFormed frame.world.signature (.var parameter) := by simp [TypeFormed]
  have free : AnnotationsFormed frame.world.signature (.free ⟨Name.global "value", .var parameter⟩) := .free formed
  simpa only [source, CheckedSourceTerm.canonical, SourceTerm.toDB, boundIndex] using free

private theorem equality_formed : TypeFormed frame.world.signature (Ty.equality source.ty) :=
  TypeFormed.function _ frame.functionArity (by simp [source, TypeFormed])
    (TypeFormed.function _ frame.functionArity (by simp [source, TypeFormed]) frame.booleanFormed)

private theorem equality_registered : ConstantInstance frame.world.signature Const.equality (Ty.equality source.ty) := by
  refine ⟨Ty.equality (.var ContextControls.equalityParameter),
    ⟨[(ContextControls.equalityParameter, .var parameter)]⟩, frame.equalityRegistered, ?_⟩
  simp [source, TypeSubst.lookup, Ty.equality, Ty.function]

def firstKey : Atom := .grounded (.string "poly-refl")
def secondKey : Atom := .grounded (.string "shared-trans")
def thirdKey : Atom := .grounded (.string "bool-instance")

def reflexivity (cache : Cache) : Invocation frame cache :=
  .refl source (by simp [source, parameter, Name.global, TermReading.SourceResolved, TypeFormation.Resolved])
    source_formed equality_formed equality_registered

private theorem refl_view (record : Record)
    (logical : (reflexivity []).LogicalResult record) :
    CanonicalTerm.EqualityViewSemantics record.conclusion source.canonical source.canonical := by
  obtain ⟨equality, constructed, parts⟩ := logical
  exact ⟨rfl, (congrArg CanonicalTerm.term parts.2.2).trans constructed.2⟩

def transitivity (record : Record) (logical : (reflexivity []).LogicalResult record) :
    Invocation frame [(firstKey, record)] :=
  .trans firstKey firstKey record record rfl rfl source.canonical source.canonical source.canonical
    (refl_view record logical) (refl_view record logical)

def specialization (first second : Record) : Invocation frame [(secondKey, second), (firstKey, first)] :=
  .instType [(Ty.bool, Ty.var parameter)] secondKey second
    (by
      intro entry member
      simp only [List.mem_singleton] at member
      subst entry
      refine ⟨?_, by simp [parameter, Name.global, TypeFormation.Resolved]⟩
      simp only [Ty.bool, TypeFormation.Resolved]
      have formed := primitive_boolean
      simp only [Ty.bool, TypeFormed] at formed
      exact ⟨⟨0, formed.1⟩, by simp⟩)
    (by
      intro entry member
      simp only [List.mem_singleton] at member
      subst entry
      exact ⟨primitive_boolean, by simp [TypeFormed]⟩)
    rfl

def mixedPlan : Plan frame [] [] 3 :=
  .event firstKey (reflexivity []) rfl rfl fun first logical =>
    .event secondKey (transitivity first logical) rfl rfl fun second _ =>
      .event thirdKey (specialization first second) rfl rfl fun third _ =>
        .stop [(thirdKey, third), (secondKey, second), (firstKey, first)]
          [(specialization first second).receipt thirdKey,
            (transitivity first logical).receipt secondKey, (reflexivity []).receipt firstKey]

/-- No supplied cache theorem is required by this complete mixed source run. -/
theorem mixed_plan_runs (state : State) :
    ∃ (cache : Cache) (receipts : List ReceiptKeys.Entry) (commands : List SourceReplay.Command),
      commands.length = 3 ∧ receipts.length = 3 ∧ Valid frame.policy frame.world cache ∧
      PureReturns program (SourceReplay.environment (frame.source [] []) commands) state
        (.expression [.symbol "hol-light:run-from", .var "state", .var "commands"]) state
        (.expression [.symbol "Some", frame.source cache receipts]) := by
  simpa using authored_plan_returns frame mixedPlan (empty_valid _ _) state

theorem transitivity_retains_both_occurrences (record : Record)
    (logical : (reflexivity []).LogicalResult record) :
    (transitivity record logical).occurrences = [firstKey, firstKey] := rfl

theorem substitution_is_nonempty (first second : Record) :
    (specialization first second).payload ≠ .symbol "HOL:Nil" := by
  simp [specialization, Invocation.payload, TypeSubstitution.maplets, Premises.keys]

/-- HOL Light writes a replacement before its variable key. The retained
substitution actually specializes the parameter, rather than merely being
a nonempty list whose operator key would be ignored. -/
theorem substitution_specializes_parameter :
    SourceSubstitution.typeAction [(Ty.bool, .var parameter)] (.var parameter) = Ty.bool := by
  simp [SourceSubstitution.typeAction, SourceSubstitution.variableType]

theorem reversed_maplet_leaves_parameter :
    SourceSubstitution.typeAction [(.var parameter, Ty.bool)] (.var parameter) = .var parameter := by
  simp [SourceSubstitution.typeAction, SourceSubstitution.variableType, Ty.bool]

theorem absent_premise_cannot_be_selected (address : Atom) (record : Record) :
    ([] : Cache).lookup address ≠ some record := by simp

theorem occupied_receipt_cannot_be_fresh :
    ReceiptKeys.presentB firstKey [(reflexivity []).receipt firstKey] ≠ false := by decide

/-- Even the zero-event path retains its endpoint; an unrelated state cannot
be spliced into it by deleting the commands. -/
theorem empty_trace_iff (state : State) (before after : Atom) :
    SourceReplay.Trace state before [] after ↔ before = after := by
  constructor
  · intro trace
    cases trace
    rfl
  · intro same
    subst after
    exact .nil _

theorem forged_endpoint_refused (state : State) :
    ¬ SourceReplay.Trace state (frame.source [] []) [] (.symbol "forged-source-state") := by
  rw [empty_trace_iff]
  simp [Frame.source, ProofLookup.sourceState]

end Mettapedia.Languages.HOLLight.MeTTa.InferenceScheduleControls
