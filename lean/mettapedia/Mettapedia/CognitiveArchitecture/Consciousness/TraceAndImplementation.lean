import Mettapedia.GSLT.Core.PredicateInvariance
import Mettapedia.GSLT.Core.ImplementationRecoding
import Mettapedia.GSLT.Causality.Hierarchy
import Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators
import Mettapedia.GSLT.Core.RelationPresentation
import Mettapedia.GSLT.Causality.ScriptedExecution
import Mettapedia.GSLT.Causality.ScriptedExecutionRecoding
import Mettapedia.GSLT.Core.OperationalReadbackControls
import Mettapedia.CognitiveArchitecture.Consciousness.Valence
import Mettapedia.CategoryTheory.LocalSections

/-!
# Observation sufficiency versus implemented organization

Public philosophical sources:

* Tim Maudlin, *Computation and Consciousness* (1989),
  https://doi.org/10.2307/2026650 .
* David Chalmers, *A Computational Foundation for the Study of Cognition*,
  https://consc.net/papers/computation.html .
* David Chalmers, *Does a Rock Implement Every Finite-State Automaton?* (1996),
  https://consc.net/papers/rock.html .
* Pawel Pachniewski, *Not artificially conscious* (2022) and *Consciousness
  Is Very Likely Not Something You Get for Free by Preserving a Pattern* (2026),
  https://mentalcontractions.substack.com/p/not-artificially-conscious and
  https://mentalcontractions.substack.com/p/consciousness-is-very-likely-not .

The formal objects below distinguish three possible sufficiency hypotheses:
dependence on recorded observations, on a selected causal equivalence, or on
further physical detail. A predicate can stand for a proposed consciousness
assignment, but no assignment is assumed or proved scientifically correct.

The causal comparison reuses the library's observational and interventional
equivalences. These are explicit, observation-dependent contracts, not the
whole of Chalmers's implementation account or Maudlin's Olympia construction.
The finite control predicate is treatment responsiveness, not consciousness.
The workspace instance below uses independently proved transitions and an
intervention-sensitive broadcast contract. Any proposed consciousness
assignment in that comparison is explicitly conditional; the public
indicator framework does not claim broadcast is necessary and sufficient.

Two different gaps are kept separate. A passive record can omit intervention
responses. Even an exact description of the entire abstract transition graph
does not by itself give its carrier the described transitions. The latter
control uses a complete table and a host constrained to stuttering; it does
not rely on the description omitting counterfactual possibilities.

The dormant-backup comparison is instantiated in the existing causal
hierarchy by `Causality.ScriptedExecution`: input-only saturated contexts
cannot distinguish the direct executor from a valid backup. Replacing the
evaluator while holding the table fixed can distinguish them. The permitted
context class is therefore part of the realization criterion.

`ContextualRealization` transports that criterion through admitted intervention
maps and operational covers. The concrete recoding changes states, tables,
evaluators and replacement commands together. The valence instance at the end
uses independently stated finite potentials: it transports authored prefix
constraints, without identifying those constraints with felt experience.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Consciousness.TraceAndImplementation

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Core.PredicateInvariance
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Causality.Hierarchy

universe uTheory uContext uRule uAtom

section Sufficiency

variable {S : GSLT.{uTheory}} {rules : ContextualRules.{uContext, uRule} S}
  (A : AdmissibleClass rules) (observations : ContextualRules.Observations.{uAtom} S)

/-- A proposed property is determined by passive observational behavior. -/
abbrev PassiveSufficient (property : S.Term → Prop) : Prop :=
  InvariantUnder (Agree A observations .association) property

/-- A proposed property is invariant under the declared intervention equivalence. -/
abbrev InterventionSufficient (property : S.Term → Prop) : Prop :=
  InvariantUnder (Agree A observations .intervention) property

/-- Passive sufficiency entails invariance under the finer causal equivalence. -/
theorem passiveSufficient_implies_interventionSufficient {property : S.Term → Prop}
    (passiveSufficient : PassiveSufficient A observations property) :
    InterventionSufficient A observations property := by
  intro first second same
  exact passiveSufficient (agree_association_of_intervention A observations same)

/-- Transferring every causal-invariance hypothesis to passive sufficiency
requires the passive boundary to identify only causally equivalent states. -/
theorem all_intervention_invariants_passive_iff :
    (∀ property : S.Term → Prop, InterventionSufficient A observations property →
      PassiveSufficient A observations property) ↔
    ∀ ⦃first second⦄, Agree A observations .association first second →
      Agree A observations .intervention first second :=
  all_invariants_transfer_iff_refinement _ _ (agree_equivalence A observations .intervention)

/-- The complete passive modal signature for the selected observations.
This is an observational description, not a physical implementation. -/
def passiveSignature (term : S.Term) :
    Formula (passive observations).Atom (passive observations).Label → Prop :=
  fun formula => (passive observations).sat formula term

theorem passiveSignature_eq_of_association {first second : S.Term}
    (same : Agree A observations .association first second) :
    passiveSignature observations first = passiveSignature observations second := by
  funext formula
  exact propext (passive_sat_iff_of_agree A observations same formula)

/-- A separating property refutes sufficiency of the record at issue, using
the library's general nonfactorization witness. No causal sufficiency
hypothesis is refuted by this conclusion. -/
theorem different_property_refutes_record_sufficiency
    {Record : Type*} (record : S.Term → Record) (property : S.Term → Prop)
    {first second : S.Term} (same : record first = record second)
    (holds : property first) (fails : ¬ property second) :
    ¬ Factors record property :=
  (NonTrivialFiber.ofProp same holds fails).not_factors

end Sufficiency

namespace ConditionalArguments

/-- The logical conflict used by Maudlin: necessity, sufficiency, and
supervenience on an activity record cannot all hold when two systems have
the same activity record but differ in implementation status. The existence
and physical adequacy of such a pair remain separate substantive premises;
this theorem does not construct Olympia or assign consciousness to it. -/
theorem necessity_sufficiency_supervenience_incompatible
    {State Record : Type*} (activity : State → Record)
    (implements conscious : State → Prop) {first second : State}
    (sameActivity : activity first = activity second)
    (firstImplements : implements first) (secondDoesNot : ¬ implements second)
    (necessity : ∀ state, conscious state → implements state)
    (sufficiency : ∀ state, implements state → conscious state)
    (supervenience : Factors activity conscious) : False := by
  have sameConscious := supervenience.constantOnFibers first second sameActivity
  have secondConscious : conscious second := sameConscious ▸ sufficiency first firstImplements
  exact secondDoesNot (necessity second secondConscious)

end ConditionalArguments

namespace ResponseControl

open ResponseTypes

/-- An independently defined causal query used as the separating predicate. -/
def responsive (term : Stage) : Prop :=
  (everyIntervention.saturated quantities).sat treatedShowsEffect term

/-- The query respects intervention equivalence at every model. -/
theorem responsive_interventionSufficient :
    InterventionSufficient everyIntervention quantities responsive := by
  intro first second same
  exact sat_underIntervention_iff_of_agree everyIntervention quantities same
    ⟨some true, AdmissibleClass.top_admissible _⟩ (.dia () (.dia () (.atom Quantity.effect)))

/-- A genuine separating instance: identical passive descriptions and
different causal-query values, while the query remains causally invariant. -/
theorem causal_invariance_compatible_with_record_insufficiency :
    InterventionSufficient everyIntervention quantities responsive ∧
      passiveSignature quantities wouldHelp = passiveSignature quantities inert ∧
      responsive wouldHelp ∧ ¬ responsive inert ∧
      ¬ Factors (passiveSignature quantities) responsive := by
  have same := passiveSignature_eq_of_association everyIntervention quantities
    association_wouldHelp_inert
  exact ⟨responsive_interventionSufficient, same,
    wouldHelp_sat_treatedShowsEffect, inert_not_sat_treatedShowsEffect,
    (NonTrivialFiber.ofProp same wouldHelp_sat_treatedShowsEffect
      inert_not_sat_treatedShowsEffect).not_factors⟩

theorem interventionSufficient_does_not_imply_passiveSufficient :
    ¬ (∀ property : Stage → Prop,
      InterventionSufficient everyIntervention quantities property →
        PassiveSufficient everyIntervention quantities property) := by
  intro transfer
  exact inert_not_sat_treatedShowsEffect
    ((transfer responsive responsive_interventionSufficient association_wouldHelp_inert).mp
      wouldHelp_sat_treatedShowsEffect)

end ResponseControl

namespace CompleteDescriptionControl

open Mettapedia.GSLT.IndexedOperational
open OperationalImplementation

/-- The entire transition graph of the existing finite implementation control. -/
def fullTable : List (Option Bool × Option Bool) := [(some false, some true)]

/-- The description is exact for every source and target, including transitions
other than any chosen actual run. -/
theorem fullTable_exact (source target : Option Bool) :
    Canary.target.Step source target ↔ (source, target) ∈ fullTable := by
  change (source = some false ∧ target = some true) ↔ _
  simp [fullTable]

/-- A host whose states only stutter cannot faithfully implement this graph
if it represents the enabled initial state. A full graph description cannot
supply the missing transition. -/
theorem no_stuttering_implementation :
    ¬ ∃ implementation : OperationalImplementation Canary.target,
      (∀ first second : implementation.State,
        implementation.step first second ↔ first = second) ∧
      ∃ source : implementation.State, implementation.encode source = some false := by
  rintro ⟨implementation, stutters, source, encoded⟩
  have enabled : Canary.target.Step (implementation.encode source) (some true) := by
    change implementation.encode source = some false ∧ some true = some true
    exact ⟨encoded, rfl⟩
  obtain ⟨next, advances, equivalent⟩ := implementation.complete enabled
  have same : source = next := (stutters source next).mp advances
  subst next
  change implementation.encode source = some true at equivalent
  rw [encoded] at equivalent
  cases equivalent

/-- A distinct host representation, with explicitly encoded low and high states. -/
inductive Signal where
  | low
  | high
  deriving DecidableEq

def signalEncoding : Signal ≃ Bool where
  toFun signal := match signal with | .low => false | .high => true
  invFun value := if value then .high else .low
  left_inv signal := by cases signal <;> rfl
  right_inv value := by cases value <;> rfl

/-- The same abstract graph has a faithful implementation on a different
carrier; material independence is not the absence of implementation laws. -/
def signalImplementation : OperationalImplementation Canary.target :=
  Canary.implementation.recode signalEncoding

theorem signal_advances : signalImplementation.step .low .high :=
  ⟨rfl, rfl⟩

theorem signal_reflects_all_semantic_steps (source : Signal) (target : Option Bool) :
    Canary.target.Step (some (signalEncoding source)) target ↔
      ∃ next : Signal, signalImplementation.step source next ∧
        Canary.target.Equiv (some (signalEncoding next)) target :=
  signalImplementation.semanticStep_iff_exists_implementationStep source target

/-- The observation asks for the actual encoded Boolean state. -/
def signalObservation : ObservedGSLT Canary.target where
  Atom := Bool
  observes expected actual := actual = some expected

theorem signalObservation_resp (atom : signalObservation.Atom)
    {first second : Canary.target.Term} (equal : Canary.target.Equiv first second) :
    signalObservation.observes atom first ↔ signalObservation.observes atom second := by
  cases equal
  exact Iff.rfl

/-- The modal host uses the already justified implementation transitions. -/
def signalHost : System signalImplementation.asGSLT :=
  signalImplementation.observedSystem signalObservation

/-- The abstract observer uses the source GSLT transitions independently. -/
def signalAbstract : System Canary.target :=
  System.ofObserved signalObservation signalObservation_resp

/-- A realization transports every formula-generated native type across
the distinct host and abstract carriers. It does not identify their entire
presheaf topoi or supply a physical consciousness-transfer premise. -/
theorem signal_formulaNativeType_iff (formula : Formula Bool Unit) (state : Signal) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF Canary.target).satisfies
        (S := ()) (signalImplementation.encode state)
        (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaNativeType
          signalAbstract formula).pred ↔
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        signalImplementation.asGSLT).satisfies (S := ()) state
        (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaNativeType
          signalHost formula).pred := by
  have same := Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.systemCover_formulaNativeType_iff signalHost
      (signalImplementation.observedCover signalObservation signalObservation_resp)
      formula state
  change (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF Canary.target).satisfies
      (S := ()) (signalImplementation.encode state)
      (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaNativeType
        signalAbstract (Formula.map _root_.id _root_.id formula)).pred ↔ _ at same
  have identityMap : Formula.map _root_.id _root_.id formula = formula :=
    Mettapedia.GSLT.HennessyMilner.Formula.map_id formula
  exact (Iff.of_eq (congrArg
    (fun mapped : Formula Bool Unit =>
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF Canary.target).satisfies
        (S := ()) (signalImplementation.encode state)
        (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaNativeType
          signalAbstract mapped).pred) identityMap.symm)).trans same

/-- The host actually advances to a state satisfying the high observation. -/
theorem signal_low_reaches_high :
    signalHost.sat (.dia () (.atom true)) .low :=
  ⟨.high, signal_advances, rfl⟩

/-- The same formula fails at the terminal state; the observer contract does
not manufacture a transition merely because the postcondition already holds. -/
theorem signal_high_cannot_advance :
    ¬ signalHost.sat (.dia () (.atom true)) .high := by
  rintro ⟨target, step, _⟩
  change signalEncoding .high = false ∧ signalEncoding target = true at step
  cases (show true = false from step.1)

end CompleteDescriptionControl

namespace WorkspaceControl

open Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators
open Mettapedia.CategoryTheory.LocalSections

/-- Restrict the already specified agent's entire passive future to a set
of ordinary interaction words. This is an actual local description, not an
independently invented experience carrier. -/
def localDescription (context : Set (List PassiveInput)) (state : State) :
    Section context (Bool × Bool × Module) :=
  fun word => passiveFuture state word.val

theorem localDescription_restrict {small large : Set (List PassiveInput)}
    (included : small ⊆ large) (state : State) :
    restrict included (localDescription large state) = localDescription small state := rfl

theorem localDescriptions_compatible (left right : Set (List PassiveInput)) (state : State) :
    Compatible (localDescription left state) (localDescription right state) :=
  fun _ _ _ => rfl

theorem localDescriptions_glue (left right : Set (List PassiveInput)) (state : State) :
    glue (localDescription left state) (localDescription right state) =
      localDescription (left ∪ right) state := by
  apply section_ext
  · exact (glue_left _ _).trans (localDescription_restrict _ _).symm
  · exact (glue_right (localDescriptions_compatible left right state)).trans
      (localDescription_restrict _ _).symm

/-- Every compatible collection of these passive descriptions agrees, even
after gluing. The independently defined intervention test still separates
the connected workspace from its shadow. -/
theorem gluing_passive_descriptions_does_not_supply_causal_equivalence
    (left right : Set (List PassiveInput)) :
    glue (localDescription left (initial .connected))
        (localDescription right (initial .connected)) =
      glue (localDescription left (initial .shadow))
        (localDescription right (initial .shadow)) ∧
      ¬ modal.Bisimilar (initial .connected) (initial .shadow) := by
  constructor
  · rw [localDescriptions_glue, localDescriptions_glue]
    unfold localDescription
    rw [ordinary_interactions_cannot_separate_modes]
  · exact intervention_modes_not_bisimilar

/-- The earlier conditional conflict now has a constructed agent-architecture
witness. Necessity and sufficiency are stipulated for this theorem, not
attributed to the indicator framework or established empirically. -/
theorem passive_record_cannot_support_broadcast_assignment
    (assigned : State → Prop)
    (necessity : ∀ state, assigned state → Broadcasts state)
    (sufficiency : ∀ state, Broadcasts state → assigned state) :
    ¬ Factors passiveFuture assigned := by
  intro supervenience
  exact ConditionalArguments.necessity_sufficiency_supervenience_incompatible
    passiveFuture Broadcasts assigned ordinary_interactions_cannot_separate_modes
    (connected_broadcasts (initial .connected) rfl)
    (shadow_not_broadcasts (initial .shadow) rfl) necessity sufficiency supervenience

/-- A passive observer merges two behavioral classes that the declared
intervention observer distinguishes. This is an actual failure of
injectivity of the existing refinement's quotient map. -/
theorem intervention_class_forgetting_not_injective :
    ¬ Function.Injective interventionRefinement.classMap := by
  intro injective
  apply intervention_modes_not_bisimilar
  apply (modal.behavioralClass_eq_iff _ _).mp
  apply injective
  change passiveModal.toBehavioralClass (initial .connected) =
    passiveModal.toBehavioralClass (initial .shadow)
  exact (passiveModal.behavioralClass_eq_iff _ _).mpr passive_modes_bisimilar

/-- The constructed workspace obstruction refutes universal descent of
intervention-invariant readouts to passive classes. Values are arbitrary
mathematical data; interpreting any such readout as experience is a separate
hypothesis rather than a consequence of the observer construction. -/
theorem not_all_intervention_readouts_passive :
    ¬ (∀ (Value : Type) (readout : State → Value),
      Factors modal.toBehavioralClass readout →
        Factors passiveModal.toBehavioralClass readout) := by
  intro descends
  exact intervention_class_forgetting_not_injective
    (interventionRefinement.classMap_injective_iff_all_readouts_descend.mpr descends)

end WorkspaceControl

namespace PremiseComparison

open Mettapedia.GSLT.RelationPresentation

universe uOrigin

/-!
The following are small logical reconstructions, not formalizations of entire
metaphysical systems. Kastrup's course presents experiential reality and
distinguishes phenomenal consciousness from meta-consciousness:
https://www.essentiafoundation.org/analytic-idealism-course/ . Ra session 13
discusses unity, individuation and the progression to self-awareness:
https://www.lawofone.info/s/13 . Neither source supplies the functions or
finite models used below. Those are explicit mathematical additions testing
which further commitments a proposed inference requires.
-/

/-- Appearances may be interpreted from experiential configurations. The
existing proof-relevant relation permits a many-to-many interpretation; no
physical-to-experience function is imposed. -/
def ExperientialOrigin {Experience Appearance : Type uOrigin}
    (appears : RelationPresentation.Rel Experience Appearance) (appearance : Appearance) : Prop :=
  ∃ experience, Nonempty (appears.evidence experience appearance)

/-- Having an assigned individual subject is separate from having an
experiential origin. The optional identity permits no assigned subject. -/
def Individuated {Occurrence Subject : Type*}
    (subjectOf : Occurrence → Option Subject) (occurrence : Occurrence) : Prop :=
  ∃ subject, subjectOf occurrence = some subject

/-- A property and a subject identity can descend independently. If subject
identity descends, equal presented structure denotes the same subject under
that hypothesis. This is not a theorem that subject identity must descend. -/
theorem same_subject_of_individuation_descent
    {Occurrence Structure Subject : Type*}
    (presents : Occurrence → Structure) (subjectOf : Occurrence → Option Subject)
    (descends : Factors presents subjectOf) {first second : Occurrence}
    (same : presents first = presents second) : subjectOf first = subjectOf second :=
  descends.constantOnFibers first second same

namespace OriginControls

/-- Two distinguishable experiential configurations produce two public
appearances. The interpretation is invertible but is not the identity. -/
def appears : RelationPresentation.Rel Bool Bool := RelationPresentation.Rel.graph Bool.not

theorem every_appearance_has_experiential_origin (appearance : Bool) :
    ExperientialOrigin appears appearance := by
  refine ⟨!appearance, ⟨⟨⟨?_⟩⟩⟩⟩
  exact Bool.not_not appearance

/-- One appearance receives an individual identity; the other does not. -/
def subjectOf (appearance : Bool) : Option Bool :=
  if appearance then some false else none

/-- The first bit supplies individuation; the second supplies a reflective
report. This is a stipulated finite control, not a source criterion. -/
def selfAware (appearance : Bool × Bool) : Prop :=
  appearance.1 = true ∧ appearance.2 = true

theorem reflective_requires_subject {appearance : Bool × Bool} (aware : selfAware appearance) :
    Individuated (fun appearance : Bool × Bool => subjectOf appearance.1) appearance := by
  refine ⟨false, ?_⟩
  simp [subjectOf, aware.1]

theorem experiential_origin_does_not_force_individuation :
    (∀ appearance, ExperientialOrigin appears appearance) ∧
      ¬ Individuated subjectOf false := by
  refine ⟨every_appearance_has_experiential_origin, ?_⟩
  simp [Individuated, subjectOf]

/-- Even adding the premise that reflective awareness requires an individual
subject leaves a model in which an individuated appearance lacks it. -/
theorem individuation_does_not_force_reflective_awareness :
    Individuated (fun appearance : Bool × Bool => subjectOf appearance.1) (true, false) ∧
      ¬ selfAware (true, false) ∧ selfAware (true, true) := by
  exact ⟨⟨false, rfl⟩, by simp [selfAware], rfl, rfl⟩

end OriginControls

namespace CopyControls

/-- The first bit identifies an occurrence; the second is its copied content. -/
abbrev Occurrence := Bool × Bool

def presents : Occurrence → Bool := Prod.snd

def property (occurrence : Occurrence) : Prop := occurrence.2 = true

def separateSubjects (occurrence : Occurrence) : Option Bool := some occurrence.1

def sharedSubject (occurrence : Occurrence) : Option Bool := some occurrence.2

theorem property_descends : Factors presents property :=
  ⟨fun content => content = true, fun _ => rfl⟩

theorem shared_subject_descends : Factors presents sharedSubject :=
  ⟨some, fun _ => rfl⟩

/-- A structure-dependent property can hold at both copies while their
proposed individual identities fail to be structure-dependent. -/
theorem separate_subject_does_not_descend : ¬ Factors presents separateSubjects := by
  intro descends
  have same := descends.constantOnFibers (false, true) (true, true) rfl
  cases same

theorem copied_property_does_not_determine_subject_identity :
    Factors presents property ∧
      property (false, true) ∧ property (true, true) ∧
      ¬ Factors presents separateSubjects ∧ Factors presents sharedSubject :=
  ⟨property_descends, rfl, rfl, separate_subject_does_not_descend, shared_subject_descends⟩

end CopyControls

namespace DormantBackupControl

open Mettapedia.GSLT.ScriptedBackup
open Mettapedia.GSLT.PrivilegedView
open Mettapedia.GSLT.Causality

/-- The all-input criterion and the evaluator-call record disagree on this
constructed backup. Neither is identified with physical causal realization. -/
theorem all_inputs_do_not_determine_evaluator_activity :
    wordBehaviour (backupStep Controls.write) Player.current Controls.recordedFalse =
      wordBehaviour Controls.write id false ∧
    activities Controls.write Controls.recordedFalse [false] = [.tableRead] ∧
    advance Controls.write Controls.recordedFalse false =
      advance (fun _ _ => true) Controls.recordedFalse false ∧
    Controls.write false false ≠ (fun (_ _ : Bool) => true) false false :=
  Controls.dormant_backup_distinction

/-- The stronger backup result lives in the existing causal hierarchy:
agreement at every input-only rung leaves component response undetermined,
and forgetting those component contexts actually merges behavioral classes. -/
theorem all_input_contexts_do_not_determine_component_response :
    (∀ rung, Agree ScriptedExecution.inputClass ScriptedExecution.observations rung
      ScriptedExecution.Controls.executor ScriptedExecution.Controls.backup) ∧
    ¬ Agree ScriptedExecution.componentClass ScriptedExecution.observations .intervention
      ScriptedExecution.Controls.executor ScriptedExecution.Controls.backup ∧
    ¬ Function.Injective
      (ScriptedExecution.componentRefinement (State := Bool) (Input := Bool)).classMap :=
  ⟨ScriptedExecution.Controls.all_input_rungs_agree,
    ScriptedExecution.Controls.component_intervention_separates,
    ScriptedExecution.Controls.component_class_forgetting_not_injective⟩

end DormantBackupControl

end PremiseComparison

/-! ## Realization boundaries and conditional assessment transport -/

namespace RealizationControl

open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational.OperationalRealization

/-- An independently constructed compiler uses two target instructions for
one source step. Public reachability agrees, while instruction counts differ. -/
theorem public_behavior_with_different_internal_paths :
    ((LoweringCanary.lowering.mapStep FusionCanary.source_step).length = 2 ∧
      ((Route.cons ⟨FusionCanary.source_step⟩ (Route.refl true)) :
        ExecutionPath FusionCanary.source false true).length = 1) ∧
    ((∃ after, FusionCanary.source.MultiStep false after ∧ after = true) ↔
      ∃ final, LoweringCanary.target.MultiStep (LoweringCanary.lowering.mapTerm false) final ∧
        LoweringCanary.sourceView final = true) :=
  ⟨LoweringCanary.implementation_count_differs, LoweringCanary.commitment_reachable_iff false⟩

/-- Forward simulation cannot supply the required reflected behavior when
the target has an escaping transition outside the compiled states. -/
theorem extra_behavior_blocks_cover :
    ¬ ∃ translation : SemanticCoveredTranslation
      Mettapedia.GSLT.IndexedOperational.OperationalImplementation.Canary.implementation.asGSLT
      Mettapedia.GSLT.IndexedOperational.OperationalImplementation.Canary.escapingTarget,
      translation.mapTerm = some :=
  Mettapedia.GSLT.IndexedOperational.OperationalImplementation.Canary.no_semantic_cover_with_some_encoding

end RealizationControl

namespace ValenceRealizationControl

open Mettapedia.GSLT.Causality
open Mettapedia.GSLT.Causality.ScriptedExecution
open Mettapedia.GSLT.Causality.ScriptedExecutionRecoding
open Valence

/-- A toy potential on a displayed Boolean state. Its welfare interpretation
is an explicit hypothesis, not a consciousness or happiness assignment. -/
def energy (machine : Machine Bool Bool) : ℚ := if machine.player.current then 0 else 1

/-- The target states use numerical codes. This potential is independently
stated as a formula on their code, rather than defined by the source observer. -/
def encodedEnergy (machine : Machine (Fin 2) Bool) : ℚ := 1 - (machine.player.current.val : ℚ)

theorem energy_commutes (machine : Machine Bool Bool) :
    encodedEnergy (recodeMachine ScriptedExecutionRecoding.Controls.boolToFin machine) =
      energy machine := by
  cases current : machine.player.current <;>
    simp [encodedEnergy, energy, recodeMachine, recodePlayer,
      ScriptedExecutionRecoding.Controls.boolToFin, finTwoEquiv, current]

def appraisal (sensitive : Bool) : TransitionAppraisal (Machine Bool Bool) Bool ℚ :=
  potentialDrop (fun machine => (if sensitive then 2 else 1) * energy machine)

def encodedAppraisal (sensitive : Bool) : TransitionAppraisal (Machine (Fin 2) Bool) Bool ℚ :=
  potentialDrop (fun machine => (if sensitive then 2 else 1) * encodedEnergy machine)

theorem appraisal_commutes (sensitive : Bool) (before after : Machine Bool Bool) (input : Bool) :
    encodedAppraisal sensitive
        (recodeMachine ScriptedExecutionRecoding.Controls.boolToFin before) input
        (recodeMachine ScriptedExecutionRecoding.Controls.boolToFin after) =
      appraisal sensitive before input after := by
  simp only [appraisal, encodedAppraisal, potentialDrop, energy_commutes]

/-- The same actual recoding that transports component interventions also
transports both declared appraisals over every actual input prefix. -/
theorem prefix_policy_recode_iff (initial : Machine Bool Bool) (inputs : List Bool) :
    RobustPrefixNonnegative Set.univ tick encodedAppraisal
        (recodeMachine ScriptedExecutionRecoding.Controls.boolToFin initial) inputs ↔
      RobustPrefixNonnegative Set.univ tick appraisal initial inputs := by
  have comparison := robustPrefixNonnegative_map_iff Set.univ Set.univ id
    (fun _ _ => Set.mem_univ _) (fun hypothesis _ => ⟨hypothesis, Set.mem_univ _, rfl⟩)
    tick tick (recodeMachine ScriptedExecutionRecoding.Controls.boolToFin) id
    (tick_commutes ScriptedExecutionRecoding.Controls.boolToFin)
    appraisal encodedAppraisal (fun hypothesis _ before input =>
      appraisal_commutes hypothesis before (tick before input) input) initial inputs
  simpa only [List.map_id] using comparison

/-- In this finite model, supplying true reaches a lower potential. Both
appraisals satisfy the prefix policy, and the recoded execution does too. -/
theorem lowering_potential_positive :
    RobustPrefixNonnegative Set.univ tick appraisal ScriptedExecution.Controls.executor [true] ∧
      RobustPrefixNonnegative Set.univ tick encodedAppraisal
        (recodeMachine ScriptedExecutionRecoding.Controls.boolToFin ScriptedExecution.Controls.executor)
        [true] := by
  have safe : RobustPrefixNonnegative Set.univ tick appraisal ScriptedExecution.Controls.executor [true] := by
    refine ⟨⟨false, Set.mem_univ _⟩, ?_⟩
    intro hypothesis _ horizon
    cases hypothesis <;> cases horizon <;>
      norm_num [accumulated, appraisal, potentialDrop, energy, tick,
        ScriptedExecution.Controls.executor, ScriptedExecution.Controls.write, direct,
        ScriptedBackup.backupStep, ScriptedBackup.advance, List.take]
  exact ⟨safe, (prefix_policy_recode_iff _ _).mpr safe⟩

end ValenceRealizationControl

#print axioms all_intervention_invariants_passive_iff
#print axioms ConditionalArguments.necessity_sufficiency_supervenience_incompatible
#print axioms ResponseControl.causal_invariance_compatible_with_record_insufficiency
#print axioms ResponseControl.interventionSufficient_does_not_imply_passiveSufficient
#print axioms CompleteDescriptionControl.fullTable_exact
#print axioms CompleteDescriptionControl.no_stuttering_implementation
#print axioms CompleteDescriptionControl.signalImplementation
#print axioms CompleteDescriptionControl.signal_reflects_all_semantic_steps
#print axioms CompleteDescriptionControl.signal_formulaNativeType_iff
#print axioms CompleteDescriptionControl.signal_low_reaches_high
#print axioms CompleteDescriptionControl.signal_high_cannot_advance
#print axioms WorkspaceControl.passive_record_cannot_support_broadcast_assignment
#print axioms WorkspaceControl.intervention_class_forgetting_not_injective
#print axioms WorkspaceControl.not_all_intervention_readouts_passive

end Mettapedia.CognitiveArchitecture.Consciousness.TraceAndImplementation
