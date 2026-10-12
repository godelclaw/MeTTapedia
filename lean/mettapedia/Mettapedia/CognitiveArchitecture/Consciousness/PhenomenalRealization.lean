import Mettapedia.CategoryTheory.PartialSections
import Mettapedia.CognitiveArchitecture.GodelClaw.GlobalWorkspace
import Mettapedia.CognitiveArchitecture.Consciousness.Valence
import Mettapedia.GSLT.Causality.ScriptedExecutionRecoding

/-!
# Contextual descriptions at operational and appraisal boundaries

The existing category of partial sections can describe complete query
interfaces rather than one scalar.  Here its features are actual modal
formulas, receipt queries, or assessor-indexed input histories.  Restriction
forgets features; refinement retains their exact values.  The operational
and appraisal laws justify particular description transports.

The workspace controls have two distinct full extensions of one passive
report, separated by an admitted component intervention.  In the receipt
model, equal published content can likewise hide disconnected mediation.
These are distinctions of executable Lean contracts, not claims about a
deployed host, consciousness, or the number of subjects.  A behavioral view
and a hypothetical experiential assignment remain different objects unless
an independently stated interpretation relates them.

Appraisal descriptions retain every assessor and chronological input word.
Values may be products or independent coordinate families.  The existing
machine recoding transports evaluators, tables and interventions, and also
transports the deliberately re-encoded appraisal.  This establishes no
empirical identification of those appraisals with experienced wellbeing.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalRealization

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Causality
open Mettapedia.CategoryTheory
open _root_.CategoryTheory

namespace FormulaDescriptions

universe uS uT uAtom uLabel uTargetAtom uTargetLabel

variable {S : GSLT.{uS}} {T : GSLT.{uT}}
  {source : System.{uAtom, uLabel} S} {target : System.{uTargetAtom, uTargetLabel} T}

/-- A structured truth assignment over an explicitly declared query context. -/
def describe (system : System.{uAtom, uLabel} S)
    (context : Set (Formula system.Atom system.Label)) (state : S.Term) :
    PartialSections.View (Formula system.Atom system.Label) Prop where
  context := context
  values query := system.sat query.val state

/-- Target answers retain the source query vocabulary through the existing
cover's formula translation.  Additional target queries are not asserted to
belong to that vocabulary. -/
def translated (cover : SystemCover source target)
    (context : Set (Formula source.Atom source.Label)) (state : T.Term) :
    PartialSections.View (Formula source.Atom source.Label) Prop where
  context := context
  values query := target.sat (query.val.map cover.mapAtom cover.mapLabel) state

/-- A two-sided operational cover proves exact equality of the transported
description; this includes negated and nested modal formulas. -/
theorem cover_description (cover : SystemCover source target)
    (context : Set (Formula source.Atom source.Label)) (state : S.Term) :
    translated cover context (cover.mapTerm state) = describe source context state := by
  apply PartialSections.View.ext
  · rfl
  intro query _ _
  exact propext (cover.sat_map query state)

/-- Context restriction is the actual presheaf restriction on query values. -/
theorem describe_restrict (system : System.{uAtom, uLabel} S)
    (context observed : Set (Formula system.Atom system.Label)) (state : S.Term) :
    PartialSections.restrict observed (describe system context state) =
      describe system (context ∩ observed) state := by
  apply PartialSections.View.ext
  · rfl
  intro _ _ _
  rfl

/-- Adding queries to the same state's description retains every prior answer. -/
theorem describe_refines (system : System.{uAtom, uLabel} S)
    {small large : Set (Formula system.Atom system.Label)}
    (included : small ⊆ large) (state : S.Term) :
    describe system small state ≤ describe system large state :=
  ⟨included, fun _ _ _ => rfl⟩

/-- The refinement is an arrow in the already constructed description category. -/
def contextArrow (system : System.{uAtom, uLabel} S)
    {small large : Set (Formula system.Atom system.Label)}
    (included : small ⊆ large) (state : S.Term) :
    describe system small state ⟶ describe system large state :=
  homOfLE (describe_refines system included state)

end FormulaDescriptions

/-! ## Workspace queries: passive agreement and component separation -/

namespace WorkspaceDescriptions

open ArchitecturalIndicators

abbrev Query := Formula Atom Input

/-- The entire passive formula vocabulary, not a finite test list. -/
def passiveContext : Set Query :=
  Set.range (fun formula : Formula Atom PassiveInput => formula.map id Input.ordinary)

def full (state : State) : PartialSections.View Query Prop :=
  FormulaDescriptions.describe modal Set.univ state

def passive (state : State) : PartialSections.View Query Prop :=
  FormulaDescriptions.describe modal passiveContext state

theorem passive_is_restriction (state : State) :
    PartialSections.restrict passiveContext (full state) = passive state := by
  apply PartialSections.View.ext
  · exact Set.univ_inter _
  intro _ _ _
  rfl

theorem passive_refines_full (state : State) : passive state ≤ full state :=
  FormulaDescriptions.describe_refines modal (Set.subset_univ _) state

/-- Equality holds for every passive modal formula, including negations. -/
theorem connected_and_shadow_passive_agree :
    passive (initial .connected) = passive (initial .shadow) := by
  apply PartialSections.View.ext
  · rfl
  intro query member _
  obtain ⟨formula, rfl⟩ := member
  exact propext ((ordinary_formulas_refine formula (initial .connected)).trans
    ((passiveModal.logicallyEquivalent_of_bisimilar passive_modes_bisimilar formula).trans
      (ordinary_formulas_refine formula (initial .shadow)).symm))

/-- Retaining the full intervention vocabulary blocks this identification. -/
theorem connected_full_does_not_refine_shadow :
    ¬ full (initial .connected) ≤ full (initial .shadow) := by
  intro extension
  have answer := extension.2 (probeFormula (broadcastWord false true) (.report, true))
    (Set.mem_univ _) (Set.mem_univ _)
  exact intervention_separates_modes.2 (Eq.mp answer intervention_separates_modes.1)

theorem full_views_distinct : full (initial .connected) ≠ full (initial .shadow) :=
  fun same => connected_full_does_not_refine_shadow (le_of_eq same)

/-- A single passive report genuinely has two distinct full operational
extensions.  Choosing one extension requires information beyond that report. -/
theorem passive_report_has_distinct_full_extensions :
    passive (initial .connected) ≤ full (initial .connected) ∧
      passive (initial .connected) ≤ full (initial .shadow) ∧
      full (initial .connected) ≠ full (initial .shadow) :=
  ⟨passive_refines_full _, connected_and_shadow_passive_agree.symm ▸
    passive_refines_full (initial .shadow), full_views_distinct⟩

/-- Compression removes the administrative event count while its independently
proved cover retains every formula answer, including component probes. -/
theorem compressed_description_exact (context : Set Query) (state : State) :
    FormulaDescriptions.describe coreModal context (coreView state) =
      FormulaDescriptions.describe modal context state := by
  apply PartialSections.View.ext
  · rfl
  intro query _ _
  exact propext (compression_preserves_and_reflects_formula query state)

end WorkspaceDescriptions

/-! ## Receipt-bearing workspace descriptions -/

namespace ReceiptDescriptions

open Mettapedia.CognitiveArchitecture.GodelClaw.GlobalWorkspace

abbrev Query := Formula (Atom Bool) (GodelClaw.GlobalWorkspace.Action Nat Bool)

/-- Queries restricted to published workspace content, without delivery
currency, specialist mediation or broker execution. -/
def contentContext : Set Query :=
  Set.range (fun history : Agent.EffectReceiptProjection.History =>
    Formula.atom (Atom.workspace history))

def full (state : State Nat Bool) : PartialSections.View Query Prop :=
  FormulaDescriptions.describe modal Set.univ state

def content (state : State Nat Bool) : PartialSections.View Query Prop :=
  FormulaDescriptions.describe modal contentContext state

def connected : State Nat Bool :=
  run (Controls.initial .connected false)
    (broadcastWord false true Agent.EffectReceiptProjection.successful)

def disconnected : State Nat Bool :=
  run (Controls.initial .shadow false)
    (broadcastWord false true Agent.EffectReceiptProjection.successful)

theorem connected_delivery_current : CurrentDelivery connected true := by
  rcases Controls.successful_receipt_is_broadcast_as_completed with
    ⟨delivery, received, current, linked, _⟩
  exact ⟨delivery, received, current, linked⟩

theorem disconnected_delivery_not_current : ¬ CurrentDelivery disconnected true :=
  Controls.split_receiver_and_sender_are_not_a_mediator.2.2

/-- Both real model executions publish identical histories.  Content-only
descriptions therefore agree even though specialist mediation differs. -/
theorem content_agrees : content connected = content disconnected := by
  have connectedContent : connected.context.view = Agent.EffectReceiptProjection.successful := by
    simp [connected, run, broadcastWord, step]
  have disconnectedContent : disconnected.context.view = Agent.EffectReceiptProjection.successful :=
    Controls.split_receiver_and_sender_are_not_a_mediator.1
  apply PartialSections.View.ext
  · rfl
  intro query member _
  obtain ⟨history, rfl⟩ := member
  change (connected.context.view = history) = (disconnected.context.view = history)
  rw [connectedContent, disconnectedContent]

/-- The existing current-delivery atom exposes the missing mediation. -/
theorem full_views_distinct : full connected ≠ full disconnected := by
  intro same
  have extension : full connected ≤ full disconnected := le_of_eq same
  have answer := extension.2 (Formula.atom (Atom.current true))
    (Set.mem_univ _) (Set.mem_univ _)
  exact disconnected_delivery_not_current (Eq.mp answer connected_delivery_current)

theorem content_refines_full (state : State Nat Bool) : content state ≤ full state :=
  FormulaDescriptions.describe_refines modal (Set.subset_univ _) state

/-- Receipt currency and causal access are explicit query distinctions rather
than judgments of subject identity from a copied content description. -/
theorem same_content_distinct_receipt_extensions :
    content connected ≤ full connected ∧ content connected ≤ full disconnected ∧
      full connected ≠ full disconnected :=
  ⟨content_refines_full _, content_agrees.symm ▸ content_refines_full disconnected,
    full_views_distinct⟩

/-- View coordinates for probes are exactly the existing execution predicates. -/
theorem probe_coordinate_exact (actions : List (GodelClaw.GlobalWorkspace.Action Nat Bool))
    (atom : Atom Bool)
    (state : State Nat Bool) :
    (full state).values ⟨probeFormula actions atom, Set.mem_univ _⟩ ↔
      observes atom (actionRun state actions) := probeFormula_exact actions atom state

end ReceiptDescriptions

/-! ## Assessor-indexed chronological descriptions -/

namespace AppraisalDescriptions

open Valence

universe uState uInput uValue uHypothesis uTarget uTargetInput uTargetHypothesis

variable {State : Type uState} {Input : Type uInput}
  {Value : Type uValue} [AddMonoid Value] {Hypothesis : Type uHypothesis}

/-- Retain a whole family of temporal appraisals.  Coordinates are individual
assessors and input words; no scalar summary of that family is selected. -/
def describe (context : Set (Hypothesis × List Input))
    (step : State → Input → State)
    (appraisal : Hypothesis → TransitionAppraisal State Input Value) (state : State) :
    PartialSections.View (Hypothesis × List Input) Value where
  context := context
  values query := accumulated step (appraisal query.val.1) state query.val.2

/-- The same source query interface, evaluated in the translated execution. -/
def translated {Target : Type uTarget} {TargetInput : Type uTargetInput}
    {TargetHypothesis : Type uTargetHypothesis}
    (context : Set (Hypothesis × List Input)) (step : Target → TargetInput → Target)
    (appraisal : TargetHypothesis → TransitionAppraisal Target TargetInput Value)
    (mapHypothesis : Hypothesis → TargetHypothesis) (mapInput : Input → TargetInput)
    (state : Target) : PartialSections.View (Hypothesis × List Input) Value where
  context := context
  values query := accumulated step (appraisal (mapHypothesis query.val.1)) state
    (query.val.2.map mapInput)

/-- Local tick and appraisal laws imply equality of every retained temporal
coordinate.  Additional target assessors or histories remain outside the claim. -/
theorem translated_exact {Target : Type uTarget} {TargetInput : Type uTargetInput}
    {TargetHypothesis : Type uTargetHypothesis}
    (context : Set (Hypothesis × List Input))
    (step : State → Input → State) (targetStep : Target → TargetInput → Target)
    (mapState : State → Target) (mapInput : Input → TargetInput)
    (mapHypothesis : Hypothesis → TargetHypothesis)
    (commutes : ∀ state input,
      mapState (step state input) = targetStep (mapState state) (mapInput input))
    (appraisal : Hypothesis → TransitionAppraisal State Input Value)
    (targetAppraisal : TargetHypothesis → TransitionAppraisal Target TargetInput Value)
    (agrees : ∀ hypothesis state input,
      targetAppraisal (mapHypothesis hypothesis) (mapState state) (mapInput input)
        (mapState (step state input)) = appraisal hypothesis state input (step state input))
    (state : State) :
    translated context targetStep targetAppraisal mapHypothesis mapInput (mapState state) =
      describe context step appraisal state := by
  apply PartialSections.View.ext
  · rfl
  intro query _ _
  exact accumulated_map step targetStep mapState mapInput commutes
    (appraisal query.1) (targetAppraisal (mapHypothesis query.1))
    (agrees query.1) state query.2

theorem describe_restrict (context observed : Set (Hypothesis × List Input))
    (step : State → Input → State)
    (appraisal : Hypothesis → TransitionAppraisal State Input Value) (state : State) :
    PartialSections.restrict observed (describe context step appraisal state) =
      describe (context ∩ observed) step appraisal state := by
  apply PartialSections.View.ext
  · rfl
  intro _ _ _
  rfl

end AppraisalDescriptions

/-! ## The constructed component-preserving machine recoding -/

namespace RecodedMachineDescriptions

open Mettapedia.GSLT.Causality.ScriptedExecution
open Mettapedia.GSLT.Causality.ScriptedExecutionRecoding
open Mettapedia.GSLT.AdmissibleContextCongruence
open Valence

variable {State Target Input Hypothesis Value : Type} [DecidableEq Input] [AddMonoid Value]

abbrev Query (State Input : Type) [DecidableEq Input] :=
  Formula ((componentClass (State := State) (Input := Input)).saturated observations).Atom
    ((componentClass (State := State) (Input := Input)).saturated observations).Label

/-- This cover uses the existing contextual realization square, including
conjugation of component-replacement commands and all table occurrences. -/
theorem formula_description_recode (coding : State ≃ Target)
    (context : Set (Query State Input)) (machine : Machine State Input) :
    FormulaDescriptions.translated (cover coding) context (recodeMachine coding machine) =
      FormulaDescriptions.describe (componentClass.saturated observations) context machine :=
  FormulaDescriptions.cover_description (cover coding) context machine

/-- Deliberately transport a declared appraisal by the proved inverse machine
recoding.  This constructs a re-encoding; it does not identify every target
appraisal with the source appraisal. -/
def recodedAppraisal (coding : State ≃ Target)
    (appraisal : Hypothesis → TransitionAppraisal (Machine State Input) Input Value) :
    Hypothesis → TransitionAppraisal (Machine Target Input) Input Value :=
  fun hypothesis before input after => appraisal hypothesis
    (recodeMachine coding.symm before) input (recodeMachine coding.symm after)

/-- The independently proved backup tick law transports every chronological
coordinate, with each assessor remaining separately indexed. -/
theorem appraisal_description_recode (coding : State ≃ Target)
    (context : Set (Hypothesis × List Input))
    (appraisal : Hypothesis → TransitionAppraisal (Machine State Input) Input Value)
    (machine : Machine State Input) :
    AppraisalDescriptions.translated context tick (recodedAppraisal coding appraisal)
        id id (recodeMachine coding machine) =
      AppraisalDescriptions.describe context tick appraisal machine := by
  apply AppraisalDescriptions.translated_exact context tick tick
    (recodeMachine coding) id id (tick_commutes coding) appraisal _ _ machine
  intro hypothesis before input
  simp only [recodedAppraisal, recodeMachine_inverse, id_eq]

end RecodedMachineDescriptions

end Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalRealization
