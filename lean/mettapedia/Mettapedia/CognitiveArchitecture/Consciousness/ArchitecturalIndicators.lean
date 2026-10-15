import Mettapedia.CognitiveArchitecture.Agent.WorldState
import Mettapedia.GSLT.Core.PredicateInvariance
import Mettapedia.GSLT.Logic.PrivilegedView
import Mettapedia.GSLT.Logic.ObserverRefinement
import Mettapedia.Logic.DisplayedAnytimeEvidence
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

/-!
# Architectural indicators, causal realization and observation refinement

Public sources:

* Butlin, Long et al., *Consciousness in Artificial Intelligence: Insights
  from the Science of Consciousness* (2023), Tables 1–2,
  https://arxiv.org/abs/2308.08708 .
* Butlin, Long et al., *Identifying indicators of consciousness in AI systems*,
  https://doi.org/10.1016/j.tics.2025.10.011 .
* Kanai and Ma, *Canonical Functionalism* (2026), §§5–6 and 12,
  https://arxiv.org/abs/2605.21506 .

The source catalogue records fourteen indicators, not fourteen completed
formalizations. The mechanistic contracts below refine workspace broadcast,
feedback and state-dependent selection on an explicit two-module architecture.
They do not define or establish phenomenal consciousness, integrated perceptual
representation, complex-task competence, or all of global workspace theory.

The architecture uses the existing `AgentState`. Its genuine transitions,
interventions and observations form a GSLT and its existing modal system.
Compression is checked by a two-sided system cover; observer refinement is
relative to the admitted commands and atomic observations. Proof receipts
retain the concrete starting state separately from the compressed view.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Core.PredicateInvariance
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.CognitiveArchitecture.Agent.WorldState
open Mettapedia.Logic.DisplayedAnytimeEvidence
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

/-! ## Source catalogue -/

inductive TheoryFamily where
  | recurrentProcessing | globalWorkspace | higherOrder
  | attentionSchema | predictiveProcessing | agencyEmbodiment
  deriving DecidableEq, Repr

inductive Indicator where
  | rpt1 | rpt2 | gwt1 | gwt2 | gwt3 | gwt4
  | hot1 | hot2 | hot3 | hot4 | ast1 | pp1 | ae1 | ae2
  deriving DecidableEq, Repr

def Indicator.family : Indicator → TheoryFamily
  | .rpt1 | .rpt2 => .recurrentProcessing
  | .gwt1 | .gwt2 | .gwt3 | .gwt4 => .globalWorkspace
  | .hot1 | .hot2 | .hot3 | .hot4 => .higherOrder
  | .ast1 => .attentionSchema
  | .pp1 => .predictiveProcessing
  | .ae1 | .ae2 => .agencyEmbodiment

/-! ## One architecture, actual updates and interventions -/

inductive Mode where
  | connected | shadow
  deriving DecidableEq, Repr

/-- Two Boolean processing modules. False selects the first module. -/
abbrev Module := Bool

/-- Proposals and a private replay copy of the last published value. -/
abbrev Operational := (Bool × Bool) × Bool

/-- Workspace contents and the last public report. -/
abbrev Context := Bool × Bool

/-- The event count, attention selection, workspace and realization mode remain
separate fields of the existing architecture-neutral agent state. -/
abbrev State := AgentState Operational Nat Module Context Mode

def proposal (bank : Bool × Bool) (module : Module) : Bool :=
  if module then bank.2 else bank.1

def setProposal (bank : Bool × Bool) (module : Module) (value : Bool) : Bool × Bool :=
  if module then (bank.1, value) else (value, bank.2)

inductive PassiveInput where
  | sense (module : Module) (value : Bool)
  | ignite
  | consume (module : Module)
  deriving DecidableEq, Repr

inductive Input where
  | ordinary (command : PassiveInput)
  | overwriteWorkspace (value : Bool)
  deriving DecidableEq, Repr

def reading (state : State) : Bool :=
  match state.capabilities with
  | .connected => state.context.1
  | .shadow => state.operational.2

/-- The shadow uses its private copy. An intervention changes the workspace
alone, so agreement in ordinary operation does not fabricate causal access. -/
def step (state : State) : Input → State
  | .ordinary (.sense module value) =>
      { state with operational :=
          (setProposal state.operational.1 module value, state.operational.2) }
  | .ordinary .ignite =>
      let value := proposal state.operational.1 state.commitments
      { state with
        operational := (state.operational.1, value)
        context := (value, state.context.2) }
  | .ordinary (.consume module) =>
      let value := reading state
      { state with
        operational := (setProposal state.operational.1 module value, state.operational.2)
        evidence := state.evidence + 1
        commitments := value
        context := (state.context.1, value) }
  | .overwriteWorkspace value =>
      { state with context := (value, state.context.2) }

def run (state : State) (commands : List Input) : State := commands.foldl step state

def passiveStep (state : State) (command : PassiveInput) : State :=
  step state (.ordinary command)

def evaluation (state : State) : Bool × Bool × Module :=
  (state.context.1, state.context.2, state.commitments)

def fullFuture : State → List Input → Bool × Bool × Module :=
  PrivilegedView.wordBehaviour step evaluation

def passiveFuture : State → List PassiveInput → Bool × Bool × Module :=
  PrivilegedView.wordBehaviour passiveStep evaluation

/-- The private copy is synchronized during ordinary operation. -/
def Coherent (state : State) : Prop := state.context.1 = state.operational.2

def ordinaryView (state : State) : Operational × Nat × Module × Context :=
  (state.operational, state.evidence, state.commitments, state.context)

def initial (mode : Mode) : State :=
  ⟨((false, true), false), 0, false, (false, false), mode⟩

theorem initial_coherent (mode : Mode) : Coherent (initial mode) := rfl

theorem reading_eq_workspace {state : State} (coherent : Coherent state) :
    reading state = state.context.1 := by
  cases mode : state.capabilities <;> simp [reading, mode]
  exact coherent.symm

theorem coherent_passiveStep {state : State} (coherent : Coherent state)
    (command : PassiveInput) : Coherent (passiveStep state command) := by
  cases command <;> simp [Coherent, passiveStep, step] <;> exact coherent

theorem ordinaryView_passiveStep {first second : State}
    (firstCoherent : Coherent first) (secondCoherent : Coherent second)
    (same : ordinaryView first = ordinaryView second) (command : PassiveInput) :
    ordinaryView (passiveStep first command) = ordinaryView (passiveStep second command) := by
  have op : first.operational = second.operational := congrArg Prod.fst same
  have count : first.evidence = second.evidence := congrArg (fun value => value.2.1) same
  have attention : first.commitments = second.commitments := congrArg (fun value => value.2.2.1) same
  have context : first.context = second.context := congrArg (fun value => value.2.2.2) same
  cases command <;>
    simp [ordinaryView, passiveStep, step, reading_eq_workspace firstCoherent,
      reading_eq_workspace secondCoherent, op, count, attention, context]

/-- Agreement covers every ordinary input word, not a selected execution. -/
theorem passiveFuture_eq_of_coherent_views {first second : State}
    (firstCoherent : Coherent first) (secondCoherent : Coherent second)
    (same : ordinaryView first = ordinaryView second) :
    passiveFuture first = passiveFuture second := by
  funext commands
  induction commands generalizing first second with
  | nil =>
      exact congrArg (fun value => (value.2.2.2.1, value.2.2.2.2, value.2.2.1)) same
  | cons command commands inductionHypothesis =>
      exact inductionHypothesis (coherent_passiveStep firstCoherent command)
        (coherent_passiveStep secondCoherent command)
        (ordinaryView_passiveStep firstCoherent secondCoherent same command)

theorem ordinary_interactions_cannot_separate_modes :
    passiveFuture (initial .connected) = passiveFuture (initial .shadow) :=
  passiveFuture_eq_of_coherent_views (initial_coherent _) (initial_coherent _) rfl

/-- Independent sensory updates admit either schedule on every state. -/
theorem parallel_sensory_updates (state : State) (left right : Bool) :
    passiveStep (passiveStep state (.sense false left)) (.sense true right) =
      passiveStep (passiveStep state (.sense true right)) (.sense false left) := by
  simp [passiveStep, step, setProposal]

/-- One Boolean workspace cannot injectively retain both proposal bits. -/
theorem limited_workspace_capacity :
    Fintype.card Bool < Fintype.card (Bool × Bool) := by decide

theorem selection_is_lossy (module : Module) : ¬ Function.Injective (fun bank => proposal bank module) := by
  cases module
  · intro injective
    have same : (false, false) = (false, true) := injective rfl
    have impossible := congrArg Prod.snd same
    cases impossible
  · intro injective
    have same : (false, false) = (true, false) := injective rfl
    have impossible := congrArg Prod.fst same
    cases impossible

/-! ## Operational indicator contracts -/

def broadcastWord (module : Module) (value : Bool) : List Input :=
  [.overwriteWorkspace value, .ordinary (.consume module)]

/-- Clear the workspace before the return step: mere retention cannot pass
this probe. Both modules must supply the previously received value. -/
def feedbackWord (value : Bool) : List Input :=
  [.overwriteWorkspace value, .ordinary (.consume false),
    .ordinary (.consume true), .overwriteWorkspace (!value), .ordinary .ignite]

def Broadcasts (state : State) : Prop :=
  ∀ module value, (run state (broadcastWord module value)).context.2 = value

def Feedback (state : State) : Prop :=
  ∀ value, (run state (feedbackWord value)).context.1 = value

def StateDependentSelection (state : State) : Prop :=
  ∀ value, (run state (broadcastWord false value)).commitments = value

theorem connected_broadcasts (state : State) (connected : state.capabilities = .connected) :
    Broadcasts state := by
  intro module value
  simp [run, broadcastWord, step, reading, connected]

theorem connected_feedback (state : State) (connected : state.capabilities = .connected) :
    Feedback state := by
  intro value
  cases value <;>
    simp [run, feedbackWord, step, reading, connected, setProposal, proposal]

theorem connected_selection (state : State) (connected : state.capabilities = .connected) :
    StateDependentSelection state := by
  intro value
  simp [run, broadcastWord, step, reading, connected]

theorem shadow_not_broadcasts (state : State) (shadow : state.capabilities = .shadow) :
    ¬ Broadcasts state := by
  intro broadcasts
  have first := broadcasts false false
  have second := broadcasts false true
  simp [run, broadcastWord, step, reading, shadow] at first second
  exact Bool.false_ne_true (first.symm.trans second)

theorem shadow_not_feedback (state : State) (shadow : state.capabilities = .shadow) :
    ¬ Feedback state := by
  intro feedback
  have first := feedback false
  have second := feedback true
  cases copy : state.operational.2 <;>
    simp [run, feedbackWord, step, reading, shadow, copy, setProposal, proposal] at first second

theorem shadow_not_selection (state : State) (shadow : state.capabilities = .shadow) :
    ¬ StateDependentSelection state := by
  intro selects
  have first := selects false
  have second := selects true
  simp [run, broadcastWord, step, reading, shadow] at first second
  exact Bool.false_ne_true (first.symm.trans second)

theorem passive_future_does_not_determine_broadcast : ¬ Factors passiveFuture Broadcasts :=
  (NonTrivialFiber.ofProp ordinary_interactions_cannot_separate_modes
    (connected_broadcasts (initial .connected) rfl)
    (shadow_not_broadcasts (initial .shadow) rfl)).not_factors

/-! ## The existing GSLT and modal interfaces -/

def theory : GSLT :=
  equalityGSLT State (fun source target => ∃ command, step source command = target)

inductive Field where
  | workspace | report | attention
  deriving DecidableEq, Repr

abbrev Atom := Field × Bool

def observes (atom : Atom) (state : State) : Prop :=
  (match atom.1 with
    | .workspace => state.context.1
    | .report => state.context.2
    | .attention => state.commitments) = atom.2

def modal : System theory where
  Atom := Atom
  observes := observes
  observes_resp := by intro atom left right same; cases same; rfl
  Label := Input
  act command source target := step source command = target
  act_resp_left := by
    intro command source other target same advances
    cases same
    exact ⟨target, advances, rfl⟩
  act_resp_right := by
    intro command source target other advances same
    cases same
    exact advances

def probeFormula (commands : List Input) (atom : Atom) : Formula Atom Input :=
  Formula.after commands (.atom atom)

theorem probeFormula_exact (commands : List Input) (atom : Atom) (state : State) :
    modal.sat (probeFormula commands atom) state ↔ observes atom (run state commands) := by
  exact modal.sat_after_deterministic step (fun _ _ _ => Iff.rfl) commands (.atom atom) state

theorem broadcast_modal_iff (state : State) :
    Broadcasts state ↔ ∀ module value,
      modal.sat (probeFormula (broadcastWord module value) (.report, value)) state := by
  simp only [Broadcasts, probeFormula_exact, observes]

theorem feedback_modal_iff (state : State) :
    Feedback state ↔ ∀ value,
      modal.sat (probeFormula (feedbackWord value) (.workspace, value)) state := by
  simp only [Feedback, probeFormula_exact, observes]

theorem selection_modal_iff (state : State) :
    StateDependentSelection state ↔ ∀ value,
      modal.sat (probeFormula (broadcastWord false value) (.attention, value)) state := by
  simp only [StateDependentSelection, probeFormula_exact, observes]

/-- The probe predicates are native types generated by the existing OSLF
construction on this architecture's GSLT. -/
def probeNativeType (commands : List Input) (atom : Atom) : GSLTNativeType theory :=
  formulaNativeType modal (probeFormula commands atom)

theorem broadcast_nativeType_iff (state : State) :
    Broadcasts state ↔ ∀ module value,
      (gsltOSLF theory).satisfies (S := ()) state
        (probeNativeType (broadcastWord module value) (.report, value)).pred :=
  broadcast_modal_iff state

theorem feedback_nativeType_iff (state : State) :
    Feedback state ↔ ∀ value,
      (gsltOSLF theory).satisfies (S := ()) state
        (probeNativeType (feedbackWord value) (.workspace, value)).pred :=
  feedback_modal_iff state

/-- Ordinary inputs select a coarser observer of the same operational states. -/
def passiveModal : System theory where
  Atom := Atom
  observes := observes
  observes_resp := modal.observes_resp
  Label := PassiveInput
  act command source target := passiveStep source command = target
  act_resp_left := by
    intro command source other target same advances
    cases same
    exact ⟨target, advances, rfl⟩
  act_resp_right := by
    intro command source target other advances same
    cases same
    exact advances

/-- Adding declared interventions is the existing observer refinement, not a
new notion of equivalence. -/
def interventionRefinement : ObserverRefinement passiveModal modal where
  mapAtom := id
  mapLabel := Input.ordinary
  observes_iff _ _ := Iff.rfl
  act_iff _ _ _ := Iff.rfl

theorem ordinary_formulas_refine (formula : Formula Atom PassiveInput) (state : State) :
    modal.sat (formula.map id Input.ordinary) state ↔ passiveModal.sat formula state :=
  interventionRefinement.sat_refine formula state

theorem passive_modes_bisimilar :
    passiveModal.Bisimilar (initial .connected) (initial .shadow) := by
  refine ⟨fun first second =>
    Coherent first ∧ Coherent second ∧ ordinaryView first = ordinaryView second,
    ⟨?_, ?_, ?_⟩, initial_coherent _, initial_coherent _, rfl⟩
  · intro first second related command next advances
    change passiveStep first command = next at advances
    cases advances
    exact ⟨passiveStep second command, rfl, coherent_passiveStep related.1 command,
      coherent_passiveStep related.2.1 command,
      ordinaryView_passiveStep related.1 related.2.1 related.2.2 command⟩
  · intro first second related command next advances
    change passiveStep second command = next at advances
    cases advances
    exact ⟨passiveStep first command, rfl, coherent_passiveStep related.1 command,
      coherent_passiveStep related.2.1 command,
      ordinaryView_passiveStep related.1 related.2.1 related.2.2 command⟩
  · intro first second related atom
    have context : first.context = second.context :=
      congrArg (fun value => value.2.2.2) related.2.2
    have attention : first.commitments = second.commitments :=
      congrArg (fun value => value.2.2.1) related.2.2
    cases atom.1 <;> simp [passiveModal, observes, context, attention]

theorem intervention_separates_modes :
    modal.sat (probeFormula (broadcastWord false true) (.report, true)) (initial .connected) ∧
      ¬ modal.sat (probeFormula (broadcastWord false true) (.report, true)) (initial .shadow) := by
  simp [probeFormula_exact, observes, run, broadcastWord, step, reading, initial]

theorem intervention_modes_not_bisimilar :
    ¬ modal.Bisimilar (initial .connected) (initial .shadow) := by
  intro bisimilar
  exact intervention_separates_modes.2
    ((modal.logicallyEquivalent_of_bisimilar bisimilar _).mp intervention_separates_modes.1)

/-! ## A nonidentity compression with full outgoing coverage -/

abbrev CoreState := Operational × Module × Context × Mode

def coreView (state : State) : CoreState :=
  (state.operational, state.commitments, state.context, state.capabilities)

def restore (core : CoreState) : State := ⟨core.1, 0, core.2.1, core.2.2.1, core.2.2.2⟩

def coreStep (core : CoreState) (command : Input) : CoreState :=
  coreView (step (restore core) command)

theorem coreStep_commutes (state : State) (command : Input) :
    coreView (step state command) = coreStep (coreView state) command := by
  cases command with
  | ordinary ordinary => cases ordinary <;> rfl
  | overwriteWorkspace _ => rfl

def coreTheory : GSLT :=
  equalityGSLT CoreState (fun source target => ∃ command, coreStep source command = target)

def coreModal : System coreTheory where
  Atom := Atom
  observes atom core := observes atom (restore core)
  observes_resp := by intro atom left right same; cases same; rfl
  Label := Input
  act command source target := coreStep source command = target
  act_resp_left := by
    intro command source other target same advances
    cases same
    exact ⟨target, advances, rfl⟩
  act_resp_right := by
    intro command source target other advances same
    cases same
    exact advances

/-- The compressed transition computes updates, and every outgoing compressed
step lifts to an actual concrete step. No finite transition catalogue is used. -/
def compression : SystemCover modal coreModal where
  mapTerm := coreView
  mapAtom := id
  mapLabel := id
  mapEquiv := by intro left right same; cases same; rfl
  observes_iff := by intro atom state; cases atom.1 <;> rfl
  mapAct := by
    intro command source target advances
    change step source command = target at advances
    cases advances
    exact (coreStep_commutes source command).symm
  liftAct := by
    intro command source target advances
    exact ⟨step source command, rfl, (coreStep_commutes source command).trans advances⟩

theorem compression_preserves_and_reflects_formula (formula : Formula Atom Input) (state : State) :
    coreModal.sat formula (coreView state) ↔ modal.sat formula state := by
  simpa only [compression, coreModal, modal, Formula.map_id] using
    compression.sat_map formula state

theorem formula_factors_coreView (formula : Formula Atom Input) :
    Factors coreView (modal.sat formula) :=
  ⟨coreModal.sat formula, fun state =>
    propext (compression_preserves_and_reflects_formula formula state)⟩

theorem compression_preserves_and_reflects_nativeType
    (formula : Formula Atom Input) (state : State) :
    (gsltOSLF coreTheory).satisfies (S := ()) (coreView state)
        (formulaNativeType coreModal formula).pred ↔
      (gsltOSLF theory).satisfies (S := ()) state (formulaNativeType modal formula).pred :=
  compression_preserves_and_reflects_formula formula state

theorem coreView_stable : PrivilegedView.StableUnder step coreView := by
  intro first second same command
  rw [coreStep_commutes, coreStep_commutes, same]

theorem coreView_keeps_evaluation : Factors coreView evaluation :=
  ⟨fun core => (core.2.2.1.1, core.2.2.1.2, core.2.1), fun _ => rfl⟩

/-- The existing canonical future-view theorem applies to the actual update
function and chosen evaluation; no new minimality axiom is introduced. -/
theorem coreView_keeps_full_future : Factors coreView fullFuture :=
  PrivilegedView.factors_wordBehaviour coreView_stable coreView_keeps_evaluation

/-- The three mechanistic questions are deliberately narrower than the
source indicators or a consciousness diagnosis. -/
inductive WorkspaceQuery where
  | broadcast | feedback | selection
  deriving DecidableEq, Repr

def workspaceAnswer (state : State) : WorkspaceQuery → Prop
  | .broadcast => Broadcasts state
  | .feedback => Feedback state
  | .selection => StateDependentSelection state

def coreAnswer (core : CoreState) : WorkspaceQuery → Prop
  | .broadcast => ∀ module value,
      coreModal.sat (probeFormula (broadcastWord module value) (.report, value)) core
  | .feedback => ∀ value,
      coreModal.sat (probeFormula (feedbackWord value) (.workspace, value)) core
  | .selection => ∀ value,
      coreModal.sat (probeFormula (broadcastWord false value) (.attention, value)) core

theorem coreView_queryComplete : QueryComplete workspaceAnswer coreView := by
  refine ⟨coreAnswer, ?_⟩
  intro state query
  apply propext
  cases query with
  | broadcast =>
      change (∀ module value, coreModal.sat _ (coreView state)) ↔ Broadcasts state
      simp only [compression_preserves_and_reflects_formula, ← broadcast_modal_iff]
  | feedback =>
      change (∀ value, coreModal.sat _ (coreView state)) ↔ Feedback state
      simp only [compression_preserves_and_reflects_formula, ← feedback_modal_iff]
  | selection =>
      change (∀ value, coreModal.sat _ (coreView state)) ↔ StateDependentSelection state
      simp only [compression_preserves_and_reflects_formula, ← selection_modal_iff]

/-- Complete future behavior also answers these questions, using the declared
workspace, report and attention outputs at the selected intervention words. -/
def futureAnswer (future : List Input → Bool × Bool × Module) : WorkspaceQuery → Prop
  | .broadcast => ∀ module value, (future (broadcastWord module value)).2.1 = value
  | .feedback => ∀ value, (future (feedbackWord value)).1 = value
  | .selection => ∀ value, (future (broadcastWord false value)).2.2 = value

theorem fullFuture_queryComplete : QueryComplete workspaceAnswer fullFuture :=
  ⟨futureAnswer, fun _ query => by cases query <;> rfl⟩

theorem passiveFuture_not_queryComplete : ¬ QueryComplete workspaceAnswer passiveFuture := by
  rintro ⟨recover, recovers⟩
  apply passive_future_does_not_determine_broadcast
  exact ⟨fun future => recover future .broadcast, fun state => recovers state .broadcast⟩

def counted (count : Nat) : State := { initial .connected with evidence := count }

theorem different_counts_same_core : coreView (counted 0) = coreView (counted 7) := rfl

theorem event_counts_do_not_factor_core : ¬ Factors coreView (fun state => state.evidence) :=
  (NonTrivialFiber.mk (counted 0) (counted 7) different_counts_same_core (by decide)).not_factors

theorem different_counts_same_full_future : fullFuture (counted 0) = fullFuture (counted 7) :=
  coreView_keeps_full_future.constantOnFibers _ _ different_counts_same_core

/-- Even complete behavior at the declared interface does not determine an
unobserved event count. Enlarging the output interface would change this claim. -/
theorem event_counts_do_not_factor_fullFuture :
    ¬ Factors fullFuture (fun state => state.evidence) :=
  (NonTrivialFiber.mk (counted 0) (counted 7) different_counts_same_full_future
    (by decide)).not_factors

/-! ## Retained evidence at refinement stages -/

/-- Concrete probe endpoints and paths retain the starting state and the
selected module/value intervention, beyond the Boolean assessment. -/
structure BroadcastReceipt (state : State) where
  final : Module → Bool → State
  path : ∀ module value, theory.RewritePath state (final module value)
  pathLength : ∀ module value, (path module value).length = (broadcastWord module value).length
  follows : ∀ module value, final module value = run state (broadcastWord module value)
  reports : ∀ module value, (final module value).context.2 = value

def pathOfCommands (state : State) : (commands : List Input) →
    theory.RewritePath state (run state commands)
  | [] => by
      change theory.RewritePath state state
      exact GSLT.RewritePath.nil (S := theory) state
  | command :: commands =>
      .cons ⟨command, rfl⟩ (pathOfCommands (step state command) commands)

theorem pathOfCommands_length (state : State) (commands : List Input) :
    (pathOfCommands state commands).length = commands.length := by
  induction commands generalizing state with
  | nil => rfl
  | cons command commands inductionHypothesis =>
      exact (congrArg (fun length => 1 + length)
        (inductionHypothesis (step state command))).trans (Nat.add_comm 1 commands.length)

def broadcastReceipt (state : State) (broadcasts : Broadcasts state) : BroadcastReceipt state where
  final module value := run state (broadcastWord module value)
  path module value := pathOfCommands state (broadcastWord module value)
  pathLength module value := pathOfCommands_length state (broadcastWord module value)
  follows _ _ := rfl
  reports := broadcasts

theorem BroadcastReceipt.sound {state : State} (receipt : BroadcastReceipt state) :
    Broadcasts state := by
  intro module value
  rw [← receipt.follows module value]
  exact receipt.reports module value

/-- The existing displayed evidence contract retains the same receipt when
the allowed probe depth increases. An absent receipt is not a refutation. -/
def broadcastEvidence (state : State) : MonotoneEvidence (Broadcasts state) where
  EvidenceAt stage := {receipt : BroadcastReceipt state //
    ∀ module value, (receipt.path module value).length ≤ stage}
  persist bounded receipt :=
    ⟨receipt.val, fun module value => Nat.le_trans (receipt.property module value) bounded⟩
  sound receipt := receipt.val.sound

theorem no_broadcast_receipt_at_depth_one (state : State) :
    ¬ Nonempty ((broadcastEvidence state).EvidenceAt 1) := by
  rintro ⟨receipt⟩
  have bounded := receipt.property false false
  rw [receipt.val.pathLength] at bounded
  change 2 ≤ 1 at bounded
  omega

theorem connected_has_depth_two_receipt :
    Nonempty ((broadcastEvidence (initial .connected)).EvidenceAt 2) :=
  ⟨⟨broadcastReceipt _ (connected_broadcasts _ rfl), fun module value => by
    rw [BroadcastReceipt.pathLength]
    exact Nat.le_refl _⟩⟩

theorem broadcastEvidence_retains_receipt {state : State} {earlier later : Nat}
    (bounded : earlier ≤ later) (receipt : (broadcastEvidence state).EvidenceAt earlier) :
    ((broadcastEvidence state).persist bounded receipt).val = receipt.val := rfl

theorem receipt_endpoints_keep_event_count (count : Nat) (module : Module) (value : Bool) :
    ((broadcastReceipt (counted count) (connected_broadcasts _ rfl)).final module value).evidence =
      count + 1 := by
  simp [broadcastReceipt, run, broadcastWord, step, counted, initial]

/-- Equal architectural behavior does not identify concrete proof endpoints. -/
theorem equal_behavior_distinct_receipt_endpoints :
    fullFuture (counted 0) = fullFuture (counted 7) ∧
      (broadcastReceipt (counted 0) (connected_broadcasts _ rfl)).final false true ≠
        (broadcastReceipt (counted 7) (connected_broadcasts _ rfl)).final false true := by
  refine ⟨different_counts_same_full_future, ?_⟩
  intro same
  have counts := congrArg (fun state : State => state.evidence) same
  simp only [receipt_endpoints_keep_event_count] at counts
  omega

theorem shadow_has_no_receipt (stage : Nat) :
    ¬ Nonempty ((broadcastEvidence (initial .shadow)).EvidenceAt stage) := by
  rintro ⟨receipt⟩
  exact shadow_not_broadcasts _ rfl ((broadcastEvidence _).sound receipt)

end Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators
