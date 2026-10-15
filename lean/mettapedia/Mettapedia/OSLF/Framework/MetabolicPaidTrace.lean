import Mettapedia.CognitiveArchitecture.Consciousness.PaidWorkspaceExperiments

/-!
# Actual paid learner events before metabolic coupling

The staged event relation keeps actual architectural commands and actual
funded probe occurrences. Its handoff offers only a calibrated public field
of the reached architectural state. Every event carries its own actual
charge, and the purse before the event is exactly its charge plus the purse
afterwards. This exposes the individual payments that a metabolic controller
must implement, rather than appending a withdrawal to an already read answer.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.MetabolicPaidTrace

open Mettapedia.GSLT
open Mettapedia.GSLT.Causality
open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.ProbeCampaign
open Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators
open Mettapedia.CognitiveArchitecture.Consciousness.PaidWorkspaceExperiments

abbrev AssayResources := AssayProbeDelivery.Resources Bool Nat Nat ⊕ Unit

abbrev assaySystem (question : Question) : System AssayResources :=
  AssayProbeDelivery.paid (protocol.test question)
    (protocol.deliveryCost question) (protocol.inspectionCost question)

abbrev assayPrice (question : Question) {site : (assaySystem question).Site}
    (firing : (assaySystem question).Instance site) : Multiset Unit :=
  AssayProbeDelivery.price (protocol.test question)
    (protocol.deliveryCost question) (protocol.inspectionCost question) firing

inductive Marking where
  | probe (state : State) (budget : Nat)
  | assay (resources : Multiset AssayResources)

def purse : Marking → Nat
  | .probe _ budget => budget
  | .assay resources => (rightPart resources).card

def responses : Marking → Multiset (Response Bool Nat)
  | .probe _ _ => 0
  | .assay resources => AssayProbeDelivery.outputs (leftPart resources)

/-- These are the original paid events, not inferred consequences of a
public answer. A calibrated handoff carries no verdict. -/
inductive Event (question : Question) : Marking → Marking → Type where
  | command (state : State) (budget : Nat) (command : Input)
      (affordable : 1 ≤ budget) :
      Event question (.probe state budget) (.probe (step state command) (budget - 1))
  | handoff (state : State) (budget session provider client : Nat) (arrival : Option Bool)
      (calibrated : ∀ value, arrival = some value → value = readField question.field state) :
      Event question (.probe state budget)
        (.assay (AssayProbeDelivery.initial session provider client arrival budget))
  | assay {source target : Multiset AssayResources}
      (occurrence : Occurrence (assaySystem question).presentation source target) :
      Event question (.assay source) (.assay target)

namespace Event

variable {question : Question} {source target : Marking}

def charge : Event question source target → Nat
  | .command _ _ _ _ => 1
  | .handoff _ _ _ _ _ _ _ => 0
  | .assay occurrence => (assayPrice question occurrence.evidence.val).card

def commands : Event question source target → List Input
  | .command _ _ instruction _ => [instruction]
  | .handoff _ _ _ _ _ _ _ => []
  | .assay _ => []

def assayEntries : Event question source target → List (assaySystem question).Entry
  | .command _ _ _ _ => []
  | .handoff _ _ _ _ _ _ _ => []
  | .assay occurrence => [⟨occurrence.site, occurrence.evidence.val⟩]

/-- The event's funding law is earned from its actual source purse and
occurrence, including both delivery and inspection instances. -/
theorem balance (event : Event question source target) :
    purse source = purse target + event.charge := by
  cases event with
  | command state budget command affordable =>
      change budget = budget - 1 + 1
      omega
  | handoff state budget session provider client arrival calibrated =>
      cases arrival <;>
        simp only [purse, charge, AssayProbeDelivery.initial,
          AssayProbeDelivery.paidOffered, rightPart_marking, ComplementaryAssay.purse,
          Multiset.card_replicate, Nat.add_zero]
  | @assay first last occurrence =>
      have enabled : (assaySystem question).Enables
          (marking (leftPart first) (rightPart first)) occurrence.evidence.val := by
        rw [marking_leftPart_rightPart]
        exact occurrence.evidence.property.1
      have conserved := funded_tokens_conserved
        (AssayProbeDelivery.system (protocol.test question))
        (@AssayProbeDelivery.price Bool Nat Nat (protocol.test question)
          (protocol.deliveryCost question) (protocol.inspectionCost question))
        (leftPart first) (rightPart first) occurrence.evidence.val enabled
      have targetPurse : rightPart last = rightPart first - assayPrice question occurrence.evidence.val := by
        have atSource := congrArg
          (fun resources => (assaySystem question).fire resources occurrence.evidence.val)
          (marking_leftPart_rightPart first)
        have fired := funded_fire
          (AssayProbeDelivery.system (protocol.test question))
          (@AssayProbeDelivery.price Bool Nat Nat (protocol.test question)
            (protocol.deliveryCost question) (protocol.inspectionCost question))
          (leftPart first) (rightPart first) occurrence.evidence.val
        have reached := occurrence.evidence.property.2.trans (atSource.symm.trans fired)
        exact (congrArg rightPart reached).trans (rightPart_marking _ _)
      have counted := congrArg Multiset.card conserved
      change (rightPart first).card = (rightPart last).card +
        (assayPrice question occurrence.evidence.val).card
      rw [targetPurse]
      simpa only [Multiset.card_add] using counted

theorem affordable (event : Event question source target) : event.charge ≤ purse source := by
  have conserved := event.balance
  omega

end Event

inductive Path (question : Question) : Marking → Marking → Type where
  | nil (state : Marking) : Path question state state
  | cons {source middle target : Marking} (event : Event question source middle)
      (rest : Path question middle target) : Path question source target

namespace Path

variable {question : Question}

def append {source middle target : Marking} :
    Path question source middle → Path question middle target → Path question source target
  | .nil _, later => later
  | .cons event rest, later => .cons event (append rest later)

def charges : {source target : Marking} → Path question source target → List Nat
  | _, _, .nil _ => []
  | _, _, .cons event rest => event.charge :: charges rest

def spent {source target : Marking} (path : Path question source target) : Nat := path.charges.sum

def commands : {source target : Marking} → Path question source target → List Input
  | _, _, .nil _ => []
  | _, _, .cons event rest => event.commands ++ commands rest

def assayEntries : {source target : Marking} → Path question source target → List (assaySystem question).Entry
  | _, _, .nil _ => []
  | _, _, .cons event rest => event.assayEntries ++ assayEntries rest

theorem ledger {source target : Marking} (path : Path question source target) :
    purse source = purse target + path.spent := by
  induction path with
  | nil _ => simp [spent, charges]
  | cons event rest inductionHypothesis =>
      have conserved := event.balance
      change _ = _ + (event.charge + rest.spent)
      omega

theorem spent_append {source middle target : Marking}
    (first : Path question source middle) (later : Path question middle target) :
    (first.append later).spent = first.spent + later.spent := by
  induction first with
  | nil _ => simp [append, spent, charges]
  | cons event rest inductionHypothesis =>
      change event.charge + (rest.append later).spent =
        (event.charge + rest.spent) + later.spent
      rw [inductionHypothesis, Nat.add_assoc]

theorem commands_append {source middle target : Marking}
    (first : Path question source middle) (later : Path question middle target) :
    (first.append later).commands = first.commands ++ later.commands := by
  induction first with
  | nil _ => rfl
  | cons event rest inductionHypothesis =>
      change event.commands ++ (rest.append later).commands =
        (event.commands ++ rest.commands) ++ later.commands
      rw [inductionHypothesis, List.append_assoc]

theorem assayEntries_append {source middle target : Marking}
    (first : Path question source middle) (later : Path question middle target) :
    (first.append later).assayEntries = first.assayEntries ++ later.assayEntries := by
  induction first with
  | nil _ => rfl
  | cons event rest inductionHypothesis =>
      change event.assayEntries ++ (rest.append later).assayEntries =
        (event.assayEntries ++ rest.assayEntries) ++ later.assayEntries
      rw [inductionHypothesis, List.append_assoc]

end Path

def fromProbe (question : Question) : {state target : State} → {budget remaining : Nat} →
    {commands : List Input} → PaidWord step state budget commands target remaining →
      Path question (.probe state budget) (.probe target remaining)
  | _, _, _, _, _, .nil state budget => .nil (.probe state budget)
  | state, _, budget, _, command :: _, .cons affordable rest =>
      .cons (.command state budget command affordable) (fromProbe question rest)

theorem fromProbe_commands (question : Question) {state target : State} {budget remaining : Nat}
    {commands : List Input} (path : PaidWord step state budget commands target remaining) :
    (fromProbe question path).commands = commands := by
  induction path with
  | nil => rfl
  | cons _ _ inductionHypothesis =>
      simp only [fromProbe, Path.commands, Event.commands, List.singleton_append, inductionHypothesis]

theorem fromProbe_entries (question : Question) {state target : State} {budget remaining : Nat}
    {commands : List Input} (path : PaidWord step state budget commands target remaining) :
    (fromProbe question path).assayEntries = [] := by
  induction path with
  | nil => rfl
  | cons _ _ inductionHypothesis => exact inductionHypothesis

def fromAssay (question : Question) : {source target : Multiset AssayResources} →
    OccurrencePath (assaySystem question).presentation source target →
      Path question (.assay source) (.assay target)
  | _, _, .refl state => .nil (.assay state)
  | _, _, .cons occurrence rest => .cons (.assay occurrence) (fromAssay question rest)

theorem fromAssay_commands (question : Question) :
    {source target : Multiset AssayResources} →
    (path : OccurrencePath (assaySystem question).presentation source target) →
    (fromAssay question path).commands = []
  | _, _, .refl _ => rfl
  | _, _, .cons _ rest => fromAssay_commands question rest

theorem fromAssay_entries (question : Question) :
    {source target : Multiset AssayResources} →
    (path : OccurrencePath (assaySystem question).presentation source target) →
    (fromAssay question path).assayEntries = (assaySystem question).pathEntries path
  | _, _, .refl _ => rfl
  | _, _, .cons occurrence rest => by
      change (⟨occurrence.site, occurrence.evidence.val⟩ : (assaySystem question).Entry) ::
        (fromAssay question rest).assayEntries =
        ⟨occurrence.site, occurrence.evidence.val⟩ :: (assaySystem question).pathEntries rest
      exact congrArg (List.cons (⟨occurrence.site, occurrence.evidence.val⟩ :
        (assaySystem question).Entry)) (fromAssay_entries question rest)

/-- This is the exact supplied paid experiment, exposing every original
command and assay instance in its order. -/
def experimentPath {state : State} {question : Question} {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) :
    Path question (.probe state budget) (.assay experiment.assay.endpoint) :=
  (fromProbe question experiment.probe).append
    (.cons (.handoff (probeEndpoint state question budget) (probeRemaining question budget)
      session provider client (request state question budget session provider client).arrival
      (by
        intro value offered
        by_cases complete : question.commands.length ≤ budget
        · simp only [request, if_pos complete] at offered
          exact (Option.some.inj offered).symm
        · simp only [request, if_neg complete] at offered
          cases offered))
      (fromAssay question experiment.assay.path))

theorem experimentPath_commands {state : State} {question : Question}
    {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) :
    (experimentPath experiment).commands = question.commands.take budget := by
  unfold experimentPath
  rw [Path.commands_append, fromProbe_commands]
  change question.commands.take budget ++ (fromAssay question experiment.assay.path).commands = _
  exact (congrArg (fun instructions => question.commands.take budget ++ instructions)
    (fromAssay_commands question experiment.assay.path)).trans (List.append_nil _)

theorem experimentPath_entries {state : State} {question : Question}
    {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) :
    (experimentPath experiment).assayEntries =
      (assaySystem question).pathEntries experiment.assay.path := by
  unfold experimentPath
  rw [Path.assayEntries_append, fromProbe_entries]
  exact fromAssay_entries question experiment.assay.path

theorem experimentPath_spent {state : State} {question : Question}
    {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) :
    (experimentPath experiment).spent = experiment.spent := by
  have staged := (experimentPath experiment).ledger
  have original := experiment.ledger
  change budget = experiment.remaining + (experimentPath experiment).spent at staged
  omega

theorem experimentPath_responses {state : State} {question : Question}
    {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) :
    responses (.assay experiment.assay.endpoint) = experiment.responses := rfl

end Mettapedia.OSLF.Framework.MetabolicPaidTrace
