import Mettapedia.GSLT.Causality.PaidProbeCampaign
import Mettapedia.GSLT.Causality.OccurrenceRealization

/-!
# Paid operational translation of probe campaigns

The source and target protocols are supplied independently. A translation
maps their actual resources and firing instances, using compatible Boolean
tests and exact delivery and inspection prices. Every retained occurrence is
mapped to a real firing; complete paths and sequential purse allocations are
then transported without replacing execution by an endpoint assertion.

The general maps below are forward maps. They can identify payloads or
providers. Inverse comparisons require separately supplied inverse laws;
equal public answers do not identify complete receipts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ProbeCampaign

open ResourceInteraction OccurrenceHistory
open ComplementaryAssay (Verdict purse)

universe r s i j q u v w

/-- A map of independently supplied resource interaction systems. -/
structure ResourceMap {R : Type r} {S : Type s}
    (source : ResourceInteraction.System.{r, i} R)
    (target : ResourceInteraction.System.{s, j} S) where
  resource : R → S
  site : source.Site → target.Site
  firing : ∀ {index : source.Site}, source.Instance index → target.Instance (site index)
  consume : ∀ {index} (event : source.Instance index),
    target.consume (firing event) = (source.consume event).map resource
  read : ∀ {index} (event : source.Instance index),
    target.read (firing event) = (source.read event).map resource
  produce : ∀ {index} (event : source.Instance index),
    target.produce (firing event) = (source.produce event).map resource

namespace ResourceMap

variable {R : Type r} {S : Type s}
  {source : ResourceInteraction.System.{r, i} R}
  {target : ResourceInteraction.System.{s, j} S}
  [DecidableEq R] [DecidableEq S]

omit [DecidableEq R] [DecidableEq S] in
theorem enabled (map : ResourceMap source target) (state : Multiset R)
    {index : source.Site} (firing : source.Instance index) (present : source.Enables state firing) :
    target.Enables (state.map map.resource) (map.firing firing) := by
  change target.consume (map.firing firing) + target.read (map.firing firing) ≤ _
  rw [map.consume, map.read, ← Multiset.map_add]
  exact Multiset.map_le_map present

theorem fire (map : ResourceMap source target) (state : Multiset R)
    {index : source.Site} (firing : source.Instance index) (present : source.Enables state firing) :
    target.fire (state.map map.resource) (map.firing firing) =
      (source.fire state firing).map map.resource := by
  change state.map map.resource - target.consume (map.firing firing) +
    target.produce (map.firing firing) = _
  rw [map.consume, map.produce]
  exact source.map_fire_of_le map.resource state firing
    (le_trans (Multiset.le_add_right _ _) present)

def occurrence (map : ResourceMap source target) {first last : Multiset R}
    (event : Occurrence source.presentation first last) :
    Occurrence target.presentation (first.map map.resource) (last.map map.resource) :=
  ⟨map.site event.site, ⟨map.firing event.evidence.val,
    map.enabled first event.evidence.val event.evidence.property.1,
    (congrArg (Multiset.map map.resource) event.evidence.property.2).trans
      (map.fire first event.evidence.val event.evidence.property.1).symm⟩⟩

def path (map : ResourceMap source target) : {first last : Multiset R} →
    OccurrencePath source.presentation first last →
      OccurrencePath target.presentation (first.map map.resource) (last.map map.resource)
  | _, _, .refl state => OccurrencePath.refl (P := target.presentation) (state.map map.resource)
  | _, _, .cons event rest => .cons (map.occurrence event) (map.path rest)

def entry (map : ResourceMap source target) (firing : source.Entry) : target.Entry :=
  ⟨map.site firing.1, map.firing firing.2⟩

theorem path_entries (map : ResourceMap source target) : ∀ {first last : Multiset R}
    (history : OccurrencePath source.presentation first last),
    target.pathEntries (map.path history) = (source.pathEntries history).map map.entry
  | _, _, .refl _ => rfl
  | _, _, .cons event rest =>
      congrArg (map.entry ⟨event.site, event.evidence.val⟩ :: ·) (path_entries map rest)

theorem path_append (map : ResourceMap source target) : ∀ {first junction last : Multiset R}
    (earlier : OccurrencePath source.presentation first junction)
    (later : OccurrencePath source.presentation junction last),
    map.path (earlier.append later) = (map.path earlier).append (map.path later)
  | _, _, _, .refl _, _ => rfl
  | _, _, _, .cons event rest, later =>
      congrArg (OccurrencePath.cons (map.occurrence event)) (path_append map rest later)

def realization (map : ResourceMap source target) :
    OccurrenceRealization source.presentation target.presentation where
  mapTerm := Multiset.map map.resource
  mapEquiv equal := congrArg (Multiset.map map.resource) equal
  mapOccurrence event := .cons (map.occurrence event) (.refl _)

theorem realization_path (map : ResourceMap source target) : ∀ {first last : Multiset R}
    (history : OccurrencePath source.presentation first last),
    map.realization.mapPath history = map.path history
  | _, _, .refl _ => rfl
  | _, _, .cons event rest =>
      congrArg (OccurrencePath.cons (map.occurrence event)) (realization_path map rest)

def reindexPath {first first' last last' : Multiset R} (sameFirst : first = first')
    (sameLast : last = last') (history : OccurrencePath source.presentation first last) :
    OccurrencePath source.presentation first' last' := by
  cases sameFirst
  cases sameLast
  exact history

theorem reindexPath_entries {first first' last last' : Multiset R} (sameFirst : first = first')
    (sameLast : last = last') (history : OccurrencePath source.presentation first last) :
    source.pathEntries (reindexPath sameFirst sameLast history) = source.pathEntries history := by
  cases sameFirst
  cases sameLast
  rfl

end ResourceMap

variable {Questions Questions' Questions'' : Type q}
  {X X' X'' : Type u} {Providers Providers' Providers'' : Type v}
  {Clients Clients' Clients'' : Type w}

/-- Compatible tests and exact prices for independently authored protocols.
The question map need not cover every target question. -/
structure Translation (source : Protocol Questions X) (target : Protocol Questions' X') where
  question : Questions → Questions'
  value : X → X'
  provider : Providers → Providers'
  client : Clients → Clients'
  test : ∀ query payload, target.test (question query) (value payload) = source.test query payload
  delivery : ∀ query payload,
    target.deliveryCost (question query) (value payload) = source.deliveryCost query payload
  inspection : ∀ query payload,
    target.inspectionCost (question query) (value payload) = source.inspectionCost query payload

namespace Translation

variable {source : Protocol Questions X} {target : Protocol Questions' X'}
  {last : Protocol Questions'' X''}

def id (protocol : Protocol Questions X) :
    Translation (Providers := Providers) (Providers' := Providers)
      (Clients := Clients) (Clients' := Clients) protocol protocol where
  question := _root_.id
  value := _root_.id
  provider := _root_.id
  client := _root_.id
  test _ _ := rfl
  delivery _ _ := rfl
  inspection _ _ := rfl

def comp (first : Translation (Providers := Providers) (Providers' := Providers')
    (Clients := Clients) (Clients' := Clients') source target)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') target last) :
    Translation (Providers := Providers) (Providers' := Providers'')
      (Clients := Clients) (Clients' := Clients'') source last where
  question := second.question ∘ first.question
  value := second.value ∘ first.value
  provider := second.provider ∘ first.provider
  client := second.client ∘ first.client
  test query payload := (second.test _ _).trans (first.test query payload)
  delivery query payload := (second.delivery _ _).trans (first.delivery query payload)
  inspection query payload := (second.inspection _ _).trans (first.inspection query payload)

variable (translation : Translation (Providers := Providers) (Providers' := Providers')
  (Clients := Clients) (Clients' := Clients') source target)

def request (offered : Request Questions X Providers Clients) :
    Request Questions' X' Providers' Clients' where
  question := translation.question offered.question
  session := offered.session
  provider := translation.provider offered.provider
  client := translation.client offered.client
  arrival := offered.arrival.map translation.value

def response (answer : Response X Clients) : Response X' Clients' :=
  (answer.1, answer.2.1, translation.client answer.2.2.1, translation.value answer.2.2.2)

def assayResource : ComplementaryAssay.Resource X Clients → ComplementaryAssay.Resource X' Clients'
  | .message session payload => .message session (translation.value payload)
  | .receiver session verdict owner => .receiver session verdict (translation.client owner)
  | .result session verdict owner payload =>
      .result session verdict (translation.client owner) (translation.value payload)

def probeResource : AssayProbeDelivery.ProbeResource X Providers Clients →
    AssayProbeDelivery.ProbeResource X' Providers' Clients'
  | .request session owner => .request session (translation.client owner)
  | .offer session server payload =>
      .offer session (translation.provider server) (translation.value payload)
  | .delivered session server owner payload =>
      .delivered session (translation.provider server) (translation.client owner) (translation.value payload)

def protocolResource : AssayProbeDelivery.Resources X Providers Clients →
    AssayProbeDelivery.Resources X' Providers' Clients' :=
  Sum.map translation.assayResource translation.probeResource

def resource : AssayProbeDelivery.Resources X Providers Clients ⊕ Unit →
    AssayProbeDelivery.Resources X' Providers' Clients' ⊕ Unit :=
  Sum.map translation.protocolResource _root_.id

def firing (query : Questions)
    {site : (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
      (source.test query) (source.deliveryCost query) (source.inspectionCost query)).Site} :
    (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients) (source.test query) (source.deliveryCost query)
      (source.inspectionCost query)).Instance site →
    (AssayProbeDelivery.paid (Providers := Providers') (Clients := Clients') (target.test (translation.question query))
      (target.deliveryCost (translation.question query))
      (target.inspectionCost (translation.question query))).Instance site :=
  match site with
  | .inl _branch => fun event => ⟨⟨event.down.session, translation.client event.down.origin,
      translation.value event.down.value, (translation.test query event.down.value).trans event.down.guard⟩⟩
  | .inr _ => fun event => ⟨event.session, translation.provider event.provider,
      translation.client event.client, translation.value event.value⟩

theorem price (query : Questions)
    {site : (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
      (source.test query) (source.deliveryCost query) (source.inspectionCost query)).Site}
    (event : (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients) (source.test query) (source.deliveryCost query)
      (source.inspectionCost query)).Instance site) :
    AssayProbeDelivery.price (target.test (translation.question query))
      (target.deliveryCost (translation.question query))
      (target.inspectionCost (translation.question query)) (translation.firing query event) =
    AssayProbeDelivery.price (source.test query) (source.deliveryCost query)
      (source.inspectionCost query) event := by
  cases site with
  | inl branch => exact congrArg purse (translation.inspection query event.down.value)
  | inr branch => exact congrArg purse (translation.delivery query event.value)

def resourceMap (query : Questions) :
    ResourceMap
      (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
        (source.test query) (source.deliveryCost query) (source.inspectionCost query))
      (AssayProbeDelivery.paid (Providers := Providers') (Clients := Clients')
        (target.test (translation.question query)) (target.deliveryCost (translation.question query))
        (target.inspectionCost (translation.question query))) where
  resource := translation.resource
  site := _root_.id
  firing := translation.firing query
  consume {site} event := by
    cases site <;>
      simp [AssayProbeDelivery.paid, funded, ResourceInteraction.System.product,
        ResourceInteraction.System.joint, ResourceInteraction.System.map,
        tokens, AssayProbeDelivery.system,
        ResourceInteraction.System.alternatives, AssayProbeDelivery.assaySystem,
        ResourceInteraction.System.raise, ComplementaryAssay.system,
        AssayProbeDelivery.deliverySystem, AssayProbeDelivery.price, firing,
        resource, protocolResource, assayResource, probeResource,
        translation.inspection, translation.delivery,
        purse]
  read {site} event := by
    cases site <;>
      simp [AssayProbeDelivery.paid, funded, ResourceInteraction.System.product,
        ResourceInteraction.System.joint, ResourceInteraction.System.map,
        tokens, AssayProbeDelivery.system,
        ResourceInteraction.System.alternatives, AssayProbeDelivery.assaySystem,
        ResourceInteraction.System.raise, ComplementaryAssay.system,
        AssayProbeDelivery.deliverySystem]
  produce {site} event := by
    cases site <;>
      simp [AssayProbeDelivery.paid, funded, ResourceInteraction.System.product,
        ResourceInteraction.System.joint, ResourceInteraction.System.map,
        tokens, AssayProbeDelivery.system,
        ResourceInteraction.System.alternatives, AssayProbeDelivery.assaySystem,
        ResourceInteraction.System.raise, ComplementaryAssay.system,
        AssayProbeDelivery.deliverySystem, firing,
        resource, protocolResource, assayResource, probeResource]

theorem marking_map (resources : Multiset (AssayProbeDelivery.Resources X Providers Clients))
    (tokens : Multiset Unit) :
    (marking resources tokens).map translation.resource =
      marking (resources.map translation.protocolResource) tokens := by
  simp only [marking, Multiset.disjSum, Multiset.map_add, Multiset.map_map]
  rfl

theorem protocol_marking_map (assay : Multiset (ComplementaryAssay.Resource X Clients))
    (probe : Multiset (AssayProbeDelivery.ProbeResource X Providers Clients)) :
    (marking assay probe).map translation.protocolResource =
      marking (assay.map translation.assayResource) (probe.map translation.probeResource) := by
  simp only [marking, Multiset.disjSum, Multiset.map_add, Multiset.map_map]
  rfl

theorem initial_map (offered : Request Questions X Providers Clients) (budget : Nat) :
    (AssayProbeDelivery.initial offered.session offered.provider offered.client offered.arrival budget).map
        translation.resource =
      AssayProbeDelivery.initial (translation.request offered).session
        (translation.request offered).provider (translation.request offered).client
        (translation.request offered).arrival budget := by
  cases arrival : offered.arrival <;>
    simp [AssayProbeDelivery.initial, AssayProbeDelivery.paidOffered,
      AssayProbeDelivery.offered, AssayProbeDelivery.waiting, ComplementaryAssay.pending,
      translation.marking_map, translation.protocol_marking_map,
      request, arrival, probeResource, assayResource]

theorem outputs_map (state : Multiset (AssayProbeDelivery.Resources X Providers Clients ⊕ Unit)) :
    AssayProbeDelivery.outputs (leftPart (state.map translation.resource)) =
      (AssayProbeDelivery.outputs (leftPart state)).map translation.response := by
  induction state using Multiset.induction_on with
  | empty => rfl
  | cons item state ih =>
    cases item with
    | inr token => simpa [resource, leftPart_cons_inr] using ih
    | inl protocolItem =>
      cases protocolItem with
      | inr probe => simpa [resource, protocolResource, AssayProbeDelivery.outputs,
          leftPart_cons_inl, leftPart_cons_inr] using ih
      | inl assay =>
        cases assay <;> simp_all [resource, protocolResource, assayResource,
          AssayProbeDelivery.outputs, ComplementaryAssay.outputs,
          leftPart_cons_inl, response]

theorem remaining_map (state : Multiset (AssayProbeDelivery.Resources X Providers Clients ⊕ Unit)) :
    rightPart (state.map translation.resource) = rightPart state := by
  induction state using Multiset.induction_on with
  | empty => rfl
  | cons item state ih =>
    cases item <;> simp_all [resource, rightPart_cons_inl, rightPart_cons_inr]

variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]
  [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']

def round {offered : Request Questions X Providers Clients} {budget : Nat}
    (original : Round source offered budget) : Round target (translation.request offered) budget where
  endpoint := original.endpoint.map translation.resource
  path := ResourceMap.reindexPath (translation.initial_map offered budget) rfl
    ((translation.resourceMap offered.question).path original.path)

theorem round_path_entries {offered : Request Questions X Providers Clients} {budget : Nat}
    (original : Round source offered budget) :
    (AssayProbeDelivery.paid (Providers := Providers') (Clients := Clients')
      (target.test (translation.question offered.question))
      (target.deliveryCost (translation.question offered.question))
      (target.inspectionCost (translation.question offered.question))).pathEntries
      (translation.round original).path =
    ((AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
      (source.test offered.question) (source.deliveryCost offered.question)
      (source.inspectionCost offered.question)).pathEntries original.path).map
        (translation.resourceMap offered.question).entry := by
  exact (ResourceMap.reindexPath_entries
    (source := AssayProbeDelivery.paid (Providers := Providers') (Clients := Clients')
      (target.test (translation.question offered.question))
      (target.deliveryCost (translation.question offered.question))
      (target.inspectionCost (translation.question offered.question)))
    (translation.initial_map offered budget) rfl
    ((translation.resourceMap offered.question).path original.path)).trans
      ((translation.resourceMap offered.question).path_entries original.path)

theorem round_responses {offered : Request Questions X Providers Clients} {budget : Nat}
    (original : Round source offered budget) :
    (translation.round original).responses = original.responses.map translation.response :=
  translation.outputs_map original.endpoint

theorem round_remaining {offered : Request Questions X Providers Clients} {budget : Nat}
    (original : Round source offered budget) :
    (translation.round original).remaining = original.remaining :=
  congrArg Multiset.card (translation.remaining_map original.endpoint)

theorem round_spent {offered : Request Questions X Providers Clients} {budget : Nat}
    (original : Round source offered budget) :
    (translation.round original).spent = original.spent := by
  have first := original.ledger
  have second := (translation.round original).ledger
  rw [translation.round_remaining original] at second
  omega

omit [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]
  [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients'] in
theorem response_bit (answer : Response X Clients) :
    (translation.response answer).2.1.bit = answer.2.1.bit := rfl

end Translation

namespace Campaign

variable {protocol : Protocol Questions X}
  [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

def reindexBudget {before after : Nat} (same : before = after)
    {requests : List (Request Questions X Providers Clients)}
    (history : Campaign protocol before requests) : Campaign protocol after requests := same ▸ history

@[simp] theorem remaining_reindexBudget {before after : Nat} (same : before = after)
    {requests : List (Request Questions X Providers Clients)}
    (history : Campaign protocol before requests) :
    (history.reindexBudget same).remaining = history.remaining := by cases same; rfl

@[simp] theorem spent_reindexBudget {before after : Nat} (same : before = after)
    {requests : List (Request Questions X Providers Clients)}
    (history : Campaign protocol before requests) :
    (history.reindexBudget same).spent = history.spent := by cases same; rfl

@[simp] theorem publicLog_reindexBudget {before after : Nat} (same : before = after)
    {requests : List (Request Questions X Providers Clients)}
    (history : Campaign protocol before requests) :
    (history.reindexBudget same).publicLog = history.publicLog := by cases same; rfl

@[simp] theorem completedTests_reindexBudget {before after : Nat} (same : before = after)
    {requests : List (Request Questions X Providers Clients)}
    (history : Campaign protocol before requests) :
    (history.reindexBudget same).completedTests = history.completedTests := by cases same; rfl

end Campaign

namespace Translation

variable {source : Protocol Questions X} {target : Protocol Questions' X'}
  {last : Protocol Questions'' X''}
  [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]
  [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']

variable (translation : Translation (Providers := Providers) (Providers' := Providers')
  (Clients := Clients) (Clients' := Clients') source target)

/-- Each translated round receives the previously translated round's actual
remaining purse. No campaign funding is duplicated between its requests. -/
def campaign : {budget : Nat} → {requests : List (Request Questions X Providers Clients)} →
    Campaign source budget requests → Campaign target budget (requests.map translation.request)
  | _, _, .nil budget => .nil budget
  | _, _, .cons first rest => .cons (translation.round first)
      ((campaign rest).reindexBudget (translation.round_remaining first).symm)

theorem campaign_remaining : ∀ {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (original : Campaign source budget requests),
    (translation.campaign original).remaining = original.remaining
  | _, _, .nil _ => rfl
  | _, _, .cons first rest => by
      change ((translation.campaign rest).reindexBudget _).remaining = rest.remaining
      rw [Campaign.remaining_reindexBudget, campaign_remaining rest]

theorem campaign_spent : ∀ {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (original : Campaign source budget requests),
    (translation.campaign original).spent = original.spent
  | _, _, .nil _ => rfl
  | _, _, .cons first rest => by
      change (translation.round first).spent + ((translation.campaign rest).reindexBudget _).spent = _
      rw [translation.round_spent, Campaign.spent_reindexBudget, campaign_spent rest]
      rfl

def packet (entry : Questions × Multiset (Response X Clients)) :
    Questions' × Multiset (Response X' Clients') :=
  (translation.question entry.1, entry.2.map translation.response)

theorem campaign_publicLog : ∀ {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (original : Campaign source budget requests),
    (translation.campaign original).publicLog = original.publicLog.map translation.packet
  | _, _, .nil _ => rfl
  | _, request :: requests, .cons first rest => by
      change (translation.question request.question, (translation.round first).responses) ::
          ((translation.campaign rest).reindexBudget _).publicLog = _
      rw [translation.round_responses, Campaign.publicLog_reindexBudget,
        campaign_publicLog rest]
      rfl

theorem campaign_completedTests : ∀ {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (original : Campaign source budget requests),
    (translation.campaign original).completedTests = original.completedTests
  | _, _, .nil _ => rfl
  | _, _, .cons first rest => by
      change (translation.round first).responses.card +
          ((translation.campaign rest).reindexBudget _).completedTests = _
      rw [translation.round_responses, Multiset.card_map, Campaign.completedTests_reindexBudget,
        campaign_completedTests rest]
      rfl

end Translation

end Mettapedia.GSLT.Causality.ProbeCampaign
