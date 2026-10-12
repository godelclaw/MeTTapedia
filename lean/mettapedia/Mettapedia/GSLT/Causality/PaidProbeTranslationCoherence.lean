import Mettapedia.GSLT.Causality.PaidProbeTranslation

/-!
# Coherence and inverse comparisons for paid probe translation

The same resource and instance calculations compose before taking public
readouts. Inverse laws are additional data on a translation; arbitrary
forward maps do not provide them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ProbeCampaign

open ResourceInteraction OccurrenceHistory

universe q u v w r i

namespace ResourceMap

variable {R : Type r} (system : ResourceInteraction.System.{r, i} R) [DecidableEq R]

/-- An ordered firing ledger determines the complete occurrence path in a
resource system, including all intermediate markings. Event proofs are
proof-irrelevant; the authored sites and instances remain in the ledger. -/
theorem path_heq_of_entries : ∀ {first last otherLast : Multiset R}
    (history : OccurrencePath system.presentation first last)
    (other : OccurrencePath system.presentation first otherLast),
    system.pathEntries history = system.pathEntries other → HEq history other
  | _, _, _, .refl _, .refl _, _ => HEq.rfl
  | _, _, _, .refl _, .cons _ _, same => by cases same
  | _, _, _, .cons _ _, .refl _, same => by cases same
  | first, last, otherLast, @OccurrencePath.cons _ _ _ middle _ event rest,
      @OccurrencePath.cons _ _ _ otherMiddle _ otherEvent otherRest, same => by
    have head : (⟨event.site, event.evidence.val⟩ : system.Entry) =
        ⟨otherEvent.site, otherEvent.evidence.val⟩ := (List.cons.inj same).1
    have tail : system.pathEntries rest = system.pathEntries otherRest := (List.cons.inj same).2
    cases event with
    | mk site evidence =>
      cases otherEvent with
      | mk otherSite otherEvidence =>
        cases evidence with
        | mk firing fired =>
          cases otherEvidence with
          | mk otherFiring otherFired =>
            simp only at head
            cases head
            have sameMiddle : middle = otherMiddle := fired.2.trans otherFired.2.symm
            subst otherMiddle
            have sameRest := path_heq_of_entries rest otherRest tail
            have sameLast := system.target_eq_of_pathEntries_eq rest otherRest tail
            subst otherLast
            have tailEq := eq_of_heq sameRest
            subst otherRest
            rfl

end ResourceMap

variable {Questions Questions' Questions'' : Type q}
  {X X' X'' : Type u} {Providers Providers' Providers'' : Type v}
  {Clients Clients' Clients'' : Type w}

namespace Round

variable {protocol : Protocol Questions X}
  [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

def reindexRequest {request request' : Request Questions X Providers Clients}
    (same : request = request') {budget : Nat} (history : Round protocol request budget) :
    Round protocol request' budget := same ▸ history

@[simp] theorem endpoint_reindexRequest {request request' : Request Questions X Providers Clients}
    (same : request = request') {budget : Nat} (history : Round protocol request budget) :
    (history.reindexRequest same).endpoint = history.endpoint := by cases same; rfl

theorem entries_reindexRequest {request request' : Request Questions X Providers Clients}
    (same : request = request') {budget : Nat} (history : Round protocol request budget) :
    HEq
      ((AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
        (protocol.test request'.question) (protocol.deliveryCost request'.question)
        (protocol.inspectionCost request'.question)).pathEntries (history.reindexRequest same).path)
      ((AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
        (protocol.test request.question) (protocol.deliveryCost request.question)
        (protocol.inspectionCost request.question)).pathEntries history.path) := by cases same; rfl

theorem eq_of_endpoint_entries {request : Request Questions X Providers Clients} {budget : Nat}
    (first second : Round protocol request budget) (sameEndpoint : first.endpoint = second.endpoint)
    (sameEntries :
      (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
        (protocol.test request.question) (protocol.deliveryCost request.question)
        (protocol.inspectionCost request.question)).pathEntries first.path =
      (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
        (protocol.test request.question) (protocol.deliveryCost request.question)
        (protocol.inspectionCost request.question)).pathEntries second.path) : first = second := by
  cases first with
  | mk endpoint path =>
    cases second with
    | mk otherEndpoint otherPath =>
      simp only at sameEndpoint sameEntries
      subst otherEndpoint
      have paths := ResourceMap.path_heq_of_entries _ path otherPath sameEntries
      exact congrArg (Round.mk endpoint) (eq_of_heq paths)

end Round

namespace Translation

variable {source : Protocol Questions X} {middle : Protocol Questions' X'}
  {target : Protocol Questions'' X''}

theorem request_id (offered : Request Questions X Providers Clients) :
    (id source).request offered = offered := by
  cases offered
  simp [request, id]

theorem request_comp (first : Translation (Providers := Providers) (Providers' := Providers')
    (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    (offered : Request Questions X Providers Clients) :
    (first.comp second).request offered = second.request (first.request offered) := by
  cases offered
  simp [request, comp, Option.map_map, Function.comp_def]

theorem response_id (answer : Response X Clients) :
    (id (Providers := Providers) source).response answer = answer := by
  rcases answer with ⟨session, verdict, client, payload⟩
  rfl

theorem response_comp (first : Translation (Providers := Providers) (Providers' := Providers')
    (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    (answer : Response X Clients) :
    (first.comp second).response answer = second.response (first.response answer) := rfl

theorem resource_id (item : AssayProbeDelivery.Resources X Providers Clients ⊕ Unit) :
    (id source).resource item = item := by
  cases item with
  | inr token => rfl
  | inl protocol =>
    cases protocol with
    | inl assay => cases assay <;> rfl
    | inr probe => cases probe <;> rfl

theorem resource_comp (first : Translation (Providers := Providers) (Providers' := Providers')
    (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    (item : AssayProbeDelivery.Resources X Providers Clients ⊕ Unit) :
    (first.comp second).resource item = second.resource (first.resource item) := by
  cases item with
  | inr token => rfl
  | inl protocol =>
    cases protocol with
    | inl assay => cases assay <;> rfl
    | inr probe => cases probe <;> rfl

theorem firing_comp (first : Translation (Providers := Providers) (Providers' := Providers')
    (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    (query : Questions)
    {site : (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
      (source.test query) (source.deliveryCost query) (source.inspectionCost query)).Site}
    (event : (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
      (source.test query) (source.deliveryCost query) (source.inspectionCost query)).Instance site) :
    (first.comp second).firing query event =
      second.firing (first.question query) (first.firing query event) := by
  cases site <;> rfl

variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]
  [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']
  [DecidableEq X''] [DecidableEq Providers''] [DecidableEq Clients'']

omit [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']
  [DecidableEq X''] [DecidableEq Providers''] [DecidableEq Clients''] in
theorem round_endpoint_id {offered : Request Questions X Providers Clients} {budget : Nat}
    (history : Round source offered budget) :
    ((id source).round history).endpoint = history.endpoint := by
  change history.endpoint.map (id source).resource = history.endpoint
  have maps : (id (Providers := Providers) (Clients := Clients) source).resource = _root_.id :=
    funext resource_id
  rw [maps, Multiset.map_id]

theorem round_endpoint_comp
    (first : Translation (Providers := Providers) (Providers' := Providers')
      (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    {offered : Request Questions X Providers Clients} {budget : Nat}
    (history : Round source offered budget) :
    ((first.comp second).round history).endpoint =
      (second.round (first.round history)).endpoint := by
  change history.endpoint.map (first.comp second).resource =
    (history.endpoint.map first.resource).map second.resource
  rw [Multiset.map_map]
  exact congrArg (fun map => history.endpoint.map map) (funext (first.resource_comp second))

theorem round_entries_comp
    (first : Translation (Providers := Providers) (Providers' := Providers')
      (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    {offered : Request Questions X Providers Clients} {budget : Nat}
    (history : Round source offered budget) :
    (AssayProbeDelivery.paid (Providers := Providers'') (Clients := Clients'')
      (target.test ((first.comp second).question offered.question))
      (target.deliveryCost ((first.comp second).question offered.question))
      (target.inspectionCost ((first.comp second).question offered.question))).pathEntries
      (((first.comp second).resourceMap offered.question).path history.path) =
    (AssayProbeDelivery.paid (Providers := Providers'') (Clients := Clients'')
      (target.test (second.question (first.question offered.question)))
      (target.deliveryCost (second.question (first.question offered.question)))
      (target.inspectionCost (second.question (first.question offered.question)))).pathEntries
      ((second.resourceMap (first.question offered.question)).path
        ((first.resourceMap offered.question).path history.path)) := by
  rw [ResourceMap.path_entries, ResourceMap.path_entries, ResourceMap.path_entries, List.map_map]
  congr 1
  funext entry
  rcases entry with ⟨site, event⟩
  exact congrArg (Sigma.mk site) (first.firing_comp second offered.question event)

theorem round_responses_comp
    (first : Translation (Providers := Providers) (Providers' := Providers')
      (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    {offered : Request Questions X Providers Clients} {budget : Nat}
    (history : Round source offered budget) :
    ((first.comp second).round history).responses =
      (second.round (first.round history)).responses := by
  rw [round_responses, round_responses, round_responses, Multiset.map_map]
  rfl

theorem campaign_publicLog_comp
    (first : Translation (Providers := Providers) (Providers' := Providers')
      (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (history : Campaign source budget requests) :
    ((first.comp second).campaign history).publicLog =
      (second.campaign (first.campaign history)).publicLog := by
  rw [campaign_publicLog, campaign_publicLog, campaign_publicLog, List.map_map]
  congr 1
  funext packet
  rcases packet with ⟨query, answers⟩
  simp only [Translation.packet, Translation.comp, Function.comp_apply, Multiset.map_map]
  rfl

omit [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']
  [DecidableEq X''] [DecidableEq Providers''] [DecidableEq Clients''] in
theorem round_id {offered : Request Questions X Providers Clients} {budget : Nat}
    (history : Round source offered budget) :
    ((id source).round history).reindexRequest (request_id offered) = history := by
  apply Round.eq_of_endpoint_entries
  · rw [Round.endpoint_reindexRequest, round_endpoint_id]
  · have aligned := Round.entries_reindexRequest (request_id offered) ((id source).round history)
    have unchanged :
        (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
          (source.test offered.question) (source.deliveryCost offered.question)
          (source.inspectionCost offered.question)).pathEntries ((id source).round history).path =
        (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
          (source.test offered.question) (source.deliveryCost offered.question)
          (source.inspectionCost offered.question)).pathEntries history.path := by
      have mapped := (id (Providers := Providers) (Clients := Clients) source).round_path_entries history
      have identity : ((id (Providers := Providers) (Clients := Clients) source).resourceMap offered.question).entry = _root_.id := by
        funext entry
        rcases entry with ⟨site, event⟩
        cases site <;> rfl
      let order := (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
        (source.test offered.question) (source.deliveryCost offered.question)
        (source.inspectionCost offered.question)).pathEntries history.path
      exact mapped.trans ((congrArg (fun mapper => order.map mapper) identity).trans (List.map_id order))
    exact (eq_of_heq aligned).trans unchanged

theorem round_comp
    (first : Translation (Providers := Providers) (Providers' := Providers')
      (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    {offered : Request Questions X Providers Clients} {budget : Nat}
    (history : Round source offered budget) :
    ((first.comp second).round history).reindexRequest (first.request_comp second offered) =
      second.round (first.round history) := by
  apply Round.eq_of_endpoint_entries
  · rw [Round.endpoint_reindexRequest, round_endpoint_comp]
  · have aligned := Round.entries_reindexRequest (first.request_comp second offered)
      ((first.comp second).round history)
    apply (eq_of_heq aligned).trans
    have direct := (first.comp second).round_path_entries history
    have staged := second.round_path_entries (first.round history)
    have inner := first.round_path_entries history
    have ordered := congrArg
      (List.map (second.resourceMap (first.question offered.question)).entry) inner
    have combined := staged.trans ordered
    rw [List.map_map] at combined
    have entries : ((first.comp second).resourceMap offered.question).entry =
        (second.resourceMap (first.question offered.question)).entry ∘
          (first.resourceMap offered.question).entry := by
      funext entry
      rcases entry with ⟨site, event⟩
      exact congrArg (Sigma.mk site) (first.firing_comp second offered.question event)
    let order := (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
      (source.test offered.question) (source.deliveryCost offered.question)
      (source.inspectionCost offered.question)).pathEntries history.path
    exact direct.trans ((congrArg (fun mapper => order.map mapper) entries).trans combined.symm)

end Translation

/-- An invertible vocabulary profile with independently proved tests and
prices. Unlike a general translation, it supplies actual operational
readback of arbitrary target rounds at corresponding requests. -/
structure ProtocolEquivalence (source : Protocol Questions X) (target : Protocol Questions' X') where
  question : Questions ≃ Questions'
  value : X ≃ X'
  provider : Providers ≃ Providers'
  client : Clients ≃ Clients'
  test : ∀ query payload, target.test (question query) (value payload) = source.test query payload
  delivery : ∀ query payload,
    target.deliveryCost (question query) (value payload) = source.deliveryCost query payload
  inspection : ∀ query payload,
    target.inspectionCost (question query) (value payload) = source.inspectionCost query payload

namespace ProtocolEquivalence

variable {source : Protocol Questions X} {target : Protocol Questions' X'}
  (comparison : ProtocolEquivalence (Providers := Providers) (Providers' := Providers')
    (Clients := Clients) (Clients' := Clients') source target)

def forward : Translation (Providers := Providers) (Providers' := Providers')
    (Clients := Clients) (Clients' := Clients') source target where
  question := comparison.question
  value := comparison.value
  provider := comparison.provider
  client := comparison.client
  test := comparison.test
  delivery := comparison.delivery
  inspection := comparison.inspection

def backward : Translation (Providers := Providers') (Providers' := Providers)
    (Clients := Clients') (Clients' := Clients) target source where
  question := comparison.question.symm
  value := comparison.value.symm
  provider := comparison.provider.symm
  client := comparison.client.symm
  test query payload := by
    simpa using (comparison.test (comparison.question.symm query) (comparison.value.symm payload)).symm
  delivery query payload := by
    simpa using (comparison.delivery (comparison.question.symm query) (comparison.value.symm payload)).symm
  inspection query payload := by
    simpa using (comparison.inspection (comparison.question.symm query) (comparison.value.symm payload)).symm

theorem request_roundtrip (offered : Request Questions X Providers Clients) :
    comparison.backward.request (comparison.forward.request offered) = offered := by
  cases offered
  simp [Translation.request, forward, backward, Option.map_map, Function.comp_def]

theorem request_roundtrip_target (offered : Request Questions' X' Providers' Clients') :
    comparison.forward.request (comparison.backward.request offered) = offered := by
  cases offered
  simp [Translation.request, forward, backward, Option.map_map, Function.comp_def]

theorem response_roundtrip (answer : Response X Clients) :
    comparison.backward.response (comparison.forward.response answer) = answer := by
  rcases answer with ⟨session, verdict, origin, payload⟩
  simp [Translation.response, forward, backward]

theorem response_roundtrip_target (answer : Response X' Clients') :
    comparison.forward.response (comparison.backward.response answer) = answer := by
  rcases answer with ⟨session, verdict, origin, payload⟩
  simp [Translation.response, forward, backward]

theorem resource_roundtrip (item : AssayProbeDelivery.Resources X Providers Clients ⊕ Unit) :
    comparison.backward.resource (comparison.forward.resource item) = item := by
  cases item with
  | inr token => rfl
  | inl item =>
    cases item with
    | inl assay => cases assay <;> simp [Translation.resource, Translation.protocolResource,
        Translation.assayResource, forward, backward]
    | inr probe => cases probe <;> simp [Translation.resource, Translation.protocolResource,
        Translation.probeResource, forward, backward]

theorem resource_roundtrip_target (item : AssayProbeDelivery.Resources X' Providers' Clients' ⊕ Unit) :
    comparison.forward.resource (comparison.backward.resource item) = item := by
  cases item with
  | inr token => rfl
  | inl item =>
    cases item with
    | inl assay => cases assay <;> simp [Translation.resource, Translation.protocolResource,
        Translation.assayResource, forward, backward]
    | inr probe => cases probe <;> simp [Translation.resource, Translation.protocolResource,
        Translation.probeResource, forward, backward]

theorem resources_injective : Function.Injective comparison.forward.resource :=
  Function.LeftInverse.injective comparison.resource_roundtrip

theorem resources_surjective : Function.Surjective comparison.forward.resource := by
  intro item
  exact ⟨comparison.backward.resource item, comparison.resource_roundtrip_target item⟩

variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]
  [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']

/-- A supplied target schedule is read back occurrence by occurrence, not
replaced by the source controller's preferred schedule. -/
def readback {offered : Request Questions X Providers Clients} {budget : Nat}
    (history : Round target (comparison.forward.request offered) budget) :
    Round source offered budget :=
  (comparison.backward.round history).reindexRequest (comparison.request_roundtrip offered)

theorem readback_endpoint {offered : Request Questions X Providers Clients} {budget : Nat}
    (history : Round target (comparison.forward.request offered) budget) :
    (comparison.readback history).endpoint = history.endpoint.map comparison.backward.resource :=
  Round.endpoint_reindexRequest _ _

/-- Recompiling the entire read-back target endpoint recovers every resource,
including provider receipts and all remaining purse tokens. -/
theorem readback_endpoint_recovers {offered : Request Questions X Providers Clients} {budget : Nat}
    (history : Round target (comparison.forward.request offered) budget) :
    ((comparison.readback history).endpoint.map comparison.forward.resource) = history.endpoint := by
  rw [comparison.readback_endpoint, Multiset.map_map]
  have inverse : comparison.forward.resource ∘ comparison.backward.resource = _root_.id :=
    funext comparison.resource_roundtrip_target
  rw [inverse, Multiset.map_id]

theorem readback_responses {offered : Request Questions X Providers Clients} {budget : Nat}
    (history : Round target (comparison.forward.request offered) budget) :
    (comparison.readback history).responses = history.responses.map comparison.backward.response := by
  unfold Round.responses
  rw [comparison.readback_endpoint]
  exact comparison.backward.outputs_map history.endpoint

theorem readback_remaining {offered : Request Questions X Providers Clients} {budget : Nat}
    (history : Round target (comparison.forward.request offered) budget) :
    (comparison.readback history).remaining = history.remaining := by
  unfold Round.remaining
  rw [comparison.readback_endpoint, comparison.backward.remaining_map]

theorem readback_spent {offered : Request Questions X Providers Clients} {budget : Nat}
    (history : Round target (comparison.forward.request offered) budget) :
    (comparison.readback history).spent = history.spent := by
  have first := history.ledger
  have second := (comparison.readback history).ledger
  rw [comparison.readback_remaining history] at second
  omega

end ProtocolEquivalence

end Mettapedia.GSLT.Causality.ProbeCampaign
