import Mettapedia.GSLT.Causality.PaidProbeTranslationCoherence

/-!
# Complete campaign trace coherence

A trace retains every actual round with its allocated budget and full
request. Equality of these typed traces determines the complete campaign.
Translation commutes with the traces and with its identity and composition;
this comparison preserves paths and provider receipts as well as answers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ProbeCampaign

universe q u v w

variable {Questions Questions' Questions'' : Type q}
  {X X' X'' : Type u} {Providers Providers' Providers'' : Type v}
  {Clients Clients' Clients'' : Type w}

abbrev RoundBundle (protocol : Protocol Questions X)
    [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients] :=
  Σ budget : Nat, Σ request : Request Questions X Providers Clients, Round protocol request budget

namespace RoundBundle

variable {protocol : Protocol Questions X}
  [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

theorem reindex_request {budget : Nat} {request request' : Request Questions X Providers Clients}
    (same : request = request') (history : Round protocol request budget) :
    (⟨budget, request', history.reindexRequest same⟩ : (RoundBundle (Providers := Providers) (Clients := Clients) protocol)) =
      ⟨budget, request, history⟩ := by cases same; rfl

end RoundBundle

namespace Campaign

variable {protocol : Protocol Questions X}
  [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

def trace : {budget : Nat} → {requests : List (Request Questions X Providers Clients)} →
    Campaign protocol budget requests → List ((RoundBundle (Providers := Providers) (Clients := Clients) protocol))
  | _, _, .nil _ => []
  | budget, request :: _, .cons first rest => ⟨budget, request, first⟩ :: trace rest

@[simp] theorem trace_reindexBudget {before after : Nat} (same : before = after)
    {requests : List (Request Questions X Providers Clients)}
    (history : Campaign protocol before requests) :
    (history.reindexBudget same).trace = history.trace := by cases same; rfl

def reindexRequests {budget : Nat} {requests requests' : List (Request Questions X Providers Clients)}
    (same : requests = requests') (history : Campaign protocol budget requests) :
    Campaign protocol budget requests' := same ▸ history

@[simp] theorem trace_reindexRequests {budget : Nat}
    {requests requests' : List (Request Questions X Providers Clients)}
    (same : requests = requests') (history : Campaign protocol budget requests) :
    (history.reindexRequests same).trace = history.trace := by cases same; rfl

theorem eq_of_trace {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (first second : Campaign protocol budget requests) (same : first.trace = second.trace) :
    first = second := by
  induction first with
  | nil budget => cases second; rfl
  | @cons budget request requests first rest ih =>
    cases second with
    | cons otherFirst otherRest =>
      have head : (⟨budget, request, first⟩ : (RoundBundle (Providers := Providers) (Clients := Clients) protocol)) =
          ⟨budget, request, otherFirst⟩ := (List.cons.inj same).1
      have tail : rest.trace = otherRest.trace := (List.cons.inj same).2
      have firsts : first = otherFirst := by
        have inner := eq_of_heq (Sigma.mk.inj head).2
        exact eq_of_heq (Sigma.mk.inj inner).2
      subst otherFirst
      have rests := ih otherRest tail
      subst otherRest
      rfl

end Campaign

namespace Translation

variable {source : Protocol Questions X} {middle : Protocol Questions' X'}
  {target : Protocol Questions'' X''}
  [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]
  [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']
  [DecidableEq X''] [DecidableEq Providers''] [DecidableEq Clients'']

variable (translation : Translation (Providers := Providers) (Providers' := Providers')
  (Clients := Clients) (Clients' := Clients') source middle)

omit [DecidableEq X''] [DecidableEq Providers''] [DecidableEq Clients''] in
def bundle (original : RoundBundle (Providers := Providers) (Clients := Clients) source) :
    RoundBundle (Providers := Providers') (Clients := Clients') middle :=
  ⟨original.1, translation.request original.2.1, translation.round original.2.2⟩

omit [DecidableEq X''] [DecidableEq Providers''] [DecidableEq Clients''] in
theorem campaign_trace : ∀ {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (original : Campaign source budget requests),
    (translation.campaign original).trace = original.trace.map translation.bundle
  | _, _, .nil _ => rfl
  | _, _, .cons first rest => by
      change translation.bundle ⟨_, _, first⟩ :: ((translation.campaign rest).reindexBudget _).trace = _
      rw [Campaign.trace_reindexBudget, campaign_trace rest]
      rfl

omit [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']
  [DecidableEq X''] [DecidableEq Providers''] [DecidableEq Clients''] in
theorem bundle_id (original : RoundBundle (Providers := Providers) (Clients := Clients) source) :
    (id source).bundle original = original := by
  rcases original with ⟨budget, request, history⟩
  have reindexed := RoundBundle.reindex_request (request_id request) ((id source).round history)
  have unchanged := congrArg (fun round : Round source request budget =>
    (⟨budget, request, round⟩ : (RoundBundle (Providers := Providers) (Clients := Clients) source))) (round_id history)
  exact reindexed.symm.trans unchanged

theorem bundle_comp
    (first : Translation (Providers := Providers) (Providers' := Providers')
      (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    (original : RoundBundle (Providers := Providers) (Clients := Clients) source) :
    (first.comp second).bundle original = second.bundle (first.bundle original) := by
  rcases original with ⟨budget, request, history⟩
  have reindexed := RoundBundle.reindex_request (first.request_comp second request)
    ((first.comp second).round history)
  have unchanged := congrArg
    (fun round : Round target (second.request (first.request request)) budget =>
      (⟨budget, second.request (first.request request), round⟩ : (RoundBundle (Providers := Providers'') (Clients := Clients'') target)))
    (first.round_comp second history)
  exact reindexed.symm.trans unchanged

omit [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']
  [DecidableEq X''] [DecidableEq Providers''] [DecidableEq Clients''] in
theorem campaign_trace_id {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (original : Campaign source budget requests) :
    ((id source).campaign original).trace = original.trace := by
  rw [campaign_trace]
  exact (List.map_congr_left (fun _ _ => bundle_id _)).trans (List.map_id original.trace)

theorem campaign_trace_comp
    (first : Translation (Providers := Providers) (Providers' := Providers')
      (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (original : Campaign source budget requests) :
    ((first.comp second).campaign original).trace =
      (second.campaign (first.campaign original)).trace := by
  rw [campaign_trace, campaign_trace, campaign_trace, List.map_map]
  exact List.map_congr_left (fun _ _ => first.bundle_comp second _)

omit [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]
  [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']
  [DecidableEq X''] [DecidableEq Providers''] [DecidableEq Clients''] in
theorem requests_id (requests : List (Request Questions X Providers Clients)) :
    requests.map (id source).request = requests :=
  (List.map_congr_left (fun _ _ => request_id _)).trans (List.map_id requests)

omit [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]
  [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']
  [DecidableEq X''] [DecidableEq Providers''] [DecidableEq Clients''] in
theorem requests_comp
    (first : Translation (Providers := Providers) (Providers' := Providers')
      (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    (requests : List (Request Questions X Providers Clients)) :
    requests.map (first.comp second).request = (requests.map first.request).map second.request := by
  rw [List.map_map]
  exact List.map_congr_left (fun _ _ => first.request_comp second _)

omit [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']
  [DecidableEq X''] [DecidableEq Providers''] [DecidableEq Clients''] in
theorem campaign_id {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (original : Campaign source budget requests) :
    ((id source).campaign original).reindexRequests (requests_id requests) = original := by
  apply Campaign.eq_of_trace
  rw [Campaign.trace_reindexRequests, campaign_trace_id]

/-- Coherent composition is equality of the complete campaigns, with all
round paths and their sequential budgets retained, after request transport. -/
theorem campaign_comp
    (first : Translation (Providers := Providers) (Providers' := Providers')
      (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (original : Campaign source budget requests) :
    ((first.comp second).campaign original).reindexRequests (first.requests_comp second requests) =
      second.campaign (first.campaign original) := by
  apply Campaign.eq_of_trace
  rw [Campaign.trace_reindexRequests, campaign_trace_comp]

end Translation

end Mettapedia.GSLT.Causality.ProbeCampaign
