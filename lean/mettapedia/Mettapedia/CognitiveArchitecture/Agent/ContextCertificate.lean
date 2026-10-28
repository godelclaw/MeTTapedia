import Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext

/-!
# Context certificates

A context certificate records which evidence revision, active queries,
commitment phase, and sources produced one bounded context projection.  The
projection receipt identifies that projection; it is not itself treated as
evidence that an external effect succeeded.

The construction is deliberately policy-neutral.  It certifies an input to a
policy but does not select an action, a model, a context size, or a scheduling
strategy.  Recoverable evidence remains outside the bounded view, following
the dynamic weakest-sufficient-view construction in `OpenEndedContext`.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.ContextCertificate

universe uRevision uQuery uPhase uSource uReceipt uView uAction

/-- Evidence named by a context projection.  `activeQueries` is explicit so a
later audit can distinguish an omitted query from an answered one. -/
structure Certificate
    (Revision : Type uRevision) (Query : Type uQuery) (Phase : Type uPhase)
    (Source : Type uSource) (Receipt : Type uReceipt) where
  evidenceRevision : Revision
  activeQueries : Finset Query
  commitmentPhase : Phase
  sources : Finset Source
  projectionReceipt : Receipt

/-- The complete payload used to issue a projection receipt.  The bounded
view is retained here even though it is not duplicated in `Certificate`. -/
structure ProjectionPayload
    (Revision : Type uRevision) (Query : Type uQuery) (Phase : Type uPhase)
    (Source : Type uSource) (View : Type uView) where
  evidenceRevision : Revision
  activeQueries : Finset Query
  commitmentPhase : Phase
  sources : Finset Source
  view : View

/-- Receipt issuance is an external, replaceable mechanism.  No injectivity or
cryptographic property is silently assumed. -/
structure Issuer
    (Revision : Type uRevision) (Query : Type uQuery) (Phase : Type uPhase)
    (Source : Type uSource) (View : Type uView) (Receipt : Type uReceipt) where
  issue : ProjectionPayload Revision Query Phase Source View → Receipt

/-- Issue a certificate from the exact payload that produced a bounded view. -/
def certify
    {Revision : Type uRevision} {Query : Type uQuery} {Phase : Type uPhase}
    {Source : Type uSource} {View : Type uView} {Receipt : Type uReceipt}
    (issuer : Issuer Revision Query Phase Source View Receipt)
    (payload : ProjectionPayload Revision Query Phase Source View) :
    Certificate Revision Query Phase Source Receipt where
  evidenceRevision := payload.evidenceRevision
  activeQueries := payload.activeQueries
  commitmentPhase := payload.commitmentPhase
  sources := payload.sources
  projectionReceipt := issuer.issue payload

@[simp] theorem certify_evidenceRevision
    {Revision : Type uRevision} {Query : Type uQuery} {Phase : Type uPhase}
    {Source : Type uSource} {View : Type uView} {Receipt : Type uReceipt}
    (issuer : Issuer Revision Query Phase Source View Receipt)
    (payload : ProjectionPayload Revision Query Phase Source View) :
    (certify issuer payload).evidenceRevision = payload.evidenceRevision := by
  rfl

@[simp] theorem certify_activeQueries
    {Revision : Type uRevision} {Query : Type uQuery} {Phase : Type uPhase}
    {Source : Type uSource} {View : Type uView} {Receipt : Type uReceipt}
    (issuer : Issuer Revision Query Phase Source View Receipt)
    (payload : ProjectionPayload Revision Query Phase Source View) :
    (certify issuer payload).activeQueries = payload.activeQueries := by
  rfl

@[simp] theorem certify_commitmentPhase
    {Revision : Type uRevision} {Query : Type uQuery} {Phase : Type uPhase}
    {Source : Type uSource} {View : Type uView} {Receipt : Type uReceipt}
    (issuer : Issuer Revision Query Phase Source View Receipt)
    (payload : ProjectionPayload Revision Query Phase Source View) :
    (certify issuer payload).commitmentPhase = payload.commitmentPhase := by
  rfl

@[simp] theorem certify_sources
    {Revision : Type uRevision} {Query : Type uQuery} {Phase : Type uPhase}
    {Source : Type uSource} {View : Type uView} {Receipt : Type uReceipt}
    (issuer : Issuer Revision Query Phase Source View Receipt)
    (payload : ProjectionPayload Revision Query Phase Source View) :
    (certify issuer payload).sources = payload.sources := by
  rfl

@[simp] theorem certify_projectionReceipt
    {Revision : Type uRevision} {Query : Type uQuery} {Phase : Type uPhase}
    {Source : Type uSource} {View : Type uView} {Receipt : Type uReceipt}
    (issuer : Issuer Revision Query Phase Source View Receipt)
    (payload : ProjectionPayload Revision Query Phase Source View) :
    (certify issuer payload).projectionReceipt = issuer.issue payload := by
  rfl

/-- A model or hand-written strategy remains a replaceable consumer of the
certificate. -/
abbrev Policy
    (Revision : Type uRevision) (Query : Type uQuery) (Phase : Type uPhase)
    (Source : Type uSource) (Receipt : Type uReceipt) (Action : Type uAction) :=
  Certificate Revision Query Phase Source Receipt → Action

/-- The certificate interface imposes no action choice: any two actions can be
selected by two policies over the same certified context. -/
theorem certificate_does_not_select_action
    {Revision : Type uRevision} {Query : Type uQuery} {Phase : Type uPhase}
    {Source : Type uSource} {Receipt : Type uReceipt} {Action : Type uAction}
    (certificate : Certificate Revision Query Phase Source Receipt)
    (left right : Action) :
    ∃ leftPolicy rightPolicy :
        Policy Revision Query Phase Source Receipt Action,
      leftPolicy certificate = left ∧ rightPolicy certificate = right := by
  exact ⟨fun _ => left, fun _ => right, rfl, rfl⟩

end Mettapedia.CognitiveArchitecture.Agent.ContextCertificate

#print axioms Mettapedia.CognitiveArchitecture.Agent.ContextCertificate.certificate_does_not_select_action
