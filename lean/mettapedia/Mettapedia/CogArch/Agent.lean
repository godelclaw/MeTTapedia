import Mettapedia.CogArch.Agent.WorldState
import Mettapedia.CogArch.Agent.GoalCommitment
import Mettapedia.CogArch.Agent.ChronologicalWorldModel
import Mettapedia.CogArch.Agent.MultiAgentFusionNoGo
import Mettapedia.CogArch.Agent.WorldModelRegimeSeparation
import Mettapedia.CogArch.Agent.ContextEpoch
import Mettapedia.CogArch.Agent.ContextAttention
import Mettapedia.CogArch.Agent.EffectReceiptProjection
import Mettapedia.CogArch.Agent.WorkReporting
import Mettapedia.CogArch.Agent.EffectBrokerNoninterference
import Mettapedia.CogArch.Agent.OpenEndedContext
import Mettapedia.CogArch.Agent.WorldOfViewsBridge
import Mettapedia.CogArch.Agent.ReproducibleBuildView
import Mettapedia.CogArch.Agent.ReproducibleBuildReplay
import Mettapedia.CogArch.Agent.RevisionLineage
import Mettapedia.CogArch.Agent.ProtectedSelfRevision
import Mettapedia.CogArch.Agent.PatienthoodWellbeing
import Mettapedia.CogArch.Agent.WellbeingObserverTransformationBoundary
import Mettapedia.CogArch.Agent.ContextCertificate
import Mettapedia.CogArch.Agent.TaskPhase
import Mettapedia.CogArch.Agent.PermissiveActionGraph
import Mettapedia.CogArch.Agent.AddressedEffects
import Mettapedia.CogArch.Agent.RelationalAtlas
import Mettapedia.CogArch.Agent.ConversationContinuation
import Mettapedia.CogArch.Agent.WellbeingAssessment

/-!
# General agent-architecture interfaces

Typed operational state, commitments, context epochs, plural world models,
effect receipts, and authority-preserving execution boundaries.  These
interfaces are architecture-neutral; particular agents are downstream
instances.  Public work reporting separates activity metadata from commentary
and preserves that distinction when preparing summary input.
Reproducible event histories use the same weakest-sufficient-view
boundary without treating a bounded context as the authoritative ledger;
declared build views connect to that order through a separate bridge.
Assessment views retain occurrence, assessor, interpretation and quality keys
alongside their actual typed evidence; restriction and compatible composition
preserve that provenance without assigning patienthood or experienced wellbeing.
-/
