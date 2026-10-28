import Mettapedia.CognitiveArchitecture.Agent.WorldState
import Mettapedia.CognitiveArchitecture.Agent.GoalCommitment
import Mettapedia.CognitiveArchitecture.Agent.GoalContinuity
import Mettapedia.CognitiveArchitecture.Agent.ChronologicalWorldModel
import Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo
import Mettapedia.CognitiveArchitecture.Agent.WorldModelRegimeSeparation
import Mettapedia.CognitiveArchitecture.Agent.ContextEpoch
import Mettapedia.CognitiveArchitecture.Agent.InstructionScope
import Mettapedia.CognitiveArchitecture.Agent.ContextAttention
import Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection
import Mettapedia.CognitiveArchitecture.Agent.WorkReporting
import Mettapedia.CognitiveArchitecture.Agent.EffectBrokerNoninterference
import Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext
import Mettapedia.CognitiveArchitecture.Agent.WorldOfViewsBridge
import Mettapedia.CognitiveArchitecture.Agent.ReproducibleBuildView
import Mettapedia.CognitiveArchitecture.Agent.ReproducibleBuildReplay
import Mettapedia.CognitiveArchitecture.Agent.RevisionLineage
import Mettapedia.CognitiveArchitecture.Agent.ProtectedSelfRevision
import Mettapedia.CognitiveArchitecture.Agent.PatienthoodWellbeing
import Mettapedia.CognitiveArchitecture.Agent.WellbeingObserverTransformationBoundary
import Mettapedia.CognitiveArchitecture.Agent.ContextCertificate
import Mettapedia.CognitiveArchitecture.Agent.TaskPhase
import Mettapedia.CognitiveArchitecture.Agent.PermissiveActionGraph
import Mettapedia.CognitiveArchitecture.Agent.AddressedEffects
import Mettapedia.CognitiveArchitecture.Agent.RelationalAtlas
import Mettapedia.CognitiveArchitecture.Agent.ConversationContinuation
import Mettapedia.CognitiveArchitecture.Agent.WellbeingAssessment
import Mettapedia.CognitiveArchitecture.Agent.CodingAgent

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
