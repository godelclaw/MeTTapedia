import Mettapedia.CognitiveArchitecture.Agent.WorldState
import Mettapedia.CognitiveArchitecture.Agent.GoalCommitment
import Mettapedia.CognitiveArchitecture.Agent.ChronologicalWorldModel
import Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo
import Mettapedia.CognitiveArchitecture.Agent.WorldModelRegimeSeparation
import Mettapedia.CognitiveArchitecture.Agent.ContextEpoch
import Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection
import Mettapedia.CognitiveArchitecture.Agent.EffectBrokerNoninterference
import Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext
import Mettapedia.CognitiveArchitecture.Agent.WorldOfViewsBridge
import Mettapedia.CognitiveArchitecture.Agent.ContextCertificate
import Mettapedia.CognitiveArchitecture.Agent.TaskPhase
import Mettapedia.CognitiveArchitecture.Agent.PermissiveActionGraph
import Mettapedia.CognitiveArchitecture.Agent.AddressedEffects
import Mettapedia.CognitiveArchitecture.Agent.ReproducibleBuildView
import Mettapedia.CognitiveArchitecture.Agent.ReproducibleBuildReplay
import Mettapedia.CognitiveArchitecture.Agent.RelationalAtlas

/-!
# General agent-architecture interfaces

Typed operational state, commitments, context epochs, plural world models,
effect receipts, and authority-preserving execution boundaries.  These
interfaces are architecture-neutral; particular agents are downstream
instances.  Reproducible event histories use the same weakest-sufficient-view
boundary without treating a bounded context as the authoritative ledger;
declared build views connect to that order through a separate bridge.  The
relational Atlas instance retains revision identity, explicit audit state,
projection loss, and visible as well as hidden conflict witnesses.
-/
