/-
# Cognitive Architecture Formalization

This module provides formal mathematical frameworks for AGI cognitive architectures,
specifically MetaMo (Motivational Meta-Model), OpenPsi, and MicroPsi.

## Modules

### MetaMo
A general mathematical framework for motivational dynamics based on Q-modules
over commutative quantales. Key results include:
- Commutativity of appraisal and decision functors
- Stability via Banach fixed-point theorem

### OpenPsi (Corrected)
A concrete instantiation of MetaMo based on Dörner's Psi theory with:
- **6 Demands** (Energy, Water, Integrity, Affiliation, Certainty, Competence)
- **4 Modulators** (Activation, Resolution, SecuringThreshold, SelectionThreshold)
- Fuzzy satisfaction computation
- Lowest-satisfaction action selection
- **QModule instance over ℝ≥0∞**

### MicroPsi
Joscha Bach's cognitive architecture with:
- **7 Demands** (Food, Water, Intactness, Affiliation, Certainty, Competence, Exploration)
- **PAD Emotional Model** (Pleasure, Arousal, Dominance)
- Utility-based action selection with emotional modulation
- **QModule instance over ℝ≥0∞**

### Bridges
Connections between modules:
- **PLN-MetaMo Bridge**: PLN truth values parameterize MetaMo dynamics
- **OpenPsi-MicroPsi Bridge**: Formal comparison of the two architectures
- **Model Expressiveness**: What each model can express that the other cannot
- **Missing Value Systems**: Value systems neither model can express

### Consciousness criteria and phenomenal descriptions
Context-sensitive realization contracts, rooted relational content presentations,
partial reports and open physical/phenomenal/indexical information bases.
Independent appraisal coordinates are preserved. Experiential interpretation and
subject identity require additional premises beyond these mathematical models.
Evidence-bearing assessment views retain exact provenance and distinguish
possible outcomes, interpretation-family coverage and complete temporal profiles.

### Values (NEW)
Unified value system extending OpenPsi/MicroPsi to handle full scope of human values:
- **Schwartz's 10 Basic Values** with circular structure
- **Haidt's 6 Moral Foundations** with profile variations
- **Deontological Constraints** (forbidden/required actions)
- **Relational Values** (trust, loyalty, love for specific individuals)
- **Temporal Values** (legacy, future generations, sustainability)
- **Meta-Values** (value learning, moral uncertainty, corrigibility)

## Key Difference: OpenPsi vs MicroPsi

| Aspect | OpenPsi | MicroPsi |
|--------|---------|----------|
| Emotional Model | 4 Modulators | PAD (3 dimensions) |
| Demands | 6 | 7 (adds Exploration) |
| Action Selection | Lowest satisfaction | Utility-based |

## References

- Goertzel & Lian, "Weakness and Its Quantale: Plausibility Theory from First Principles"
- Cai, Goertzel et al., "OpenPsi: Realizing Dörner's 'Psi' Cognitive Model" (AGI 2011)
- Bach, "MicroPsi 2: Modeling Motivation" (AGI 2015)
- Goertzel et al., "Probabilistic Logic Networks"
-/

import Mettapedia.CogArch.MetaMo.Main
import Mettapedia.CogArch.Consciousness
import Mettapedia.CogArch.Agent
import Mettapedia.CogArch.Agent.Bridges.PLN
import Mettapedia.CogArch.AttentionEconomy
import Mettapedia.CogArch.AttentionEconomyResourceControl
import Mettapedia.CogArch.CognitiveSchematic
import Mettapedia.CogArch.CognitiveSchematicAttentionEconomy
import Mettapedia.CogArch.CognitiveSynergy
import Mettapedia.CogArch.AttentionGuidedMindAgentWave
import Mettapedia.CogArch.CognitiveSynergyWave
import Mettapedia.CogArch.MindAgentServiceScheduling
import Mettapedia.CogArch.TriggeredMindAgentSpace
import Mettapedia.CogArch.TriggeredSpaceActivationPolicy
import Mettapedia.CogArch.MindAgentStoreAdmission
import Mettapedia.CogArch.ForegroundChainingPremiseService
import Mettapedia.CogArch.FundedScheduledPremiseService
import Mettapedia.CogArch.ValuedCostedPremiseService
import Mettapedia.CogArch.ForegroundChainingActivationPolicy
import Mettapedia.CogArch.ForegroundChainingClosureBoundary
import Mettapedia.CogArch.ForegroundBackgroundParallelWave
import Mettapedia.CogArch.AtomicForegroundBackgroundWave
import Mettapedia.CogArch.ProtectedMindAgentWave
import Mettapedia.CogArch.ApproximateProtectedTransitionAdvice
import Mettapedia.CogArch.ProtectedForegroundBackgroundCheckedArticle
import Mettapedia.CogArch.ForegroundBackgroundSemanticRouteBinding
import Mettapedia.CogArch.ForegroundBackgroundGSLTILRouteBridge
import Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
import Mettapedia.CogArch.TriggeredOccurrenceRouteRealization
import Mettapedia.CogArch.RecurrentMindAgentPortfolio
import Mettapedia.CogArch.RecurrentParallelMindAgentWave
import Mettapedia.CogArch.AtomicRecurrentMindAgentWave
import Mettapedia.CogArch.RecurringValuedCostedPremiseService
import Mettapedia.CogArch.RecurrentMindAgentBackpressure
import Mettapedia.CogArch.FairRecurrentMindAgentBackpressure
import Mettapedia.CogArch.FiniteRecurrentPremiseCost
import Mettapedia.CogArch.RecurrentMindAgentGSLTILRouteBridge
import Mettapedia.CogArch.RecurrentMindAgentStreamProductivity
import Mettapedia.CogArch.NestedMindAgentExecutionBoundary
import Mettapedia.CogArch.MindWorldRepresentationRealization
import Mettapedia.CogArch.Agent.RevisionLineage
import Mettapedia.CogArch.Agent.ProtectedSelfRevision
import Mettapedia.CogArch.Agent.PatienthoodWellbeing
import Mettapedia.CogArch.EGIClaimTracker
import Mettapedia.CogArch.ProblemSolvingMethods
import Mettapedia.CogArch.OpenPsi.Main
import Mettapedia.CogArch.MicroPsi.Main
import Mettapedia.CogArch.Bridges.Main
import Mettapedia.CogArch.Values.Main
import Mettapedia.NARS.Bridges.CogArch
