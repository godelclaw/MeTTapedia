# Cognitive Architecture — Motivations, Agents & Consciousness Criteria (Lean 4)

A *cognitive architecture* is a computational theory of how an agent's
motivations, emotions, and decisions fit together into one working mind: what it
wants, how a stimulus changes those wants, and how those wants pick an action.
This directory formalizes such architectures in Lean and asks what they have in
common — and what they leave out.

The organizing abstraction is **MetaMo**, a category-theoretic *motivational
Q-module*: motivational state lives in a module over a quantale of "intensities,"
an **appraisal** functor maps environmental stimuli to changes in that state, and
a **decision** functor maps state to actions. Two well-known psychological
architectures appear as concrete MetaMo instances — **OpenPsi** (the OpenCog
realization of Dörner's *Psi* theory, with six demands and four modulators) and
**MicroPsi** (Bach's architecture, with seven demands and a PAD emotion model) —
which lets the formalization compare them on a common footing and *prove* where
they coincide and where they fall short. The `Values/` strand then extends the
picture beyond the consequentialist core both architectures share (Schwartz
values, Haidt's moral foundations, deontological/relational/temporal/meta layers),
and the work-in-progress **GödelClaw** kernel (`GodelClaw/`) builds an
ethical-agent layer — policy kernel, tool broker, gate chain, "mindlock" — on top.

## Modules

### MetaMo

MetaMo is a six-file motivational Q-module framework.

- `MetaMo/Basic.lean`
  - MetaMo/Basic.lean defines Q-module structure with scalar multiplication

- `MetaMo/Appraisal.lean`
  - MetaMo/Appraisal.lean defines environmental stimulus appraisal functors

- `MetaMo/Decision.lean`
  - MetaMo/Decision.lean defines action selection functors

- `MetaMo/Commutativity.lean`
  - MetaMo/Commutativity.lean proves appraisal-decision commutativity

- `MetaMo/Dynamics.lean`
  - MetaMo/Dynamics.lean proves stability via Banach fixed-point arguments

- `MetaMo/Main.lean`
  - MetaMo/Main.lean aggregates the MetaMo module interface

### OpenPsi

OpenPsi is a five-file formalization of Dorner Psi with six demands and four modulators.

- `OpenPsi/Basic.lean`
  - OpenPsi/Basic.lean defines demands, modulators, and action-selection rules

- `OpenPsi/FuzzyLogic.lean`
  - OpenPsi/FuzzyLogic.lean defines fuzzy satisfaction computation

- `OpenPsi/ActionSelection.lean`
  - OpenPsi/ActionSelection.lean defines demand-driven action selection

- `OpenPsi/MetaMoInstance.lean`
  - OpenPsi/MetaMoInstance.lean defines OpenPsi as a QModule over ENNReal

### MicroPsi

MicroPsi is a three-file formalization with seven demands and PAD decomposition.

- `MicroPsi/Basic.lean`
  - MicroPsi/Basic.lean defines demands, PAD model, and utility action selection

- `MicroPsi/MetaMoInstance.lean`
  - MicroPsi/MetaMoInstance.lean defines MicroPsi as a QModule over ENNReal

### Bridges

Bridges is five files of cross-architecture comparison and limits.

- `Bridges/PLNMetaMoBridge.lean`
  - Bridges/PLNMetaMoBridge.lean connects PLN evidence quantales to MetaMo

- `Bridges/OpenPsiMicroPsiBridge.lean`
  - Bridges/OpenPsiMicroPsiBridge.lean compares OpenPsi and MicroPsi as MetaMo instances

- `Bridges/ModelExpressiveness.lean`
  - Bridges/ModelExpressiveness.lean analyzes expressiveness boundaries

- `Bridges/MissingValueSystems.lean`
  - Bridges/MissingValueSystems.lean proves value-system gaps outside consequentialism

### Agent world state and plural context

`Agent/` contains the general, architecture-neutral state and context layer used
by cognitive agents:

- `WorldState.lean`, `GoalCommitment.lean`, and `ContextEpoch.lean` distinguish
  recoverable world evidence, active commitments, and epoch-scoped views. The
  core world-state and compaction theory has no PLN import.
- `EffectReceiptProjection.lean` and `EffectBrokerNoninterference.lean` retain
  exact effect receipts while proving when bounded projections and independent
  brokers are safe.
- `MultiAgentFusionNoGo.lean` and `WorldModelRegimeSeparation.lean` show why
  locally coherent agent views need not form one global classical model.
- `WorldOfViewsBridge.lean` gives proof-relevant relational coordination and an
  explicit locally coherent but non-gluable chart family.
- `OpenEndedContext.lean` proves that a fixed context sufficient for an
  accumulated state-separating query schedule must be injective. For each finite
  active query family it constructs the canonical weakest sufficient view,
  refreshed from recoverable evidence.

These modules preserve the semantic content of the GödelClaw agent-world-state
development while placing the reusable mathematics under the general
`CogArch.Agent` hierarchy. The minimal world-model hierarchy is
in `Mettapedia.Logic.WorldModel`; additive PLN evidence is attached explicitly
by `Agent/Bridges/PLN/WorldStateEvidence.lean`. PLN-specific calculi and truth
readouts remain under `Mettapedia.PLN.WorldModel`.

### Consciousness criteria and realization

[`Consciousness/ArchitecturalIndicators.lean`](Consciousness/ArchitecturalIndicators.lean)
compares connected and split workspace mechanisms using actual interventions.
They can agree on every passive input history while differing when the workspace
state is changed. [`GodelClaw/GlobalWorkspace.lean`](GodelClaw/GlobalWorkspace.lean)
uses these results as shared architecture contracts.

[`Consciousness/TraceAndImplementation.lean`](Consciousness/TraceAndImplementation.lean)
connects execution, observation and causal criteria. Its workspace descriptions
are local sections over input experiments. Compatible sections can be joined,
while the resulting passive description still loses the intervention distinction.
The general constructions live in
[`GSLT/Dynamics/ScriptedBackup.lean`](../GSLT/Dynamics/ScriptedBackup.lean) and
[`GSLT/Causality/ScriptedExecution.lean`](../GSLT/Causality/ScriptedExecution.lean),
alongside
[`CategoryTheory/LocalSections.lean`](../CategoryTheory/LocalSections.lean):

- A validated recording with dormant backup machinery matches direct execution
  for every external input continuation. Its table reads and evaluator calls
  remain different, including under changes to the dormant evaluator.
- Input-only contexts preserve agreement at every rung of the causal hierarchy.
  Admitting evaluator replacement refines that comparison and separates the
  constructed machines. The context-forgetting map loses behavioral distinctions;
  neither full input behavior nor a state-projection cover implies static
  faithfulness or physical causal realization.
- Compatible assignments over arbitrary covers have a constructed unique global
  section. Additional constraints require their own gluing laws; locally uniform
  descriptions on disconnected contexts can fail to have a uniform extension.
- Explicit premise comparisons distinguish experiential origin, an individuated
  subject and reflective awareness. Description invariance alone leaves subject
  identity undetermined. These are small mathematical reconstructions with stated
  premises; they supply no empirical consciousness assignment.

[`GSLT/Causality/ContextualRealization.lean`](../GSLT/Causality/ContextualRealization.lean)
connects the realization criterion to operational covers and context-theory
hosting. Its commuting intervention square transports modal formulas and
formula-generated native types; vocabulary and context coverage yield exact
comparison at every causal rung. The concrete
[`ScriptedExecutionRecoding.lean`](../GSLT/Causality/ScriptedExecutionRecoding.lean)
instance changes states, tables, evaluators and replacement commands together.
The existing consciousness comparison now also reuses the compiler lowering
control: public reachability agrees while one source instruction becomes two
target instructions. An escaping target transition blocks an operational cover.

[`Consciousness.lean`](Consciousness.lean) collects this framework with the
following complementary modules:

- [`PhenomenalContent.lean`](Consciousness/PhenomenalContent.lean) constructs a
  category of rooted relational event presentations. Arrows retain event maps,
  propagation, reflexive links and formation/separation predicates. A faithful
  forgetful functor exposes the underlying event system. Pain and joy at the
  selected event are separate from internally sustaining suffering and happiness
  carriers; further descriptive features remain independently expressible.
  Its `EnrichedContent` category retains arbitrary structured qualities at every
  event, with each quality constraining the actual event maps. Feature restriction
  acts on these presentations and commutes with the corresponding report pullback.
  Positive facts transport along structure-preserving maps, while exact facet
  descriptions transport along isomorphisms. Adding propagation can create a
  sustaining carrier, so positive preservation alone does not give exact profile
  preservation. Full Yoneda interfaces reconstruct objects up to isomorphism
  within this chosen category; incomplete reports can forget distinct event
  maps. The construction supplies candidate phenomenal structure, not a
  consciousness assignment.
- [`PhenomenalRealization.lean`](Consciousness/PhenomenalRealization.lean) uses
  [`PartialSections.lean`](../CategoryTheory/PartialSections.lean) for actual modal
  experiment descriptions, receipt descriptions and chronological appraisals.
  Existing operational covers preserve full formula descriptions. Workspace and
  receipt controls show that identical passive content can have distinct causal
  extensions. Machine recoding preserves separately indexed appraisal histories.
- [`PhenomenalScrutability.lean`](Consciousness/PhenomenalScrutability.lean) connects
  content descriptions to explicit physical, phenomenal and indexical information
  bases, using the generic
  [`ComponentBases.lean`](../Logic/Propositions/ComponentBases.lean). Its concrete
  interpretation admits compatible additions without a totality clause. Reports,
  phenomenal information and subject/time information settle different questions.
  Any adequacy result is relative to the specified sentence language, rather than
  a proof of Chalmers's general scrutability thesis or a causal production claim.

The partial-description report adjunction is constructed from context restriction.
It is not an empirical identification with a qualia/report adjunction. Gluing
compatible descriptions likewise does not merge subjects or manufacture
independent corroboration.

[`Consciousness/Valence.lean`](Consciousness/Valence.lean) separates learning
reward, architectural affect and authored transition appraisal. It reuses
observer visibility and occurrence-indexed wellbeing judgments. Finite
execution appraisals take values in arbitrary additive monoids, including
products and independently indexed coordinate families. They compose
chronologically and transport through actual tick/appraisal commutation.
Optional additive readouts commute with accumulation; a scalar balance loses
pain and suffering coordinates even across histories with the same endpoint.
All four authored pain, suffering, joy and happiness quantities can be
positive while that balance is zero. `potentialDrop` is a unit-step finite-difference
reconstruction of Joffily and Coricelli's proposed free-energy dynamics; it does
not establish an empirical model of experience. The relational account in
[`Cybernetics/ReflexiveValence.lean`](../Cybernetics/ReflexiveValence.lean) remains
a distinct hypothesis rather than being identified with scalar appraisal.

`RobustPrefixNonnegative` requires a nonempty admitted assessor family and a
nonnegative cumulative appraisal at every input prefix. Enlarging that family
can block permission, and transport requires coverage of its target assessors.
Zero final appraisal can hide a negative prefix. A permitted trace can still
contain a negative episode, so the criterion is not a suffering-free guarantee.
An instance on the actual Boolean-to-`Fin 2` machine recoding preserves two
independently stated toy appraisals and their prefix constraints. Arithmetic
evidence remains separate from evidence of patienthood or felt valence.

### Evidence, uncertainty and temporal assessment

[`Agent/WellbeingAssessment.lean`](Agent/WellbeingAssessment.lean) pairs partial
assessment assignments with typed evidence ledgers. Exact keys retain the
occurrence, assessor, interpretation and independently named quality. Restriction
filters existing witnesses; compatible composition appends both ledgers.
Different assessors can retain different reports, while conflicting values at
one exact key prevent a common refinement. Missing data remains distinct from
an observed zero. The concrete report-retrieval family certifies authored ledger
positions, without certifying experiential truth or independent corroboration.

[`InterpretationAssessment.lean`](Consciousness/InterpretationAssessment.lean)
keeps a separately supplied state-to-outcome interpretation relation. Possible
outcomes require one jointly fitting state and interpretation. Refinement removes
possibilities; enlarging the interpretation family adds them. `Robust` checks
every supported outcome and requires nonempty support; `SupportsFamily` separately
requires a witness for each admitted interpretation. Compatible local descriptions
can still lack a jointly realizing operational state. Intersecting projected
outcome sets can lose correlations that the joint witness retains. Translation
equivalence requires coverage of target interpretation witnesses as well as
forward preservation.

[`AssessmentEvidence.lean`](Consciousness/AssessmentEvidence.lean) proves that
compatibility with an evidence-bearing assignment is equivalent to agreement
with every ledger entry. Typed report retrieval and operational agreement remain
distinct obligations. Its controls provide genuine retrieval witnesses for a
report that disagrees with a separately specified candidate state.

[`AppraisalTrajectory.lean`](Consciousness/AppraisalTrajectory.lean) retains every
actual intermediate state and transition assessment using the existing executor.
Independent coordinate types carry their own authored policies. Append and
translation laws preserve complete profiles, including executed prefix contexts.
Two histories can have the same endpoint and full multidimensional accumulated
appraisal yet different episodes and protection judgments. A permitted repair
segment does not retroactively certify an earlier path-policy violation.

[`WorkspaceAssessment.lean`](Consciousness/WorkspaceAssessment.lean) connects
possible-outcome assessment to the existing receipt-bearing workspace model.
Its current-delivery query suffices for an operational currency assessment;
published content alone does not. Re-publication can preserve content and the
historical receipt while invalidating its current authority. These executable
Lean contracts supply neither deployed-host conformance nor an assessment of an
agent's felt experience.

### Values

Values is nine files extending beyond consequentialism.

- `Values/SchwartzValues.lean`
  - Values/SchwartzValues.lean defines Schwartz ten-value circumplex structure

- `Values/MoralFoundations.lean`
  - Values/MoralFoundations.lean defines Haidt six moral foundations

- `Values/DeontologicalLayer.lean`
  - Values/DeontologicalLayer.lean defines duty constraints above consequential utility

- `Values/RelationalValues.lean`
  - Values/RelationalValues.lean defines individual-dependent relational values

- `Values/TemporalValues.lean`
  - Values/TemporalValues.lean defines legacy and future-generation value structure

- `Values/MetaValues.lean`
  - Values/MetaValues.lean defines values about values including corrigibility

- `Values/FOETBridge.lean`
  - Values/FOETBridge.lean connects value formalization to FOET

### GödelClaw (work in progress)

`GodelClaw/` (including `GodelClaw/Ethics/`) is a work-in-progress
ethical-agent kernel — a policy kernel, tool broker, gate chain, and "mindlock"
with a MetaMo bridge, over a meaning/agency ethics layer.
[`GodelClaw/Core.lean`](GodelClaw/Core.lean) takes a concrete value proposition
and evidence for it through `CoreValueDeclaration`. Its docstring records the
replacement of the former opaque `UniversalLovingCare` postulate.

## Key results

- OpenPsi and MicroPsi are MetaMo QModule instances.
- Appraisal-decision commutativity is proven when the quantale is commutative.
- Contractivity is a sufficient condition for unique motivational equilibrium.
- Gap analysis shows that both base architectures are fundamentally consequentialist.

## Formalization status

The 2026-10-09 realization and local-view batch builds with the existing
architectural-indicator and GödelClaw workspace consumers. Its seven implementation
modules pass warnings-as-errors and a kernel-dependency audit: 578 declarations,
with dependencies limited to `propext`, `Quot.sound` and `Classical.choice`.
Those counts include existing declarations in the edited modules. Qualification
covers that batch and its stated consumers; the earlier directory-wide inventory
was dated 2026-08-25.

The subsequent contextual-realization and valence batch qualifies five modules:
57 new named theorems, five warnings-as-errors checks, and an audit of 316 kernel
declarations using only the same three standard axioms. Its scoped build includes
the existing GödelClaw workspace consumer. The audit includes earlier declarations
in the edited modules; it is not a directory-wide or deployed-runtime qualification.
The reproducible scope and checks are recorded in
[`QUALIFICATION.json`](../../artifacts/context-realization-valence-20261009/QUALIFICATION.json).

## References

- Zhenhua Cai, Ben Goertzel & Nil Geisweiller, [*OpenPsi: Realizing Dörner's "Psi" Cognitive Model in the OpenCog Integrative AGI Architecture*](https://doi.org/10.1007/978-3-642-22887-2_22) (AGI 2011, LNCS 6830, Springer) — the OpenPsi demands/modulators formalized in `OpenPsi/`.
- Dietrich Dörner, [*Bauplan für eine Seele*](https://www.spektrum.de/magazin/bauplan-fuer-eine-seele/825713) (Rowohlt, 1999) — the *Psi* theory underlying both OpenPsi and MicroPsi.
- Joscha Bach, [*Principles of Synthetic Intelligence: Psi — An Architecture of Motivated Cognition*](https://global.oup.com/academic/product/principles-of-synthetic-intelligence-9780195370676) (Oxford University Press, 2009) — the MicroPsi architecture (demands + PAD model) formalized in `MicroPsi/`.
- Shalom H. Schwartz, [*Universals in the Content and Structure of Values*](https://doi.org/10.1016/S0065-2601(08)60281-6), in *Advances in Experimental Social Psychology* 25 (1992), 1–65 — the ten-value circumplex in `Values/SchwartzValues.lean`.
- Jonathan Haidt, [*The Righteous Mind: Why Good People Are Divided by Politics and Religion*](https://righteousmind.com/) (Pantheon, 2012) — Moral Foundations Theory in `Values/MoralFoundations.lean`.
- Alan Gewirth, [*Reason and Morality*](https://press.uchicago.edu/ucp/books/book/chicago/R/bo25842059.html) (University of Chicago Press, 1978) — the Principle of Generic Consistency underlying the Gewirth/FOET ethics layer in `GodelClaw/Ethics/` and `Values/FOETBridge.lean`.
- Mateus Joffily and Giorgio Coricelli, [*Emotional Valence and the Free-Energy Principle*](https://doi.org/10.1371/journal.pcbi.1003094) (2013) — the source hypothesis for the discrete potential-difference appraisal.
- Kent Berridge, Terry Robinson and J. Wayne Aldridge, [*Dissecting components of reward: liking, wanting, and learning*](https://pmc.ncbi.nlm.nih.gov/articles/PMC2756052/) (2009) — distinguishes components of reward rather than equating reward with pleasure.
- Robert Long et al., [*Taking AI Welfare Seriously*](https://arxiv.org/abs/2411.00986) (2024) — motivates welfare assessment under uncertainty.

---
*Realization and local-view qualification updated 2026-10-09.*
