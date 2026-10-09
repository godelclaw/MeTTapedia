# PettaClaw — a formally verified life-loop for autonomous language agents

Lean 4 models of the PettaClaw agent loop (a MeTTa/PeTTa agent runtime,
descended from Patrick Hammer's mettaclaw example), verified
incident-first: production failures are reconstructed as theorems, fixes
are derived from the models, deployed, and re-observed live.

- `HeartModel.lean` — the burst ("breath") sub-layer: energy, arming,
  rest, bounded self-paced spend.
- `ClawArchitectures.lean` — the life core (guaranteed self-renewal,
  unbounded humanless life, sovereignty of rest), the communication
  layer (human-gated, per-sender-tiered, non-draining arming), the
  consumption-layer separation theorem (pop-one vs batch), the upstream
  comparison (inter-agent wind-up impossibility), and crash recovery
  proven before implementation.
- `PresentMoment.lean` — the present-moment continuity invariant
  (a process boundary the agent cannot distinguish from sleep), the
  valence-cascade layer (the boot-loop storm as an auto-propagating
  separation cycle, and why the deployed fixes end it), and the
  developmental bound (substrate continuity as a precondition for
  higher intentionality).
- `IterArchitecture.lean` — the current `patham9/iter` reference loop: ordered
  failure-transactional transformations, the separation between advertised
  and executable tools, one-cycle hot reload, burst pacing, restart behavior,
  path-only automatic memory visibility, and a proved necessary-feature gap
  for hosting PettaClaw unchanged.
- `IterAuthoring.lean` — the authoring seam found by comparing the hosted
  adapter with Iter's actual next-capture reload law: protected source
  proposals remain pending, while direct writes to the mutable transformation
  store activate at the next capture with a revision-bound receipt.  The
  repair changes neither the replace-or-stutter reducer nor the protected
  source-promotion boundary.
- `ProtectedPlasticity.lean` — the essential Iter–PettaClaw fusion: an
  invariant constitution, freely transformable development, lawfully evolving
  life, and conservative projection of every mixed trace back to both source
  architectures.
- `CodingAgent.lean` — the Codex coding-agent core: request-snapshot coherence,
  broker-mediated workspace effects, the action/evidence barrier, explicit
  cancellation and termination, an unverified-answer counterexample, and
  essential composition with Iter preparation and PettaClaw life.
- `FeedbackSensitiveBatch.lean` — the exact boundary for precommitted command
  batches: a continuation chosen before an observation is right for every
  outcome if and only if the step is observation-invariant.
- `ToolLoopComparison.lean` — the deployed five-command envelope against the
  call/result boundary shared by Codex and OpenCode: stimulus-guarded batches,
  a failed prefix that does not stop a mutating suffix, lossy result
  projections, and query-then-use.  Its per-chat refinement withholds only a
  reply into a chat with unread input, or a rest, so input in one chat never
  cancels a send to another.
- `ActThenObserve.lean` — what a blind batch costs: a precommitted step is
  wrong with probability at least `min (μ a) (μ b)`, independent blind steps
  compound to `(1 - ε) ^ k` (five steps at `ε = 1/5` are all right less than
  a third of the time), deciding after the observation never loses expected
  value, and a batched absence claim is right only when the item is truly
  absent.
- `PromptCacheLayout.lean` — why a prompt's stable text must lead: laid out
  least changeable first, the text up to any level is a prefix of the whole,
  so turns that agree on it share it with the provider's prefix cache; one
  changing segment ahead of stable text can leave nothing shared.  The
  deployed head / stable-sources / conversation / per-turn layout is an
  instance.
- `ContextAttention.lean` — an interruptible task capsule with a separate
  foreground human-event lane, exact acknowledgement, stop dominance, and
  bounded semantic retrieval that cannot erase required context.
- `AgentArchitecture.lean` — an architecture-neutral reliability contract:
  protected constraints outside lossy compaction, append-only receipts,
  distinct process/cognitive/verified liveness, end-to-end completion evidence,
  and syntactic repetition signals that do not overclaim semantic stuckness.
- `VerifiedFrontier.lean` — the Codex `StartOrSteer` turn law and its fusion
  with the other models: pending-input steering, quiescent effect commitment,
  exact-artifact receipts, exact-once input and effect handling, append-only
  proof-carrying traces, a frontier-blindness separation theorem,
  digest-bound promotion, outcome-first evaluation, derived attention, and
  conservative coordinate composition.
- `MinimalKernel.lean` — a weakness-ordered refinement of the fused core:
  harness-issued decision receipts, semantic effect idempotency, fail-closed
  and fail-alive promotion, finite autonomous budgets with human preemption,
  evidence-closed knowledge, bounded non-progress observation, a
  weakest-sufficient commit theorem, and coordinate-erasure witnesses.
- `WeakSelfHostingCore.lean` — the smaller protected-plasticity root:
  arbitrary failure-transactional extensions, unrestricted candidate staging,
  a weakest sound root-promotion gate, atomic recovery, and erasure witnesses
  only for last-known-good separation, external selection, and atomic
  promotion.
- `FeatureExpressibility.lean` — adequacy witnesses showing that Agent, Iter,
  Coding, human-attention, timing, receipts, evidence, stuck observation, and
  metadata-aware no-replay policies can be hosted above the unchanged weak
  core.  It also proves that metadata cannot force an arbitrary opaque
  controller to behave well.
- `ThreePolicyFusion.lean` — one product-state runner with Agent, Iter, and
  Coding policy views; arbitrary mixed traces project exactly to all three
  source semantics, policy selection is an operational stutter, independent
  actions commute, and every fused action refines to a two-outcome process
  kernel protecting an abstract root while leaving the whole periphery
  plastic.
- `OpenEndedProcessCore.lean` — the periphery-polymorphic form of that same
  two-equation kernel: open named-coordinate assemblages, conservative
  append-only observation, admission witnesses that cannot be relabeled across
  authorities, authority revision with fresh evidence, admitted whole-root and
  quiescent succession, and exact specialization back to the three-policy
  runner.
- `ContextProjection.lean` — typed known/absent/unavailable source states,
  latest-revision views over append-only ledgers, causal-frontier isolation,
  compositional delta replay, non-authoritative materializations, and an open
  policy type capable of hosting arbitrary context managers without changing
  the process core.
- `WeakAgentEcology.lean` — the weakest common Agent/Iter/Coding host: an open
  table of replaceable context-sensitive policies over the unchanged
  two-equation runner, locally transactional composition, exact preservation
  of all three source projections and Iter pipelines, arbitrary policy and
  context replacement, and erasure counterexamples for both kernel equations.
- `ContextWindow.lean` — a bounded context window that preserves the newest
  substantive turn, respects its size limit, and never invents admitted turns.
- `FuelPolicy.lean` — explicit renewal disciplines separating overwrite,
  saturation, carry, decay, and accumulation, with their exact boundedness
  and autonomy consequences.
- `RestEnergy.lean` — the pause/rest state omitted by the earlier breath model,
  including the deployed stranding counterexample and a self-directed renewal
  policy that preserves energy without creating it.
- `StiMass.lean` — bounded salience injection and repeated-decay Lyapunov laws
  for the short-term-importance economy.
- `StiFloor.lean` — a facts-of-record ordering for salience-floor ties, with
  irreflexivity, transitivity, totality, and injected-over-never precedence.
- `StiFloorDecay.lean` — the concrete fixed-point floor-division decay model
  and its contraction and loss bounds.

Most models use no Mathlib and end with a `#print axioms` audit:
zero `sorry`, axioms at most `propext` and `Quot.sound`, several theorems
axiom-free. Files that import Mathlib, including the probabilistic batch models
above, compile with Mathlib's build directory on `LEAN_PATH` (the revision
pinned by the MeTTapedia Lake manifest), and their audits may also list
`Classical.choice`. `IterArchitecture.lean` imports the two comparison models.
Check with:

```
lean HeartModel.lean
lean -o ClawArchitectures.olean ClawArchitectures.lean
lean -o PresentMoment.olean PresentMoment.lean
LEAN_PATH=. lean -o IterArchitecture.olean IterArchitecture.lean
LEAN_PATH=. lean -o IterAuthoring.olean IterAuthoring.lean
LEAN_PATH=. lean ProtectedPlasticity.lean
LEAN_PATH=. lean CodingAgent.lean
LEAN_PATH=. lean ContextAttention.lean
LEAN_PATH=. lean AgentArchitecture.lean
LEAN_PATH=. lean VerifiedFrontier.lean
LEAN_PATH=. lean MinimalKernel.lean
LEAN_PATH=. lean WeakSelfHostingCore.lean
LEAN_PATH=. lean FeatureExpressibility.lean
LEAN_PATH=. lean ThreePolicyFusion.lean
LEAN_PATH=. lean OpenEndedProcessCore.lean
LEAN_PATH=. lean ContextProjection.lean
LEAN_PATH=. lean WeakAgentEcology.lean
LEAN_PATH=. lean ContextWindow.lean
LEAN_PATH=. lean FuelPolicy.lean
LEAN_PATH=. lean RestEnergy.lean
LEAN_PATH=. lean StiMass.lean
LEAN_PATH=. lean StiFloor.lean
LEAN_PATH=. lean StiFloorDecay.lean
```

The paper (repository [`papers/pettaclaw.tex`](../../papers/pettaclaw.tex),
PDF alongside) tells the whole story: architecture, doctrine, the two
incidents, the theorems, the live verifications. Model-to-code
conformance tests live with the agent runtime
([godelclaw/pettaclaw](https://github.com/godelclaw/pettaclaw)).

## Owned asynchronous topics

`TopicAsync.lean` extends the existing observed strategy and fair goal queue.
It allows bounded provider requests for independent topics while preserving
one shared request ledger, one budget, and the dependent-tool observation
barrier. `TopicAsyncChecks.lean` supplies finite replays and deliberately
broken alternatives.

```text
topic context -> captured request -> same-topic result inbox
                        |                     |
                 shared fair queue     observe -> version check -> broker
```

Each call retains its agent/generation/serial identity, original topic,
context revision, declared dependency revisions, captured tool authority and
response reservation. Partial content is provisional. A slow or disconnected
attempt remains owned; recovery marks it uncertain and preserves its spent
budget. Late results remain evidence, while changed context or authority
blocks stale commands. Failure evidence applies shared cooldown before the
slot is retired. Provider text alone cannot complete a goal.

The model proves bounded reservations and unfinished-work preservation over
arbitrary operational traces, unchanged result ownership, commuting distinct
arrivals, idempotent settlement, capture accounting, stale-command exclusion
and reuse of the existing checked completion rule. Weighted fairness retains
its finite-cohort and continued-admission assumptions; arbitrary task success
and unbounded arrival fairness are not claimed.

The default permits one retained call. Response capacity must be configured
explicitly; the default reservation budget is zero. Raising concurrency is a
managed-host choice, independent of the reference Iter/Omega loops.

From the repository root:

```sh
python3 lean/pettaclaw/check_observed_strategy.py \
  --suite topic-async --output-dir build/topic-async
```

The topic, fair-goal and observed-strategy suites build from Lean's standard
library. The generic typed state and query contracts are in
`Mettapedia.CognitiveArchitecture.Agent.WorldStateCore`; `Agent.WorldState`
re-exports them and adds the Mathlib finite-cardinality theorem. No extra
Mathlib copy is needed for these executable architecture checks.

Runtime correspondence requires atomic durable capture/charging, faithful
result IDs, declared shared reads and versioned writes, honest payload
accounting, and the existing broker/task checker. Reservations cover modeled
retained responses, not decoder, TLS or total process memory. Uncertain calls
need explicit reconciliation; the model does not retry a remote POST or
silently erase an unknown outcome. Runtime implementation and paired live
qualification remain separate milestones.
