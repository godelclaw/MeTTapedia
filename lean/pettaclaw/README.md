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
- `IterArchitecture.lean` — the `patham9/iter` seed loop: ordered
  failure-transactional transformations, the separation between advertised
  and executable tools, one-cycle hot reload, burst pacing, restart behavior,
  and a proved necessary-feature gap for hosting PettaClaw unchanged.
- `ProtectedPlasticity.lean` — the essential Iter–PettaClaw fusion: an
  invariant constitution, freely transformable development, lawfully evolving
  life, and conservative projection of every mixed trace back to both source
  architectures.
- `CodingAgent.lean` — the Codex coding-agent core: request-snapshot coherence,
  broker-mediated workspace effects, the action/evidence barrier, explicit
  cancellation and termination, an unverified-answer counterexample, and
  essential composition with Iter preparation and PettaClaw life.
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

The models use no Mathlib and end with a `#print axioms` audit:
zero `sorry`, axioms at most `propext` and `Quot.sound`, several theorems
axiom-free. `IterArchitecture.lean` imports the two comparison models.
Check with:

```
lean HeartModel.lean
lean -o ClawArchitectures.olean ClawArchitectures.lean
lean -o PresentMoment.olean PresentMoment.lean
LEAN_PATH=. lean -o IterArchitecture.olean IterArchitecture.lean
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
```

The paper (repository [`papers/pettaclaw.tex`](../../papers/pettaclaw.tex),
PDF alongside) tells the whole story: architecture, doctrine, the two
incidents, the theorems, the live verifications. Model-to-code
conformance tests live with the agent runtime
([godelclaw/pettaclaw](https://github.com/godelclaw/pettaclaw)).
