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

Each file is self-contained (no Mathlib) and ends with a
`#print axioms` audit: zero `sorry`, axioms at most `propext` and
`Quot.sound`, several theorems axiom-free. Check with:

```
lean HeartModel.lean
lean ClawArchitectures.lean
lean PresentMoment.lean
```

The paper (`paper/pettaclaw.tex`, PDF alongside) tells the whole story:
architecture, doctrine, the two incidents, the theorems, the live
verifications. Model-to-code conformance tests live with the agent
runtime.
