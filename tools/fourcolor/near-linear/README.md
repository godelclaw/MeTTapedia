# Near-linear Four Colour catalogue bridges

The two configuration files are unmodified inputs from
[near-linear-4ct/reducible-configurations](https://github.com/near-linear-4ct/reducible-configurations),
pinned to `c2ce7a96e35256201526e2abb51a39d04a588b53`.
Their MIT notice is retained in [LICENSE](LICENSE); [sources.json](sources.json)
records the individual hashes. The associated paper is
[The Four Color Theorem with Linearly Many Reducible Configurations and Near-Linear Time Coloring](https://arxiv.org/abs/2603.24880).

The Lean bridge identifies `D0000` and `D0001` with the existing diamond
configurations 1 and 2. It checks all source rows, complete adjacency,
prescribed internal degrees, every cyclic neighbour list and ordered boundary
alignment. A boundary-triangle insertion between the two source presentations
commutes with the existing reference insertion. Their repair laws reuse the
shared profile certificate and the general boundary-split theorem.

The repair conclusion produces an actual graph colouring compatible with any
supplied Kempe-closed exterior trace relation containing the initial proper
trace. The second entry's repaired witness also has a compatible GSLT insertion
history. This history records construction choices; it does not compute the
exterior Kempe recolourings.

From the repository root, source fidelity can be replayed with:

```sh
python3 tools/fourcolor/near-linear/audit_diamond_sources.py
```

From `lean/fourcolor-classical`, the kernel and dependency audit is:

```sh
lake build MettapediaFourColor.NearLinearDiamondAudit
```

The audit covers 23 roots and excludes all original configuration certificates
and complete Four Colour endpoints. The shared finite profile is retained.
See [diamond-source-audit.json](diamond-source-audit.json) and
[diamond-measurements.json](diamond-measurements.json).

These two entries were already covered by the existing mathematics. The bridge
adds no catalogue compression credit and changes neither the 633 coverage
entries nor the 629 original certificate dependencies in the complete assembly.
It does not verify the rest of the new catalogue, its geometric supply theorem,
its simultaneous repairs or its near-linear running time.
