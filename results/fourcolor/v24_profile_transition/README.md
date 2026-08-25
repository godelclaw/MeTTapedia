# Measured `(5,0)` two-pair profile transitions

These two JSON files record measured one-ring transitions using the two
connectivity roles named in the compositional manuscript:

- `alpha-beta`;
- `alpha-gamma`.

They do not include the extra `beta-gamma` role retained by the older
conservative Lean profile.  At the measured bulk cuts, the five capped face
partials are the fixed vector `[3,3,3,3,3]`, so that component contributes one
value to these experiments.

| setting | states | edges | self-loops | max distance to a self-loop | fingerprint |
|---|---:|---:|---:|---:|---|
| closed tube | 60 | 594 | 20 | 2 | `3690cb214cfb56a6` |
| annular tangle | 455 | 6751 | 93 | 2 | `66df6f15e49b595e` |

The JSON conclusion is not trusted by the Lean generator.  The generator
rechecks the two-pair label, CSR dimensions, target bounds, self-loop list,
SHA-256-derived fingerprint, and reverse distances before emitting flat,
paged `ByteArray` payloads and indexed path witnesses.

The resulting Lean theorems prove weak L2 for exactly these decoded finite
transitions.  They do **not** identify either measured transition with every
source-legal corridor.  That source-fidelity theorem, and the manuscript's
strong self-loop theorem restricted to the alive Pascal sector, remain
separate obligations.

Regeneration is performed by
`tools/fourcolor/generate_weak_self_loop_certificate.py`; concrete invocation
arguments are the result JSON, the aggregate Lean output path, its module and
namespace names, and `--page-size 16`.
