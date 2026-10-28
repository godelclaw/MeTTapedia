# Evidence and cognitive state

`EvidenceRevision` models evidence-bearing memory records. `DerivedBeliefs`
tracks derivation support, contradiction and withdrawal. `AttentionEvidence`
connects canonical PLN evidence and world-model extraction to independent
attention state.

Stamped observations replace a keyed contribution, so the same delivered
observation is not added twice. Association evidence concerns a link's usefulness;
it is not factual support for either endpoint. Explicit deletion recomputes an
edge's aggregate from retained support.

Uniform attenuation lowers evidence totals and confidence while preserving the
improper-prior strength view for positive finite scaling. It is generally not
idempotent. Confidence-weighted normalized shares may change even when strength
does not. Path attention is not full PLN deduction: the complementary route
and rule-specific semantic assumptions remain necessary.

The ranking-margin theorem reuses the canonical premise-selection library. Its
error bounds are hypotheses, not a certification of floating-point arithmetic.

Attention's locality tail `(1−α)^(k+1)` and the reasoning shell error
`2|Γ|C^n` in `Logic.MarkovLogicLocalQueryApproximation.shell_query_error` both
express contraction per hop. Restart α is agent-chosen; uniform Dobrushin C
is a property of the knowledge model. Near C = 1 this certificate needs larger
shells, not a conclusion that every query is hard. This is a DLR approximation
result, not a theorem about loopy BP iteration.

`AttentionEvidence.spreading_revision_commute` fixes the supplied attention
kernel and separates attention from world-model revision. Selecting where to
reason cannot itself strengthen factual evidence. Regret calibration, graph
learning, actual context selection and native floating point remain separate
obligations; no runtime integration is claimed by these bridges.
