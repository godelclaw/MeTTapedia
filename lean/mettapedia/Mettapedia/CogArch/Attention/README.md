# Attention dynamics: how far, when to stop, and when spreading helps

Attention is operational relevance, distinct from factual evidence, confidence,
proof validity and computational cost. The finite theory uses exact real sums.
It does not certify native floating point or empirical retrieval quality.

| Quantity | Owner | Theorems |
|---|---|---|
| Restart α; or retention/half-life and spread fraction d (reach) | Agent chooses | `lazy_ppr_eq_ppr`, `sti_unroll`, `sti_steady_state`, `lazy_ppr_tail`, `outside_mass_le_leakage`, `ppr_ge_depth` |
| Top-k margin and change per round | Runtime observes | `error_le_change`, `next_error_le`, `topk_frozen`, `certified_topk` |
| Pointwise leakage ℓ of a turn's useful cluster | Offline benchmark measures | `outside_mass_le_leakage` |
| Calibration δ = l1(q − c·ppr) | Offline benchmark estimates | `topk_regret_le_l1`, `spreading_regret` |
| Uniform Dobrushin constant C | Property of the knowledge model | `shell_query_error` |

## Reach and the actual ECAN operations

`ThreeTimescale` specifies STI/MTI/LTI, reserves, elapsed-time decay and adjacent
consolidation. `Spreading` applies conservative transport to STI. `Equilibrium`
uses the existing `Restart.RestartWalk`; there is no additional restart or l1
implementation. Row kernels use the existing `restartingWalk` adapter.

The separate ECAN repository exposes `ecan:stimulate`, `ecan:spread`,
`ecan:advance` and `ecan:consolidate`; it does not impose a cycle order.
`ecan:spread` updates one source using its current value. A fixed repeated
linear schedule, fixed graph and equal elapsed intervals are assumptions of
these equilibrium statements, not claims that a global sweep runs today.

For a lazy kernel M = (1−d)I + dP and continuation/retention 0 ≤ ρ < 1,
`lazy_ppr_eq_ppr` identifies its equilibrium with plain P at continuation
c = ρd/(1−ρ+ρd). `sti_unroll` expands arbitrary effective inputs as discounted
transported impulses. `sti_steady_state` bounds error to ppr(u)/(1−ρ) by ρ^t
for constant effective input u. If stimulus enters before spread and decay,
the effective input is ρM times that raw stimulus (`stimulate_spread_decay`).
Stimulus added afterwards is already the effective input. Consolidation does
not change STI; reserve accounting remains a separate theorem.

For half-life h > 0 equal cycles, ρ = 2^(−1/h). The effective geometric mean
hops c/(1−c) equals ρd/(1−ρ), approximately 1.44·d·h for sufficiently large h.
This describes the fixed schedule, not a universal law of every ECAN caller.
Disabled decay (ρ = 1) is outside this equilibrium theorem, not forbidden.

## Observable stopping

For x' = step(s,x), the remaining fixed-point error is at most
(1−α)/α · l1(x'−x). If every selected item beats every unselected item in x'
by more than twice that bound, `certified_topk` certifies the exact fixed
point's selection. The theorem has no fixed round limit. Strict-gap
certification need not terminate at an exact tie, and it does not establish
that the fixed point ranks useful evidence. All statements assume a fixed
walk and stimulus while the computation runs.

`PremiseActivation` is a different view: cumulative graph discovery followed
by ranking. Its depth determines the discovered pool; it is not simply a
precision setting. `ranking_cannot_recover_missing` records why ranking
cannot recover a needed premise missing from that pool. These are discovery
sets, not permissions to inspect sources.

## Clusters, useful hits and concepts

For a unit nonnegative seed supported in S, suppose every member j sends at
most ℓ of its transition mass outside S. Then `outside_mass_le_leakage` gives
outside PPR mass at most (1−α)ℓ/(α+(1−α)ℓ). At α = 1/2 and ℓ = 1/20 this is
1/21 (about 4.8%). This is a pointwise leakage assumption, stronger than an
average conductance claim. It does not discover a relevant cluster.

`ppr_ge_depth` retains each depth-t contribution with factor α(1−α)^t.
Increasing α reduces the leakage bound while changing deep-path activation;
there is no theorem that one α is optimal for all tasks or cluster radii.
`concept_shortcut` lower-bounds a supplied i→C→j path by α(1−α)^2βw.
Uniformly linking C to m members gives w = 1/m: larger fans dilute this
contribution. The lemma compares paths in the supplied graph, not retrieval
before and after learning a concept. It does not prove concept quality.

If q(i) is the probability of needing i, sum over a selected set is expected
useful hits (independence is unnecessary). For positive scale c, `spreading_regret`
bounds loss against every k-item comparator by
δ + 2c(1−α)^r, with δ = l1(q−c·ppr(s)). The scale matters because a turn may
need multiple items while the seed has unit mass. If q = c·ppr(s), the exact
ranking is optimal (`walk_generated_needs_optimal`). Otherwise calibration
is an explicit world assumption, not a consequence of high attention.

Recorded usage supplies labels, not automatically the probability of need:
missed evidence and selection bias matter when estimating δ. Displaying or
ignoring a memory is not by itself positive or negative evidence of usefulness.
When the iteration term falls below δ, the bound becomes calibration-dominated;
it does not prove zero subsequent benefit or concavity of useful hits.

`SpreadingExamples` contains exact finite counterexamples: another round can
replace needed B by a hub even at convergence, and useful discovery can be
0,0,0,2 by depth before a bridge pays off. The latter uses five nodes; the
otherwise equivalent three-leaf variant requires six. Conservation also does
not prevent duplicate-edge routing bias; source identities remain essential.

## The belief-side connection

`Logic.MarkovLogicLocalQueryApproximation.shell_query_error` packages the
existing restricted-DLR theorem: under a uniform 0 ≤ C < 1 influence bound,
a query on Γ answered on its n-shell under any boundary differs from any full
DLR answer by at most 2|Γ|C^n. Attention's tail (1−α)^(k+1) and this reasoning
tail share geometric contraction. The agent chooses α; C belongs to the
knowledge model. Near C = 1 the certificate decays slowly; this does not prove
that every local query is difficult. Dobrushin contraction is sufficient,
not necessary, and the result is not loopy BP convergence.

`PLN.Bridges.CogArch.AttentionEvidence.spreading_revision_commute` keeps
attention selection separate from world-model revision. The theorem fixes
the supplied kernel; it does not validate a stale search after graph revision.
Attention selects where to reason and does not itself change what evidence
warrants. Runtime context integration is not claimed here.

## Related work, not formalized here

- [Andersen–Chung–Lang (2006), Local Graph Partitioning using PageRank Vectors](https://www.cs.cmu.edu/~15859n/RelatedWork/local_partitioning_full.pdf): conductance-based local partitioning.
- [Zhu–Lattanzi–Mirrokni (2013)](https://arxiv.org/abs/1304.8132): internal-connectivity and conductance refinements.
- [Kloumann–Ugander–Kleinberg (2017)](https://arxiv.org/abs/1607.03483): block-model justification of ranking weights.
- [Li–Chien–Milenkovic (2019)](https://arxiv.org/abs/1905.10881): generalized PageRank depth weights.
- [HippoRAG 2](https://arxiv.org/abs/2502.14802): empirical motivation only.

`Audit` prints theorem dependencies separately from production imports.
