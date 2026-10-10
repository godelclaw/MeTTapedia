# Agent memory: essential mechanisms in Lean

These Lean 4 models extract five mechanisms from published agent-memory
systems and state what a long-lived companion agent needs from each. Every
mechanism pairs safety laws with liveness, termination or quantitative bounds.
The models assume a MeTTa named space as the authoritative store. Vector,
keyword and graph indexes are derived from it and are never the source of truth.

The files import Mathlib only and are self-contained. They contain no `sorry`
and declare no axioms. Their theorems depend on at most `propext`,
`Classical.choice` and `Quot.sound`.

## Sources

| System | Paper | Core mechanism used here |
| --- | --- | --- |
| HippoRAG | arXiv 2405.14831 (NeurIPS 2024) | OpenIE triples form a knowledge graph with synonym edges (cosine ≥ 0.8). Query entities seed Personalized PageRank (damping 0.5), weighted by node specificity (the inverse of the number of passages containing the node). Passages are ranked by count-weighted node scores. |
| HippoRAG 2 | arXiv 2502.14802 | Passage nodes and `contains` edges join the graph. The query is matched to triples, and an LLM filters them. PPR seeds phrase nodes by triple scores and all passage nodes by dense similarity, with weight 0.05. |
| GraphRAG | arXiv 2404.16130 | An LLM extracts entities, relations and claims from 600-token chunks. Hierarchical Leiden communities (levels C0–C3) get bottom-up LLM summaries. Global questions run map-reduce over community summaries. |
| Zep / Graphiti | arXiv 2501.13956 | Three tiers: episodes (non-lossy raw input), entities with fact edges, and communities. Each fact has valid/invalid times on the event timeline and created/expired times on the ingestion timeline. A contradicting fact closes an older one at its own start. Retrieval combines cosine, BM25 and BFS search, reranking (RRF, MMR, graph distance) and a context builder. |
| Mem0, Mem0ᵍ | arXiv 2504.19413 | An LLM extracts candidate facts. For each, it retrieves the 10 most similar memories and chooses ADD, UPDATE, DELETE or NOOP. DELETE removes the memory. The graph variant marks conflicting relations invalid instead of removing them. |
| A-MEM | arXiv 2502.12110 | Zettelkasten notes (content, time, keywords, tags, context, embedding, links). An LLM links each new note to its top-k neighbours (k = 10) and rewrites their keywords, tags and context. |

Reciprocal rank fusion follows Cormack, Clarke and Büttcher (SIGIR 2009).

## Ranking for long-lived companion agents

The needs are consistency over years, changing facts, contradiction handling,
provenance, multi-hop associative recall, consolidation and bounded cost.

1. **Bitemporal claims with derived invalidation (Zep/Graphiti, Mem0ᵍ).**
   Facts about a person change, and the agent must know what was true when and
   what it believed when. No other mechanism addresses changing facts and
   contradictions without destroying history. Formalized in
   `BitemporalClaims.lean`.
2. **Event-sourced memory commands with a draining queue (Mem0's update phase).**
   This is the write path every other mechanism depends on. It must be
   replayable, auditable and retry-safe, and every candidate must reach a
   decision. Formalized in `EventSourcedMemory.lean`.
3. **Personalized PageRank recall (HippoRAG 1 and 2).** It gives multi-hop
   associative recall in one retrieval step, with no iterative LLM calls. Its
   cost is a fixed number of sparse matrix-vector products with a provable
   error. Formalized in `PersonalizedPageRank.lean`.
4. **One retrieval contract (Zep's search and rerank; dense top-k in all
   five).** It makes "index, not truth" precise: what an index must guarantee,
   how a lagging index stays correct, when reranking is exact, and what
   fusion preserves. Formalized in `RetrievalContract.lean`.
5. **Hierarchical summaries (GraphRAG communities, Zep communities, Mem0's
   rolling summary).** They help with global questions. They are lossy derived
   caches and must carry exact provenance; they are useful later, not first.
   Their exact part is formalized in `HierarchicalSummary.lean`.
6. **Note links with annotation evolution (A-MEM).** Links between memories are
   useful as provenance-carrying assertions. Rewriting other notes' annotations
   in place is not.

### What not to adopt

- **Destructive DELETE and overwriting UPDATE (Mem0).** They erase the history
  needed to audit or undo a wrong LLM judgement. Use tombstones and versions.
- **In-place invalidation stamps as the truth (Graphiti).** Overwriting
  `t_invalid` loses either the history before a change or the view held earlier
  (`inplace_stamps_lose_history`). It also cannot undo a cut when the cutting
  fact is withdrawn (`retraction_restores`). Equal start times leave two values
  valid at once. Stamps may be cached, but only as values derived from the log.
- **GraphRAG's whole-corpus indexing.** Leiden over the full graph plus an LLM
  summary for every community, rebuilt when the corpus changes, does not fit a
  memory that grows every day. A global answer also costs one LLM call per
  community chunk.
- **A-MEM's unversioned memory evolution.** An LLM rewriting neighbours'
  keywords, tags and context on every insertion compounds drift, with no
  provenance or rollback.
- **LLM judgements and thresholds as irreversible facts.** Contradiction
  verdicts, entity merges and synonym edges (cosine ≥ 0.8) should be recorded
  as retractable assertions with their source.
- **Similarity or PPR mass as belief strength.** Retrieval scores rank
  candidates. They are not PLN truth values and do not count as independent
  evidence.

### Where the models depart from the sources

- Mem0's DELETE removes the memory (`M ← M ∖ {mᵢ}` in its Algorithm 1).
  Tombstones, revisions and idempotency keys are additions here. Only Mem0ᵍ
  keeps invalid relations.
- Zep's paper describes one direction of invalidation. Graphiti's code also
  closes a newly learned fact about earlier events at the start of a later known
  one, and it overwrites `invalid_at` and `expired_at` in place.
- Invalidation is monotone only without retractions (`invalidation_monotone`).
  With retractions it is not, by design (`retraction_restores`).
- Graphiti does not bound invalidation work by key. It searches semantically
  similar edges and asks an LLM. With structural slots the bound is sharper: an
  operation changes the derived interval of at most one other claim.

## Files and theorems

Tags: **S** safety, **L** liveness or progress, **Q** quantitative bound.

### `BitemporalClaims.lean` (`AgentMemory.Bitemporal`)

A slot (for example a person's home city) receives `Claim`s: value, event-time
start, optional declared stop, and source episode. The log holds `assert` and
`retract` entries, and each entry's position is its knowledge time. Nothing is
mutated. At knowledge time `τ`, a live claim determines its slot at event time
`t` when it has started, has not reached its stop, and no live claim of higher
priority (later start, then later knowledge) has started (`Covers`, `Holds`,
`Believes`).

- `history_never_lost`, `entry_stable` (S): operations only append, and recorded
  entries never change.
- `asOf_stable`, `believes_stable` (S): later operations never change the view
  at an earlier knowledge time. Past beliefs can be reconstructed exactly.
- `covers_unique`, `believes_functional` (S): a slot has at most one value per
  (event time, knowledge time).
- `holds_provenance` (S): every belief comes from a logged, unretracted claim
  with its source episode.
- `covers_iff_latest`, `covers_or_unknown` (S): the view equals "latest started
  claim wins unless it has stopped", and it is always decided. A stopped claim
  leaves the value unknown and does not revive an earlier one.
- `assert_visible`, `holds_after_assert_iff` (L): a new claim takes effect
  immediately, on exactly its derived interval. Out-of-order recollections are
  closed by facts already known about later events.
- `loss_has_cause` (L): a claim stops determining its slot only through a logged
  retraction or a logged claim of higher priority.
- `retract_permanent`, `retracted_never_holds_again` (L): a retraction takes
  effect at once and permanently, whatever is appended later.
- `assert_preserves_other_slots` (Q): an assertion never changes another slot's
  view.
- `assert_cuts_at_most_one`, `retract_restores_at_most_one`, `cut_at_most_one`
  (Q): each operation changes the derived interval of at most one other claim.
  A cache of interval ends needs at most two updates per assertion.
- `invalidation_monotone` (S): without retractions, knowledge only shortens
  derived intervals. `retraction_restores` is the counterexample once
  retractions are allowed.
- `covers_iff_of_distinct_starts` (S): with distinct starts, the timeline does
  not depend on the order in which claims were learned.
- `inplace_stamps_lose_history`: a Graphiti-style in-place store loses either
  the history before a move or the past view.

### `EventSourcedMemory.lean` (`AgentMemory.EventLog`)

Commands `add`, `update`, `delete` and `noop`, each carried by an `Op` with an
idempotency key. A `Store` holds per-record version histories (newest first;
content `none` is a tombstone) and the set of decided operation identities.
`replay` folds `apply` over the log. A `Pipeline` holds candidate facts with
deferral budgets; `step` asks an arbitrary oracle (the LLM) to commit a command
or defer.

- `replay_append` (S, Q): replay equals snapshot plus tail. Recovery costs one
  step per operation after the snapshot.
- `apply_noop_history`, `apply_delete`, `apply_update`, `apply_add`,
  `apply_inactive` (S): command effects. A deletion appends a tombstone and the
  old content stays in history. An update keeps the identifier and advances the
  revision by one.
- `add_never_reuses` (S): a used identifier, even a deleted one, cannot be added
  again.
- `apply_history_suffix`, `replay_history_suffix` (S): history is never lost.
- `execH_comm`, `apply_comm` (S): operations on distinct records commute.
- `apply_idempotent`, `replay_eq_replay_firstDeliveries`, `replay_retry` (S):
  arbitrary retried deliveries replay to the same store as the first
  deliveries. This is exactly-once under at-least-once delivery.
- `apply_history_of_ne`, `total_revisions_le` (Q): an operation writes at most
  one version, to its own record. Total history grows by at most one version
  per operation.
- `drains` (L): for every oracle, including one that always defers, the queue
  is empty after `work` steps (sum of budget + 1 per candidate).
- `resolved_perm`, `nextOp_after_drain` (S, Q): every candidate is resolved
  exactly once and consumes exactly one operation identity.
- `commit_takes_effect`, `fresh_step` (L): with fresh operation identities, a
  committed decision is never discarded as a retry.
- `unbudgeted_never_drains`: without a deferral budget, an always-deferring
  oracle keeps a nonempty queue nonempty forever.

### `PersonalizedPageRank.lean` (`AgentMemory.PPR`)

A `RestartWalk` has a nonnegative, column-substochastic matrix `P`, where
`P i j` is the probability of a step from `j` to `i`, and a restart probability
`α ∈ (0, 1]`. One `step` maps `x` to `α s + (1 - α) P x`. `ppr s` is defined
through the inverse of the resolvent `x ↦ x - (1 - α) P x`.

- `step_contract`, `iterate_contract` (Q): one step contracts ℓ¹ distance by
  `1 - α`.
- `ppr_fixed`, `ppr_unique` (S): the PPR vector is the unique fixed point.
- `ppr_add`, `ppr_smul`, `ppr_sub` (S): it is linear in the seed.
- `iterate_error` (L, Q): power iteration converges, with ℓ¹ error at most
  `(1 - α)^k` times the initial error.
- `iterate_error_dist` (Q): with distributions, the error is at most
  `2 (1 - α)^k`. At `α = 0.5`, ten iterations give an error below 0.002.
- `ppr_nonneg`, `ppr_mono`, `passage_scores_mono` (S): nonnegative seeds give
  nonnegative scores, scores are monotone in the seed, and HippoRAG's
  count-weighted passage scores inherit monotonicity.
- `ppr_mass`, `ppr_mass_le` (S): a stochastic walk conserves the seed's mass; a
  substochastic one does not increase it.
- `ppr_unroll`, `mass_outside_reach` (Q): the mass outside the `k`-step reach of
  the seed is at most `(1 - α)^(k+1)` times the seed's mass.

### `RetrievalContract.lean` (`AgentMemory.Retrieval`)

An index is `Sound` for an exact relation when it returns every true answer.
`refine` re-checks candidates against the current store. `IsTopK` specifies
top-k selection with any tie-breaking. `rrf` is reciprocal rank fusion with
constant `c`.

- `refine_correct` (S): refinement never reports a false answer or a record
  missing from the store, whatever the index returns.
- `refine_exact`, `sound_iff_refine_exact` (S, L): refinement returns exactly
  the true answers, and every true answer is found, if and only if the index is
  sound.
- `sound_of_abstraction`, `lower_bound_range_sound` (S): an index over an
  abstraction or projection is sound when it never rejects a true answer. A
  projected distance that never exceeds the true distance is one such case.
- `sound_inter`, `sound_union`, `sound_mono` (S): soundness composes over
  metadata filters.
- `lagging_sound` (S): an index built at an older revision, plus a scan of the
  records written since, stays sound. Deletions need no index update.
- `refine_card_le`, `refine_lagging_card_le` (Q): the exact check runs at most
  once per candidate, with at most `|candidates| + |delta|` checks.
- `exists_topK`, `rerank_exact` (S): if the candidates contain some true top-k,
  every top-k of the candidates is a true top-k.
- `rerank_exact_of_bound` (S): the same holds when every non-candidate is
  certified to score no higher, for example by an upper bound.
- `rrf_perm`, `rrf_unanimous`, `rrfTerm_anti` (S): fusion ignores the order of
  its input rankings and respects unanimous preferences.
- `rrf_pos_iff`, `rrf_ge_of_rank`, `rrf_le` (S, Q): fusion gives positive score
  exactly to items that some ranking returned, at least `1/(c + m)` for rank
  `m` in any one ranking, and at most `|rankings|/(c + 1)`.

### `HierarchicalSummary.lean` (`AgentMemory.Summary`)

A `children` function splits each community into sub-communities. `hsum` and
`hsup` aggregate bottom-up through `n` levels.

- `hsum_eq_flat` (S): additive aggregates (counts, sums, evidence totals) through
  any number of levels of disjoint sub-communities equal the aggregate over the
  members.
- `hsup_eq_flat`, `provenance_exact` (S): idempotent aggregates (supporting
  episodes, latest update time) are exact through any covering hierarchy, even
  with overlapping communities. Provenance stays exact while summary text is
  lossy.
- `mean_of_means_ne_mean`: averaging sub-community averages is wrong. Cache the
  sum and the count instead.
- `sum_update_of_not_mem`, `card_containing_le_one`, `update_cost_le_levels`
  (Q): an update changes only the summaries of communities containing the
  member, at most one per level.
- `stale_iff` (S): a cached summary is stale exactly when a member changed after
  its recorded latest time.

## Realization in CeTTa

The named space stays authoritative, and every structure below is derived from
its atoms. Atom shapes are proposals.

### Bitemporal claims

```metta
(Claim $kt (Slot $subject $attribute) $value $start $stop (Episode $source))
(Retract $kt $target-kt)
(Episode $source $time $raw)             ; non-lossy input, as in Zep
```

`$kt` is a strictly increasing knowledge time (the claim's log position or the
space revision at commit), and `$stop` is `Open` or `(Until $t)`. Claims and
retractions are only added, never removed or patched.

- MeTTa view: `(claims:holds $slot $t $tau)` matches the slot's claims with
  `$kt ≤ $tau` and no `(Retract $k $kt)` with `$kt < $k ≤ $tau`. It takes the
  maximum by `($start, $kt)` among claims started by `$t`, then checks `$stop`.
  This is `covers_iff_latest`. Matching on the slot is the per-key index, so a
  view or write touches only one slot (`assert_preserves_other_slots`).
- An optional cache `(ClaimEnd $kt $end)` of derived interval ends needs at most
  the new claim and its predecessor updated per assertion, and one entry per
  retraction (`assert_cuts_at_most_one`, `retract_restores_at_most_one`). The
  cache is disposable and can be rebuilt from the claims.
- Policy: an LLM turns episodes into claims and assigns slots. Assigning a slot
  replaces Graphiti's per-edge contradiction prompt. Policy decides between a
  change (a new claim with a later start) and a correction (a retraction plus a
  new claim). Temporary states (a trip) get their own slot, because a stopped
  claim leaves its slot unknown.
- PLN: a claim's value may carry `(stv s c)`. The temporal rule decides which
  claim governs an event time. Merging evidence for the same claim is a separate
  PLN revision step.
- No tensor kernels are needed. This is symbolic matching.

### Event-sourced memory commands

```metta
(MemoryOp $op-id $cmd)                    ; (Add $id $content) (Update $id $content) (Delete $id) Noop
(MemoryVersion $id $revision $op-id $content)   ; $content = Tombstone after Delete
(Decided $op-id)
(Pending $candidate $budget)
```

- The current `memory:dispatch` removes the old `Memory` atom on upsert, patch
  and delete, following Chroma's semantics. The proposed change keeps versions
  and computes the active view as the newest version (`apply_delete`,
  `apply_update`). `revision` here counts a record's versions. The store-wide
  revision of `MemoryCollection.lean` still guards concurrent commits.
- The adapter already sends a request identifier with each batch, but the
  service's receipt cache is bounded. Exactly-once beyond that window needs
  `(Decided $op-id)` atoms in the space (`replay_eq_replay_firstDeliveries`).
- The consolidation loop takes one `Pending` atom per step. It retrieves the
  most similar memories (Mem0 uses 10) and lets the LLM commit a command or
  defer. A deferral decrements the budget, and budget 0 records an expiring
  `Noop`. `drains` bounds the loop by the sum of budgets plus one per
  candidate, whatever the model answers.
- Kernels: the similar-memory lookup uses the existing `tensor:cosine-rows`
  and `retain-top-k-keyed-atom`.

### Personalized PageRank recall

```metta
(Node $id $kind)                          ; Entity | Claim | Memory | Episode
(Edge $from $to $weight $kind)            ; Mentions | Relation | Synonym | Link
```

The graph is derived from claims, memories and episodes. Entities connect to the
claims and memories that mention them, as with HippoRAG 2's `contains` edges.
Synonym and A-MEM-style links are retractable assertions with sources.

- Kernels to add to `lib_tensor`:
  - `tensor:csr` builds a CSR matrix (row pointers, column indices, f64
    weights) from edge rows and normalizes columns to sum to 1. Dangling
    columns can send their mass back to the seed, which keeps `P` stochastic
    and makes `ppr_mass` apply.
  - `tensor:spmv` is CSR times a dense f64 vector. It is the only
    per-iteration kernel.
  - `tensor:axpy` computes `α s + (1 - α) y`. It can be composed from
    `tensor:add` and `tensor:mul` with a full scalar tensor.
  - `tensor:l1-diff` reports the convergence error.
  - `tensor:top-k-masked` ranks only memory or passage nodes.
- Iteration budget: run a fixed `K` instead of looping until convergence.
  `iterate_error_dist` gives error at most `2 (1 - α)^K`. At `α = 0.5`, `K = 10`
  gives at most 0.002 and `K = 20` at most 2·10⁻⁶. For large graphs, expanding a
  `k`-hop frontier first loses at most `(1 - α)^(k+1)` of the mass
  (`mass_outside_reach`).
- Policy: build the seed from query entities matched by embedding, with
  HippoRAG's specificity weight `1/(number of memories mentioning the node)`.
  ECAN short-term importance can scale the seed. Monotonicity (`ppr_mono`)
  guarantees that raising a node's attention never lowers any score. Fuse PPR
  ranks with dense ranks by RRF. PPR mass is relevance, never a PLN strength.

### One retrieval contract

- Truth is the space. The packed index (`Packed rows matrix norms` in
  `lib_memory_collection`) is built from one snapshot revision. Today every
  applied write resets it to `Missing`, so each write forces a full rebuild.
  `lagging_sound` permits an incremental alternative: keep the packed index,
  scan the records written since its revision as a small delta, and refine
  against the current records. Deletions then need no index work, and a
  rebuild only bounds the delta (`refine_lagging_card_le`).
- Exact refinement is the existing `memory:filter` over `Eq`/`And`/`Or`
  metadata, re-run on candidates (`refine_exact`, `sound_inter`,
  `sound_union`).
- Kernels: `tensor:cosine-rows` and `retain-top-k-keyed-atom` exist. Exact
  pruning needs a certificate kernel, for example per-block maximum row norms
  with the Cauchy–Schwarz bound `q·x ≤ |q| |x|`, or u8-quantized vectors with a
  proven error bound (`rerank_exact_of_bound`, `lower_bound_range_sound`).
- Fusion is MeTTa policy: rankings from cosine, keyword match, PPR and graph
  BFS fuse by `rrf` with `c = 60`. The `rrf_*` laws state what fusion
  preserves.

### Hierarchical summaries

```metta
(Community $id $level $parent)
(Member $community $node)
(Summary $community $text (Stats $count $sum $latest $sources) $built-at)
```

- The text comes from an LLM and is lossy. `Stats` holds aggregates that are
  exact at every level (`hsum_eq_flat`, `hsup_eq_flat`): counts and evidence
  sums, the latest member update and the set of supporting episodes. A summary
  cites `$sources` exactly (`provenance_exact`).
- Freshness is one comparison: rebuild when the members' latest update exceeds
  `$built-at` (`stale_iff`). A member update marks at most one community per
  level (`update_cost_le_levels`), so refresh work is bounded by the depth.
- Communities can be maintained incrementally, as in Zep: a new node joins the
  community held by most of its neighbours, with periodic full refreshes.
  GraphRAG's whole-corpus Leiden rebuild is the expensive alternative.
- No tensor kernels are needed beyond the existing ones.

## Limits and open questions

- The PPR model works over real numbers. f64 rounding, summation order and
  dangling-node handling need their own error bounds or tests.
- Slot assignment is an LLM judgement. The theorems assume it is given; a wrong
  slot is repaired by retraction, not prevented.
- When should conflicting claims supersede each other in time, and when should
  they merge as PLN evidence? The models cover supersession only.
- A-MEM link evolution is ranked but not modeled. For hierarchical summaries
  only the exact aggregates are modeled; the adequacy of LLM-written text is
  not.
- These are model laws. Runtime correspondence needs finite replays and
  deliberately broken implementations, checked against the deployed code.

## Checking

From `lean/mettapedia`, with the pinned Mathlib build available:

```sh
lake env lean ../pettaclaw/AgentMemory/BitemporalClaims.lean
lake env lean ../pettaclaw/AgentMemory/EventSourcedMemory.lean
lake env lean ../pettaclaw/AgentMemory/PersonalizedPageRank.lean
lake env lean ../pettaclaw/AgentMemory/RetrievalContract.lean
lake env lean ../pettaclaw/AgentMemory/HierarchicalSummary.lean
```
