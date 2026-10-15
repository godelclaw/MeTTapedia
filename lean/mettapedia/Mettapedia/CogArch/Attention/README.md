# Attention dynamics

Attention measures operational relevance. It is distinct from factual evidence,
confidence, proof validity and computational cost.

- `ThreeTimescale` specifies real-valued short-, medium- and long-term importance,
  reserve accounting, elapsed-time decay and adjacent consolidation.
- `Spreading` applies conservative finite transport to the short-term horizon.
- `PremiseActivation` describes broad, caller-selected finite-round discovery
  followed by a separate ranking view. More rounds expand the discovered pool;
  no theorem asserts that ranking or answer quality necessarily improves.
- `Audit` checks kernel dependencies separately from production imports.

The generic kernels, restarting walks and convergence results live in
`ProbabilityTheory/MarkovChain`. Stamped association evidence, world-model
extraction and ranking margins meet attention in `PLN/Bridges/CogArch`.

For an agent consumer, begin with direct retrieval seeds, expand all supplied
neighbours for the chosen number of rounds, then rank the combined pool.
Keep the source identity with every result. The caller owns the round count,
spread fraction and score mixture; zero spread disables redistribution.

Conservation does not prevent duplicate-edge routing bias. Observations need
stable source identities. Displaying or ignoring a memory is not, by itself,
positive or negative evidence of usefulness. These exact-real specifications
do not certify native floating-point behavior or empirical retrieval quality.
