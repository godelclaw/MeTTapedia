# Retrieval and selector contracts

`SelectorContract` separates candidate selection guarantees from exact answers.
`RetrievalContract` specifies authoritative records, candidate soundness, exact
refinement and score fusion. `NativeTensorRetrieval` covers versioned base/delta
indexes and incremental exact retrieval.

These are algorithmic contracts, independent of a memory system or embedding
backend. Working-memory behavior and source-linked summaries live in
`CognitiveArchitecture/Memory`; premise-selection scoring results live in
`PLN/InferenceControl/PremiseSelection`.

`TopKSelection` reuses the existing top-k contract with exact cardinality. It
bounds utility regret by score error on exchanged items, by l1 error, and by
`2k` times uniform error. Positive rescaling preserves selection. Interpreting
utility as probability of need makes its sum expected useful hits; the algebra
does not establish that calibration.

`certified_topk` uses the last-round restart residual and a strict score gap
to certify the exact fixed point's selection. No fixed round limit is needed;
termination at ties and usefulness of the fixed point are not asserted.
`Audit` checks dependencies separately from production imports.
