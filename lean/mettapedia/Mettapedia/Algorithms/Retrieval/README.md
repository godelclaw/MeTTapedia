# Retrieval and selector contracts

`SelectorContract` separates candidate selection guarantees from exact answers.
`RetrievalContract` specifies authoritative records, candidate soundness, exact
refinement and score fusion. `NativeTensorRetrieval` covers versioned base/delta
indexes and incremental exact retrieval.

These are algorithmic contracts, independent of a memory system or embedding
backend. Working-memory behavior and source-linked summaries live in
`CogArch/Memory`; premise-selection scoring results live in
`PLN/InferenceControl/PremiseSelection`.
