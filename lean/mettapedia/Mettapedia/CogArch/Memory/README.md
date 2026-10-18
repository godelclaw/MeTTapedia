# Memory state and views

These models cover working-memory attention, event-sourced revision,
bitemporal claims, source-linked hierarchical summaries, and explicit memory
refinement and retirement. Their identities and freshness conditions describe
the represented state, independently of any particular agent runtime.

`Indexing` separates acknowledged intent, indexed content and retrieval coverage.
It proves delivery after a successful retry prefix and shows why liveness and
coverage need additional assumptions. `SourceObservations` separates
delivery IDs, source support and distinct interpretations. `PinSupersession`
exhibits unbounded append-only growth and proves that replacing a current topic
does not increase the current topic count. Unavailable reads supply no update
base. These are abstract contracts, not proofs of runtime refinement or relevance.

Revision-bound goal assessment and continuation belong in
`CogArch/Agent/GoalContinuity`; they reuse the task-phase and required-context
interfaces rather than treating a completed task as a satisfied goal.

Generic selector, tensor-index and exact-refinement contracts live in
`Algorithms/Retrieval`. Evidence aggregation and derived-belief support live in
`PLN/Bridges/CogArch`. Personalized PageRank lives in
`ProbabilityTheory/MarkovChain/Restart`.
