# Coloring curriculum: maintained theory and historical WIP

The maintained mathematical library is
[`../FourColor/Curriculum/Actual.lean`](../FourColor/Curriculum/Actual.lean)
and its imported modules. It contains graph and coloring basics, clique
obstructions, degree and edge bounds, minimal-counterexample normal forms,
support and isomorphism transport, and explicit small-graph classification
and sharpness theorems. These results do not assume planarity or prove the
Four-Color Theorem.

`FourColor` retains the complete `Actual` import surface. The enclosing
MeTTapedia target `FourColorCore` builds that root together with
`FourColor.IntegrationCore`; the latter adds compositional algebra and the
naive run-completion counterexample. Current validation and proof-dependency
results are recorded under `mettapedia/artifacts/integration-20261028`.

The following older teaching sheets are research WIP and are excluded from
those roots:

* `FourColor/Curriculum/F2Parity.lean` contains parity examples and unfinished
  exercises.
* `FourColor/Curriculum/PathXOR.lean` contains path-sum examples and unfinished
  exercises.
* `FourColor/Curriculum/LineGraph.lean` contains elementary adjacency examples;
  its historical application notes are not evidence that another proof's
  obligations have been discharged.

Their original source locations and content are retained for provenance.
The earlier exercise roadmap and blocker counts are historical, not a
completion contract for the maintained library. Useful lemmas may be
extracted into subject modules after checking their exact assumptions and
existing Mathlib equivalents; unfinished exercises do not become premises
of maintained theorems.
