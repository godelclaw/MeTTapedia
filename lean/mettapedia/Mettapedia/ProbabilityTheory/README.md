# Probability Theory (Lean 4)

## The idea

Probability is the mathematics of *reasoning under uncertainty* — and a recurring
discovery is that you do not have to *postulate* the rules of probability; you can
**derive** them from much weaker, more obviously-reasonable assumptions about how a
rational agent should weigh evidence. That derivational spirit is what unifies this
directory.

A few threads, each with a one-line "why":

- **Where do the sum and product rules come from?** Cox's functional-equation
  development constructs a multiplicative regraduation on `(0,1]` under explicit
  range, order, associativity and continuity hypotheses. Knuth–Skilling's ordered
  semigroup route uses its stated separation hypotheses. An event probability
  calculus additionally needs the event structure and compatible complement law.
  Neither associativity alone nor a taxonomy label supplies all of this.
- **What if you can't commit to a single probability?** Real agents often only know
  that a probability lies *between* bounds. *Imprecise probability* and *belief
  functions* (Dempster–Shafer) formalize reasoning with whole *sets* of allowed
  distributions (credal sets) instead of one.
- **How do you reason about many interacting variables?** *Bayesian networks*
  encode conditional independence as a graph, so you can read off "X tells you
  nothing new about Z once you know Y" (*d-separation*) and compute efficiently.
- **What about probabilities over probabilities, or non-commutative randomness?**
  *Higher-order probability* treats the probability itself as uncertain; *free* and
  *quantum* probability replace ordinary (commuting) random variables with
  operator-algebra analogues.
- **How does all of this connect to the standard measure-theoretic foundation, and
  to category theory?** The *measure bridge* and *Markov-category / optimal-transport*
  views tie the elementary derivations back to Mathlib's measure theory and to the
  categorical (`Kleisli`-of-a-monad) picture of probabilistic maps.

Lean makes the assumptions and representation maps part of each checked statement.

## Topics

| Area | Where | What it formalizes |
|------|-------|--------------------|
| Cox foundations | `ProbabilityTheory.Cox` (standalone), local `Cox/Regraduation.lean` and `Cox/DiscontinuousCounterexample.lean` | canonical product derivation; positive-power uniqueness and interior calibration; controls separating algebraic rules from valid Cox operations |
| Knuth–Skilling foundations | standalone `KnuthSkilling.*`, local `Common/OrderedCombination.lean` and `Hypercube/KnuthSkilling/` | canonical representation hypotheses, calibration, sequential actions and interval observations |
| Probability "hypercube" | `Hypercube/` (23) | the axis space of inference: commutativity, distributivity, precision, ordering, additivity — **has its own [README](Hypercube/README.md)** |
| Bayesian networks | `BayesianNetworks/` (30) | local Markov property, d-separation, inference |
| Imprecise probability / belief functions | `ImpreciseProbability/` (7), `BeliefFunctions/` (1), `ImpreciseProbability.lean`, `BeliefFunctions.lean` | credal sets, Dempster–Shafer belief functions |
| Higher-order probability | `HigherOrderProbability/` (6) | probabilities over probabilities — **has its own [README](HigherOrderProbability/README.md)** |
| Free / quantum probability | `FreeProbability/` (2), `QuantumProbability/` (1), `QuantumProbability.lean` | non-commutative probability |
| Optimal transport / Markov category | `OptimalTransport/` (1), `MarkovCategory/` (1) | transport and categorical views of probabilistic maps |
| Distributions & structures | `Distributions/` (2), `Structures/` (1), `Common/` (6), `Foundations/` (1) | shared building blocks (e.g. valuations, common foundations) |
| Bridges & unification | `MeasureBridge.lean`, `Unified.lean`, `UnifiedProbabilityBridge.lean`, `CommonFoundations.lean`, `AssociativityTheorem.lean`, `FiniteMeasureSupport.lean`, `Basic.lean` | ties the strands to Mathlib measure theory and to one another |

The canonical proof implementation is the standalone foundations package
(`lean/standalone/ks-foundations-of-inference`), using `KnuthSkilling.*` and
`ProbabilityTheory.Cox.*`. Local Cox entrypoints import it without redeclaring
its structures. The hypercube modules are interpretation and example layers.

`Common/OrderedCombination.lean` distinguishes the generated iterate range from
a representation of the whole carrier. Its right-regular action retains
sequential order; additive readouts and interval envelopes are separate
observations. Nonempty families with a shared positive anchor have point
envelopes. Completeness alone does not fix a scale or force shrinking bounds.

## Checking

Build the relevant targets from the Lean package root:

```bash
lake build Mettapedia.ProbabilityTheory.Cox Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling
lake build Mettapedia.ProbabilityTheoryClean
```

These checks qualify their declared import graphs; they are not a status claim
for unrelated probability developments. Theorem statements distinguish supplied
structures, derived laws, and counterexamples.

## References

- Richard T. Cox, [*Probability, Frequency and Reasonable Expectation*](https://doi.org/10.1119/1.1990764), American Journal of Physics 14(1):1–13 (1946) — the consistency-axiom derivation of the sum/product rules.
- Kevin H. Knuth & John Skilling, [*Foundations of Inference*](https://doi.org/10.3390/axioms1010038), Axioms 1(1):38–73 (2012) — inference as the unique consistent valuation on an ordered lattice (the flagship `Hypercube/KnuthSkilling/` lane).
- E. T. Jaynes, [*Probability Theory: The Logic of Science*](https://doi.org/10.1017/CBO9780511790423) (Cambridge University Press, 2003) — the Cox/Bayesian programme.
- Glenn Shafer, [*A Mathematical Theory of Evidence*](https://press.princeton.edu/books/paperback/9780691100425/a-mathematical-theory-of-evidence) (Princeton University Press, 1976) — Dempster–Shafer belief functions.
- Bruno de Finetti, "La prévision: ses lois logiques, ses sources subjectives," *Annales de l'Institut Henri Poincaré* 7 (1937); modern treatment in Olav Kallenberg, [*Probabilistic Symmetries and Invariance Principles*](https://doi.org/10.1007/0-387-28861-9) (Springer, 2005).
- Tobias Fritz, [*A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics*](https://doi.org/10.1016/j.aim.2020.107239), Advances in Mathematics 370 (2020) — the Markov-category view.

## See also

- [`Hypercube/README.md`](Hypercube/README.md) — the inference hypercube and the
  Knuth–Skilling foundations (flagship).
- [`HigherOrderProbability/README.md`](HigherOrderProbability/README.md) —
  probabilities over probabilities.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 74 .lean files, 1 with sorries.*
- `FreeProbability/Basic.lean` — 1 sorry
