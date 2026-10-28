# Higher-order probability

A `ParametrizedDistribution Θ X` retains a Markov kernel and a probability law
on its parameters. `kyburgJoint` retains the parameter and outcome together;
`flatten` integrates out the parameter to obtain the outcome marginal.

For a fixed action and a measurable nonnegative utility depending only on the
outcome, flattening preserves expected utility. It therefore preserves comparisons
between such fixed actions. The results do not assert sufficiency for policies
that observe the parameter or reuse it across later draws.

## Reusing a latent parameter

`LatentReuse.lean` distinguishes two laws on `X × X`:

- `sharedPair`: sample one parameter, then two conditionally independent outcomes.
- `freshPair`: sample independently twice from the flattened marginal.

Both marginals equal `flatten`. The independently defined `observeAgain` kernel
retains the first observation and draws again at its original parameter. Applied
to `kyburgJoint`, it gives exactly `sharedPair`.

For each measurable event `A`, the difference between the real probabilities of
`A × A` under the shared and fresh laws is the variance of the component event
probability. All integrability and finiteness conditions follow from the Markov
and probability assumptions. Equality holds exactly when that event probability
is almost surely constant at the flattened probability. This is a per-event
criterion; it supplies neither a simultaneous null set for all events nor an
ordering of the entire pair measures.

The Boolean controls reuse the original Bernoulli kernel. A fixed fair coin and
a uniform mixture of deterministic coins both flatten to the fair-coin law.
Their shared-parameter TT probabilities are respectively 1/4 and 1/2. For the
endpoint mixture, TF has shared probability zero and fresh probability 1/4.
A constant kernel has identical shared and fresh pair laws. An unsupported δ₂
pulled back to the parameter interval [0,1] has zero mass.

## Modules

| Module | Contents |
|---|---|
| `Basic` | Supplied kernel and mixing law, joint law, marginals, weighted sums |
| `KyburgFlattening` | Event probabilities and fixed outcome-only expected utilities |
| `GiryMonad` | Bind/join identification, Dirac unit laws and associativity |
| `LatentReuse` | Retained-parameter execution, marginals, variance and exactness |
| `DeFinettiConnection` | Boolean prefix laws, mixture bridge and separating controls |
| `CategoricalConnection` | Finite-alphabet product normalization and mixture bridge |
| `ProbabilityMeasureBorelBridge` | Borel measurability for probability-measure spaces |

The Giry laws establish composition for the supplied laws. They do not establish
uniqueness of monad multiplication, evidence sufficiency, or exchangeability.
The right unit is the Dirac identity kernel, not a constant kernel. The PLN
interpretation remains in `Mettapedia.PLN.Bridges.ProbabilityTheory.PLNKyburgReduction`.

## References

- Kyburg, [*Higher Order Probabilities*](https://arxiv.org/abs/1304.2714).
- Giry, [*A categorical approach to probability theory*](https://doi.org/10.1007/BFb0092872).
- The independently defined mixture models in `Mettapedia.ProbabilityTheory.Exchangeability`.
