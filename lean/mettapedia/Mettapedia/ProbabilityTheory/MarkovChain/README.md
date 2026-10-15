# Finite Markov transport

`Restart` proves existence and uniqueness of a finite restarting walk's fixed
point, linearity in the stimulus, nonnegativity, monotonicity, mass laws,
iteration error bounds and bounded-hop locality. Its matrix is column oriented.

`FiniteMassTransport` uses mathlib's row-stochastic matrix submonoid for outgoing
kernels. It normalizes nonnegative edge weights, supplies a self-loop at dangling
rows, proves conservative lazy transport and finite-round reachability, and
adapts this orientation to `Restart`. Continuation mass `a` corresponds to
restart probability `1-a`; the fixed-point theorem requires `0 ≤ a < 1`.

Both modules use real numbers. Matrix coefficients may be routing shares without
being calibrated probabilities about an external world. The duplicate-edge
counterexample separates preservation of total mass from invariance of routing.

The a posteriori bounds `error_le_change` and `next_error_le` use observed
last-round change to bound remaining error. `outside_mass_le_leakage` assumes a
unit nonnegative seed supported in a specified cluster and pointwise outgoing
leakage bounds; it does not infer cluster relevance or formalize conductance
refinements. `ppr_ge_depth` bounds each discounted depth contribution without
claiming that contribution is useful. `Audit` prints kernel dependencies.
