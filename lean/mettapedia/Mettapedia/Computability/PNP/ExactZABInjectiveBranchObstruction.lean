import Mettapedia.Computability.PNP.ExactZABInjectiveBranchObstructionExactDecisionList
import Mettapedia.Computability.PNP.ExactZABInjectiveBranchObstructionSharedAffineFeature
import Mettapedia.Computability.PNP.ExactZABInjectiveBranchObstructionSharedDecisionList

/-!
# P vs NP crux: the live injective exact-ZAB branch still forces huge budgets

The noninjective extractor branch is already blocked by visible collisions.
This file targets the live alternative branch: even if the extractor is
injective, any surjective exact/shared exact `z+a+b` ERM route still has to pay
explicit lower bounds on its route parameters.

In particular:

* the raw exact decision-list ERM route needs extractor width
  `r ≥ 2^(n + 2k) - (2k + 1)`;
* the shared exact affine-feature ERM route needs at least `n + 2k` shared
  features;
* the shared exact affine-decision-list ERM route needs combiner width
  `p ≥ 2^(n + 2k) - 1`.

These statements do not use noninjectivity at all, so they speak directly to
the remaining injective-encoder branch.
-/
