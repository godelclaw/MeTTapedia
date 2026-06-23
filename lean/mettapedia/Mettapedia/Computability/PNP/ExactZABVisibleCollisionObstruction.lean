import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionCore
import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionTargets
import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionRecovery
import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionERM

/-!
# P vs NP crux: noninjective `z` extractors block every exact-visible-summary route

`ExactZABExtractorCollisionObstruction.lean` already kills the raw exact
decision-list route when two latent states share the same visible summary
`(zfeat(z), a, b)`.

This file lifts that collision argument to the broader route surfaces whose
predictors are still functions only of that same visible summary:

* non-shared exact affine-feature / sparse-threshold / affine-decision-list
  families on `(zfeat(z), a, b)`;
* shared-basis exact affine-feature / sparse-threshold / affine-decision-list
  families on `(zfeat(z), a, b)`.

So once `zfeat` is noninjective, no such route can be surjective onto the full
exact rule class, regardless of which downstream combiner family is used.
-/
