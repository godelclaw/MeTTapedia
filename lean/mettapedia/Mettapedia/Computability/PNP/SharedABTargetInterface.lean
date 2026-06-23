import Mettapedia.Computability.PNP.SharedABDecisionListRecoveryInterface

/-!
# P vs NP grassroots: unified target interfaces for the shared raw `(a, b)` route

This compatibility module preserves the original import surface for shared
raw `(a,b)` target interfaces.  The declarations live in semantic modules:

* `SharedABTargetInterfaceCore`
* `SharedABDecisionListRecoveryInterface`

The mathematical burden is now cleanly separated:

* quotient invariance under the reduced raw visible surface `(a, b)`,
* one fixed shared affine basis on that reduced surface,
* one combiner class on the resulting shared feature vector.

Once those hypotheses are packaged, the exact-surface compression target follows
immediately with the corresponding budget.
-/
