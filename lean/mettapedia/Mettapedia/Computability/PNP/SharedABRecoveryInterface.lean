import Mettapedia.Computability.PNP.SharedABRecoveryInterfaceSparseThreshold

/-!
# P vs NP grassroots: recovery interfaces for the shared raw exact `(a, b)` route

This compatibility module preserves the original import surface for shared raw
exact `(a,b)` recovery interfaces.  The declarations live in semantic modules:

* `SharedABRecoveryInterfaceAffine`
* `SharedABRecoveryInterfaceSparseThreshold`
* `SharedABRecoveryInterfaceData`

These modules package the remaining generic ingredients for the shared raw
exact affine-feature and sparse-threshold routes:

* one shared affine basis on the raw exact `(a, b)` bits,
* one corresponding realization of the switched family through that basis, and
* one bad-code agreement bound.

Once those data are supplied, both the exact visible compression target and the
weighted exact-recovery lower bound follow automatically.
-/
