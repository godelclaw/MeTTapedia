# Exact boundary reduction

`LinearBoundaryReduction.lean` is imported unchanged from
[zariuq/MeTTapedia, revision 1d882c9f03383d58ad7afbcfaf43abbc88291ece](https://github.com/zariuq/MeTTapedia/blob/1d882c9f03383d58ad7afbcfaf43abbc88291ece/lean/mettapedia/Mettapedia/GSLT/Dynamics/LinearBoundaryReduction.lean),
under the repository's MIT license. It eliminates an invertible linear
interior block, preserves the internal forcing as an affine term, reconstructs
the interior, and preserves arbitrary predicates on the exposed response.

For block equations `C v + D w = j` and `A v + B w = r`, it gives

```text
w = D⁻¹(j - C v)
r = (A - B D⁻¹ C)v + B D⁻¹j.
```

`ConstrainedBoundaryReduction.lean` retains conditions on the reconstructed
interior:

- `constrained_elimination` preserves any predicate on `(v,w)`.
- `feedback_elimination` handles a state-dependent load `j = F(v,w)`.
  The reduced problem still requires `j = F(v,D⁻¹(j-Cv))`.
- `same_response_iff` identifies exactly which changes in the internal load
  are invisible at the boundary.

The last statement concerns observation, not equality of internal states.
Likewise, `feedback_elimination` is an exact equivalence, not a theorem
that the fixed-point problem has a solution or that it is stable.

The vector spaces may be spaces of histories. Such an application must
construct the linear inverse on the chosen history space, retain the initial
datum, and retain the nonlinear evolution constraint. Static invertibility
does not supply those analytic obligations.

The Navier–Stokes package's `MettapediaNS.FilteredHistory` separately derives
the complementary-mode equation, forcing compatibility, and signed Duhamel
history from the actual infinite Fourier coefficient solution. It does not
yet instantiate an inverse history operator in this block system. The
two layers distinguish exact elimination from dynamical realizability;
neither bounds arbitrary-data nonlinear regeneration.
