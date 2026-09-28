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

## Signed costs and Bellman verification

`BoundaryBellman.lean` equips the existing `Core.LooseRelationEquipment`
witnesses with real signed costs. Composing two witnesses retains their common
intermediate state and adds their costs. For a reserve `R`, the local condition

```text
cost(h : x -> y) + R(y) <= R(x)
```

composes through every finite compatible history. If the terminal reserve is
nonnegative, the initial reserve pays the total cost. `upper_comp_iff` gives
the backward Bellman budget law without assuming a finite state space,
discounting, a finite supremum, or an optimizer. `Bounds.of_domination` and
`Domination.comp` preserve upper bounds under witness transport with a proved
cost inequality.

`StateErasureExample` preserves each individual event cost while forgetting
whether the source is charged or spent. The forgotten relation permits a
positive loop and has no state-only reserve; the retained relation has a
nonnegative reserve controlling every finite prefix. Thus preservation of
individual costs does not justify forgetting the states that constrain their
composition.

This distinction complements the history and erasure analysis in
[F1R3FLY's history note](https://github.com/F1R3FLY-io/publications/blob/4504c70f04e3b5595c27f3a21a057bc403b0f97c/history-functor/history-endofunctor.pdf)
and the ledger formalization in
[`CostExactness.lean`](https://github.com/zariuq/MeTTapedia/blob/1d882c9f03383d58ad7afbcfaf43abbc88291ece/lean/mettapedia/Mettapedia/GSLT/Dynamics/CostExactness.lean).
A conserved expression `remaining + spent = initial` alone supplies neither
nonnegativity of `remaining` nor identification with physical energy.

`MettapediaNS.WholeSpaceHistoryBridge` is an actual fluid consumer. Its edges
are smooth unforced whole-space NS evolutions, and its costs are integrals of
the physical order-energy production. It proves the kinetic-energy case and
states the stronger order-one reserve as a sufficient continuation hypothesis.
Constructing that reserve, or identifying a transported-frame/stochastic
observable with a suitable cost and nonnegative reserve, remains open.
