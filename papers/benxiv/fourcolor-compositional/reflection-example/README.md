# A complete compression example: ten charge checks from three representatives

The reference discharging case `f10_242` checks ten bounds separately.
[`ReflectedHubcap.succeeds`][example] proves the same local exclusion from
three checked representatives and general transport and summation theorems.
The [complete Four Colour assembly][complete] consumes this replacement.

This is a completed example of semantic proof compression. It concerns
discharging charge bounds; a new uniform theorem replacing a family of
colouring-reducibility checks remains a separate milestone.

## 1. Retain the meaning of each check

The input `p10_241r` describes constraints around a hub of arity ten. Its ten
positions require these upper bounds on incoming net charge:

```text
position:  0  1  2  3  4  5  6  7  8  9
bound:     4  5  5  4  2  4  5  5  4  2
```

[`ChargeBound.of_check`][semantics] turns a successful checker result into a
statement about actual maps: every valid hub fitting the complete input part
has the indicated edge charge at most the supplied bound. The validity
hypotheses include the minimal-counterexample conditions used by discharging.
Soundness of the reducibility predicate is supplied by the checked catalogue
in the complete assembly.

This semantic statement is the object we transport and compose. It records
the input constraints and the numerical bound, rather than just retaining a
Boolean answer.

## 2. Transport representatives and compose their bounds

[`ChargeBound.reflect`][semantics] proves a uniform theorem: a bound for any
nonempty input part gives the same bound for its reflected part. The proof
uses the reference's mirror-map and charge-invariance theorems, with the
necessary shift of the distinguished position. It does not assume that the
Boolean checker commutes with reflection.

This is a theorem about all fitting maps. A particular map need not itself
have reflection symmetry: reflecting the entire map transports the fitting
condition and charge, so the universal bound applies.

For this specific part, `ReflectedHubcap.representatives` kernel-checks the
complete rotated inputs and bounds against three representatives:

| Representative position | Positions supplied by equality or reflection | Upper bound | Total contribution |
| --- | --- | --- | --- |
| 0 | 0, 3, 5, 8 | 4 | 16 |
| 1 | 1, 2, 6, 7 | 5 | 20 |
| 4 | 4, 9 | 2 | 4 |

The only independent charge-checker computations are `check_zero`,
`check_one` and `check_four`. One additional finite classification verifies
the table using full input parts, not just a coarse boundary summary.

`ChargeBound.successful_of_bounds` then composes these bounds. The reference's
initial charge is `60 - 10n`, hence −40 at arity ten. Therefore

\[
\text{final charge}\;\leq\;-40 + 4\cdot4 + 4\cdot5 + 2\cdot2 = 0.
\]

A valid hub selected with positive final charge cannot fit this part. This
is exactly the local exclusion needed at this leaf of the coverage proof.

## 3. Replace a dependency of the completed theorem

The reconstructed arity-ten presentation calls
`ReflectedHubcap.succeeds` at the leaf formerly discharged by `f10_242`.
Its split tree and covered cases are retained. The replacement feeds
`Orbit10.exclude10`, and then the unconditional colouring and supported
construction endpoints in `CompositionalComplete`.

[`CompleteAudit`][audit] checks those endpoint dependency closures. They must
contain `ReflectedHubcap.succeeds` and `ChargeBound.reflect`; the original
`f10_242` and all ten original `c10_242_*` check declarations must be absent.
The audit also checks that the final theorem consumes the catalogue and the
geometric colouring reconstruction, with only the permitted standard axioms.

Thus this example replaces **seven independent discharging computations**:
ten become three, plus one separately counted input-classification check.
These seven are already included in the [ledger's total of 231][ledger].
No catalogue entry is removed, and no runtime or artifact-size saving is
claimed.

## What this demonstrates for the compositional programme

The sequence is concrete: interpret certificates, transport their meanings,
compose the resulting bounds, and substitute the proof in the finished
theorem. The reflection theorem applies beyond this one case, and subsequent
consumers use it at several arities. Reuse happens at the mathematical level
without having to prove that two checker executions behave identically.

The charge argument is expressed directly in Lean's hypermap semantics;
its result is consumed by the assembly connected to GSLT colouring witnesses.
It does not introduce another GSLT or establish a geometric graph-replacement
theorem. For that stronger next example, the [main guide][guide] records the
two-branch triangle-colouring theorem and its remaining planar reducibility
obligation.

The classical discharging mathematics and mirror-map facts come from
Robertson, Sanders, Seymour and Thomas, and Gonthier and Werner, through
Chris Emery's Lean port. The measured change here is how semantic bounds
replace repeated checks in that development.

[example]: ../../../../lean/fourcolor-classical/MettapediaFourColor/ReflectedHubcap.lean
[semantics]: ../../../../lean/fourcolor-classical/MettapediaFourColor/ChargeBound.lean
[complete]: ../../../../lean/fourcolor-classical/MettapediaFourColor/Complete.lean
[audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/CompleteAudit.lean
[ledger]: ../../../../tools/fourcolor/classical/compression-ledger.json
[guide]: ../README.md
