# The Krenn–Gu structural layer

This directory specializes MeTTapedia's reusable perfect-matching theory to the
three-colour GHZ equations of the Krenn–Gu conjecture. The generic definitions and
proofs now live under `Mettapedia.Combinatorics.Matching`; historical Krenn module
paths remain as compatibility imports where downstream files still use them.

The structural theorems here remain uniform in the finite vertex set. They are
Krenn-specific because they consume the GHZ target equations, support minimality,
or the conjecture's three-colour hypotheses—not because they assume a fixed size.

Build with `lake build KrennLib`; the bridge to the official statement is
`lake build KrennGeneralBridge`.

## Shared objects

**`amplitude W c`** — the sum, over the perfect matchings of the whole vertex
type, of the product of the weights of their edges read through a colouring.

**`pmSum W c S`** — the same sum over the perfect matchings of a *subset*. A
matching of `S` is carried by a permutation of the whole vertex set that moves
every vertex of `S` and fixes everything outside, so a recursion deleting two
vertices never changes the type. On the whole vertex set the two agree.

**`Pairing`** — a perfect matching as a structure: a partner function with the two
involution laws. Convenient for building matchings; `MatchingBridge` identifies it
with the permutation form the amplitude sums over.

**`Pairing.SupportedBy G`** — the condition that every edge selected by a pairing
belongs to a graph. `GraphMatchingBridge` converts supported pairings to and from
Mathlib's `Subgraph.IsPerfectMatching`, and preserves graph support under exchange.

**`LocalSwap V A`** — a matching of the vertex set `A`, extended by the identity.
Its `config` is the family of whole-graph matchings agreeing with it on `A`.

All four objects above are defined in the shared MeTTapedia matching hierarchy and
are merely imported here.

## Shared results used here

### Matchings of a subset — `MatchingSum`

| | |
|---|---|
| `pmSum_expand` | the deletion recursion: pair a fixed vertex with each other in turn |
| `eq_pmSum_of_rec` | anything satisfying that recursion *is* the matching sum |
| `card_pairingsOn` | a set of even size `n` has `(n-1)!!` matchings; an odd set none |
| `pmSum_congr` | locality: only edges inside `S` matter |
| `pmSum_comp` | naturality under recolouring |
| `pmSum_of_forced` | a vertex with one admissible partner forces that edge |

### Splitting and cancelling — `LocalCancellation`

| | |
|---|---|
| `sum_closing_eq_pmSum_mul` | matchings respecting a split contribute the product of the two sides' sums |
| `sum_config_eq_mul_pmSum` | a configuration contributes its inside product times the complement's sum |
| `sum_config_mul_comm` | configurations contribute in the ratio of their products over `A` |
| `sum_biUnion_config_eq_zero` | a family of matchings of `A` whose products sum to zero drops out entirely |

### Cancellation in general — `Amplitude`

| | |
|---|---|
| `amplitude_eq_zero_of_sign_reversing` | a sign-reversing involution on matchings kills the amplitude |
| `amplitude_eq_sum_sdiff_of_sign_reversing_on` | one defined on part of them kills exactly that part |

### Alternating cycles — `Mettapedia.Combinatorics.Matching.Pairing` and `Kempe`

| | |
|---|---|
| `four_le_card_of_closed_disagree` | an alternating cycle costs four vertices |
| `four_mul_card_le_of_disjoint_disagreements` | so cycles number at most a quarter of the vertices |
| `Pairing.exchange` | exchange along a closed set; `edges_exchange` computes its edges |
| `exchange_trivial_of_card_le_seven` | below eight vertices every exchange is the identity or the swap |

The shared hierarchy also contains the two-pivot crossing calculus, invariant-set
restriction, Hall bounds, structural nonvanishing, loop erasure and support,
perfect-matching graph bridges, four-vertex and six-vertex matching expansions,
four-vertex pairing classification, block-rank identities, the fourth-matching theorem,
and orbit normalization. None imports Krenn or assumes the GHZ equations.

## Krenn-specific results

### Constructions: where solutions come from

| | |
|---|---|
| `ColourPerMatching.amplitude_spec` | if the coloured edges of every totally-coloured matching agree and each colour is worn by exactly one matching, the induced weights solve the equations |
| `FourVertices.solvable_two` | four vertices carry a three-colour solution, so the conjecture's exclusion of them is necessary |
| `CycleSolution.spec` | two colours at every even vertex count, so the bound of two is attained |
| `EvenCycle.eq_altPerm` | a matching along a cycle is one of the two alternating ones |

The colouring may be partial: an uncoloured edge weighs zero, so a matching using
one is never admitted. That is how a graph with missing edges is expressed, and
without it the construction would have only the four-vertex instance.

### Gauge — `Gauge`

`exists_normalized`: a configuration whose monochromatic amplitudes are merely
nonzero rescales to one where they are exactly one, every vanishing condition
surviving. So demanding the value one excludes no solution.

### The official statement — `GeneralOfficialBridge`

`eqSystemN_iff_amplitude_const` identifies the official equation system with a
condition on the amplitude, at every vertex count and dimension.
`solvable_iff_eqSystemN` shows the two notions of solution coincide, and
`official_conjecture_of_descent` states the conjecture in the official terms,
resting on one descent hypothesis and the six-vertex base case.

## What the whole library is for

The conjecture ranges over every even vertex count. `KrennGu.conjecture_of_descent`
reduces it to a single hypothesis — a solution on `2n` vertices yields one on
`2n - 2` — together with the six-vertex base case, and
`GeneralOfficialBridge.official_conjecture_of_descent` states that reduction in the
official statement's own terms.

That hypothesis is open. One route to it is closed: factorisation-based descent
needs a boundary-vanishing condition which, over all supports of the six-vertex
complete graph, holds nowhere above connectivity two — precisely the regime the
literature already settles. The cancellation results are the live alternative.

## A recurring device

Regrafting one configuration into another, deleting a matched pair, and extracting
a matching of the complement are all *right multiplication by a fixed
permutation*. Each therefore yields a permutation for free and inverts for free,
by the group law rather than by a construction carrying its own inversion lemmas.
The subtype-based composition law in `Amplitude` needs a glue construction and its
inverses; the `pmSum` version needs neither.


## Contraction and the incidence matrix

`CapIncidence` treats the contraction of a pair of sites. Contracting replaces the
amplitude by a flat term plus a correction, and the corrections leaving the amplitude
flat away from a permitted defect shape form the kernel of an explicit matrix built
from the weights.

`entry_eq_zero_of_offSupport` gives a *sufficient* reason for an entry of that matrix
to vanish: the weight block of a meeting edge is identically zero. It assumes nothing
about where the weights came from, so it binds a hypothetical solution as readily as a
constructed one. It is not a necessary condition — an entry can vanish through
cancellation inside the cap matrix with every block nonzero — so failure of the
criterion never establishes that no cap exists.

`entry_eq_zero_of_star` is the consequence: a contracted site meeting the residual set
in at most one place gives a star, an empty system, and an unconstrained contraction.
In graph terms it asks for two adjacent sites of low degree.

The restriction to stars and triangles is forced rather than chosen: a family of pairs
lies inside one such shape exactly when it is pairwise intersecting.

Whether a usable cap exists is decided by two linear functionals on the kernel — the
diagonal and the contraction scalar — each of which must be nonzero.
`exists_both_ne_zero` settles when that is possible: if each functional is nonzero
somewhere on the kernel, some single vector makes both nonzero, and the witness is one
of `u`, `v`, `u + v`. Checking basis vectors one at a time answers a different and
strictly weaker question, and a recognizer that does so under-reports.

Caps have been found and exactly verified on cubic supports at eight vertices — on the
cube, contracting a pair with a star defect, constant diagonal `-3/4`, contraction
scalar `-91/16`, every flatness constraint satisfied over the rationals. Such caps are
not generic, however: with wide-range weights none appear on the cube or on Wagner's
graph, while with small integer weights they appear exactly when some edge block is
singular.

The mechanism is visible in the tensor form of the rows. Writing the site vectors
`u(k,x) a = W s((p,a),(k,x))` and `v(l,y) b = W s((q,b),(l,y))`, each row's coefficient
array is a symmetrised product of one `u` with one `v`. On a cubic support only
neighbours of the contracted sites contribute, and the surviving rows span a tensor
product of two site spans, which fills the whole cap space unless a factor drops rank
— that is, unless an edge block is singular.

So cap existence at these sizes is a determinantal condition on the weights. Whether
the solution variety meets that locus is open, and is not answerable by sampling,
since the relevant points are exactly the non-generic ones.

## Second-order expansion

`prod_add_of_support_le_two` and `pmSum_perturb_two` carry the expansion to second
order. A defect on two edges meets a matching in at most two of them, so the perturbed
matching sum is an exact quadratic — flat, linear, and a cross term — and stops there
rather than becoming a series. The cross term arises when one matching uses both defect
edges, which is what a first-order representation cannot carry.

`absorb_defect_two` folds such a defect back into perturbed weights up to a residue
carrying the quadratic coefficient, and `absorb_defect_two_of_second_vanishes` records
that the reduction returns an object of the same kind exactly when that coefficient is
zero. `second_order_factors` shows the coefficient is the defect's values at its two
edges times a double cofactor depending only on the weights; for disjoint defect edges
that cofactor is the matching sum over the vertices they leave behind.

This machinery stands on its own. It is not forced by any proved failure of the
first-order route, and the four-vertex matching sum it meets is a recurring candidate
crux rather than an object shown to control every route.

`pmSum_compl_eq_zero_of_ne_zero` gives the factorisation dichotomy in usable form — a
set whose matching sum is nonzero forces its complement's to vanish — while which side
vanishes is undetermined.

## Trust

Every result is checked by the Lean kernel alone. No result depends on any axiom
beyond `propext`, `Classical.choice` and `Quot.sound`, several depend on strictly
fewer, and none uses a compiler-trusting tactic.
