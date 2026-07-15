# Ben Goertzel proof-attempt formalization index

Last synchronized: 2026-07-16.

This is the living index for MeTTapedia's formal review of Ben Goertzel's proof
attempts concerning the Four-Color Theorem, P versus NP, three-dimensional
Navier–Stokes global regularity, and the four-dimensional Yang–Mills mass gap.
It records both the ideas in Ben's manuscripts and the current formal verdict.

None of the four companion documents is a primary mathematical source. Ben's
original manuscripts define the proposed routes; the companions record what
the formalization has verified, refuted, reduced, or left open. A clean Lean
axiom audit certifies a theorem's implication, not the truth of hypotheses
stored in structure fields or passed as named premises.

## At a glance

| Route | Original proof idea | Current formal verdict | Companion |
|---|---|---|---|
| Four Color, v23 | Annular difference spanning; CAP5-free radius-one locality; execution of mixed Kempe switches through Penrose–Kauffman operators and local reachability on a canonical three-cell collar | Encoded local audits and substantial composition machinery are checked. Graph-fidelity and global assembly obligations remain open; an encoded-model seam failure refutes the collar-to-ambient reinterpretation as written in that model. This does not challenge the already-established Four-Color Theorem. | [source](goertzel_4cp.tex), [PDF](goertzel_4cp.pdf) |
| P versus NP, v13 | An upper–lower clash in polytime-capped conditional description length on a gauge-buffered locked SAT ensemble; CD evidence normalization, an Atomic Evidence Budget, boundary mixing, and fixed-clock incompressibility oppose the self-reduction upper bound under `P = NP` | The adaptive gauge-product law and substantial mechanical scaffolding are checked. The exact faithful M4 target is nevertheless machine-checked uninhabited: D.8 message rigidity, D.31 public-syntax neutrality, D.48 opposite-phase coupling, Definition 7.4 support-wide pair neutrality, and full public observability are jointly inconsistent on a nonempty target. The route requires revision; no separation is proved. | [source](goertzel_pnp.tex), [PDF](goertzel_pnp.pdf) |
| Navier–Stokes, v7 | Lift Navier–Stokes to heat flow on `SDiff(T³)`, apply a Cole–Hopf transform, push the gradient down at the identity, and control Beale–Kato–Majda through identity carré-du-champ energy | The original local adjoint hypothesis H1 is refuted in a normalized Fourier shear model. A stochastic-Lagrangian repair has a checked conditional BKM skeleton, but its pancake closure requires the still-open pointwise scale-local strain budget `ScaleLocalPancakeStrainBudget`. | [source](goertzel_ns.tex), [PDF](goertzel_ns.pdf) |
| Yang–Mills, v14 | Wilson lattice regularization; multiscale extended-extraction RG bootstrap; stopping-scale KP polymer expansion and clustering; glue back to fine scales; OS reconstruction and nontriviality | Exact extraction repairs and a derivative-aware boundary-cochain scaffold are checked, but the actual-lattice O.9/F.4 target is refuted by a hypercubic, non-O(4) Wilson jet. A complete four-coordinate H(4) Cartan quartic basis and identity dual chart are now certified; the fixed-width dimension-16 extension is separately refuted because inactive padding is incompatible with a faithful invertible census. The live repair is unpadded/dependent F,D syntax (or a padding quotient), or a quantitative continuum/Symanzik projection. All analytic Wilson-RG, KP, and continuum/OS inputs remain open. | [source](goertzel_ym.tex), [PDF](goertzel_ym.pdf) |

## Four-Color route

Ben's v23 argument recasts a plane triangulation as a bridgeless planar cubic
dual and encodes its three edge colors by the nonzero elements of
`F₂²`. Its three pillars are deliberately distinct:

1. an algebraic spanning theorem for the zero-boundary annular difference space;
2. a CAP5-free minimal-counterexample normal form giving radius-one confinement
   and controlled interaction of anchored Kempe cycles; and
3. an execution theorem which does not assume false additivity of mixed
   color-pair switches, but realizes them as generally noncommuting involutions
   in the Penrose–Kauffman coloring state space and reduces execution to local
   reachability in a canonical three-cell gadget.

The formal work preserves this separation. Finite encoded-state audits do not
automatically imply graph-level Kempe-step soundness, and collar-local words do
not automatically lift to ambient annulus words. The companion tracks those
bridges explicitly and treats the encoded seam countermodel as a route warning,
not as a refutation of the Four-Color Theorem.

## P-versus-NP route

V13 replaces v12's claim that short computation becomes syntactically local
with an evidence-accounting argument. The public SAT instance is meant to have
many witnesses but one global readout message. Under `P = NP`, SAT
self-reduction would recover that message with constant program description.
The lower side attempts to prove linear fixed-clock description complexity by
normalizing observer traces into neutral, safe-buffer, and hidden-gauge atoms;
bounding their total resolving evidence; combining this with boundary mixing;
and applying compression from exponentially small success.

The formalization proves exact finite adaptive hidden-gauge product uniformity
on the regioned scaffold, positive-rank free gauge action, full-syntax catalog
facts, and many trace/counting components. The final source reconciliation also
finds a structural contradiction before the analytic frontiers are used:
opposite-message phase coupling must contain supported pairs; D.31 and
Definition 7.4 make all fully visible public-syntax atoms equal on those pairs;
full observability makes the public instances equal; D.8 then makes their
message coordinates equal, contradicting the opposite phases. Therefore no
new lock family can inhabit the complete faithful interface without revising
at least one manuscript role.

## Navier–Stokes route

V7 proposes a lift–linearize–push-down pipeline. A positive heat datum on the
volume-preserving diffeomorphism group evolves under a sum-of-squares generator;
the logarithmic Cole–Hopf transform gives a group-level HJB potential; its frame
gradient is evaluated at the identity to produce a divergence-free velocity;
and a uniform identity-energy estimate is intended to close the
Beale–Kato–Majda vorticity criterion.

The formal countermodel shows that v7's local `H^m → H^m` adjoint bound H1
loses control even inside every positive chart radius. The repair lane instead
uses cotangent/stochastic-Lagrangian transport and a microlocal
vorticity-stretching analysis. Its algebra, conditional pushdown, frozen-strain
obstruction, and plane-wave null-structure canaries are checked. The remaining
pin is not merely “regularity is hard”: it is the self-consistent pointwise
scale-local inequality represented by `ScaleLocalPancakeStrainBudget`.

## Yang–Mills route

V14 begins with finite Wilson lattice gauge theory, runs an RG flow intended to
contract irrelevant activities while following asymptotic freedom, obtains
physical-scale clustering from a KP polymer expansion, transfers clustering
back through the RG maps, and invokes OS reconstruction to obtain a continuum
Hamiltonian and spectral gap. Extended extraction through canonical dimension
16 is intended to offset polymer recombination losses.

The formalization now distinguishes three different statements:

1. the scalar inequality for a supplied recursion constant, which is checked;
2. a concrete finite Wilson-polynomial extraction, for which coefficient-majorant
   truncation is gauge invariant and norm one; and
3. the actual v14 action-sector extraction and Wilson RG map, for which the
   necessary lattice representatives, quotient basis, dual jets, conditioning,
   and weighted analytic estimates have not been supplied. F.4's on-shell
   reduction and O.9's off-shell census do not define the same coordinate space.

A later exact SU(2) witness decides the proposed Lorentz-only coordinate target.
The sum of squared Wilson plaquette potentials has canonical dimension 8 and
fourth Cartan jet proportional to
`F01^4 + F02^4 + F03^4 + F12^4 + F13^4 + F23^4`. An explicit rational
orthogonal rotation changes its value from `1` to `337/625`. The jet is an
actual hypercubic lattice invariant but not an O(4) scalar, whereas every span
of O.9.3's Lorentz contractions remains O(4)-invariant. Thus neither the
off-shell nor on-shell relation policy admits a complete Lorentz-only census
for the actual finite-spacing lattice.

Range alone does not control a projection norm. Union-support recombination is
norm one, while `14` is a rooted local branching count rather than a universal
contact bound. The F.5 and Appendix-O factor ledgers disagree, and neither
derives `C_true`. The derivative-free Cartan quartic restriction now has a
certificate-producing four-element H(4) basis, exact representative duals,
and identity conditioning. The attempted fixed-width extension through
dimension 16 is not faithful: inactive padding creates distinct raw points
with identical active syntax, and no invertible exact census can make every
basis column padding-invariant. The next substantive work is therefore to
construct finite unpadded/dependent F,D syntax or a checked padding quotient,
then enumerate the full H(4)-stable relation quotient and rederive its duals
and conditioning. The alternative is a separately proved continuum/Symanzik
projection with quantitative control of every discarded artifact. Only after
one of those constructions is sealed can the connected Wilson cumulant/KP
bound be proved in the same norm.

## Status discipline

- “Proved” means a theorem about the stated object was checked in the relevant
  formal system.
- “Conditional” means the implication was checked while named mathematical
  inputs remain premises.
- “Refuted” means an explicit countermodel or contradiction theorem was checked.
- A finite or toy inhabitant establishes consistency only for that toy; it does
  not transfer to a manuscript ensemble by analogy.
- No companion in this directory claims a new solution of an open Millennium
  problem.
