# Ben Goertzel proof-attempt formalization index

Four Colour and Yang–Mills entries updated: 2026-10-06. Navier–Stokes entry
updated: 2026-10-05. The P-versus-NP entry retains its earlier status.

The [Four Colour overview](goertzel_4cp.pdf) opens with the compositional
mechanism, checked family reductions, the open geometric coverage theorem
and the latest distinction-interface results. Earlier derivations and
dated route audits remain in appendices. The [source](goertzel_4cp.tex) and
[proof-plan guide](fourcolor-compositional/README.md) link this account to
the exact formal statements and compression ledger.

This is the living index for MeTTapedia's formal review of Ben Goertzel's proof
attempts concerning the Four-Color Theorem, P versus NP, three-dimensional
Navier–Stokes global regularity, and the four-dimensional Yang–Mills mass gap.
It records both the ideas in Ben's manuscripts and the current formal verdict.

The original manuscripts define the proposed routes. The companions record
their derivations and the current formal results; the exact source statements
and declared hypotheses govern every checked claim. A clean Lean axiom audit
certifies a theorem's implication, not the truth of hypotheses stored in
structure fields or passed as named premises.

## At a glance

| Route | Original proof idea | Current formal verdict | Companion |
|---|---|---|---|
| Four Colour, compositional programme | Open pieces, shared colouring witnesses, uniform reductions and geometric recognition | Complete classical reconstruction checked for finite noncrossing plane drawings and exact source GSLT constructions. Coverage retains 633 configurations and 629 original certificate dependencies; shared arguments replace four certificates and 336 discharging computations. Exact distinction transport supports two source repairs, while its measured information cost warns against assuming a compact interface. Universal family supply and termination remain open. | [current overview](goertzel_4cp.pdf), [source](goertzel_4cp.tex), [proof plan](fourcolor-compositional/README.md) |
| P versus NP, v13 | An upper–lower clash in polytime-capped conditional description length on a gauge-buffered locked SAT ensemble; CD evidence normalization, an Atomic Evidence Budget, boundary mixing, and fixed-clock incompressibility oppose the self-reduction upper bound under `P = NP` | The adaptive gauge-product law and substantial mechanical scaffolding are checked. The exact faithful M4 target is nevertheless machine-checked uninhabited: D.8 message rigidity, D.31 public-syntax neutrality, D.48 opposite-phase coupling, Definition 7.4 support-wide pair neutrality, and full public observability are jointly inconsistent on a nonempty target. The route requires revision; no separation is proved. | [source](goertzel_pnp.tex), [PDF](goertzel_pnp.pdf) |
| Navier–Stokes, SG–Cole–Hopf and stochastic-geometric repair | Stochastic viscosity, geometric depletion and control of complete histories; originally a heat lift to `SDiff(T³)` with an identity-energy bound | The H1 adjoint bound fails in the audited shear model. Actual local evolution and conditional continuation are checked on both domains. Compatible whole-space histories and distinction observers are Lean-certified. Analytic coupled-parent calculations pay the leading return and show a depleting next correction; the full arbitrary-data history payment remains open. | [current overview](goertzel_ns.pdf), [source](goertzel_ns.tex) |
| Yang–Mills, Wilson/RG route | Exact integration of short-distance fluctuations; weak-to-strong entrance; spatial polymer clustering; observable transport and OS reconstruction | Actual SU(2) scale-two Haar blocking, finite-depth composition and spatial contraction are checked on an explicit strong-coupling interval. Eliminated Maxwell fluctuations have a volume-independent gap `1/4096` modulo gauge, with the Wilson quadratic normalization and Gaussian covariance bound. Exact transport retains discarded covariances: their spatial control along the weak-coupling trajectory, entrance, and the nontrivial continuum construction remain open. Detailed extraction audits and numerical diagnostics are retained in appendices. | [current overview](goertzel_ym.pdf), [source](goertzel_ym.tex) |

## Four-Color route

The [current guide](fourcolor-compositional/README.md) follows the later
Goertzel/Fable compositional note and explains the completed repair. Its
classical coverage argument reuses Robertson–Sanders–Seymour–Thomas through
Gonthier–Werner and Emery. The complete theorem consumes actual colouring
reconstruction and the shared discharging proofs; it does not prove the
manuscript's distinct bounded-width or generating-base assertions.

The latest source application proves that equal evaluated relation snapshots
can have different extension answers after the same update. Its common
region-labelled interface transports both admitted repairs and every finite
composition exactly, retaining one shared interior colouring for full-source
reconstruction. The independent census finds 44,040 such reports among 44,286
labelled proper boundaries, so this interface is not credited as compression.
The next repair obligation is component routing with its hidden update choices
retained. These local results remove no further coverage entry.

The earlier v23 stage remains useful background:

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

The [current overview](goertzel_ns.pdf) opens with the stochastic-geometric
mechanism, the exact signed-renewal continuation target, actual compatible
histories and the remaining physical estimate. The detailed earlier SG audit
and microlocal derivations are retained as appendices.

V7 proposes a lift–linearize–push-down pipeline: heat on the volume-preserving
diffeomorphism group, a logarithmic Cole–Hopf/HJB potential, a frame-gradient
pushdown and identity-energy control of vorticity. Its local adjoint H1 bound
fails in the audited Fourier shear model. The repaired route retains stochastic
Lagrangian transport, geometric feedback and history control without relying
on that bound. Actual local solutions, pressure, uniqueness and conditional
continuation are now available separately on the torus and whole space.

The recent coupled-parent benchmark retains every generated output and the
canonical pressure. Its original heat source has zero self-nonlinearity, yet
actual parent interactions generate positive stretching. The complete leading
return has a finite original-data payment; the next amplitude correction is
strictly depleting in every parent channel. An actual-flow comparison follows
in a precisely stated small-amplitude finite-interval regime. These physical
results are analytic with exact arithmetic checks, not newly Lean-certified
PDE estimates.

The distinction application connects a datum-fixed margin below observer
saturation to whole-space continuation. It also certifies an algebraic
obstruction to exact prediction from an energy/source summary. The physical
identification shows why directional parent information matters. A summary
preserving a valid upper cost bound can still suffice. The complete evolving
higher return, concentration and arbitrary-data history payment remain open.
Detailed derivations and checks are in the
[NS integration guide](../../lean/navier-stokes/README.md) and
[lab catalogue](../../lean/navier-stokes/labs/README.md).

## Yang–Mills route

The [current overview](goertzel_ym.pdf) leads with the mechanism: integrate
short-distance fluctuations exactly, reach a controlled spatial interaction
regime, transport the original observables, then construct the continuum
quantum field theory. The [source](goertzel_ym.tex) links each current claim
to its Lean statement. Earlier extraction audits and stopping-scale numerical
diagnostics remain in appendices.

For the actual SU(2) ordered-product block map, the formalization proves:

- Exact Haar measure transport, generated densities and observables, and
  agreement of direct and staged integration at every finite depth.
- Spatial interaction contraction by `4 exp(-2)` inside radius `1/2`, with
  explicit Wilson entry threshold `1 / (128 exp(32 + 4η))`, uniformly in
  volume and depth for fixed `η > 0`.
- The complete covariance transport identity, including discarded scale
  contributions, and a depth-independent total variance budget. Fixed-depth
  conditional spatial estimates are also available at strong coupling.
- A volume-uniform gap `1/4096` for the Maxwell quadratic form on eliminated
  fields modulo fiber-preserving gauge transformations, together with its
  actual Wilson action normalization and conditional Gaussian size bounds.
- A conditional stopping-scale bridge giving physical decay rate
  `m = η / rMax`, with entrance and observable transport as separate inputs.

The current crux is spatial control of discarded covariances and transported
means under the actual generated measures at weak coupling. The quadratic
gap does not establish nonlinear background or large-field control. Entrance
from a weak-coupling cutoff sequence and a nontrivial continuum/OS
construction remain open. Compact-group strong-coupling transfer gaps and
site reflection positivity are proved lattice inputs, not a continuum gap.

The v14 extraction audit remains relevant: the advertised factor ledgers
disagree, range alone does not bound an extraction projection, and the
complete coupled physical quotient and its conditioning are not yet
supplied. The proved strong-coupling contraction does not validate that
separate weak-coupling recursion constant. See the
[formal module index](../../lean/mettapedia/Mettapedia/QuantumTheory/YangMills/README.md)
for the detailed theorem map.

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
