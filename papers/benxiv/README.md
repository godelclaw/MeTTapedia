# Ben Goertzel proof-attempt formalization index

Four Colour entry updated: 2026-10-06. Navier–Stokes entry updated: 2026-10-05.
Other entries retain their own earlier status and are not reassessed by these
updates.

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
| Yang–Mills, v14 | Wilson lattice regularization; multiscale extended-extraction RG bootstrap; stopping-scale KP polymer expansion and clustering; glue back to fine scales; OS reconstruction and nontriviality | The natural finite Wilson-polynomial extraction has norm one, but v14's range-only `P_ext` data cannot transfer that bound. The advertised recursion constant is not derived; its two ledgers disagree and several factor inferences fail as written. OUR hypercubic boundary-cochain repair continues the same Wilson/RG/KP/OS proof programme and defines the coordinate-free joint invariant relation space. Its covariant-commutator rows needed the Leibniz rule: the earlier joint space contains a vector with nonzero background value, while every corrected relation vanishes on every gauge background and the corrected space has certified rank at least `11558`. It is not yet a complete census, conditioning certificate, RG bound, or continuum construction. Numerical evidence indicates that the stopping-scale step cannot be instantiated in the weak-coupling regime the bootstrap provides; on the hierarchical lattice, where the flow is exact, four-dimensional U(1) confines as well, so that lattice cannot model the missing crossing. The missing crossing input is stated in Lean, proved sufficient for exponential clustering uniformly in the volume, and shown to fail at β = ∞ for four-dimensional U(1) and five-dimensional gauge fields; proving it for four-dimensional SU(2) is open; at strong coupling it is proved for Wilson-type measures uniformly in the volume. A necessary condition testable at finite coupling is proved: a twist-compatible crossing family has vanishing twist free energy on large tori. Monte Carlo finds it vanishing for four-dimensional SU(2) and not for four-dimensional U(1) or five-dimensional SU(2), where the centre twist is classically costly (U(1)) or weak coupling persists (SU(2), whose twist eaters make it classically free). | [source](goertzel_ym.tex), [PDF](goertzel_ym.pdf) |

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
   necessary basis, dual jets, conditioning, and weighted analytic estimates
   have not been supplied.

Range alone does not control a projection norm. Union-support recombination is
norm one, while `14` is a rooted local branching count rather than a universal
contact bound. The F.5 and Appendix-O factor ledgers disagree, and neither
derives `C_true`. OUR repairs are a continuation of Ben's proof programme,
not a separate endpoint: the repaired finite target preserves the same Wilson
lattice, RG, KP, glue, and OS dependency chain while repairing its false
coordinate bridges. Its joint invariant relation submodule now has a
certificate of rank at least `11558`; the next substantive work is a complete
joint census and conditioning certificate, Wilson-to-cochain dual jets, and
the connected Wilson cumulant/KP bound in the same norm.

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
