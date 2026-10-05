# Navier–Stokes upstream integration

This package uses Lean 4.34.0-rc2 to import the existing OpenAI and
Alpöge–Buckmaster fluid-analysis libraries directly. It is a migration and
integration surface, not another copy of their mathematical developments
and not a completed regularity proof.

The existing MeTTapedia sources are available through `MettapediaFluid` with
`srcDir = ../mettapedia`. The repository's other Lean packages keep their own
toolchains. Compatibility of an existing module with this package must be
checked explicitly; adding the source root does not certify its migration.
The shared library also includes the existing Markov-category kernel interface
imported by the Navier–Stokes semigroup module, and the GSLT linear boundary
reduction and compatibility theorems in `Mettapedia.GSLT.Dynamics`. Its costed
history interface uses the existing `GSLT.Core.LooseRelationEquipment`.

## Pinned dependencies

- OpenAI/NavierStokesAndEuler:
  `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`.
- tristanbuckmaster/fluid_lean, package `euler-blowup`:
  `d0124689230b58b4f86e7b90ac59de06404b3b6b`.
- mathlib: `85e3a25e006c35636f0e53b0e9296caca2685bc0`, the upstream
  Lean 4.34.0-rc2 revision.

The explicit mathlib requirement comes last so that its shared transitive
dependency versions take precedence over the older EulerBlowup manifest.

Upstream sources remain in their original package with their original
attribution and licenses. `MettapediaNS.UpstreamAudit` imports the actual
pressure-commutator, viscous-propagator, and arbitrary-positive-viscosity
periodic uniqueness theorems and prints their axioms. It also imports the
existing coherent-pair estimate from the canonical MeTTapedia source tree.
It does not replace their analytic hypotheses with assumptions about the
desired global regularity conclusion.

## Boundary reduction and hidden histories

The [joint strain-source estimate](labs/README.md#a-joint-strain-source-after-paying-complete-coarse-histories)
combines directional observations into one positive quadratic stock on
both R3 and T3. The original energy pays all coarse interactions, including
the coarse fluid's own nonlinear output, through an exponential reserve.
The remaining work is one explicit strain contraction; pressure and the
antisymmetric velocity gradient cancel in that pairing. An exact triad
still has positive work above its allotted diffusion. Its signed history
bound remains open, while the conditional continuation implication is
checked against the existing Lean consumers. The estimates are analytic
with exact algebraic fixtures, not new Lean certificates.

The [transverse-parent response test](labs/README.md#transverse-parents-create-an-exponential-receiver-response)
shows why polynomial responses for separate shear families cannot simply
be combined. Two transverse parents in an exact unforced periodic flow
produce receiver gradient growth exceeding every fixed polynomial in
amplitude times horizon, on suitable finite positive-viscosity intervals.
The example is globally smooth and paid by the existing exponential
planar-parent reserve. It identifies a necessary joint response cost;
it does not refute a full-datum allowance or the one-axis bound below.
The continuum argument is analytic with exact algebraic checks.

The [finite parent-response bound](labs/README.md#finite-response-to-a-changing-parent-with-the-nonlinear-input-retained)
controls the full response to a periodic first-harmonic parent whose
amplitude and orientation may change throughout the history. Retaining
neutral modes gives a positive reserve with cubic polynomial weights
fixed by the original energy and horizon. It applies to arbitrary smooth
periodic prefixes and retains all residual self-interaction as an explicit
signed input. A bound on that input would give order-one continuation;
its arbitrary-data payment remains open. Exact fixtures include parent
feedback, generated higher means and positive internal input. This is an
analytic result with rational checks, not a new Lean certificate or a
whole-space extension.

The [complete quotient-return test](labs/README.md#a-balanced-fluid-generates-positive-optimized-work-through-its-changing-dual)
retains the evolving optimizer when differentiating the cubic work. An
exact elliptic residual bounds its full response. A balanced periodic 3D
datum has zero initial work and zero viscous contribution to its first
work derivative, yet actual unforced evolution generates positive work
on a short interval. Freezing the optimizer predicts the wrong sign.
A first-order signed history forecast fails locally while remaining
positive. A coercive second-order completion repairs that balanced
example at every positive amplitude and viscosity, but a different
phase regenerates the completion itself and defeats its payment at
large amplitude. This concerns the chosen cubic observation, not a
blowup or a failure of every full-datum allowance. The results are
analytic with exact rational checks, not new Lean certificates.

The [quotient heat payment](labs/README.md#heat-dissipation-of-the-optimal-quotient-without-a-nondegenerate-gauge)
removes the smooth, nonvanishing optimizer assumption from the cubic
continuation observation on R3 and T3. A heat-semigroup comparison controls
its weighted spatial derivatives even at zeros. Every interaction with a
fixed-scale smoothed velocity factor is bounded by diffusion and linear
stock growth, with a coefficient fixed by the original energy. One signed
fine-history estimate remains.
Exact three-dimensional fixtures show that the remaining work can have
either sign, and its sign can change with the chosen smoothing scale.
The arbitrary-history allowance remains open. These are analytic results
with exact algebraic checks, not new Lean certificates.

The [optimal cubic gradient test](labs/README.md#optimal-gradient-removal-leaves-signed-physical-renewal)
removes the preceding covector overcharge by minimizing over every gradient
representative of the physical velocity. This correction succeeds on the
exact shear, but its minimum can increase on an actual smooth unforced 3D
history. Two explicit periodic families have the same optimized stock and
diffusion cost and opposite nonlinear feedback. A complete analytic
remainder bound fixes the initial parameters before the evolution. This
rules out automatic decrease under instantaneous gauge optimization;
finite full-datum history payment remains open. The new argument is
analytic with exact checks, not Lean-certified.

The [rotation-preserving covector calculation](labs/README.md#rotation-preserving-covector-histories-and-the-cost-of-a-gradient)
reuses the existing physical covector reconstruction and separates rotation
from strain without discarding either history. A scalar reserve pays the
coarse strain couplings in a continuation norm; the joint fine history
remains open. An exact identity shows that accumulated quadratic covector
strain input is gradient storage plus its diffusion. Even a pressure-free
decaying shear has positive such work, with an explicit finite allowance.
Thus auxiliary covector growth cannot be identified with dangerous fluid
stretching. The new estimates and actual-flow examples are analytic with
exact checks, not new Lean certificates.

The [pressure-deformation source payment](labs/README.md#pressure-deformation-has-a-finite-source-payment-but-a-critical-concentration-gap)
constructs a nonnegative original-energy reserve for the full space-time
L1 magnitude of the actual pressure-deformation source. It retains its
complete evolution, including the mixed diffusion term. That reserve also
pays every source coupling with at least one fixed-scale smoothed gradient
in the critical continuation norm, leaving an exact joint fine-gradient
interaction. A localized unforced swirl and exact NS scaling show why
that payment alone cannot
control the critical history observation, even at a fixed pressure cutoff.
The initially pressure-free cyclic datum generates a solenoidal pressure
return at third order. A stronger, precisely stated source norm would
suffice for continuation; its arbitrary-data payment remains open.
These are analytic results with exact checks, not new Lean certificates.

The [recent-pressure reconstruction](labs/README.md#recent-pressure-deformation-histories-reconstruct-the-actual-fluid)
bounds the transported incoming fluid and coarse-pressure history over a
fixed time window using original resources. The remaining divergence-free
pressure impulse is exactly an evolving pressure-deformation interaction,
with all propagators belonging to the same actual flow. A bound on its
accumulated L9 norm would give the existing continuation criterion.
Complete short-time jets exhibit a nonzero such return in unforced 3D
data: a transported pressure gradient need not stay a gradient. The
arbitrary-history allowance remains open; these analytic results and
exact checks are not new Lean certificates.

The [aged joint-memory estimate](labs/README.md#aged-stress-memory-is-absorbed-up-to-linear-joint-stock-growth)
controls old memory's fine pressure work and complete transport commutator,
plus coarse canonical-pressure generation, by one quarter of the joint
diffusion and a linear function of the joint stock. Its coefficients are
fixed by original resources and a prescribed positive memory age. A fixed
integrating factor leaves an explicit recent-memory/fine-pressure history
estimate sufficient for continuation. That estimate remains open: older
parents still influence the current velocity and generate new stress.
The argument is analytic with exact algebra and full Fourier jet checks;
it is not a new Lean certificate or an unconditional stock bound.

The [first nonlinear memory-pressure return](labs/README.md#the-first-nonlinear-memory-pressure-return-has-both-signs)
has opposite signs on two thin-parent families at the same fixed cutoff.
Both enlarged observations initially decrease, but one family subsequently
generates positive fine memory work. Exact limiting coefficients identify
the competing receiver and parent contributions. This refutes automatic
nonpositivity of that work, not a finite full-datum history allowance or
regularity. The actual-interval argument is analytic with exact Fourier
checks; no new Lean theorem is claimed.

The [stress-memory pressure payment](labs/README.md#stress-memory-pressure-has-an-age-dependent-original-energy-payment)
retains the actual positive tensor generated by viscous parent gradients.
Drift-independent smoothing bounds its pressure primitive over every
available unforced history from the original energy, on R3 and T3.
A nonnegative reserve retains the ages of past contributions across
segments. It pays the enlarged observation's complete coarse-pressure
work and repairs the initial growth in the unequal-decay test below.
Fine memory-pressure work and the nonlinear source history remain open.
The estimates and short-time repair are analytic with exact checks,
not new Lean certificates or an arbitrary-data regularity theorem.

The [unequal-decay pressure test](labs/README.md#unequal-parent-decay-can-overwhelm-joint-pressure-diffusion)
shows that the retained viscous pressure source cannot be absorbed by any
universal multiple of the joint diffusion. An explicit periodic datum
has source greater than three times that diffusion while kinetic energy
decreases. Opposing parent pressures lose their cancellation as their
viscous decay rates differ. The strict gap persists on an actual short
unforced NS interval; the full-datum history allowance remains open.
The proof is analytic with exact Fourier and rational checks, not Lean-certified.

The [convex joint pressure observation](labs/README.md#a-convex-pressure-observation-pays-diffusion-transfer-and-coarse-histories)
controls the explicit velocity/pressure diffusion transfer and pays all
coarse-pressure work from one original-energy reserve on R3 and the
zero-mean periodic domain. Its complete generated source still contains
pressure, transport and viscous stress production. A stated bound on that
signed history would give a general three-dimensional continuation
criterion. The bound remains open; the derivation is analytic with exact
symbolic checks, not a new Lean theorem.

The [validated pressure-regeneration sign](labs/README.md#a-validated-whole-space-sign-rejects-instantaneous-pressure-stock-monotonicity)
now encloses the whole-space initial coefficient between 0.0000213 and
0.0000404 for the fixed Gaussian observation. Every mixture, spatial,
density and rounding error is included, with an analytic bound at infinity.
Combined with exact amplitude homogeneity, this rejects universal
instantaneous monotonicity of the completed pressure/receiver stock on
unforced data. The finite full-datum history allowance remains open.
The result uses validated ball arithmetic and analytic arguments; it is
not a new Lean theorem.

The [whole-space regeneration calculation](labs/README.md#whole-space-pressure-regeneration-has-a-controlled-spatial-tail)
provides the exact Gaussian-mixture representation of pressure and its
complete nonlinear variation, together with the analytic tail estimate
used by that certificate.

The [full-tangent diagnostic](labs/README.md#full-initial-tangents-test-pressure-stock-regeneration)
tests the completed pressure/receiver stock using pressure variation from
the full NS velocity tangent. In two Gaussian families, diffusion reduces
the computed stock while nonlinear pressure production has opposite signs.
A large-amplitude case shows growth despite positive viscosity. Grid and
box refinements preserve the signs. The b^2=8 nonlinear coefficient now
has the separate whole-space certificate above; the other reported
coefficients and fixed-amplitude derivative remain numerical. These
results concern differential payment; the full-datum history allowance
remains open.

The [joint pressure/receiver correction](labs/README.md#a-joint-pressure-correction-needs-a-positive-completion)
identifies a pressure cancellation from diffusion of both interacting
factors. The signed correction alone can overwhelm the stock on actual
unforced Gaussian data. A positive cubic completion restores control of
the stock. Its added pressure component has nonnegative weighted diffusion;
the mixed viscous terms remain in the coupled source with pressure,
transport and receiver deformation. Its history payment is open. Exact
symbolic checks support the analytic argument; no new Lean certificate is claimed.

The [pressure-turnover test](labs/README.md#isotropic-energy-does-not-prevent-rapid-pressure-turnover)
constructs actual unforced data with the same initial pressure and isotropic
energy tensor but opposite directional pressure-transfer rates. At fixed
energy, concentration makes even a fixed-scale smoothed pressure change
arbitrarily fast compared with kinetic dissipation. The leading distant
parent is generated at second order in time. Its existing signed memory
allowance still pays it; a bound on instantaneous turnover does not follow.
The joint short-scale history remains open. These are analytic actual-flow
arguments with exact symbolic checks, not new Lean certificates.

The [pressure-channel payment](labs/README.md#coarse-pressure-is-paid-while-both-source-channels-can-increase-the-stock)
bounds the complete pressure smoothed at any fixed spatial scale from the
original kinetic energy. One remaining allowance pays both coarse source
contributions and the known smooth subtraction throughout the domain and
every available prefix. Exact spatial integrals show that swirl-generated and meridional
pressure have opposite signs on a coupled datum; either can increase the
regular stock. The short-scale remainder can exceed all diffusion while
kinetic energy decreases. Its full-datum history payment remains open.
These are analytic results with exact symbolic checks, not new Lean proofs.

The [paid smooth parent subtraction](labs/README.md#a-positive-circulation-weight-pays-the-complete-parent-subtraction)
adds a fixed positive floor to the observer's circulation weight while
retaining the original stochastic density. The resulting physical stock
is regular at the axis and at infinity. Every transport, viscous and
reaction term introduced by subtracting the known generated parent has
an explicit original-energy payment, without a smallness assumption.
The residual pressure has a finite, exact signed pairing and remains the
open history estimate. An isotropic initial energy tensor can conceal
positive local residual pressure work. The bounds and actual-flow tests
are analytic with exact symbolic checks, not new Lean certificates.

The [pressure-tail history](labs/README.md#the-generated-pressure-tail-has-a-finite-history-payment)
uses the established whole-space asymptotic profile to identify a generated
pressure component from the actual energy tensor. An explicit nonnegative
Bellman correction pays its complete signed history from the original
energy, retaining the accumulated tensor across every segment. The full
pressure remainder is still unpaid. The same analysis shows that the
squared pressure diagnostic can become infinite on a smooth unforced flow
while its original signed work stays finite. This failure concerns the
exponent-10/3 density; the original exponent-three choice avoids it.
The PDE arguments are analytic with exact algebraic checks, not new Lean
certificates or an arbitrary-data regularity theorem.

The [integrated pressure test](labs/README.md#whole-space-pressure-can-increase-the-joint-stock)
shows that the joint strain/swirl stock can increase on an actual unforced
history even after all viscous and axis losses, while kinetic energy falls.
The full canonical pressure integral is checked exactly. A complementary
estimate absorbs the derivatives of its observer into diffusion, retaining
a localized pressure-increment cost and the signed cost of the axis
subtraction. Paying that history from the original datum remains open.
The local PDE and limiting arguments are analytic, with exact symbolic
checks and no new Lean declarations.

The [joint strain/swirl perspective](labs/README.md#a-joint-strain-and-swirl-perspective-cancels-direct-amplification)
cancels direct quadratic amplification using a positive density transported
by the same actual axisymmetric fluid. Its physical-volume diffusion is
nonnegative, including an axis loss. Paying the remaining signed pressure
work would give an angular-velocity Serrin continuation bound. An exact
Gaussian test shows why the pressure needs retained orientation and hidden
parents: identical scalar measurements and energy can give opposite local
rates. The pressure-history payment remains open. These equations, tests
and conditional continuation arguments are analytic with exact checks,
not new Lean certificates or a general three-dimensional regularity proof.

The [generated core-inflow test](labs/README.md#generated-core-inflow-can-be-strong-while-its-signed-history-is-paid)
separates the pointwise inflow cap from the signed core cost it was meant
to control. An actual pure-swirl flow can generate arbitrarily strong
inward motion inside every radius permitted by the prescribed energy rule,
while its swirl-weighted core compression remains favorable. A uniform
local argument retains this favorable sign simultaneously for all radial
cutoffs. It extends the first-return sign for radially decreasing swirl
profiles to the actual joint-stock consumer. The interval is local in
rescaled time; later renewal and arbitrary-data continuation remain open.
The calculation and interval proof are analytic with exact checks.

The [critical circulation/swirl test](labs/README.md#coupled-circulation-and-swirl-stocks-can-grow-while-energy-falls)
shows both scale-invariant stocks increasing together on an actual unforced
axisymmetric history. No nonnegative constant weighting makes their sum
monotone on all such flows. A complementary estimate pays all meridional
compression outside a cylinder from the original circulation maximum and
kinetic energy. The cylinder may shrink with energy under an explicit rule;
one nonnegative reserve pays the complete exterior history. Compression
inside the core remains as a signed defect. These analytic results retain
the full coupled equations and have exact checks; neither propagation of
the core condition nor arbitrary-data continuation is established.

The [multiscale renewal test](labs/README.md#actual-multiscale-bursts-have-a-geometric-charge-that-energy-misses)
constructs any prescribed finite number of stretching episodes in one
globally regular unforced whole-space flow, with uniformly bounded initial
kinetic energy, which can be normalized to exactly one. The packets are
prepared in the initial datum, and finer packets act earlier; this is not
a dynamically generated infinite cascade.
An existing critical no-swirl circulation norm records their total initial
resource. Viscous loss across retained vorticity nodes charges every episode
by an amount independent of scale. This supplies an actual geometric
payment in that class and tests the weaker kinetic-energy toll. The argument
uses established no-swirl theory and finite-profile stability; its PDE
steps remain analytic, supported by exact Gaussian and scaling checks.

The [band-enclosure escape test](labs/README.md#a-paid-band-can-lose-its-geometric-enclosure-while-the-reserve-still-pays)
refutes automatic propagation from initial confinement under the specified
energy-priced widening rule. An actual smooth unforced history generates
two daughter directions which no affordable coordinate band and prescribed
single-axis core can jointly enclose. The daughters' first self-stretching
coefficient is positive; most comes from the pre-existing parents. Their
integrated work can exceed the full viscous cost, while the datum-dependent
linear allowance still pays it. The next target is the signed residual
(BE9)--(BE11), which allows temporary geometric failures. The interval
arguments are analytic with exact source checks, not new Lean certificates.

The [spectral-band geometric payment](labs/README.md#spectral-bands-pay-non-mean-daughters-before-the-geometric-remainder)
allows the entire low-vertical-frequency band, or the union of three coordinate
bands, to exchange energy at arbitrary amplitude. A cubic comparison pays
its contribution from full kinetic dissipation on both R3 and T3. The spectral
geometry condition is imposed only on the remaining field. An actual local
history produces a large non-mean daughter while this new remainder stays
controlled. Band width may also grow under an explicit energy-dependent
ceiling whose cost has a finite original-data payment. Proving the remaining
geometry under this paid rule remains open. These are analytic arguments
with exact source checks, not new Lean certificates.

The [pancake estimate with an evolving mean](labs/README.md#large-generated-means-fit-a-geometric-history-payment)
removes the small-exterior requirement from the actual vertical average of
a periodic flow. Its complete internal forcing and reciprocal interactions
have an original-energy payment already established in the library. Applying
the spectral condition only to the oscillatory remainder gives an explicit
nonnegative reserve for signed stretching and a Bellman supersolution.
A genuinely three-dimensional local history generates a large mean while
its oscillatory exterior remains small. Propagating the latter condition
through arbitrary histories remains open. These results are analytic with
exact source checks; the periodic average is not transferred to whole space.

The [quantitative pancake estimate](labs/README.md#spectral-pancake-width-and-a-critical-leakage-payment)
pays stretching on every smooth unforced prefix if the transverse spectral
width grows slower than the three-quarter power of frequency and the complete
exterior stays small in L3. The common spectral axis may change with time.
The bound retains all mixed interactions and gives an explicit gradient-energy
continuation bound. Increasingly thin, energy-normalized whole-space data
show why unrestricted sideways concentration defeats the corresponding
pointwise absorption estimate. Another exact source immediately creates
motion outside its initial spectral region. Propagating the width and leakage
conditions from arbitrary data remains open. The physical estimates and
localization are analytic with exact Fourier checks, not new Lean certificates.

The [actual-return energy test](labs/README.md#actual-pattern-returns-have-no-uniform-fractional-energy-toll)
shows that genuine three-dimensional unforced pattern cycles can lose an
arbitrarily small fraction of their initial kinetic energy while accumulating
a fixed positive maximum-vorticity cost. The three patterns remain separated
modulo every rigid motion of the fixed torus. Initial amplitude grows across
this family; absolute energy loss need not vanish. A uniform fractional-energy
charge per return therefore fails, while the existing parent-history reserve
still pays these regular cycles. The analytic result retains the complete
nonlinear perturbation and does not refute a full-datum allowance or the
signed-renewal target.

The [moving-frame escape bound](labs/README.md#generated-motion-forces-shape-change-even-in-a-moving-rigid-frame)
extends the generated-packet test to a neighborhood of an entire translated
and rotated whole-space shape family. The frame follows the actual fluid;
all coordinate terms are retained and bounded through its matching equations.
A nonnegative local reserve pays the accumulated maximum vorticity during
each continuous visit, uniformly over physical amplitude and scale when
the normalized viscosity is at most one. Later returns can restore the
reserve and still need a payment from the original datum. The slice and
physical bound are analytic, supported by exact symmetry checks; no new
Lean certificate or arbitrary-history bound is claimed.

The [two-observer Bellman obstruction](labs/README.md#two-scalar-observations-admit-a-forced-concentration-history)
shows why matching kinetic energy, the velocity fourth moment and their
genuine instantaneous unforced rates is insufficient for composing fluid
histories. This relaxation admits finite-time concentration and has no
smooth coercive reserve satisfying the stated all-state inequality.
The full velocity lift requires a nonzero force which cancels generated
modes while doing zero net work in both observed budgets. Its integrated
L2 force norm diverges. Retaining a generated packet also bounds how long
an actual unforced history can remain near that normalized shape, in
nonlinear turnover time. Later returns remain open. These whole-space
arguments are analytic with exact Fourier and scaling checks; they are
not an unforced singularity and do not exclude full-state or
compatible-history reserves.

The [adaptive heat-reserve obstruction](labs/README.md#a-later-return-defeats-both-heat-window-and-weight-controls)
allows the initial window to be selected from the complete datum and both
window and weight to change throughout the history. One smooth periodic
datum has zero initial heat-work and intrinsic capacities at every heat
age. Its fourth moment nevertheless exceeds its initial value along an
actual unforced viscous solution. Every nonnegative correction in the tested
family therefore fails to make the reserve nonincreasing. The complete
later return and viscous loss are retained. This is an analytic local
result with exact Fourier checks; an independent initial-data allowance
and arbitrary-history regularity remain open.

The [zero intrinsic-capacity test](labs/README.md#a-zero-intrinsic-capacity-cannot-be-repaired-by-changing-its-weight)
rules out adaptive scalar weights for the latest correction on a prescribed
heat window. Three equal-wavelength input waves have negative intrinsic
work at every heat age, yet their complete generated source renews the
pressure-work reserve. An actual positive-viscosity solution keeps the
added capacity zero while the original reserve increases. No finite scalar
weight can change this. The source's competing decay rates must be retained;
other reserves, datum-selected windows and integrated allowances remain open.
The local PDE argument is analytic with exact Fourier checks, not a new
Lean certificate.

The [intrinsic pressure-work capacity](labs/README.md#a-reserve-for-the-next-pressure-interaction-repairs-the-first-return-but-rebounds)
stores the next nonlinear interaction and repairs the entire oblique
family's initial reserve growth, at arbitrary amplitude. The complete
next return nevertheless makes this corrected reserve rebound along the
same unforced viscous history. The moving heat window and the initial
viscous loss are retained. One explicit state rules out every constant
nonnegative weight, including a datum-selected weight; a full-datum integrated
allowance remains open. Exact arithmetic supports the local analytic
argument; no new Lean certificate is claimed.

The [oblique cyclic renewal law](labs/README.md#oblique-cyclic-geometry-renews-both-intrinsic-and-covariance-work)
separates two parts of the remaining short-age problem. An unbounded
family starts with zero pressure at every heat age, but its complete
three-parent cycle immediately creates pressure. Both intrinsic and
covariance contributions renew the heat-work reserve; the intrinsic
term has the leading short-age order. Thus a bounded covariance-only
payment misses that term. Exact family formulas retain the physical
metric, all generated modes and positive viscosity. The actual local
interval argument remains analytic; no arbitrary-history bound follows.

The [finite heat-window renewal payment](labs/README.md#resolved-nonlinear-renewal-has-an-original-energy-payment)
pays the absolute self-renewal at all auxiliary diffusion ages beyond any
fixed positive cutoff, on every available unforced history. It also pays
the pressure work entering a truncated reserve through that cutoff.
A backward-moving heat window cancels the crossing term exactly. The
remaining short-age nonlinear budget has a continuation consumer and is
still open; shortening the window alone does not prove its payment.
The physical estimates are analytic with exact Fourier and clock checks.

The [evolving filtered-parent payment](labs/README.md#evolving-filtered-parents-have-one-full-energy-payment)
extracts the current coarse parent from the actual full fluid. At any
fixed positive scale, its complete source and mixed interactions have a
payment from one decreasing full-energy reserve and a datum-controlled
Gronwall factor, without smallness or a favorable transfer sign. The
nonorthogonal cross energy and covariance feedback are retained. The
remaining self-renewal of the unresolved fluid has an explicit
continuation consumer, but its all-prefix bound is open. Refining the
scale has an additional cost. The physical estimates are analytic with
exact Fourier checks, not new Lean certificates.

The [Gaussian covariance renewal test](labs/README.md#gaussian-covariance-can-add-to-nonlinear-heat-history-renewal)
retains the exact difference between heating a nonlinear source and
interacting heated fields. On a complete shape interval, this covariance
adds a strictly positive amount to the reserve's renewal; an analytic
transfer realizes it in actual generated unforced motion. A cyclic family
instead loses exactly one seventh of its positive intrinsic comparison.
The work depends on the alignment of anisotropic covariance with the full
pressure response. Its physical evolution retains diffusion and nonlinear
regeneration; arbitrary-history payment remains open. These are analytic
results with exact Fourier checks, not new Lean certificates.

The [heat-work parent payment](labs/README.md#original-heat-parents-have-a-payment-in-the-heat-work-reserve)
controls the original source and every mixed parent contribution to the
new reserve, on both whole space and the mean-zero torus. It retains the
transport-pressure and heat commutators. Heat smoothing, the original
kinetic-energy bound and a fraction of quartic diffusion pay these terms
on every available prefix, without smallness. A finite-horizon allowance
for nonlinear renewal by the generated motion remains open. The general
estimates are analytic, supported by exact identities, not new Lean
certificates.

The [joint cyclic cancellation](labs/README.md#complete-cyclic-parents-deplete-the-first-generated-heat-work)
retains the full evolving parents in an arbitrary-strength three-shear
family. Their complete first pressure-work response is strictly depleting,
even where the isolated generated motion has positive self-renewal.
A datum-controlled local remainder covers every auxiliary heat age and
bounds the generated heat-work capacity by a constant times t^(29/3).
This is an analytic local result with exact polynomial certificates;
later renewal and arbitrary-horizon payment remain open. No new Lean
certificate or amplitude-smallness assumption is used.

The [heat-work reserve](labs/README.md#a-heat-work-reserve-can-be-rebuilt-by-unforced-motion)
stores all positive fourth-moment pressure work along a field's complete
free-diffusion history. Diffusion spends it exactly, but unforced motion
can rebuild it while losing kinetic energy. An exact family and an analytic
transfer to actually generated motion refute automatic viscous payment of
that replenishment. Joint parent contributions remain essential. These
are analytic results with exact Fourier checks, not new Lean certificates.

The [signed generated-velocity fourth moment](labs/README.md#signed-fourth-moment-work-retains-a-weaker-physical-payment-target)
pays all original heat couplings at arbitrary amplitude and leaves a
signed self-pressure budget with a direct continuation consumer. Earlier
pressure-gradient examples initially deplete this signed work. A separate
mean-zero shear and fast receiver generate the opposite sign; a viscous
interval argument refutes zero payment for the specified weight. The
full-datum allowance remains open. These are analytic results supported
by exact complete Fourier calculations, not new Lean certificates.

The [complete scalar-control envelope](labs/README.md#an-exact-control-envelope-rules-out-every-scalar-schedule-in-the-unit-interval)
rules out the tested leading pressure allowance for every measurable
weight in[0,1], including feedback with access to the future. Exact
positive convolution kernels bound all possible benefit from early
negative work. A uniform analytic remainder gives one finite violating
time for all those choices on an actual regular flow. This closes a
control loophole in that allowance; the nonlinear source-work payment
for a larger reserve remains open. No new Lean certificate is claimed.

The [joint generated-pressure test](labs/README.md#retaining-mixed-pressure-does-not-universally-repair-the-original-stock)
retains a controllable fraction of the mixed pressure in the generated
pressure observation. It repairs one shape's leading allowance on a whole
interval of weights, while two other actual regular-flow families defeat
every constant real weight, including a weight chosen from the datum.
Sixteen prescribed time schedules also fail their respective leading
allowances. The complete pressure evolution identifies the observer-change
cost and gives it a separate original-data payment; the nonlinear source
work remains open. These are analytic results with exact checks, not new
Lean certificates or singularity constructions.

The [original-heat pressure separation](labs/README.md#original-heat-interactions-have-an-arbitrary-data-payment)
pays the heat pressure and every mixed pressure interaction with the generated
motion from the full initial datum, on each prescribed horizon and without
smallness. The solenoidal Lie-bracket identity already present in the Lean
library removes a derivative from the mixed term. Pressure produced by the
generated motion itself remains unpaid. Its first complete feedback exceeds
the allowance predicted from the first generated parents, even though their
return is depleting. A uniform small-data remainder turns this into failure
of that particular stock on actual regular flows. The general payment,
stock failure and continuation connection are analytic, not new Lean certificates.
A [short pressure-cost enclosure](labs/README.md#enclosing-a-finite-amplitude-pressure-prefix)
uses the same cancellation and retains the complete nonlinear residual.

The [finite-amplitude pressure-gradient test](labs/README.md#finite-amplitude-histories-of-the-joint-pressure-gradient-stock)
retains the same original allowance while increasing the strength of the
three interacting parents. A bounded numerical sweep preserves the observed
saving through a computed tail-entry point, with separate grid/time checks
of the early pressure-producing interval.
An analytic comparison connects the pressure-cost error to the existing
velocity-error and viscous-dissipation controls. The numerical prefixes are
not yet continuum enclosures; arbitrary-data payment remains open.

The [joint pressure-gradient stock](labs/README.md#whole-history-pressure-payment-depends-on-the-joint-parent-strengths)
integrates through the entire viscous decay, including source creation and
the return into the original parents. An initially favorable example later
exceeds its cubic forecast's total allowance. A different joint balance of
the same three parents gives an all-time original-stock payment, with a
uniform analytic remainder in a small-data neighborhood. This pressure clock
feeds the existing stochastic continuation consumer. The result tests actual
complete histories, but does not leave the small-data regime or provide a
new Lean certificate.

The [pressure-source return test](labs/README.md#pressure-producing-capacity-can-renew-before-its-original-modes-recover)
follows the resource suggested by the preceding pressure-storage obstruction.
Generated source modes can outweigh a depleting return into the original
source. Including material transport reverses some comparisons, but an
explicit oblique example remains adverse at every positive viscosity.
A separate analytic estimate connects an accumulated source bound to the
existing pressure-clock continuation criterion. That original-data payment
remains open. Exact NS coefficients support the short physical comparisons;
these are not new Lean certificates or singularity constructions.

The [adaptive pressure-subtraction test](labs/README.md#bounded-adaptive-pressure-subtraction-cannot-pay-the-oblique-return)
tests an evolving signed correction whose spatial integral remains
coercive. Actual unforced flows starting with zero pressure defeat every
weight in the proposed range on a positive-viscosity interval, even if
the weight has access to the future. Exact generated-pressure coefficients
and a uniform local Taylor argument retain the initial viscous loss.
The failure concerns this bounded correction and its original allowance;
a larger full-datum reserve remains open. The physical interval argument
is analytic, not a new Lean certificate or a numerical PDE enclosure.

The [quadratic pressure-storage test](labs/README.md#pressure-and-speed-grow-in-every-positive-quadratic-observation)
gives an explicit family of actual unforced NS initial states for which
every fixed positive quadratic form in squared speed and canonical
pressure increases, including coefficients selected from that datum.
The complete derivative retains viscosity and all generated pressure.
Opposite velocities have the same initial pressure and speed but reverse
the nonlinear feedback. The planar member has an independent all-time
vorticity reserve for the pressure-amplitude clock; the corresponding
arbitrary 3D payment remains open. These are analytic conclusions with
exact polynomial checks, not new Lean certificates.

The [time-reversal pressure estimate](labs/README.md#time-reversal-removes-a-derivative-from-the-pressure-history-bill)
reuses the classical forward/backward martingale argument on the same
incompressible stochastic history. It replaces a pressure-gradient cost
by a pressure-amplitude clock, retaining the correlation of the two
martingales and the full evolving source. Its full 3D comparison consumer
needs fewer spatial derivatives of the velocity error. The clock's
original-data payment remains open; the stochastic theorem and consumer
are analytic, with exact algebraic checks, not new Lean certificates.

The [interacting planar pressure reserve](labs/README.md#an-interacting-planar-reserve-pays-adverse-pressure-sampling)
pays the entire stochastic pressure history of arbitrary smooth planar
parents and passive vertical receivers, with no smallness assumption.
Its original allowance is a fixed torus constant times the initial
vorticity L-infinity norm times its L2 norm, divided by viscosity.
An exact example has adverse fluid-versus-Brownian sampling while still
satisfying that all-time payment. The full 3D extension retains three
unpaid contributions: parent replenishment, Reynolds pressure and
fluctuating pressure. This is an analytic consumer of classical planar
estimates with exact algebraic checks, not a new Lean regularity theorem.

The [same-pressure sampling comparison](labs/README.md#pressure-production-and-stochastic-sampling-have-distinct-signs)
separates evolving pressure production from the paths that sample it.
On actual smooth, zero-mean unforced flows, fluid drift can either increase
or decrease the fourth pressure-impulse moment relative to drift-free
Brownian sampling of that identical pressure. Exact viscosity-polynomial
jets identify the competing terms: a positive mixing form and a signed
correlation with the changing pressure source. Thus Brownian-only
domination cannot replace the actual history target. The local physical
comparison is analytic, supported by exact checks, not Lean-certified.

The [finite-amplitude pressure test](labs/README.md#finite-amplitude-tests-of-the-original-oblique-pressure-stock)
keeps one original parent geometry and increases its strength. Numerical
histories through time one half remain below the original leading stock;
the strongest tested amplitude has a substantially larger relative saving.
Grid refinement supports this observation but does not give a continuum
enclosure. The existing analytic pressure-impulse criterion makes this a
direct continuation target: an original-data fourth-moment bound uniform
over all available prefixes would control velocity in L4 and hence
enstrophy. Arbitrary-data payment and formalization of that stochastic
bridge remain open.

The [complete cancellation boundary](labs/README.md#the-complete-cancellation-boundary-retains-the-original-payment)
now has a strictly negative next pressure correction for every ratio of
the remaining two parents. The preceding correction also has a negative
late tail throughout that boundary. A uniform analytic remainder then
pays the original cubic-pressure stock for every time, for each fixed
shape at sufficiently small amplitude. Together with the strict-sign
cases, this classifies the leading stock throughout the three-parent
family in the small-amplitude regime. Exact full-history coefficients
support the analytic result; it is not a new Lean theorem or an
arbitrary-data continuation bound.

The [stronger oblique prefix](labs/README.md#arithmetic-enclosure-of-the-stronger-oblique-prefix)
now has a positive generated velocity receiver and paid pressure history
through time 1/64 at amplitude eight and viscosity one. Two consecutive
intervals retain all sixteen fields, exact shared endpoints and accumulated
errors. This is an analytic/computational enclosure under the stated
arithmetic model, not a Lean certificate. Later returns, the global tail
and arbitrary-data payment remain open.

The [relative-vorticity comparison](labs/README.md#relative-vorticity-controls-a-retained-pressure-history)
retains an exact curl/transport cancellation and lowers the growth loss
available to the existing physical error bound. Its full curvature work
and dissipation feed the same inherited pressure history. Exact algebra
and outward scalar checks support the analytic estimate. Replaying the
stronger oblique history improves the comparison substantially. The earlier
coarse spatial residual obstruction led to the refined finite prefix above;
the later sign-return history remains unenclosed. This is not a fluid
counterexample or an arbitrary-data reserve.

The [slow-parent calculation](labs/README.md#a-fast-receiver-leaves-a-slower-pressure-parent)
identifies a four-step transfer from an oblique receiver into a slowly
decaying mode. On actual sufficiently small unforced flows, its new
pressure tail eventually exceeds every fixed multiple of the original
cubic pressure forecast. The integrated corrected stock above that
forecast still pays these small flows. This separates failure of a decay
profile from failure of an accumulated allowance. Stronger-amplitude
numerical histories test the latter without resetting their moments;
they remain unenclosed. The arbitrary-data payment is open.

The [complete oblique stock calculation](labs/README.md#an-adverse-return-consumes-additional-original-pressure-stock)
shows that the adverse correction persists over the whole viscous clock.
For actual sufficiently small flows, the exact cubic forecast's total
stock is eventually exceeded. A larger stock, containing the full first
nonlinear correction and a controlled remainder margin, pays all times.
Exact differential certificates and independent Brownian integration
support the analytic result. The small-amplitude restriction remains;
the coarser Wiener allowance and arbitrary-data payment are not refuted.

The [oblique-parent test](labs/README.md#oblique-parents-reverse-the-pressure-history-correction)
shows where the orthogonal return law stops applying. An explicit sheared
cyclic datum has a favorable signed contribution, but its two positive
costs exceed that payment. The complete pressure history exceeds its
correctly matched cubic heat forecast on an actual initial interval at
every positive viscosity. Scaled copies satisfy an explicit global
diffusion payment, so this comparison failure also occurs in globally
regular flows. A larger full-datum allowance remains possible.

The [unequal-scale pressure return](labs/README.md#a-complete-pressure-return-depletes-across-unequal-scales)
proves a favorable initial comparison for an unbounded cyclic family,
with arbitrary independent parent strengths and positive viscosity.
The complete pressure-impulse correction has an explicit negative sign
even at the scale ratios where the earlier pressure-parent energy reserve
increases. Equal strengths admit a uniform signed margin for this return.
The actual local interval is analytic; later returns and arbitrary-horizon
payment remain open.

The [complete pressure-history comparison](labs/README.md#enclosed-pressure-controls-with-inherited-history)
now combines complete residuals, field majorants and outward scalar controls
for one shared reference. Two consecutive reciprocal-flow intervals pass
with identical shared endpoints and inherited moments and trajectory error.
This certifies a finite physical prefix under the analytic comparison and
stated arithmetic model. The full prefix through a small-gradient tail
is still under test; the arbitrary-data payment remains open.

The [complete pressure operator enclosure](labs/README.md#full-operator-balls-for-shared-pressure-histories)
retains every generated Fourier mode and encloses reconstruction, transforms,
pressure and all conditional-moment sources for the same shared reference.
Independent rational checks cover all sixteen time coefficients. On the
first grid-40 reciprocal interval, the largest relative arithmetic allowance
is 4.73 percent, in the velocity H1 residual. The complete history consumer
above adds field majorants and scalar controls to those residuals.

The [correlated residual arithmetic](labs/README.md#outward-arithmetic-for-correlated-pressure-residuals)
encloses signed inner products and complete time-polynomial norm bounds
with explicit rounding errors. Its first reciprocal-flow interval loses
less than seven parts per billion to this scalar arithmetic. A shared
Bernstein reference preserves exact interval seams and inherited moment
means. The physical operator's coefficient errors and complete pressure
controls remain separate obligations; no stronger prefix is certified.

The [complete-time residual test](labs/README.md#a-pressure-history-residual-needs-its-complete-time-polynomial)
exhibits an exact decaying NS shear whose inaccurate quintic reference
has zero residual at both endpoints and the midpoint, even with matching
endpoint equation jets. The repair retains the complete time polynomial
and its signed coefficient correlations. Four interval probes of the
reciprocal flow support the resulting bounds; full-history and arithmetic
enclosures remain separate obligations.

The [pressure-history comparison](labs/README.md#pressure-history-comparison-from-velocity-error-dissipation)
connects velocity-error dissipation to the original stochastic pressure
impulse. A coupling with shared Brownian noise accounts separately for
changed pressure and changed trajectories; the retained conditional moments
have a triangular residual estimate. The existing small-gradient tail also
pays the future pressure impulse, including its mixed costs with the past.
This is an analytic sufficient condition with exact algebraic checks.
Its stronger-amplitude numerical tests sample time residuals and do not
certify an actual prefix. The arbitrary-data payment remains open.

The [reciprocal heat-payment test](labs/README.md#whole-time-heat-payment-for-reciprocal-parents)
proves that the complete first nonlinear pressure correction stays favorable
for every time and every ratio of two interacting parents. Exact differential
cascades certify the coefficient signs. A uniform analytic remainder gives an
actual all-time comparison with the original Brownian heat forecast in a small
two-amplitude disk, with a finite stock determined by the original data.
Separating the coefficient into pressure-source and transport contributions
exhibits a positive shared cost that must remain in their joint payment.
The stronger-amplitude comparison remains open. A conditional finite-time
handoff pays its tail while retaining the accumulated impulse; numerical
prefixes do not certify that handoff. The physical identification and remainder
are analytic, not new Lean certificates.

The [joint renewal test](labs/README.md#balanced-reciprocal-parents-defeat-the-joint-rational-allowance)
finds a whole-fluid failure of the two-coefficient rational pressure allowance.
For an interval of balanced three-dimensional parent ratios, the first complete
correction is favorable but the next complete return exceeds the predicted
saving. The comparison fails on an actual short unforced interval at every
positive viscosity. Nonconstant original labels related by physical symmetry
have equal costs, so summing their allowances gives the same failure with zero
pooling loss. Exact full-output jets and a separate viscous moment recurrence
are checked; the actual interval and symmetry identification remain analytic.
This refutes the specific rational payment, not the coarser heat forecast or
the existence of a larger full-datum history bound.

The [labelled later-return test](labs/README.md#a-retained-label-can-pass-its-initial-payment-and-fail-later)
shows why retaining component labels does not finish the pressure payment.
On one actual unforced positive-viscosity history, the complete two-coefficient
component allowance is initially favorable and is later exceeded. The strict
crossing persists for genuinely three-dimensional perturbations with generated
reciprocal parents and positive initial growth of integrated vortex stretching.
The reference crossing and full NS jets have exact algebraic checks; smooth
labels, viscous persistence and the fixed-interval perturbation argument remain
analytic. This refutes the componentwise extension, not the total sum of all
component allowances or a larger full-datum reserve. The explicit planar
reference still has a finite all-time pressure allowance.

The [rotating-core pooling test](labs/README.md#a-rational-pressure-allowance-is-not-preserved-by-pooling-rotating-cores)
refutes a universal extension of the first-two-coefficient rational pressure
allowance. Each isolated smooth core passes its local comparison; combining
two cores at different rotation scales reverses it on an actual unforced
positive-viscosity interval. The first two Euler time coefficients stay fixed
while the next one grows. These planar flows have zero vortex stretching.
An exact mixture identity identifies the cost lost by pooling; labelled
moments restore a valid initial comparison on the same actual fluid history.
Their subsequent coupled payment remains open. The result is analytic with
exact algebraic checks, not a new Lean certificate or a refutation of the equal-scale cyclic
envelope or of arbitrary-data regularity.

The [complete cyclic history certificate](labs/README.md#complete-time-slabs-and-rounding-in-a-cyclic-history-certificate)
closes an all-time signed-renewal budget for the actual unforced periodic
datum `(sin y,sin z,sin x)` at viscosity 1/4. Its allowance is 132.
The same comparison accepts every smooth mean-zero solenoidal perturbation
with gradient L2 norm at most `2^(-28)`, retaining the additional original-datum
term `2H|g(u0)|`. Entire time slabs, generated modes and rounding errors
are enclosed before a small-gradient tail proves global continuation.
This is an analytic/computational certificate under an explicit IEEE
arithmetic model, not a new Lean certificate. The arbitrary-data history
bound and the sharper pressure-moment comparison remain open.

The [preceding prefix calibration](labs/README.md#prefix-validation-with-transport-cancellation)
explains the choice of control: an unsigned Fourier estimate can grow
enormously between two exact decaying unforced flows. The coupled energy
and gradient comparison retains transport cancellation, strain, Hessian
and viscous costs. Its complete-time validation is the certificate above.

The [pressure-history handoff](labs/README.md#a-finite-pressure-history-handoff-and-a-projection-blind-spot)
gives an explicit future reserve once an actual mean-zero periodic flow has
velocity Fourier norm below viscosity, in period-2pi units. It pays the full
remaining pressure impulse while preserving the original accumulated impulse
and its mixed fourth-moment costs. Entry and the preceding history still need
certified bounds. A separate exact cellular example exposes a measurement
failure: a projection can reproduce the velocity exactly while deleting its
entire pressure history. The new full spatial residual checks those hidden
channels. The physical reserve is analytic; the algebraic fixtures and
numerical discovery prefixes are not new Lean certificates.

The [pressure-parent renewal test](labs/README.md#renewal-beyond-the-first-pressure-generating-parent)
finds the limit of that extra reserve. Across an unbounded cyclic frequency
family, the first return into the original pressure-generating field is
depleting. Newly generated Fourier components nevertheless outweigh it from
frequency six onward. On one actual viscous interval both retained-energy
concentration and the full pressure-generation norm increase, defeating
every nonnegative weighting of those two norms. The old-direction return
pays only three quarters of the generated square in the high-frequency
limit. This is an analytic obstruction to the monotone reserve, with exact
symbolic checks; a larger original-data history allowance remains open.

The [joint pressure correction test](labs/README.md#joint-pressure-corrections-and-a-paid-generating-parent)
rules out every fixed positive quadratic combination of retained energy and
pressure as a universally decreasing reserve. One actual coupled flow defeats
all such weights on the same positive-viscosity interval, including weights
chosen from its original datum. Remembering the pressure-generating parent
repairs that interval: its initial squared size pays the signed concentration
work while retaining half the diffusion. The amplitude-scaled allowance is
explicit, but the conservative time window is not numerically evaluated.
Later renewal of that parent remains unpaid. These are analytic interval
results with exact full Fourier checks, not new Lean certificates or a
counterexample to global regularity.

The [retained-energy alignment test](labs/README.md#retained-energy-concentration-and-pressure-alignment)
removes part of the stochastic fourth-moment overcharge while keeping a
sufficient continuation norm. For arbitrary-amplitude ABC histories, the
retained energy follows the heat equation even when the fourth moment grows.
General single-shell Beltrami histories have an explicit all-time payment for
their alignment defect. Changing cyclic parents can nevertheless make the
weaker concentration first decrease and then exceed its initial value.
The complete pressure defect and its signed work remain the arbitrary-history
obligation. These are analytic results with exact algebraic checks, not new
Lean certificates or a proof of arbitrary-data global regularity.

The [combined pressure envelope](labs/README.md#a-combined-pressure-bound-beyond-the-first-return)
pays the favorable and adverse feedback terms together. It gives an analytic
all-time comparison at small amplitude and a uniform initial interval on the
nonlinear clock for strong amplitudes. An actual small-amplitude history
nevertheless violates instantaneous domination of its cost rate by the
envelope's rate: earlier savings must remain available to later intervals.
The full value bound at arbitrary amplitudes and horizons remains open.
Exact sign certificates and numerical discovery prefixes accompany the
analytic arguments; none is a new Lean certificate.

The [complete cyclic pressure payment](labs/README.md#whole-time-cyclic-pressure-depletion-and-a-funded-continuation)
extends the favorable local return to an all-time comparison for sufficiently
small, independently varying cyclic parent amplitudes in two frequency
patterns. Exact exponential-polynomial certificates prove the sign throughout
time; an analytic remainder estimate then controls the actual nonlinear
flows. Their pressure-impulse allowance is proportional to the fourth power
of the product of all three parent amplitudes. The signed reserve keeps the
existing moments across continuation seams. The smallness condition remains
essential to the proof, and its conservative radius is not numerically
evaluated. The next nonlinear correction is strictly positive throughout
time, so successive feedback terms do not all deplete the observation.
These are analytic physical results with exact algebraic checks,
not new Lean certificates or an arbitrary-data bound.

The [pressure-impulse return test](labs/README.md#pressure-impulse-returns-and-the-failure-of-local-funding)
retains the complete stochastic fourth moment on two cyclic flow families.
Their first correction beyond a matched generated-pressure forecast is
strictly depleting for every positive viscosity, including the mixed-scale
datum that defeated an earlier entropy sign rule. Separately, one fixed
smooth three-dimensional datum generates pressure acceleration where its
initial velocity vanishes to high order. Neither its velocity fourth moment
nor its pressure-impulse fourth moment can be bounded pointwise by any finite
multiple of the passively transported initial fourth moment. This rules
out that local funding rule; a global reserve with spatial exchange remains
possible. The actual short-time arguments are analytic with exact checks,
not a global history bound or new Lean certificates.

The [physical Bellman payment](labs/README.md#a-bellman-payment-for-complete-stochastic-pressure-histories)
bounds the full stochastic pressure history for steady Euler Laplace
eigenparents, including genuinely three-dimensional ABC flows of arbitrary
amplitude and common wave number. Its initial allowance is independent of
viscosity and that wave number. A second application allows an arbitrary
smooth passive vertical component; the stronger entropy can increase there
while its entire history remains paid. The Bellman state retains both the
accumulated martingale and its unspent variation. For arbitrary flows,
the exact remaining target is an initial-data bound on the fourth moment
of the actual pressure impulse. Energy already pays its second moment.
These stochastic and PDE results are analytic with exact checks, not new
Lean certificates or a bound for mutually regenerating parents.

The [stochastic pressure-history entropy test](labs/README.md#stochastic-pressure-histories-entropy-and-a-coercive-moment)
identifies an auxiliary velocity distribution whose mean is the actual fluid.
Gaussian relative entropy pays its full spatial Fisher dissipation from the
original kinetic energy, but cannot control concentration. Quartic Gibbs
entropy controls a sufficient continuation norm; its pressure work remains
unpaid. An actual unforced positive-viscosity history makes this stronger
entropy first decrease and then exceed its initial value. Even an exact
decaying shear generates a nonzero third central moment, ruling out an
automatic Gaussian closure. The density, entropy and interval arguments are
analytic, supported by exact moment and complete Fourier-jet checks; they
are periodic statements, not new Lean certificates or a blowup construction.

The [cyclic entropy law and its scale boundary](labs/README.md#cyclic-entropy-depletion-and-its-scale-boundary)
proves a negative first nonlinear velocity-moment return for every positive
choice of three cyclic parent amplitudes at a common spatial scale. Changing
one parent's spatial frequency from one to four reverses that sign. A uniform
local comparison gives actual unforced positive-viscosity histories whose
regularized cubic velocity moment first decreases and then exceeds its initial
value, while kinetic energy decreases. These analytic results retain every
generated mode; the algebra and weighted enclosures are exact. They distinguish
a valid family depletion law from a false extension across scales. Payment
for repeated arbitrary histories remains open; no blowup is constructed.

The [complete Bernoulli return test](labs/README.md#pressure-storage-and-the-complete-bernoulli-return)
separates an observer cost from physical amplification. On one actual
three-dimensional unforced viscous history, two positive pressure completions
increase while a regularized cubic velocity moment lies below its heat
forecast. Removing the initial pressure-variance term cancels the second
return but leaves an adverse fourth return. Exact weighted enclosures and
a uniform smooth inviscid comparison establish the signs on an actual
positive-viscosity interval. These analytic results rule out the stated
monotone reserves; they do not refute a full-data allowance or regularity.

The [cubic pressure reserve](labs/README.md#cubic-velocity-pressure-work-and-a-bernoulli-reserve)
uses a critical quantity preserved by incompressible material pullback.
A nonnegative pressure correction pays its full signed history, including
half the viscous cost, for the stated cellular flows with an arbitrary smooth
vertical component. The cubic quantity itself can grow on these actual viscous
flows. A separate genuinely three-dimensional datum generates pressure from
zero and violates the proposed automatic sign of the correction's defect.
The exact arbitrary-flow defect and its enstrophy-continuation consumer are
identified; a full-data payment for that defect remains open. These are
analytic arguments with exact checks, not new Lean certificates. The imported
forced construction has finite direct cubic force work but must violate
this signed pressure budget, providing a separate adversarial test.

The [material critical-history test](labs/README.md#material-coordinates-critical-diffusion-and-a-paid-physical-metric)
shows why following the actual fluid does not remove the geometric cost:
an unforced positive-viscosity flow can increase its critical norm measured
in fixed material labels, even with zero pressure. Retaining the evolving
physical metric restores the negative diffusion term. For arbitrary smooth
profiles transported by the stated shear, its deformation has an explicit
original-data payment for the complete continuation criterion. The exact
metric identity also holds along arbitrary smooth NS prefixes; paying its
deformation under unrestricted interacting parents remains open. These are
analytic statements with exact checks, not new Lean certificates.

The [relative self-work history test](labs/README.md#a-change-of-self-interaction-sign-with-finite-history-payment)
finds a sign reversal on an actual unforced viscous history: an initially
Beltrami perturbation first depletes, then produces, critical difference
mass through its own nonlinear term. An explicit commutator bound nevertheless
pays its absolute self-work over all time, for arbitrary smooth passive
profiles in the specified shear class. The payment uses original directional
variation and the parent's finite lifetime. Small genuine 3D feedback retains
the sign reversal and a full-history allowance; unrestricted parent renewal
remains open. These are analytic arguments with exact polynomial and rational
checks, not new Lean certificates.

The [critical shear-mixing test](labs/README.md#critical-amplification-in-a-paid-unforced-mixing-history)
shows that a fixed multiple of the initial critical mass is also insufficient.
Actual globally regular periodic flows can amplify that mass by an arbitrarily
large factor. A stochastic representation nevertheless gives an explicit
nonlinear initial-data allowance for the entire triangular reference history.
The amplification persists in genuinely three-dimensional, globally regular
perturbations with nonzero feedback into the original shear. A more
conservative allowance pays their complete coupled histories under the
explicit stability condition, which can require a very small perturbation.
No arbitrary-coupling payment is asserted. These are analytic PDE arguments
with exact checks, not new Lean certificates.

The [critical-history concentration test](labs/README.md#fixed-energy-concentration-of-the-actual-critical-history)
limits what energy-funded boundary observations can establish. On both R3
and the fixed torus, actual smooth unforced solutions with unit initial
kinetic energy can have arbitrarily large short bursts in the critical
history cost (494). Their kinetic energy loss tends to zero along this
family. Therefore a uniformly finite energy-only sum of quartet payments
cannot dominate that cost. An allowance from the full initial datum remains
open; these examples require a payment comparable to its initial critical
mass. The PDE interval and periodization arguments are analytic, supported
by exact source, viscosity-polynomial and scaling checks, not Lean-certified.

The [quartet phase-history bound](labs/README.md#actual-quartet-phase-dynamics-and-a-paid-observation-history)
derives the actual phase torque, shows uniform initial depletion of the
higher-frequency original parents, and tests the proposed angular alignment.
The angular feedback can point toward greater production. For any smooth
unforced periodic history, however, a fixed quartet's weighted rotation and
viscous maintenance have a finite allowance from the full initial energy.
The source includes every surrounding mode. This supplies a concrete paid
joint observation; it does not control the critical cost at arbitrary scales.
The physical results are analytic with exact algebra checks.

The [phase-sensitive second return](labs/README.md#phase-sensitive-second-return-of-the-complete-helical-flow)
compares actual 3D unforced evolution with its first Picard forecast. Two
families have identical initial spectral energies and helicity: one has a
strictly depleting fourth-order correction to negative-helicity mass, while
the other has a strictly amplifying correction. Both retain every generated
mode and pressure, at arbitrary fixed amplitudes and positive viscosity.
The sign depends on a joint parent phase. Negative mixed feedback alone
does not settle it, because the new second-generation square also contributes.
These are analytic short-time comparisons with exact polynomial checks;
the complete-history continuation allowance remains open.

The [complete-source helicity test](labs/README.md#complete-source-helicity-and-a-paid-changing-geometry)
shows that the full generated field can favor the opposite helicity even
when every initial mode has positive helicity. An explicit 3D periodic
datum and a whole-space localization retain all outputs and pressure.
The two-coordinate calibration nevertheless has an explicit all-time
allowance for the same signed production, at arbitrary amplitude. Thus
the failed source-sign rule does not prevent a complete history payment.
General 3D feedback remains unpaid. These are analytic results with exact
checks, not new Lean certificates.

The [helical renewal test](labs/README.md#helical-geometry-coherent-children-and-a-critical-history-reserve)
uses the classical helical decomposition while retaining the full NS equation.
Two same-sign parent pairs each produce a child with negative-helicity fraction
1/37, but their coherent sum produces an entirely negative-helicity child.
Complete return jets show positive critical storage above the heat forecast.
The exact signed production term has an explicit continuation consumer; its
arbitrary-data history payment is open. The physical arguments are analytic
with exact checks, and no decimated-model theorem is substituted for full NS.

The [fixed-band renewal calculation](labs/README.md#fixed-spectral-bands-and-coherent-generation-of-stretching)
absorbs any fixed finite band of vertical frequencies using the full energy
reserve, while retaining all interactions. Two elliptically polarized
parents generate positive signed stretching in an initially empty tail;
their shared cross term reverses the separate polarization signs. Actual
short unforced histories refute automatic pointwise viscous payment of
that tail. A two-coordinate version nevertheless has an explicit full-data
finite-horizon allowance. The genuinely 3D history payment remains open.
These are analytic results with exact checks, not new Lean certificates.

The [solenoidal geometric observation](labs/README.md#solenoidal-geometric-observations-and-a-complete-two-coordinate-payment)
discards gradients and nonpositive stretching directions before charging
the joint geometry. It has an explicit all-time payment for arbitrary
amplitudes of the known three-component, two-coordinate class, including
positive stretching. Actual 3D hidden modes introduce retained Reynolds
sources; an exact example makes the averaged parent's energy and enstrophy
grow. A logarithmic Fourier estimate nevertheless absorbs the actual
coordinate average using the full energy reserve. The remaining fluctuation
cost retains the full vorticity and curl; its original-data payment is open.
These are analytic arguments with exact checks, reusing the existing
certified Fourier inequality; no new Lean theorem is asserted.

The [physical enstrophy receiver](labs/README.md#physical-enstrophy-receiver-and-a-diffusion-feedback-budget)
retains the actual vorticity weighting in the geometric continuation
estimate. A finite original-data allowance for its cost, even with feedback
below the full normalized dissipation, would close the existing criterion.
The receiver's exact reaction and its concentration/direction costs are
retained. Known decaying eigenflow families have an explicit all-time
payment; the imported forced candidate violates the proposed allowance.
The arbitrary-data unforced payment remains open. These are analytic
arguments with exact checks, not new Lean-certified regularity results.

The [viscous geometric-cost test](labs/README.md#viscous-creation-of-signed-geometric-cost)
shows that diffusion can increase the signed directional observation on
an exact unforced cellular flow with zero actual stretching. The failure
holds at every amplitude and positive viscosity, and persists after
smooth regularization. A complete joint square pays one derivative term
from the existing initial-energy reserve; its angular and pressure
sources remain unpaid. This distinguishes a local diffusion-sign
shortcut from the open arbitrary-history estimate. The new results are
analytic with exact checks, not new Lean-certified physical bounds.

The [signed impulse geometry calculation](labs/README.md#signed-impulse-geometry-and-a-physical-continuation-allowance)
adapts the Chae--Lee geometric energy criterion to the original passive
parent and pressure impulse. A datum-controlled time integral of one
positive signed triple product would give an explicit nonnegative
reserve and the existing signed-renewal continuation allowance on both
domains. The complete pressure and mixed-diffusion sources are retained.
Exact decaying eigenflow families pass the test; actual unforced data
can create positive cost from zero initial impulse; the imported forced
candidate has infinite total cost. The arbitrary-data unforced payment
remains open. These are analytic arguments with exact checks, not new
Lean-certified physical estimates.

The [physical forcing test](labs/README.md#physical-forcing-defects-and-compatible-internal-sources)
shows analytically that the imported whole-space forced candidate defeats
the exact remaining exponential pressure-history bound, although its
direct normalized curl-force contribution has a finite allowance. The
complete reserve acquires an explicit orientation and impulse correction.
For an unforced flow, a fixed Fourier split instead produces two coupled
vorticity equations with opposite internal sources; their cross correlation
is necessary to recover the full squared-vorticity equation. Exact NS jets
and a smooth rotating forced shear check these identities. This identifies
constraints a history payment must use; it does not bound arbitrary
unforced histories or certify a new Lean theorem.

The [original-data boundary estimate](labs/README.md#original-data-boundary-smoothing-and-unrestricted-controls)
pays the endpoint score of every complete backward sampling history
using only the short regular interval guaranteed by the original datum.
A capped age weight gives a uniform payment for all bounded sampling
controls on both R3 and T3, with no controlled-density ratio assumption.
On the torus, kernel composition also pays the uncapped conditional
exponential at this boundary. The revised pressure reserve retains the
cap's derivative and all compatible squares. These analytic results
remove an endpoint cost; the interior pressure-connected stretching
source remains open. The kernel argument itself also allows forcing
outside the certified initial interval, so it cannot alone establish
the unforced regularity conclusion. Exact symbolic checks accompany
the derivation; no new Lean declarations are added.

The [conditional deformation payment](labs/README.md#conditional-deformation-and-an-original-energy-payment)
removes precisely the part of stochastic deformation invisible to all
endpoint observations. On the fixed torus, incompressibility and
drift-independent mixing bound the retained noise's second moment by
the original kinetic energy and viscosity, uniformly over sampling
duration on every available smooth prefix. A whole-space counterpart
uses the existing divergence-free kernel bound. These estimates pay a
terminal directional-score cost for sampling controls whose terminal
density ratio has a prescribed bound. They impose no small-data
restriction on the fluid, but do not pay arbitrarily concentrated
controls or the full integrated stretching source. The elliptic,
stochastic and PDE arguments are analytic with exact algebra checks;
no new Lean declarations are added.

The [projected-noise test](labs/README.md#projected-score-noise-and-conditioning-on-the-endpoint)
retains the complete joint evolution of vorticity direction and score
noise. Its proposed unconditioned exponential moment is infinite on an
explicit, globally smooth, decaying 3D Beltrami flow, while the actual
terminal score remains bounded. A change-of-measure argument identifies
the repeated sampling loops responsible for the failure. An exact
linear density equation retains the endpoint-conditional memory and
gives a sharper replacement for the failed bound. A rotating helical
shear supplies a positive calibration: the controlled directional-score
payment stays finite despite spatially varying vorticity direction.
These results are analytic with exact checks; they refute the tested
stronger noise-moment relaxation,
not the arbitrary-data continuation target.

The [compatible score-control calculation](labs/README.md#compatible-score-controls-and-stochastic-pressure-history)
combines the receiver reserve with relative entropy without spending the
sampling penalty twice. An exact unforced shear shows that the formal
pointwise maximizer need not be the gradient of any density; a retained
projection square measures this incompatibility. A stochastic
integration-by-parts formula identifies the actual score as Brownian
motion, a bounded original passive contribution, and pressure/rotation
noise along the same history. It also gives a finite entrance allowance
for the joint reserve on arbitrary smooth prefixes. Brownian and passive
terms have explicit payments; the remaining exponential noise moment and
the complete stretching history are open. The arguments are analytic
with exact algebra checks, not new Lean theorems.

The [normalized pressure-score calculation](labs/README.md#normalized-pressure-score-histories-and-the-point-kernel-endpoint)
derives the complete directional and mixed pressure equations, retaining
their spatial flux under controlled sampling. Normalization restores a
vorticity-growth factor beside the signed geometric diffusion. An actual
point-source kernel in an exact decaying unforced shear defeats a family
of positive quadratic pointwise Bellman certificates: their source grows
like inverse sampling time, although the pressure impulse vanishes.
The same candidate's terminal cost nevertheless has a finite payment for
every controlled sampling history of that shear, using half the control
penalty. Its stochastic entrance cost is also finite and nonzero. These
results distinguish local certificates from complete history payments;
the general full-datum allowance remains open. They are analytic with
exact algebra checks; no new Lean declarations are added.

The [physical kernel-score budget](labs/README.md#physical-kernel-entropy-and-the-joint-vorticity-score)
pays time-weighted Fisher information for point-source sampling along
arbitrary available smooth prefixes. Its allowance uses viscosity and
the original energy on whole space, and only viscosity and the fixed
domain on the torus. It also pays the time-weighted, uncontrolled
pressure-score observation. A joint vorticity-score equation cancels
explicit strain but retains an adverse geometric diffusion term. An
exact decaying unforced shear increases Fisher information for a smooth
receiver while its pressure impulse stays zero. Removing the time weight
and controlling the full Bellman histories remain open. These results
are analytic with exact algebra checks; no new Lean declarations are added.

The [pressure-impulse receiver calculation](labs/README.md#pressure-impulse-flux-and-the-receivers-entropy)
retains the exact spatial flux of the remaining stretching. Its bulk
derivative terms combine with diffusion into squares; a controlled
receiver retains an additional entropy cost and an orientation-weighted
impulse magnitude. An actual unforced history defeats paying its
remaining exponential moment solely from sampled impulse magnitude:
the former starts at order t^2, the latter at order t^4. Point-receiver
concentration and the full-datum allowance remain open. These are
analytic identities and interval arguments with exact checks; no new
Lean declarations are added.

The [passive-parent Bellman payment](labs/README.md#passive-parent-gradient-payment-and-the-pressure-impulse-remainder)
pays the gradient of the original velocity transported passively along
the actual fluid, including its sampling-control cost. Its allowance
depends on the original velocity maximum, viscosity and horizon, with
no smallness or unknown future norm. It leaves an explicit signed
pressure-impulse reaction, whose exponential history bound would imply
continuation. An actual unforced example makes this remainder positive
immediately. Four Lean inequalities certify the potential and squares;
the PDE comparison, stochastic integration and continuation reduction
remain analytic. The remainder is still open for arbitrary data.

The [signed-reaction calculation](labs/README.md#signed-reaction-renewal-and-gradient-correction)
retains the complete pressure and diffusion in the remaining stretching
reward. A positive gradient correction reverses the highest-derivative
diffusion term and cancels one strain contraction. A universal bound by
the original maximum fails: a family of smooth unforced data exceeds its
initial global corrected maximum for every fixed coefficient. A second
family isolates genuine pressure-driven creation of stretching, with zero initial stretching and
vorticity gradient at the receiver. Lean certifies six scalar ingredients
of the first family's whole-domain bound. Physical identification and
positive-time evolution remain analytic; a full-datum renewal allowance
is not refuted or established by these finite bursts.

The [joint sampling law](labs/README.md#joint-history-change-of-measure-and-velocity-payment)
keeps the metric loss and its sampling drift together. An exact change
of control removes both at the cost of one bounded endpoint term,
preserving the full control penalty. It strengthens the separate payment
below. Initial kinetic energy also pays accumulated velocity magnitude
under these controlled sampling laws. Ordinary stretching remains open;
an actual smooth datum increases its global vorticity maximum immediately.
Lean certifies the two control-shift identities. Path-measure, occupation
and positive-time arguments remain analytic, with exact physical fixtures.

The [metric-loss Bellman estimate](labs/README.md#metric-loss-bellman-payment-and-the-actual-sampling-density)
pays the transported-metric part of directional conversion along every
available smooth unforced history, using an original-data regularizer.
It leaves a quarter of the sampling-control penalty for the ordinary
stretching reaction. An exact density transformation also bounds the
uncontrolled receiver by a killed incompressible diffusion; the whole-space
estimate reuses Hess-Childs--Raquepas--Rowan's concentration theorem.
The remaining stretching and terminal concentration are not paid by these
results. The physical and stochastic arguments are analytic, supported
by exact fixtures; no new Lean theorem or arbitrary-data bound is claimed.

The [vorticity-direction payment](labs/README.md#vorticity-direction-payment-and-the-concentration-obstruction)
reuses Qian's classical vorticity--energy reserve, retaining its geometric
diffusion and nonnegative strain remainder. It pays spatial variation of
vorticity direction along every smooth unforced history, without a frame
normalization. Its local balance retains the actual boundary pressure
flux, whose total absolute cost is bounded at each fixed observation
scale. The directional-conversion equation still retains strain and mixed
frame derivatives. An actual concentrated whole-space family
rules out a universal linear conversion payment from this reserve alone.
The general estimates and positive-time argument are analytic, with exact
fixtures; no new Lean theorem or arbitrary-data bound is claimed.

The [joint covariance reserve](labs/README.md#a-joint-reserve-with-the-evolving-memory-retained)
uses incompressibility and the classical div--curl estimate to retain
pressure without losing derivatives. Mean-frame diffusion pays its gradient
product. Normalizing by the largest frame size reached so far gives a
nonnegative original-data reserve for weighted observations along every
smooth periodic history. The weights weaken as that frame size grows;
controlling this conversion remains open. These are analytic estimates,
supported by exact fixtures, with no new Lean regularity theorem.

The [evolving covariance calculation](labs/README.md#evolving-covariance-compatibility-and-its-pressure-cost)
derives the actual velocity–covariance discrepancy equation and its signed
work identity. Covariance gives a favorable anisotropic diffusion term;
a four-wave family makes the associated pressure-Hessian work larger.
An original background realizes the same pressure excess while enstrophy
increases. This rules out that isolated absorption, while retaining the
full-datum history estimate as the open target. Exact Fourier checks
support the analytic physical arguments; no new Lean theorem is claimed.

The [joint-parent boundary law](labs/README.md#joint-parent-covariance-and-ordered-release-histories)
retains the correlations that jointly determine the released fluid and its
frame memory. It allows an incoming frame and gives a finite strain price
for each actual fast release. A prescribed finite sequence can be realized
with all parents present in the original datum. Changing the release order
can leave the same limiting velocity but different inherited frame tensors
and different ordinary-vorticity conversion. These are analytic physical
limits with exact coefficient and pressure checks. Paying arbitrary later
parents generated by the fluid remains open.

The [inherited-frame calculation](labs/README.md#the-frame-inherited-from-an-oscillatory-parent)
tracks the original transported frame through an actual parent release.
Its mean tends to the identity, but its covariance retains a nonzero
tensor determined by the parent envelope. The release has a finite
integrated strain allowance uniform in the carrier frequency. An explicit
descendant then has decreasing weighted vorticity and increasing ordinary
vorticity along the fluid: the conversion factor worsens. Thus the frame
must retain both its parent history and the later cost of that conversion.
The profile and physical derivatives have exact checks; uniform release
and solution-interval arguments are analytic, not new Lean proofs.

The [source-direction reserve test](labs/README.md#source-direction-reserves-transport-and-schur-elimination)
adds the source's physical time derivative and also tests its transport
adjustment. A positive square locally pays the capacity-return example
below. Another actual released descendant makes every constant positive
quadratic form in either pair grow while core stretching remains costly.
Even minimizing the integrated square over its mixing coefficient at
each time leaves a growing Schur complement. The calculation identifies
the additional work that changing observation weights would have to pay.
These are analytic physical-interval results with exact matrix checks;
the full-datum history allowance and arbitrary-data regularity remain open.

The [source-capacity return](labs/README.md#an-actual-source-capacity-return-with-positive-core-cost)
gives an actual unforced periodic history on which the generated remainder's
source capacity returns to its earlier value while its enstrophy increases
and its remaining stretching cost is positive. The construction retains
the original heat reference and uses the oscillatory-parent release below.
It rules out paying every core-cost interval from a time-independent
function of this scalar capacity alone, even with parameters chosen from
the original datum. The full fluid does not return to its previous state;
its kinetic energy decreases. The interval and release arguments are
analytic, with exact Fourier jets and return brackets, not new Lean proofs.
Reserves retaining additional state or history and the full-datum allowance
remain open.

The [descendant geometry and all-scale absorption](labs/README.md#descendant-source-geometry-and-all-scale-separated-absorption)
identify source deformation as the main positive renewal in the released
adverse phase; covariance reinforces it, and the complete capacity growth
initially accelerates. Separately, an original-data frequency rule absorbs
an unbounded family of sufficiently separated interactions into one eighth
of the remainder's viscous dissipation. It combines disjointly with the
fixed-band payment below and leaves an explicit, smaller core-history
estimate for the same continuation theorem. The released adverse examples
remain in that core. These results are analytic with exact algebra checks;
no arbitrary-data regularity or new Lean certification is claimed.

The [descendant-capacity test and fixed-band payment](labs/README.md#descendant-capacity-renewal-and-a-fixed-band-force-payment)
show that one input phase reversal, preserving every modal energy, can
reverse a released descendant's stretching and capacity-renewal signs.
An actual unforced history defeats every constant normalization beta>=8
and every added nonnegative constant multiple of the source capacity,
at a fixed original-parent parameter. Separately, kinetic dissipation
pays the total low-band force supplied by all high-frequency parents
on every smooth prefix, with a finite original-energy reserve. Using
the full fluid and its original heat reference together also pays a
named portion of the generated-stretching target. The cost of following
finer receiving scales remains explicit and unpaid.
These physical results are analytic with exact algebra checks; the
arbitrary-data continuation estimate remains open.

The [oscillatory-parent release](labs/README.md#an-oscillatory-parent-releases-a-self-stretching-descendant)
constructs actual smooth unforced periodic histories whose fast initial
motion leaves a slower, self-stretching descendant. The initial-layer
analysis retains the pressure-generated vertical velocity and its return
into the carrier, then uses local stability to control the actual flow.
It refutes the current normalized reserve's universal pointwise payment
at each fixed parameter; the integrated full-datum allowance remains open.
The original parents' decay does not erase their surviving descendants.
The PDE realization is analytic, with exact Fourier checks, not a new
Lean-certified theorem or an unforced blowup construction.

The [finite heat-parent lifetime](labs/README.md#a-single-original-heat-reserve-for-all-time)
replaces the horizon-growing weight by one finite original-data allowance
for the original heat source and all mixed interactions. It applies on
every available smooth prefix on either domain; generated self-stretching
remains open. An exact triangular example starts with zero projected
nonlinearity, but unequal heat rates generate a later source. Its entire
remainder history is paid explicitly for arbitrary amplitudes. The reserve
therefore measures the original heat history, not just its initial source.
These PDE results are analytic with exact Fourier fixtures, not new Lean
declarations or an arbitrary-data regularity proof.

The [original-heat remainder estimate](labs/README.md#original-heat-parents-and-the-generated-remainders-critical-cost)
pays the original heat field and its cross-interactions over any prescribed
finite horizon, using only the full initial datum and viscosity. It applies
to every available smooth unforced prefix without a smallness assumption.
The remaining sufficient estimate concerns weighted self-stretching of
the actual nonlinear remainder, which starts at zero. Exact smooth seeds
give both signs for its first generated self-stretching, so that term
cannot simply be discarded. This reuses the classical heat-flow/remainder
decomposition; the physical estimates and continuation implication are
analytic, with exact Fourier checks, not new Lean-certified theorems.

The [normalized-storage history test](labs/README.md#normalized-storage-and-an-actual-first-generation-obstruction)
starts with zero stretching and strict initial payment, then follows the
stretching generated by the actual unforced flow. A common weight repairs
the initial payment for an entire amplitude, viscosity and dilation family,
but every fixed member of this normalized-storage family fails on a short
whole-space history after concentration. The initial source capacity remains
large enough to supply a separate reserve: the original heat trajectory's
source capacity pays this first burst without replenishment. Extending that
payment beyond the controlled local interval remains open. This distinguishes
payment at the initial state from payment preserved by evolving geometry.
The solution-history arguments are analytic; their Fourier fixtures
and complete observer derivatives have exact checks, not new Lean proofs.

The [concentrated receiver test](labs/README.md#concentration-and-the-limits-of-kinetic-energy-corrections)
shows that the joint source storage cannot satisfy its proposed universal
differential payment after adding any fixed continuously differentiable
function of kinetic energy alone. Smooth unit-energy concentrating data
have positive quintic renewal of order lambda^(11/2), exceeding the lower
orders of viscosity, source loss and the energy correction. The construction
retains pressure and generated mean outputs, and applies to actual short
unforced histories. It leaves full-initial-datum allowances open: the
initial source capacity itself grows with concentration. Localization and
PDE claims are analytic; the accompanying Fourier checks are exact.

The [filtered-source history payment](labs/README.md#filtered-source-histories-paid-from-full-energy)
pays the complete nonlinear renewal above any fixed positive heat cutoff,
through every smooth unforced periodic history, without a perturbative
smallness assumption. Its nonnegative reserve is an explicit multiple of
the fifth power of the full velocity's L2 norm. The evolving source adjoint
retains pressure, covariance and surrounding parents; its norm growth also
has an original-energy bound at fixed resolution. Refining the resolution
has two additional positive costs. The resulting estimate removes the
coarse part of the quintic defect in (214), while the small-heat-time part
remains open. These are analytic bounds with exact Fourier fixtures, not
new Lean-certified physical theorems.

The [covariance--Poisson correction test](labs/README.md#a-covariance-poisson-correction-and-its-complete-physical-defect)
derives a signed correction whose two principal diffusion terms cancel
the covariance work exactly. Its remaining covariance and observer
derivatives do not have a universal favorable sign. Explicit horizontal
input data in a frequency belt of relative width at most `1/16` violate
the corrected half-dissipation payment while the total trial reserve is
strictly positive. The original reserve pays at those initial states.
This rejects the proposed unit correction with the stated energy-cube
coefficient; it does not alter the earlier controlled-history result.
The full derivative and strict margins have exact rational fixtures;
their smooth-interval interpretation remains analytic.

The [source-transport and covariance decomposition](labs/README.md#source-transport-cancellation-and-the-evolving-covariance-interface)
identifies the signed terms left in the receiver reserve's highest nonlinear
derivative. Source transport cancels exactly; source deformation, heat
covariance work and surrounding-parent work remain. Only the anisotropic
covariance contributes to the projected force. Its physical-time equation
retains both viscous loss and the full nonlinear parents. Exact smooth
initial data show that covariance can reverse a depleting source-deformation
sign, even with zero initial mean. The calculation reuses Gaussian-filter
stress identities and tests the complete pressure projection. The PDE and
stochastic interpretations are analytic; no new Lean declarations are
asserted. Paying this combined work over arbitrary histories remains open.

The [receiver-history payment](labs/README.md#source-square-payment-through-an-actual-refeeding-history)
now carries the same energy-cube reserve through the entire constructed
feed--return--feed interval, including the generated mean. It also pays
through any prescribed finite number of the constructed approximate pattern
cycles after strengthening the original perturbation threshold. A quantitative
H3 estimate controls the complete reserve derivative, and the allowance is
fixed from the original data. Eight theorems in
`MettapediaNS.EnergyCubeReceiverReserve` certify the scalar payment,
interval composition and actual whole-space energy-cube derivative.
The periodic Sobolev identification and cycle application remain analytic.
The controlled neighborhood is essential; its replacement for arbitrary
interacting flows remains open.

The [source-square receiver test](labs/README.md#nonnegative-source-storage-and-an-energy-cube-repair)
completes the signed heat correction to a globally nonnegative storage.
The storage still fails its proposed universal payment: exact hidden-phase
data give positive nonlinear production exceeding the half-dissipation
allowance. Adding a fixed multiple of the full kinetic energy cubed repairs
both tested phases at every amplitude and integer harmonic dilation,
giving a short payment interval of each actual smooth NS solution.
This uses the leading-term design principle from polynomial fluid
Lyapunov methods. Controlling the reserve after the geometry changes
remains open. The heat identities and interval arguments are analytic,
with exact rational Fourier checks, not new Lean declarations.

The [receiver heat-correction test](labs/README.md#heat-lifetime-corrections-and-the-next-receiver-generation)
now gives an explicit signed correction and a quartic initial allowance
for generated stretching. The allowance pays the first return on a short
interval of the actual three-dimensional seed flow. It does not give a
universal history certificate: two smooth data with equal energy,
enstrophy, current stretching, signed heat forecast and quartic stock
have opposite next renewal costs. A scaled member violates the proposed
differential payment while its reserve is strictly positive. The full
evolving-mean defect is retained. These conclusions are analytic with
exact Fourier checks; no new Lean declarations are asserted.

The [fixed-parent feedback payment](labs/README.md#paying-the-weighted-feedback-into-a-fixed-smooth-parent)
now covers repeated nonlinear replenishment of an observed parent in an
arbitrary smooth unforced history. For a fixed smooth solenoidal test field,
its full internal source is bounded by kinetic energy. The square of that
energy pays the source multiplied by enstrophy and the bounded exponential
weight of the parent reserve. Eleven theorems in
`MettapediaNS.WholeSpaceParentFeedback` include the actual whole-space
source equation and interval payment. The periodic realization and its
combination with the preceding shear reserve are analytic.
Unobserved stretching and changing-observer costs remain open; this payment
does not exclude the imported forced construction or prove global regularity.

The [parent-weighted fluctuation reserve](labs/README.md#a-joint-parent-weight-pays-transfers-that-fixed-quadratic-weights-cannot)
tests a concrete certificate for the remaining signed stretching.
A fixed nonnegative quadratic Fourier storage cannot pay its universal
differential budget: exact shear transfers force a lowest-mode weight
of at least `2N(N+1)` across N receiver steps. This does not exclude
datum-dependent or nonlinear history certificates.
On the full triangular shear/passive-scalar class, the joint weight
`(exp(2|a|/nu)-1)Z` instead pays fluctuation stretching on every interval,
without a bandwidth restriction or resetting its allowance. Its derivative
retains both parent-renewal and receiver defects in a generalization.
Eight scalar/sequence theorems are kernel-certified in
`MettapediaNS.ShearFluctuationReserve`; the physical realization and
interval estimates remain analytic. Mutual renewal in arbitrary flows
is still open.

### Mathematical sources and concrete reuse

The cycle and history work uses established fluid dynamics and model
reduction alongside the existing formal library. The following are
mathematical sources, not additional Lean axioms or automatically imported
formal proofs.

| Source | Reused idea and present consumer | Scope still requiring proof |
| --- | --- | --- |
| [Gibson, Halcrow and Cvitanovic, *Visualizing the geometry of state space in plane Couette flow*](https://arxiv.org/abs/0705.3957) | Describe dynamics using coherent states and actual connecting trajectories. The [reciprocal cycle construction](labs/README.md#actual-three-dimensional-pattern-cycles-with-reciprocal-feedback) uses separated pattern observations with full-history tracking. | Their Couette setting has moving walls and energy input. Its recurrent solutions are not unforced periodic-torus examples; the local construction has approximate finite returns. |
| [*Exterior and vector calculus views of incompressible Navier-Stokes port-Hamiltonian models*](https://doi.org/10.1016/j.ifacol.2021.11.074) | Make energy exchange and viscous loss explicit at an interface. Equation (127) in the reciprocal-cycle lab identifies equal and opposite powers for an actual modal parent and its full remainder. | The modal split is derived directly; a spatial traction/velocity port realization or a complete port-Hamiltonian formalization is not supplied. Energy exchange alone does not control stretching. |
| [Lohmayer and Leyendecker, *Exergetic Port-Hamiltonian Systems: Navier-Stokes-Fourier Fluid*](https://arxiv.org/abs/2204.05135) | Typed graphical interfaces and composition with energy accounting inform the organization of solution components. Existing `BoundaryBellman` composition retains the intermediate witness and spent reserve. | This thermodynamic model includes additional state variables. Its full semantics is not identified with the incompressible NS history category here. |
| [Chorin, Hald and Kupferman, *Optimal prediction and the Mori-Zwanzig representation of irreversible processes*](https://math.huji.ac.il/~razk/Publications/PDF/CHK00.pdf) | Eliminating hidden variables leaves memory and an initial hidden-state contribution. Equation (131) retains these through an exact nonlinear Duhamel constraint. | This is not a closed Mori-Zwanzig memory kernel or an imported orthogonal-dynamics theorem; kernel construction, approximation error and any statistical assumptions remain separate. |
| [Constantin and Iyer, *A stochastic Lagrangian representation of the 3-dimensional incompressible Navier-Stokes equations*](https://arxiv.org/abs/math/0511067) | Stochastic trajectories and covector reconstruction connect viscous dynamics to physical velocity. The existing `CovectorFluidBridge` treats its projected equation under explicit hypotheses. | The complete probabilistic construction and arbitrary-data stretching payment are not consequences of the reconstruction algebra alone. |
| [Morosi and Pizzocchero, *On approximate solutions of the incompressible Euler and Navier-Stokes equations*](https://arxiv.org/abs/1104.3832) | A posteriori residual and norm estimates connect approximations to actual solutions. The transfer-reversal examples use this validation principle with an explicitly derived nonlinear L2 comparison. | Their Sobolev control inequalities include an existence conclusion under their hypotheses. The local L2 transfer certificate instead uses the separately established global stability neighborhood; it does not establish arbitrary-data regularity or import their norm constants. |
| [Bardos, Lopes Filho, Nussenzveig Lopes, Niu and Titi, *Stability of Two-dimensional Viscous Incompressible Flows Under Three-dimensional Perturbations and Inviscid Symmetry Breaking*](https://arxiv.org/abs/1201.2742) | Relative kinetic energy compares a full flow with a known symmetry-preserving reference. The [reference-stretching reserve](labs/README.md#reference-stretching-paid-without-perturbative-smallness) couples that energy to a negative-Sobolev observation of generated feedback. | Their cylinder boundary hypotheses and constants are not imported unchanged. The new smooth comparison is derived on the stated torus/whole-space domains and leaves pure perturbation self-stretching unpaid. |
| [Goulart and Chernyshenko, *Global Stability Analysis of Fluid Flows using Sum-of-Squares*](https://arxiv.org/abs/1101.1043) | Use an inviscid invariant for the highest polynomial degree, and signed lower-degree corrections. The [energy-cube repair](labs/README.md#nonnegative-source-storage-and-an-energy-cube-repair) applies this design to receiver storage and certifies a scalar quadratic sign by its exact discriminant. | Their result concerns stability relative to a reference flow. Here only the stated initial-data families and short actual intervals are paid; arbitrary-history stretching control and unresolved-mode estimates remain open. |
| [Johnson, *On the role of vorticity stretching and strain self-amplification in the turbulence energy cascade*](https://arxiv.org/abs/2102.06844) | Equations (2.44)--(2.46) identify Gaussian-filter covariance through a heat equation and filtered gradient products. The [source-covariance interface](labs/README.md#source-transport-cancellation-and-the-evolving-covariance-interface) uses that identity with filter variance `2nu s`, then pairs its anisotropic stress with the receiver reserve's actual observer. | The borrowed filtering identity is kinematic. The new signed observer work and physical-time covariance equation do not supply a closed memory model, stochastic-control identification or arbitrary-history payment. |

The operative interface is a compatible history, not just a named flow
pattern. For the new cellular family, the observed parent coefficient
alpha and hidden field h obey the full NS equations together; the powers
`alpha F` and `-alpha F` cancel, and one original reserve pays every
later interval of `|F|`. Opposite hidden phases give the same observed
initial parent and energy but opposite transfer. Thus a reduced model
must retain joint information or prove an upper bound valid for every
compatible hidden history.

This already has concrete formal support: `FilteredHistory` retains
hidden coefficient histories for diagonal Fourier multipliers;
`LinearBoundaryReduction.System.feedback_elimination` preserves an
internally generated load after linear elimination;
`BoundaryBellman.CostedRelation.Bounds.comp` and `Bounds.iterate`
compose certified costs; and `WholeSpaceHistoryBridge.Segment.comp`
glues actual whole-space solutions with matching full endpoint data.
None of these is a nonlinear Schur inverse, a closed fluid memory kernel,
or an identification of the new periodic rank-one projection with the
existing diagonal Fourier theorem. Those mathematical distinctions remain
part of the interface specification.

### Existing formal reduction

The imported [linear Schur reduction](../mettapedia/Mettapedia/GSLT/Dynamics/README.md)
retains the affine contribution of internal forcing. Its constrained extension
also retains the equation generating that forcing from the reconstructed
interior. It provides no nonlinear Navier–Stokes inverse or stability bound.

`MettapediaNS.FilteredHistory` uses `InfiniteFilteredEquation` and
`FourierRelaxation` to derive the following identities from the existing
`LocalInfiniteVelocitySolution`. For a static bounded Fourier multiplier `P`,
write `v = P u`, `w = u-v`, and let `R` be the full viscous coefficient RHS:

```text
v' = R(v) + F_P(u)      F_P is the actual pressure-corrected subgrid force
w' = (I-P) R(u)         the hidden modes obey the same unforced evolution
```

`forcing_eq_subgrid` proves that any claimed force in the first equation
equals `F_P(u)`. `reconstructs_unforced_coefficient` proves the converse
coefficient equation when that equality, `P(v+w)=v`, absolute convergence of
the convolution, and the hidden evolution hold. It asserts no existence of
such hidden modes, spatial smoothness, or whole-space realization.

`hidden_mode_history` additionally retains the complete signed history:

```text
exp(d_q t) w_q(t)
  = w_q(0) + (1-P_q) integral_0^t exp(d_q s) N_q(u(s)) ds,
d_q = 4 pi^2 nu |q|^2.
```

Here `N` uses every nonlinear parent and the Leray projection. Time is
physical time. The complex phases, the original hidden datum, and the
coupling to the full field remain. Moving filters would add their time
derivative. Constructing a Schur inverse on a suitable space of these
histories and bounding repeated regeneration remain open.

This distinguishes three embedding questions. Reproducing an exact velocity
on an open region requires matching its differential equation, up to a
pressure gradient; reproducing an angular mean or Fourier observation permits
an effective Reynolds/subgrid force; reproducing an approximate singular
mechanism needs quantitative control of the approximation and its history.
These are different claims.

There is an analytic obstruction to exact local reproduction of the specific
OpenAI construction by an unforced flow: its axial component is zero on an
open annular region and nonzero on the axis inside the same fixed ball at
sufficiently late times. Spatial analyticity of a smooth unforced viscous
solution and the identity theorem exclude such agreement on that ball,
regardless of changes outside it. This inference uses Theorem 2.1,
Remark 2.6 and Claim A.3 of
[Constantin–Ignatova–Vicol](https://arxiv.org/pdf/2609.20803v1).
It is not a Lean theorem here, and does not exclude approximate reproduction
or reproduction of selected observations. Their Theorem 1.1 separately
excludes singularity for an exact shrinking axisymmetric core with its stated
anisotropic mean bounds and analytic forcing, including zero forcing.

The geometric route continues to target the interaction between a coherent
part and its complement. The common-axis estimate and mixed-axis obstruction
in `papers/ns_forced_tail_budget.tex` must be read together: coherent depletion
is controlled for the stated class; a full-datum bound on signed regeneration
through the complement is still required. Boundary elimination must preserve
the stretching observable and its resource accounting, not only velocity.

## Bellman certificates on actual fluid histories

`MettapediaNS.WholeSpaceHistoryBridge` instantiates
`GSLT.Dynamics.BoundaryBellman` with actual smooth, unforced `NSEvolution`
segments on `ℝ³`. Each segment retains its full initial and final velocities,
positive physical duration, and viscosity. Compatible segments concatenate
to another actual evolution. The window state also retains elapsed time.

For each derivative order `n`, `production_integral` identifies the signed
cost with the literal PDE energy production:

```text
cost_n(segment) = integral_segment production_n dt = E_n(end) - E_n(start).
cost_n(segment) + R(end) <= R(start).
```

The second line is the certificate obligation. Composition cancels the
intermediate reserves, without granting a new initial allowance at each seam.
The kinetic case `n = 0` has the proved certificate `R = 0`, by the unforced
energy inequality (`kinetic_bounds`, `kinetic_history_cost_nonpos`).

For `n = 1`, `orderEnergy_le_of_reserve` derives a gradient-energy bound at
every time from a nonnegative reserve certificate for all admissible segments
in the finite window. `hasNSEvolution_of_bellman` then applies the existing
whole-space continuation theorem. Its hypothesis requires such a real-valued
reserve for each horizon, over all full velocity states. The initial value
depends on the full datum. Existence of this stronger certificate is open;
it is not established by the composition theorem or the kinetic-energy case.
A more restricted certificate may instead use a proved reachable-state space.

This cost is ordinary signed order-energy production including full viscous
dissipation. It is not identified with the auxiliary caloric renewal or the
transported-frame energy. Those observables need their own production and
comparison theorems. Likewise, no identification with a Schrödinger bridge
optimizer is asserted. The framework permits such a later consumer while
keeping its fluid realization and analytic bound as explicit obligations.

The next concrete geometric observable is recorded in
[`labs/transported_frame_metric.py`](labs/transported_frame_metric.py) and
`StochasticLagrangian.TransportedFrameMetric`. A transported vector and its
positive frame tensor have an inverse-metric quadratic form whose explicit
strain terms cancel, leaving a nonpositive diffusion square and the exact
forcing term. Its regularized negative logarithm satisfies a drifted HJB
identity with a nonnegative geometric source. The Lean module proves the
finite matrix algebra; the stochastic realization and parabolic comparison
are analytic. Exact unforced shear and Beltrami tests retain the physical
equation and pressure. A bound on the changing metric in the actual
vorticity direction remains open, so this observable is not yet a reserve
for the ordinary order-one production.

`StochasticLagrangian.TransportedFrameDirection` checks the scalar quotient
and HJB algebra needed for that comparison. The metric diffusion loss enters
the physical-to-metric ratio with a positive sign. A logarithmic scalar
renormalization cancels this term from both sides of the corresponding HJB
barrier, leaving the ordinary physical stretching obligation. The exact lab
`transported_frame_direction.py` supplies smooth periodic unforced initial
data with positive stretching and pressure-driven stretching production at
a point where the metric diffusion cost is zero. This excludes a proposed
local payment by that cost alone; full-datum reserves and joint tensor,
pressure and history corrections remain open. The existing
`LocalMaterialStretching.hasDerivAt_stretchingAlong` supplies an actual
material-evolution identity for this retained stretching variable.

`StochasticLagrangian.PressureBoundaryResponse` gives an energy-paid part
of that pressure history. It proves sharp bounds for the explicit fourth
Newtonian angular kernel, its spatial integral away from a fixed radius,
and the time-integrated response under a common energy bound. Directions
and integration regions may change with time. Analytic identification
with the actual whole-space far-pressure Hessian gives
`||P_far|| <= 6 ||u0||_2^2/(pi R^5)`. The identification with the physical
pressure and its operator norm is not yet a Lean theorem in this module.

For the joint quantity `|omega|^2+tau^2|(grad u)omega|^2`, a bounded
far-pressure contribution is absorbed with coefficient `1/tau+tau K`.
The signed near-pressure work and viscous cross-gradient term remain
uncontrolled. The companion `labs/pressure_boundary_response.py` derives
the exact exterior pressure of a compact radial swirl and checks two
whole-space initial-data constructions with the same local core and
energy but opposite pressure-driven second directional growth. These are
analytic local unforced-flow tests, not recurrent-growth or singularity
results. Their derivation and formal scope are in the labs README.

`StochasticLagrangian.SwirlPressureHistory` continues this test to the
first pressure-response derivative. The analytic calculation uses actual
local unforced evolutions of a radial core and counter-rotating remote
swirl pairs. Their initial pressure-excess tensor can point in any
trace-free symmetric direction. With a common remote radial profile and
radius, its initial rate consists of viscous decay plus a rotation
commutator with zero quadratic work. Different widths can instead cause
the combined pressure norm to grow as cancellation between individually
decaying parents is lost; the module certifies an explicit example.
The radial geometry immediately develops meridional motion, so this is
an initial law, not an invariant class of solutions.

The Lean module proves the nonnegative energy allocation in an eigenvector
frame and an interval certificate for symmetric matrix histories with an
explicit geometry defect: the final squared pressure norm plus the
integrated damping cost is at most the initial squared norm plus the
integrated defect cost. Bounding that defect for arbitrary physical
histories, and connecting this pressure reserve to directional vorticity,
remain open. The physical first derivative is analytic; the companion
`labs/swirl_pressure_history.py` checks its algebra and independently
cross-checks its pressure-source integral numerically.
These fixed-distance tests specify necessary history information; they
do not supply the open estimate for nearby parents at changing scales.

`StochasticLagrangian.AlignedPressureReserve` supplies a candidate that
jointly retains directional strain, vorticity and incoming pressure.
The analytic test in `labs/compressed_parent.py` places remote swirl
packets inside a compact axial straining flow. Their initial pressure
rate includes changing separation, deformation, reaction of the
surrounding fluid and the exact finite-background correction. The
resulting aligned feedback has a positive polynomial reserve controlling
physical vorticity. Lean proves its signed defect identity and interval
balance, including the terminal reserve. The geometry is not invariant,
and no arbitrary-flow defect allowance is proved.

`StochasticLagrangian.LocalDirectionalPressure` identifies the strain
slot with the actual local unforced periodic solution along material
paths, away from vorticity zeros. The rate keeps the nonalignment square,
the actual directional pressure Hessian and both viscous Laplacians.
The physical pressure expression and a retained pressure summary may
differ; their difference enters the strain defect explicitly. Initial
agreement with a remote excess does not identify their later histories.

The lab checks that spatial diffusion requires additional cross-gradient
terms, and that actual planar-flow correlations make those terms
dissipative. The earlier mixed-parent flow already makes the observed
joint reserve increase initially. A separate compact compression test
shows why replacing the retained pressure history by an instantaneous
pressure expression can also cause initial growth. These facts leave
the signed full-datum history budget open; they are not singular flows.

`MettapediaNS.WholeSpacePressureHistory` pays one actual pressure-history
source from the kinetic energy that viscosity consumes. For a smooth
unforced whole-space evolution, let `Fν,R` be the separated fourth
Newtonian kernel applied to `-2ν Σj ∂j u ⊗ ∂j u`, sampled at any moving
receiver and unit direction. The checked estimate retains the terminal
energy:

```text
integral_0^t R(s)^5 |Fν,R(s)(s)| ds + (6/pi) E(t) <= (6/pi) E(0).
```

Here `E=||u||_2^2` and every sampled radius is positive; it may shrink.
In a nonnegative regime of the joint reserve, choosing
`R^5 |omega|^2 >= Λ > 0` bounds this pressure-slot work by
`[1995/(77 pi Λ)] (2ν ||grad u||_2^2) reserve`. This supplies the concrete
correction `reserve * exp([1995/(77 pi Λ)] E(t))` for this channel.
The radius choice does not remove the near field, moving-cutoff terms,
or the other geometric and viscous defects.

The accompanying exact Fourier checker `labs/pressure_history_source.py`
retains the full generated source and verifies two forms of the actual
pressure evolution, directional cancellation and the instantaneous
pressure-input defect. The general PDE identification of the kernel
source is analytic; the source bound and its actual energy payment are
Lean-certified. Nonlinear transport and pressure-velocity reaction,
nearby interactions, and a nonnegative physical reserve remain the main
unpaid obligations. The whole-space kernel estimate is not asserted for
the periodic Green function.

The analytic calculation in `labs/transverse_strain_history.py` now
retains arbitrary transverse strain and changing vorticity direction.
A compact smooth whole-space datum realizes the complete pressure
comparison at its initial core. For `Omega=|omega|>0`, the nonnegative
transverse quantity `K=delta^2+(19/4)|Sxi-(xi·Sxi)xi|^2` has an exact
actual-flow evolution with the physical pressure and both viscous
Laplacians retained. In the comparison dynamics its normalization
`kappa=K Omega^(-10/7)` decreases during extension, giving an explicit
vorticity bound for one such episode from its incoming state.

Compression with a turning direction can replenish this resource:
the compact unforced test has `L kappa=171/7>0` while its initial
pressure and viscous defects vanish. This rules out global monotonicity
of that candidate, not a full-datum history allowance. The next physical
obligation includes compression-to-extension cycles, their pressure
defects and the cost of crossing low-vorticity regions. The general
identities and compact local-flow argument are analytic, checked by
exact angular integration and complete Fourier tangents; no new Lean
certification or arbitrary-data bound is asserted for this extension.

`StochasticLagrangian.StrainCycleReserve` supplies a nonnegative
sixth-order polynomial of strain and vorticity that is conserved by
the complete compact-core comparison, including turning and anisotropy.
Its eigenframe certificate and signed moment-defect production are
Lean-certified. It is not itself coercive in vorticity. An analytic
quantitative estimate uses it to bound the intrinsic compression/turning
cost whenever the strain spectral diameter satisfies
`diam(S)^2 <= (63/190)|omega|^2`. The resulting comparison-history
allowance is `(684/7)(1+J6_initial) times elapsed time`, with no restart
after individual episodes. The normalized scalar payment is also
Lean-certified; the spectral estimate and physical moment identification
remain analytic.

The accompanying `labs/strain_cycle_reserve.py` retains actual pressure
and viscosity in the invariant's evolution. A positive-viscosity Fourier
datum increases it, so its comparison conservation cannot be used for
unforced NS without paying those defects. A compact actual unforced
family makes a short compression-and-return cycle strictly inside the
spectral regime. This is a finite-cycle construction, not repeated
unbounded renewal. The remaining obligations are the invariant's signed
physical production, the other transverse-resource defects and entry
or exit through the complementary strain-dominated regime.

`StochasticLagrangian.StrainCycleDiffusion` and the accompanying exact
lab test the stochastic extension on compatible incompressible spatial
jets. A complete periodic unforced family has positive parabolic
production of `J6` at zero spatial gradient, including its actual
pressure contribution. The old instantaneous pressure-strain weight
also has an unfavorable quartic diffusion term. Changing its vorticity
weight to `|omega|^2` cancels that term in the family and pays the initial
`J6` diffusion source. The resulting quartic expression is
`5(omega.Somega)^2/|omega|^2 +(63/95)|omega|^4 -2 omega.Pomega`.
Its positive core is explicit; the directional pressure mismatch can
destroy positivity. A rotated parent packet does so, and a separate
positive-viscosity datum has positive parabolic production. The Lean
certificates cover the jet expansion and rate comparisons; the full
physical equation and Fourier realizations remain analytic. None of
these initial-time tests establishes an arbitrary-history allowance.
Under its stated coercivity and separation-scale hypotheses,
`WholeSpacePressureHistory.quartic_viscous_source_le` transfers the
existing kinetic-loss payment to this corrected quantity, with the same
coefficient `1995/(77 pi Lambda)`. The other physical defects remain open.

`StochasticLagrangian.PressureCoreEnvelope` removes that pressure-sign
condition by smoothly taking the maximum of the regularized pressure
expression and its nonnegative core, with a positive offset. The resulting
`Y` satisfies `Y >= 1+(44/95)|omega|^4` without a pressure hypothesis and
has an explicit upper bound from the initial strain, vorticity and pressure
Hessian. Fixed positive regularizers make it smooth at vorticity zeros.
The smooth-switch derivatives are Lean-certified; its parabolic switching
term is favorable. The complete branch equations remain analytic, with
independent exact Fourier checks in `labs/pressure_core_envelope.py`.
The earlier packet tests now have positive reserve and nonpositive
production, while a general unforced datum still has positive production.
`WholeSpacePressureHistory.reserve_viscous_source_le` pays the separated
viscous pressure channel at any fixed radius `R>0`, including zero
vorticity, with coefficient `9/(pi R^5)` times actual kinetic-energy loss.
The correction `Y exp(9 E(t)/(pi R^5))` absorbs this channel over the full
history. The remaining normalized signed production, not positivity,
is the open Bellman-history estimate for this candidate.

`MettapediaNS.WholeSpaceCubicHistory` pays a further physical channel over
entire unforced histories: cubic stress transport at fixed separation.
The common flux envelope `B=||u||_2 ||u||_4^2` is at most actual kinetic
loss plus `a=27 S^6 E0^3/(32 nu^3)`, where `S` is the imported Sobolev
constant. Its history allowance retains terminal kinetic energy.
The full stress identity also gives an analytic signed bound `E0` on
pressure transfer into any fixed global unit direction. A moving or
spatially weighted observer adds explicit transport, rotation, diffusion
and pressure boundary work; the corresponding endpoint certificate is
Lean-checked, while its actual-fluid identification is analytic.
The exact lab `pressure_stress_transport.py` retains every one of those
terms. The remaining geometry question is the cost of tracking a small,
rotating, possibly shrinking dangerous region. Fixed-scale signed bounds
do not supply the required uniform allowance for such histories.

`MettapediaNS.WholeSpacePressureObserver` bounds a smooth separated
pressure observation with the reserve's actual normalized weight by
`9 E(t)/(pi R^5)`. Its complete signed generator can consequently be
paid by endpoints. The same certified bound controls the change in the
logarithmic reserve when that separated pressure is removed from its
observation; the nearby dynamics still retain all physical pressure.
The analytic identification uses a receiver and its
parents driven by the same backward Brownian displacement: the kernel
sees only their relative fluid velocity, while the shared diffusion
retains mixed gradients of the fields. The exact lab
`synchronous_pressure_history.py` recovers the actual pressure evolution
after parent integration and includes the evolving reserve weight.
The stochastic identification and endpoint expectation are analytic;
the spatial primitive bound is Lean-certified. Mixed gradients can have
either sign, and the individual weight and near-field costs remain open.

`MettapediaNS.PressureCoreReaction` pays the direct distant-pressure
reaction that remains in the strain after changing that observation.
Its normalized size is at most `(9/4) ||P_far||_F`, uniformly in strain,
vorticity, nearby pressure and the positive regularizers. The analytic
separated-kernel bound gives the actual fixed-radius history allowance
`27 E0 H/(pi R^5)`, along any receiver history on a horizon `H`.
The scalar sensitivity and its conversion are Lean-certified; the
actual tensor/PDE identification is analytic. The exact companion lab
`near_pressure_reaction.py` keeps the full pressure in the nearby parent
equation and retains its singular-kernel commutator and all gradient
terms. Its Fourier splits check the identity, not a spatial cutoff.
The corrected reserve still has positive production on smooth unforced
data. Nearby parent histories and shrinking scales remain unpaid.

`MettapediaNS.PressureViscousMemory` isolates why receiver diffusion alone
cannot pay every pressure source. A smooth two-wave periodic family has
mean squared speed four and zero receiver first gradients, but a positive
parabolic viscosity contribution to `Y`, with normalized rate at least
`(16/55) nu n^2`. This is an instantaneous obstruction; the temporal heat
derivative is a different quantity. The scalar family bounds are
Lean-certified, and its full Fourier realization is exact-symbolically
checked in `labs/viscous_parent_memory.py`.

The same lab develops an analytic correction on actual smooth prefixes:
retain the positive matrix `C` solving `D C=2nu sum_j partial_j u tensor
partial_j u`, `C(0)=0`. Its trace mass is exactly `E0-E(t)`. The augmented
stress `u tensor u+C` has fixed trace mass and retains the full signed
pressure work while its explicit viscous source cancels. The backward
stochastic representation identifies `C` as expected accumulated velocity
quadratic variation, generally not terminal velocity covariance. This
state composes through the actual advection-diffusion propagator without
restarting its resource. Its pressure correction cancels the identified
initial defect. The construction and identification are analytic; full
NS time jets check the equations and trace conservation through two time
derivatives. Nearby memory pressure, the transport commutator, and the
remaining geometric gradients still require a signed history bound.

`MettapediaNS.ViscousMemoryEntropy` supplies scalar certificates for a
nonnegative reserve on those actual memory histories. For fixed `eta>0`,
add `integral [tr C-eta log det(I+C/eta)]` to kinetic energy. The analytic
PDE balance shows that its decrease pays both
`2nu eta tr((eta I+C)^(-1) G)` and the nonnegative matrix gradient cost
`nu eta sum_j ||(eta I+C)^(-1/2) (partial_j C) (eta I+C)^(-1/2)||_F^2`.
The total payment plus the terminal reserve is exactly the initial
kinetic energy, so this resource is not reset at history boundaries.

Where the largest regularized memory eigenvalue is at least twice the
second, the same cost controls the principal-direction projector's
spatial gradients and complete backward stochastic drift, including
diffusion. The corresponding analytic spacetime bounds have constants
`4E0/eta` for its noise quadratic variation and `48E0/eta` for its
parabolic drift. These are integrated over space; they do not bound
arbitrary individual or controlled receivers. The memory direction is
also not identified with the vorticity direction. The exact lab
`viscous_memory_entropy.py` checks the entropy balance, pressure and
projector formulas on complete unforced shear histories. Scalar entropy
and orientation coefficients are Lean-certified; the actual matrix/PDE
history theorem is analytic. Its remaining consumer is the signed
nearby-pressure/vorticity estimate, with receiver concentration retained.

`MettapediaNS.ViscousMemoryPressure` now bounds the action of the memory
stress divergence using that paid matrix metric. Analytically, for a
smooth receiver tensor `M` with pressure `q_M`, the signed memory-pressure
pairing is bounded by `alpha E0` plus
`integral tr(H) grad(q_M).H grad(q_M)/(4 alpha nu eta)`, where
`H=eta I+C` and `alpha>0`. The second term is an explicit unpaid receiver
cost. Six finite-dimensional statements certify the weighted divergence,
pairing and rank-one defect bounds. The pressure integration and actual
history application remain analytic.

The exact `viscous_memory_pressure.py` test also shows why directions alone
do not close this estimate. Complete unforced Taylor--Green histories
retain a constant memory eigenframe, yet transport generates memory
pressure at second order in time and a positive direct contribution to
the current reserve over a short interval. This refutes a turning-only
payment with no further allowance, not a full-datum history budget.
The full entropy metric still charges amplitude changes. A whole-space
heat-kernel check shows that the displayed receiver norm diverges in
the unsmoothed point-receiver limit even with zero memory. It therefore
cannot be inserted directly into the Bellman target; physical pressure
cancellations and concentration control remain necessary.

`MettapediaNS.ViscousMemoryNormalization` supplies a more direct candidate:
divide the joint envelope by `h=det(I+C/eta)^(1/3)`. Analytically,
`1<=h<=1+tr C/(3eta)`, and the actual memory equation gives
`D h=h Q_geom`, with `Q_geom` a nonnegative source-plus-shape cost.
The nonnegative resource
`integral [|u|^2+tr C-3eta(h-1)]` pays `3eta integral h Q_geom`.
The normalized logarithm has auxiliary sampling drift
`-u+2nu grad(log h)` and remaining source `B_near-Q_geom`.
A Doob density identifies this law with a reweighting of actual viscous
paths; it does not change the fluid equation. Memory is retained at seams.

A uniform full-datum bound on `Y_hat/h` would suffice for continuation
in both settings: it bounds `|omega|^4` by a constant times `1+tr C`.
Splitting low and high vorticity avoids integrating the constant over
whole space. `WholeSpaceMemoryEnvelope` now certifies the connection to
the actual unforced PDE and the official whole-space continuation theorem:
the literal production obeys `W'<=W+integral |omega|^4`, and a finite-mass
majorant turns this into a linear inequality for `W=integral |omega|^2`.
The proof uses Betchov's identity and a finite sum of squares; it requires
no pressure singular-integral estimate or interpolation inequality.
The determinant/PDE memory construction and stochastic identification
remain analytic. Exact matrix jets and complete shear histories check
those formulas. The periodic continuation application remains analytic.

`WholeSpaceMemoryExcess` further permits the spatial mass bound to vary
in time, requiring only a uniform bound on its time integral. Consequently
it suffices analytically to bound the space-time excess
`integral integral (exp(-kappa t)Y_hat-b h)_+`, for a fixed initial-data
threshold `b`. Here `kappa` pays the already controlled separated reaction.
This allows pointwise peaks and places the remaining estimate in the same
spatially integrated setting as the paid geometric cost. The lab derives
its exact signed pressure/parent-production target, retaining changing
geometry, all nearby terms and accumulated memory.

Both modules also certify failure of their respective mass criteria for
the actual imported forced singularity. They retain its smooth compact
forcing and bounded derivative norms; no hypothetical surrogate is used.
Analytically, its accumulated memory and geometric payment still have
finite spatial budgets, but its space-time envelope excess is unbounded.
This excludes a proof based only on those finite budgets. It does not
refute an estimate using the exact unforced parent equations, nor identify
which separate term of the new reserve carries the forced divergence.
The signed excess bound and the stronger controlled-history bound remain
open; neither is supplied by the normalization alone.

For pressure estimates, `ViscousMemorySoftExcess` supplies the differentiable
alternative `F=(X-b h)_+^2/X`. It obeys `X<=2b h+F`, so its time-integrated
mass also supplies the actual continuation hypothesis. Its convex
perspective Hessian pays the gradient of its continuous threshold weight.
The lab identifies why this matters on a complete unforced mixing family:
a sharp region selector gives an infinite derivative-based pressure norm
even when actual memory-pressure work is zero. The differentiable weight
removes that interface defect. This does not control the remaining tensor
derivatives or the nonlocal weighted receiver cost.

The same family has genuine vortex stretching and an explicit stochastic
parent-history bound, yielding a finite all-time excess allowance. The
horizontal parent decays by the heat equation and drives a passive vertical
component. The PDE and full-history estimate are analytic; exact algebra
checks the reduction and the limiting interface. Extending the payment to
mutually amplifying NS parents remains open. These periodic examples are
not finite-energy whole-space fields or arbitrary-flow estimates.

`PressureDiffusionCompletion` supplies scalar certificates for a repair of
the remaining tensor derivative. The exact lab first exhibits genuinely
three-dimensional unforced data whose canonical pressure and retained-memory
correction leave a positive quadratic viscosity contribution to the preceding
envelope. This excludes an automatic nonnegative-diffusion comparison, not a
finite history allowance. Its datum-fixed excess is initially inactive.

The analytic repair keeps both pressure and core branches and completes them
by `48 (||grad u||_F^2+sqrt(sigma^2+||P_hat||_F^2))^2`, for fixed positive
`sigma`. Taking the Euclidean norm of these two positive completed branches
gives a smooth convex observable `Psi>=12|omega|^4`. Its diffusion pays the
entire strain-receiver derivative, with the explicit local weight `1/Q`,
where `Q=||grad u||_F^2+sqrt(sigma^2+||P_hat||_F^2)`. The existing soft-excess
continuation bridge can consume its coercivity; the already controlled
stochastic mixing family also retains a finite all-time allowance.

Nine Lean statements certify scalar curvature, branch and receiver-payment
steps. The uniform matrix differentiation and physical PDE application are
analytic, with exact algebra checks in `labs/pressure_diffusion_completion.py`.
The completion adds genuine reaction terms, which remain in the signed
history obligation. Its local weighted gradient payment does not bound the
anisotropic nonlocal memory-pressure norm. Neither arbitrary-data continuation
nor the repeated renewal estimate is established by this repair.

`WholeSpacePressureDiffusion` now ties a new pressure cost to the actual
constructed Helmholtz pressure of arbitrary smooth solenoidal whole-space
velocity. Two integrations by parts give
`integral |P|^2 = integral tr((grad u)^2)^2` and
`integral |grad P|^2 <= 4 integral |grad u|^2 |grad^2 u|^2`.
These are spatial identities and estimates for actual fluid pressure,
without a prescribed pressure matrix or future-solution bound.

Consequently the difference `P_C=P_hat-P` obeys
`nu integral |grad P_C|^2 <= (33/56) integral D_Psi`, provided the
completed diffusion supplies its displayed physical Hessian lower bound.
The strict coefficient follows from a weighted square, not an assumption
that memory pressure has a favorable sign. The pressure identities and
this conditional diffusion adapter are Lean-certified; construction of
the evolving memory and the full matrix Hessian remain analytic.

Analytically, fixed low frequencies of `P_C` are bounded by the finite
positive memory mass, and high frequencies by this derivative payment.
This yields a full-horizon unweighted pressure-square allowance plus an
arbitrarily small multiple of the full diffusion. The soft excess pays
`a_b D_Psi`, so transferring the estimate to its varying active weight
is a separate open obligation. The joint strain/pressure memory reaction
also retains the pressure transport commutator: the lab verifies its
exact compensation under a constant-velocity shift. A sign change of
an isolated boost-dependent fragment is not a physical history obstruction.

`WholeSpacePressureLocalization` identifies the exact signed correction
for a varying spatial weight on actual canonical fluid pressure. For
`P=Hess p`, the full pressure flux is
`P grad(Delta p)-(1/2)grad|P|^2`. For a nonnegative smooth weight `a`
with all jets in L²,
the completed memory-pressure payment becomes

```text
nu integral a |grad P_C|^2
  <= (33/56) integral a D_Psi
     +(33/28)nu integral grad a.[P grad(Delta p)-(1/2)grad|P|^2].
```

Twelve declarations certify the weighted identities, the literal flux
formula and this conditional payment. Approximation extends the identity
analytically to the actual continuous soft-excess selector on a smooth
prefix with decaying memory jets and a threshold above the far-field
offset. Its signed flux still requires payment, together with the joint
pressure/strain reactions and transport commutator, over arbitrary histories.

The companion [cellular parent history](labs/cellular_parent_history.py)
provides a pressure-bearing stochastic example beyond the zero-pressure
triangular shear. A horizontal streamfunction in one Laplacian eigenshell
has a heat-decaying unforced NS evolution and drives an arbitrary smooth
vertical component independent of the vertical coordinate. Its remaining
parent reserve `A1 exp(-nu lambda t)/nu`, with `A1` the sum of streamfunction
amplitudes, pays every accumulated parent-shear segment without refilling
at seams. Stochastic characteristics bound the vertical gradient; an
explicit finite allowance also controls the retained horizontal memory
derivatives and hence the memory pressure. This analytically bounds the
completed envelope on every prescribed horizon for this periodic class.
The exact PDE reduction and coefficients are checked; the stochastic and
memory estimates are not new Lean theorems. Resolved-prefix diagnostics use
the actual varying selector and complete memory. The horizontal parents
decay autonomously, so the class does not establish a payment for mutually
regenerating arbitrary three-dimensional parents.

`CellularParentRenewal` now tests that restriction against genuine internal
feedback. Two transverse modes with vertical dependence feed an existing
cellular parent through the complete infinite NS coefficient equation.
Reversing one hidden cosine phase reverses the parent's energy transfer
while preserving the full initial energy. The receiving-pair rate includes
viscosity and the exact unit-torus normalization. The complete kinetic
balance still dissipates energy: the receiving gain is supplied internally.
The apparent force on the receiving plane wave is identified with the
existing pressure-corrected subgrid force, not an independently prescribed
fluid force. These source, energy and derivative-consumer statements are
Lean-certified; construction of their short-time history is not newly
formalized here.

The [reciprocal parent lab](labs/reciprocal_parent_history.py) retains every
generated output in its exact initial calculation. For its stated data,
the projected heat-style parent reserve initially increases despite zero
external forcing. Resolved short prefixes retain all velocity components,
all six memory entries, canonical pressure and the signed parent-transfer
ledger. This refutes autonomous decay of that projected reserve outside
the restricted cellular class. It does not refute a corrected full-datum
reserve or establish recurrent unbounded renewal. Paying the signed
pressure flux and joint reaction over arbitrary interacting histories
remains the continuation obligation.

`WholeSpacePressureAugmentation` supplies an alternative spatial payment
for a stronger sufficient observable. Add the square of the actual
canonical pressure Hessian to the completed joint observer:

```text
Phi=Psi+|P|^2,       D_Phi=D_Psi+2nu|grad P|^2,
nu a|grad P_C|^2 <= (33/56)a D_Phi.
```

This payment is pointwise for every nonnegative selector. Its integrated
consumer accepts any bounded measurable selector, including the continuous
soft-excess weight, with no localization flux or weight-derivative estimate.
The completed observer-Hessian lower bound is an explicit application
obligation. The literal square diffusion identity uses the constructed
whole-fluid pressure; it does not introduce an independently chosen matrix.
The additional initial mass is at most `integral |grad u0|^4`, and the
augmented soft-excess bound still implies the actual vorticity criterion.
Nineteen public definitions and theorems certify these spatial statements
and the conditional continuation adapter.

The stronger candidate has an additional signed pressure-production term.
Writing `K` for the pressure-Hessian observer and
`D=partial_t+u.grad-nu Delta`, the physical equation is

```text
D P = -K(u tensor grad p+grad p tensor u)
       +[u.grad,K](u tensor u)-2nu K(grad u (grad u)^T).
```

The complete extra production `2P:D P` remains in the history obligation.
The [pressure-square lab](labs/pressure_square_augmentation.py) checks this
equation against the full exact initial NS operator and retains every
Fourier output. Its equal-energy phase pair has opposite signed additional
production. This does not refute the candidate's integrated history bound,
and the new diffusion payment does not establish that bound. Time evolution,
memory construction and the full physical matrix Hessian remain analytic.

`WholeSpacePressureReceiver` pays the full spatial derivative of the added
canonical receiver `N=2aP`, including the derivative of its selector. For
`z=Phi/h`, `a=(1-b^2/z^2)_+` and active curvature `c=2b^2/z^3`, it proves

```text
partial_k N = 2a partial_k P + 2P c partial_k z       almost everywhere,
nu integral |grad N|^2 <=8nu integral a|grad P|^2+16 integral J,
J=nu h c|grad z|^2.
```

The weight has a globally Lipschitz extension. Its minimum at zero handles
the cutoff level without assuming that level set has measure zero. The
actual receiver is locally Lipschitz and belongs to `L²`; the derivative
integrability is concluded from the native diffusion payment. Ratio
regularity, `|P|²<=hz` and instantaneous integrability of `J` are explicit.
The ratio's Lipschitz modulus does not enter the payment, and there is no
division by the selector. Retaining the canonical pressure square supplies
`|P|²<=Phi` when the previous observable is nonnegative.

The module also constructs the actual `L²` Helmholtz pressure component of
the receiver divergence and proves

```text
nu ||grad q_N||_2^2 <=24nu integral a|grad P|^2+48 integral J.
```

Its sign agrees with `-Delta q_N=div div N`. The estimate is **unweighted**;
it does not pay the anisotropic memory-weighted pressure norm. Identification
with the weak Poisson potential uses the locally Lipschitz weak derivative
interpretation, which is analytic here; the Lean theorem constructs the
pressure component directly from the literal almost-everywhere divergence.
The weak/time PDE chain rule and the signed allowance for arbitrary parent
histories remain open. This is a further spatial payment for the stronger
sufficient observable, not a global reserve certificate.

`MemoryAgePressure` separates old memory from newly generated parent memory.
For a prescribed age `delta>0`, scalar incompressible diffusion gives the
analytic whole-space estimate

```text
||U(s,t)||_(L1->Linfinity) <=(sqrt(3)/pi^2)[nu(t-s)]^(-3/2).
```

Positivity, the original source-mass payment and composition then bound
`C_old=U(t-delta,t)C(t-delta)` by `L_delta I`, with
`L_delta=E0 sqrt(3)/(pi^2 (nu delta)^(3/2))`. For `t<delta`, old memory is
zero. The rest is the actual positive recent source integral; no account is
reset. The normalized periodic estimate has a separate explicit constant.
The propagator and age identification are analytic, not Lean-certified.

For `K=eta+L_delta`, `c=tr C_recent`, and any receiver pressure gradient `v`,
the module certifies the directional comparison

```text
tr(H) v.Hv <=3K^2|v|^2+K c|v|^2+(3K+c)v.C_recent v,
H=eta I+C_old+C_recent.
```

It retains turning, anisotropy and the isotropic trace term without a
common eigenframe. The simpler trace consequence is
`tr(H)v.Hv<=5K^2|v|^2+3c^2|v|^2`. Its literal spatial consumer uses the
constructed canonical receiver pressure, positivity, the displayed old
bound and an explicit integrable recent remainder. Combined with the
analytic entropy pairing, an already native-paid receiver admits a finite
datum-fixed old-memory allowance and a still unpaid recent-memory cost.
This does not identify the canonical component with the full joint effective
receiver or pay the complete signed pressure production and commutator.

The [age-splitting lab](labs/memory_age_pressure.py) also exhibits a measuring
defect exactly: projecting the gradient square of a smooth unforced shear
to the same Fourier band can make its auxiliary memory source negative.
The real stochastic memory remains positive. The scalar negative certificate
is Lean-checked; the Fourier identification is checked by exact arithmetic.
An age-split numerical prefix failing positivity is excluded from physical
payment evidence. Ordinary spectral compression needs an additional
positivity argument before it represents this memory reserve.

### Complete pressure-source evolution and a local viscous payment

`WholeSpacePressureProduction` differentiates the actual canonical pressure
source at every interior time of a smooth whole-space NS evolution. With
`B=grad u`, `s=tr(B²)`, `P=Hess p` and
`D=partial_t+u.grad-nu Delta`, the kernel-certified law is

```text
D s=-2tr(B³)-2tr(BP)-2nu sum_j tr((partial_j B)²),
D(s²)=-4s tr(B³)-4s tr(BP)-4nu s sum_j tr((partial_j B)²)
       -2nu|grad s|².
```

The pressure source is identified from the evolution's solenoidal velocity
and canonical pressure. The crossed viscous term can be positive, but its
absolute value is bounded pointwise and in the genuine spatial integral:

```text
|4nu s sum_j tr((partial_j B)²)|
  <=4nu|B|² sum_j|partial_j B|²,
```

for `nu>=0`. This is half the local strain-gradient density in the completed
diffusion lower bound, and the pointwise comparison retains any common
nonnegative selector. Identification of that full candidate matrix Hessian
is still an analytic application obligation.

The [exact checker](labs/pressure_source_production.py) retains all Fourier
outputs, including a resonant pair with crossed viscous productions
`+48/175` and `-48/175`, interacting parents, constant drift, and nonzero
external forcing at a tested state. It identifies the complete unweighted
pressure-square production with the source-square production. That integrated
time identification is analytic, not an additional Lean theorem here.
A variable weight adds a nonzero differentiated localization flux in these
fixtures. The selected canonical pressure square cannot be replaced by the
local source square without it. The cubic, pressure, flux and fresh-memory
history payments remain open.

### Selected pressure cotangent on actual evolving parents

`SelectedPressureCotangent` reconstructs the first variation of the
canonical pressure from both velocity parents. Its finite increment is
the actual pressure gradient of `u+c v`, with the linear cross interaction and
quadratic `c²` remainder retained. Along an actual whole-space NS
evolution, every pressure-Hessian entry has this time derivative with
the complete viscous right-hand side.

For the receiver `N=2aP`, let `V=-Pi_gradient div N`. Incompressibility
makes `(u.grad)v-(v.grad)u` solenoidal. The complete divergence-form
pressure work therefore equals the work of the local velocity cotangent

```text
ell=-2(grad u)^T V,
integral ell.v=-<div N, pressureVariation(u,v)>.
```

The identity is kernel-certified for compatible smooth velocity directions
and for the actual NS time derivative. The receiver is the constructed
negative Helmholtz projection, including its selector derivative. The
weak integration-by-parts identification with `integral 2aP:partial_t P`
remains a separate analytic obligation for the Lipschitz selector.

No bound on the future strain is needed for the kernel-certified spatial
comparison and its integrability:

```text
|ell|²/(1+|grad u|²)<=4|V|²,
nu integral |ell|²/(1+|grad u|²)<=192 Q_native,
Q_native=sum_k(2nu integral a|partial_k P|²+integral J_k).
```

The literal receiver consumer retains the existing positivity, Lipschitz,
pressure/ratio and selection-diffusion integrability hypotheses. This is
a component norm payment, not a bound on its nonlinear time work or on
the remaining joint strain/pressure/memory cotangents.

The [exact selected-pressure checker](labs/pressure_selected_cotangent.py)
retains all Fourier outputs on interacting 3D states and their complete
NS tangents. Replacing `chi=(-Delta)^-1 divdiv(aP)` by `a tr((grad u)²)`
gives nonzero erroneous work. Constant drift changes a fixed Eulerian
selected derivative, with exact compensation by transport. The selector's
own time derivative is kept separately from its pressure-variation leg.

### Complete joint receiver: local payments and signed work

The completed observable uses the full velocity gradient `B`, including
its antisymmetric part. Write `q=sqrt(sigma²+|P_hat|²)`, `Q=|B|²+q`,
`Phi=Psi(B,P_hat)+|P|²`, and `R_native=J+a D_Phi`. Uniform analytic
matrix estimates and kernel-certified scalar combinations give

```text
nu |grad(a Psi_B)|²/Q <=15000 R_native,
nu (q/Q) |grad(a Psi_Phat+2aP)|² <=3500 R_native.
```

Both spatial slots vary together. The second payment retains `q/Q`;
the existing unweighted canonical `2aP` estimate does not pay the full
pressure receiver. Matrix differentiation and weak receiver construction
are analytic application obligations, stated in the
[complete derivation](labs/README.md#complete-joint-receiver-payments-and-an-actual-parent-obstruction).

`JointReceiverDiffusion` also proves the signed divergence-form velocity
work on the actual whole-space NS tangent, with both `L²` receiver
divergences retained. It identifies the pressure derivative from that
evolution. The interpretation of those divergences as the completed
matrix observable remains an explicit weak-calculus obligation.

An analytic actual-state family shows why a uniform instantaneous payment
of the full projected receiver norm cannot replace its signed work:

```text
u_n=(n sin y, n^-2 sin(n x),0), C_0=0,
p_n=2 cos y cos(n x)/(n²+1).
```

For the test threshold `b=1`, the complete normalized velocity-cotangent
cost grows as `n^6`, while native diffusion grows as `n^4`. The full
nonlinear work has zero spatial mean at this state, and diffusion and the
capacity source make the initial excess mass decrease. Pressure, both
parents and actual positive memory generation are retained. These are
smooth divergence-free planar data embedded in three dimensions.

The threshold is not the route's above-initial-supremum choice. The result
refutes the specified uniform spatial norm comparison, not a finite
full-datum history allowance or arbitrary-data regularity. The asymptotic
argument is analytic; the exact checker verifies the canonical fields,
full tangents and phase parity. Optional independent quadratures are
spatial diagnostics, not time evolutions or continuum enclosures.

## Checked applications and semantic interfaces

### Signed viscous pressure source and a finite-initial-resource correction

`SignedViscousPressure` constructs the actual tensor rows of
`G=(grad u)(grad u)^T` and certifies their divergence and canonical source
pressure from all three derivative parents. An ordinary unweighted
projection and local Cauchy--Schwarz give

```text
||grad q_G||_2^2 <= integral |grad u|^2 sum_k |partial_k grad u|^2,
nu ||grad q_G||_2^2 <= (1/8) integral D_Phi.
```

The second statement retains the completed matrix diffusion lower bound
as an explicit analytic input. No weighted projection contraction is used.
The canonical pressure trace also certifies the flux matrix square
`|P+sI|^2=|P|^2+s^2`, with `s=tr((grad u)^2)`.

The analytic bilinear Hessian identity retains the moving-selector flux
in the canonical viscous pressure work. A candidate correction
`F_b+8(Phi-Phi_infinity)` supplies its unselected diffusion from one finite
initial resource. It pays the complete explicit viscous pressure term
while leaving at least one quarter of the total diffusion:

```text
R_b'+D_total/4 <= integral (a+8)R_NL - C_capacity.
```

Here `R_NL` is the FULL unforced strain, pressure and transported-memory
reaction, including its transport commutator; it is not bounded by this
result. The correction is nonnegative, dominates the earlier soft excess
and retains its actual whole-space continuation adapter in Lean. Its
analytic initial bound depends on the full datum rather than energy alone.
Neither the matrix/time application nor a uniform signed history allowance
is kernel-certified. The same spatial estimates hold at forced states,
where the generator has an additional force-production leg.

The [signed source checker](labs/signed_viscous_pressure.py) retains every
3D Fourier parent/output and a nonzero selector flux. Optional independent
quadratures use the actual soft selector and full initial PDE generator,
with an optional datum-fixed threshold above the initial envelope. They
do not construct a time history or a continuum enclosure. See the
[complete derivation](labs/README.md#signed-viscous-pressure-flux-and-a-reserve-financed-by-the-full-datum)
for the precise costs, finite initial deposit and remaining signed estimate.

### A paid pressure-impulse history on the actual fluid drift

`PressureImpulseHistory` uses an actual unforced whole-space `NSEvolution`
and a componentwise passive history `H` transported and diffused by that
velocity, with `H(0)=u_0`. The auxiliary structure contains its literal PDE
and smoothness, without an assumed energy estimate. For `I=H-u`, Lean proves

```text
(partial_t+u.grad-nu Delta)I=grad p,      I(0)=0,
spent(t)=||I(t)||_2^2+2nu integral_0^t ||grad I||_2^2
        =2 integral_0^t <I,grad p>,
0<=spent(t)<=4||u_0||_2^2.
```

The nonnegative reserve `4||u_0||_2^2-spent(t)` pays the signed work on
each later interval, retaining `H`, `I` and the original initial label.
Signed payments may decrease; positive variations are not controlled.
Construction of this auxiliary PDE history and its stochastic realization
are analytic, not kernel-certified existence results.

The analytic backward stochastic formula identifies the transported
memory `C` with covariance of the PRESSURE-COMPENSATED terminal velocity.
Covariance of the raw terminal velocity is different. The joint summary
retains the cross moment between the initial velocity and its pressure
impulse, as checked on full evolving 3D NS time jets. For forced flow the
compensation contains `grad p-f`; the force impulse cannot be erased even
when its instantaneous kinetic work vanishes.

This supplies a paid physical history channel, rather than a bound on
critical stretching. Its named geometric consumer is the response of a
changing pressure-Hessian receiver `N`: with `A=grad I`, the analytic identity
`P=(partial_t+u.grad-nu Delta)A+AB` retains the full adjoint response
`N B^T-(partial_t+u.grad+nu Delta)N` and its endpoints. Controlling that
response from the original full datum remains open. Neither a
Schrodinger-bridge optimizer nor the full nonlinear reserve is identified
with the paid impulse alone. See the
[history derivation and bounded tests](labs/README.md#pressure-compensated-history-a-paid-channel-and-its-geometric-consumer).

### Actual vorticity geometry with both retained parents

`RetainedParentCompletion` keeps the original fluid gradient
`B=B_H-A`, where `B_H=grad H` and `A=grad I`. Its literal whole-space
field reconstruction, actual-vorticity comparison and actual derivative-parent
source payment are kernel-certified. The companion analytic completion keeps
the original vorticity/strain branches evaluated at B, and uses

```text
R=|B_H|^2+|A|^2,      Q=R+sqrt(sigma^2+|P_hat|^2),
Psi_joint=1+sqrt((p0(B,P_hat)+192Q^2)^2+(c0(B)+192Q^2)^2),
Phi_joint=Psi_joint+|P|^2.
```

It controls the ACTUAL vorticity and retains sufficient mixed diffusion
to pay the same full derivative-parent viscous pressure source. The scalar
curvature certificates retain the physical matrix lower bounds as inputs;
the full matrix and evolving PDE identification remain analytic.

The actual parent equations are `D B_H=-B_H B`, `D A=P-AB`. Only the
radial completion's direct pressure injection is transferred at `A(0)=0`;
the vorticity geometry, pressure commutators and later impulse-pressure
work remain. This does not remove parent deformation or prove a signed
renewal allowance. Exact Fourier tests retain both signs of that deformation
and a favorable direct pressure contribution. See the
[joint derivation and tests](labs/README.md#retained-parent-completion-with-the-actual-vorticity-geometry).

### A paid covector-parent channel and its physical conversion

The retained gradients transport as covectors. `CovectorParentHistory`
certifies their literal whole-space gradient rates and applies the existing
inverse-frame cancellation to the original passive and pressure-impulse
rows, retaining the canonical pressure Hessian and every derivative.

The analytic inverse-flow coframe obeys `D N=-B^T N-NB`, `N(0)=I`.
For `Q=N^-1`, the normalized passive-parent gradient has negative-square
production and a finite payment from the original gradient datum. The
impulse gradient additionally retains the signed work `2tr(A Q P^T)`.
Construction of N, inverse differentiation and physical-time comparison
remain analytic; the weighted impulse work and ordinary-vorticity
conversion are not bounded by the certified algebra.

An analytic integration-by-parts transfer expresses the impulse-pressure
receiver through that same covariant derivative. Diffusion absorbs it,
leaving `nu^-1 integral tr(Q)|grad p|^2`. Exact evolving Fourier jets
retain the pressure and metric derivatives in this transfer. A finite
original-datum bound on the remaining weighted pressure-force history
is still required; it is not an assumed continuation resource.

Using the forward frame instead leaves an indefinite diffusion term.
A compact central swirl and a distant disjoint swirl give an analytic
unforced short-history counterexample to its proposed nonpositive
generator. Exact canonical-pressure and parent/frame time jets verify
the positive fourth-order coefficient; the correct inverse coframe has
a negative coefficient. This rejects only the forward-frame shortcut.
Neither a full-datum history allowance nor unforced regularity is refuted.
See the [covector derivation and tests](labs/README.md#covector-parent-history-and-pressure-generated-frame-diffusion).

### Joint reconstruction isolates the changing-metric pressure work

`JointCoframePressure` reconstructs the actual fluid gradient before
estimating the two parents separately. Its metric square retains their
signed cross moment. The literal canonical NS gradient production is
`-2tr(B Q P^T)-2nu F_B`, with the same complete covariant diffusion.

For solenoidal whole-space smooth L² fields, pressure-Hessian symmetry
and integration by parts give
`integral tr(B Q P^T)=-integral sum B_ik (partial_i Q_kj) (grad p)_j`.
The certified spatial class is a constant matrix plus a smooth L² matrix
correction; the scalar pressure need not be L². Every spatially constant
matrix cancels, including anisotropic ones. No evolving coframe
construction or physical-time allowance is assumed by this identity.

The companion exact test retains full unforced pressure, coframe and
cross-moment time jets. The integrated pressure work starts at zero but
has a strictly negative first derivative on genuine 3D data, while the
initial total production retains negative diffusion. A universally
dissipative pressure sign therefore fails, conditional on the analytic
short-prefix identification. A finite original-datum signed commutator
payment and conversion to physical vorticity remain open. See the
[joint derivation and complete tests](labs/README.md#joint-coframe-pressure-and-the-retained-cross-moment).

The companion `JointCoframeCompletion` certifies a nonnegative completion
`Z=B+A^T`. The actual canonical Hessian cancels from its rate, leaving
`D Z=-Z B+(A^T B-B^T A^T)`. Its full supplied-coframe production retains
that original impulse deformation and negative covariant diffusion.
The actual antisymmetric gradient is reconstructed jointly from B_H and Z.
Exact unforced time jets give a positive first derivative of the retained
source work. Thus cancelling the explicit pressure does not make the new
source dissipative. A coupled history payment and physical conversion
remain open; see the [completion test](labs/README.md#nonnegative-pressure-endpoint-completion).

### Stochastic velocity covectors reconstruct the actual fluid

`CovectorFluidBridge` certifies the nonlinear reconstruction in the
[Constantin--Iyer representation](https://arxiv.org/abs/math/0511067):
for a smooth velocity covector m, set u to its actual Helmholtz projection.
The complete covector RHS `D m=-(grad u)^T m` projects exactly to
`nsProjectedRhs`, and `curl m=curl u`. The gradient difference is retained;
it is not an independently selected force. The literal whole-space field
reconstruction and supplied-coframe rate algebra are kernel-certified.

Analytically, m starts at u_0 and is the expectation of the inverse-flow
pullback of that same datum. The same inverse-flow moment N and Q=N^-1
give `D(m^T Q m)=-2nu F_m`, where
`F_m=sum_j |partial_j m-(partial_j N)Qm|_Q^2`.
This yields a normalized channel paid by the original velocity energy.
The stochastic construction and physical-time comparison are not yet
kernel-certified. Nor does this identify a Schrodinger-bridge optimizer.

Ordinary vorticity additionally retains the curl of the connection
`(partial_j N)Qm`. Lean certifies its exact reconstruction and a pointwise
conversion exposing both metric coercivity and that extra curl. Exact
full unforced time jets show initial signed transport cancellation but
positive later connection work. A finite original-datum history bound
and control strong enough for continuation remain open. See the
[physical bridge and curl-conversion test](labs/README.md#actual-covector-reconstruction-and-the-retained-curl).

### Retaining the joint original parent pays a geometric source error

`CovectorJointParent` certifies the literal parent RHS
`g_t=nu Delta g-(u.grad)g+(g.grad)u`; that RHS is solenoidal when u and g
are solenoidal whole-space smooth L² fields. Analytically, the same stochastic flow
has `g=E[J u_0(A)]`, where J is the inverse of the inverse-flow frame F.
This original forward parent differs from the moment quotient `a=N^-1m`.
Complete unforced time jets show that a can acquire nonzero divergence
while g remains solenoidal. Neither auxiliary parent replaces fluid velocity.

For a normalized finite joint law, Lean proves
`V=E|v-Fa|^2=h-a.m`, `0<=V<=h`, and `g-a=E[J(v-Fa)]`,
when `Na=m`. Every receiver z satisfies
`|z.(g-a)|^2<=V(z^T M z)`, with `M=E[J J^T]`.
The frames and original terminal parents share each sample. Independently
recombining them changes the response and the reserve.

The concrete consumer is the complete covariant-gradient source
`N (partial_j B) a`. Its combined receiver is
`z=sum_j (partial_j B)^T r_j`. One variance pays its entire error:
`2 sum_j r_j.(partial_j B)a <= 2 sum_j r_j.(partial_j B)g+V+z^T M z`.
This finite transfer is kernel-certified. Under the continuous stochastic
identification, `D V=2nu F_m` and spatial `integral V<=||u_0||_2^2`.
The stochastic construction and time comparison remain analytic. The
retained parent work, receiver cost, other full gradient-production terms,
and a conversion strong enough for continuation are still open. See the
[joint parent derivation and full rate tests](labs/README.md#joint-original-parent-variance-and-the-geometric-source).

### The current-gradient receiver cancels; its history defect remains

`CovectorReceiverGeometry` identifies the previous source receiver with
literal whole-space smooth fields. At every current velocity,
`sum_j (partial_j B)^T partial_j u=grad(|B|^2/2)`. Its Helmholtz
projection and integrated work against any solenoidal parent vanish.
Thus the projected receiver and parent work depend only on
`E_j=r_j-partial_j u`. These are kernel-certified current-field statements;
they do not assert that the evolving defect stays zero.

Retaining the original passive parent H gives `Y=R-grad H`, where R has
columns r_j. Lean certifies `E=grad(H-u)+Y` on the actual fields and
the supplied full-rate cancellation
`D Y=-B^T Y-YB-B^T grad H+S`, with the original Hessian/connection
source S retained. The physical-time rate and its signed payment remain
analytic/open; removing the explicit pressure Hessian is not a bound.

Volume preservation identifies the joint forward moment as
`M=E[adj(F^T F)]`, rather than `adj(E[F^T F])`. Lean certifies that
finite joint identity and the algebraic rate of
`Gamma=M-adj(N)`. Analytically its full parabolic equation is
`D Gamma=B Gamma+Gamma B^T+2nu sum_k adj(partial_k N)`.
The signed source has no universal favorable matrix sign. Complete
unforced initial PDE jets and a compactly localized straining core
reject the shortcut `M<=adj(N)`, including the full receiver cost's
actual direction. Localization, stochastic construction and the
positive-time passage are analytic, not Lean-certified. No full-datum
history allowance or global-regularity claim is refuted. See the
[receiver, pressure-completion and area-memory tests](labs/README.md#actual-receiver-cancellation-and-signed-area-memory).

### A transported original-gradient tensor retains physical curl

`JointReceiverTensor` lifts both covariant indices on the same original
stochastic path. Write `alpha=X^-1`, `F=grad alpha`, `G=F^T F`, and
`C=E[G tensor G]`. The finite normalized joint law gives a positive
definite C and certifies

```text
A=E[F^T (grad u_0)(alpha) F],
vec(A)^T C^-1 vec(A)<=E|grad u_0(alpha)|_F^2.
```

Analytically, `D A=-B^T A-AB`, where `D=partial_t+u.grad-nu Delta`
and `B=grad u`. Its inverse joint metric cancels both strains, leaving
the complete nonnegative diffusion cost. This payment uses the original
gradient energy, with no allowance reset at history boundaries.
Differentiating the Constantin--Iyer velocity covector produces
`grad m=A+E[sum_a u_0,a(alpha) Hess(alpha_a)]`. The second tensor is
symmetric, so the physical curl is exactly A's antisymmetric part.
Lean certifies this actual smooth-field curl reconstruction with the
symmetry identification explicit, and proves the finite original-label
bound and supplied full production identity. Continuous stochastic
construction, differentiation and physical-time comparison remain
analytic, rather than consequences of finite samples.

The changing metric still needs a datum-fixed conversion controlling
physical vorticity over every admissible continuation. That is the
missing arbitrary-history estimate. A finite normalized payment alone
does not bound the ordinary gradient energy. The earlier completed
receiver Y retains its separate, generally nonzero internal source;
the source-free original tensor does not erase that source.

Independent averaging cannot replace C by `N tensor N`, with `N=E G`:
the parabolic product rule adds a signed cross-diffusion term. Exact
canonical unforced jets retain it and the joint area's covariance.
A force also adds curl absent from the original-data tensor, even when
its initial kinetic work is zero. The forced representation requires
the accumulated pulled-back source. See the
[joint tensor, original payment and curl tests](labs/README.md#joint-two-index-metric-and-original-gradient-payment).

### Physical curl needs only its actual direction's frame budget

`JointCurlGeometry` combines the retained joint metric's Cauchy bound
with its exact skew/area channel. For a normalized finite common law,
det F=1, `J=F^-1`, `M=E[J J^T]`, and `q_A=vec(A)^T C^-1 vec(A)`,
Lean certifies, for every direction z,

```text
(z.curl A)^2 <= 2 q_A z^T M z,
|curl A|^4 <= 2 q_A (curl A)^T M (curl A).
```

With the previously stated curvature symmetry and gradient projection
difference, this curl is the literal whole-space field's vorticity.
Thus a bound `omega^T M omega<=kappa |omega|^2` suffices for
`|omega|^2<=2kappa q_A`. It asks for the actual curl direction's cost,
not uniform coercivity in every tensor direction. Lean also proves
the conversion with kappa=1 when every retained J^T preserves that
curl, as in a common planar normal channel. A nonzero z-independent
periodic field is not a finite-energy whole-space field.

There is a positive analytic consumer with genuine stretching. In the
actual periodic triangular mixing class
`u=(a exp(-nu t) sin y,0,v)`, `v(0)=b sin x`, the stochastic bounds
give `|v_x|<=b exp(-nu t)` and
`|v_y|<=ab exp(-nu t)(1-exp(-nu t))/nu`, for a,b>=0 and nu>0.
Every original forward frame has the form

```text
J=[[1,beta,0],[0,1,0],[gamma,delta,1]],
|beta|<=r=a/nu,  |gamma|<=s=b/nu,  |delta|<=rs,
tr(JJ^T)<=kappa=3+r^2+s^2+r^2s^2.
```

The finite triangular conversion is kernel-certified. The stochastic
construction, pathwise comparison and integrated original-gradient
payment are analytic; together they give an all-time enstrophy allowance
`2kappa ||grad u_0||_2^2` for this periodic class. No new allowance is
assigned at a history boundary. The vertical component does not feed
back into the horizontal parent; reciprocally amplifying parents remain
the missing extension.

Volume preservation and coherence alone cannot pay the geometric
conversion. A single determinant-one frame has q_A=2 but curl square
4lambda^2. This is a kinematic obstruction, not a finite-energy NS
counterexample. Actual canonical unforced initial jets also allow
the directional geometry to increase from its initial value. The
complete evolution retains mixed derivatives of vorticity and M;
their signed payment over arbitrary histories is open. See the
[directional curl, mixing history and full cost-rate tests](labs/README.md#physical-curl-and-a-paid-triangular-parent-history).

### Reciprocal parents renew pressure; their full signed history remains

The [cyclic pressure-history lab](labs/cyclic_pressure_history.py) evolves
the feedback test `u_0=a(sin y,sin z,sin x)` with positive viscosity.
It retains all velocity components, generated Fourier outputs and the
original forward moment M, starting at the identity. At the fixed
symmetry centre, write

```text
B=[[0,alpha,beta],[beta,0,alpha],[alpha,beta,0]],
ell=alpha+beta,   omega=(beta-alpha)(1,1,1),
Pi=partial_x partial_y p,   mu=(1,1,1)^T M(1,1,1)/3.
```

The complete smooth equations are
`ell'=nu Delta ell-(alpha^2+beta^2)-2Pi` and
`mu'=nu Delta mu+2ell mu`. Thus the actual curl-direction cost is mu
when the curl is nonzero; mu is defined without dividing by curl at its
zeros. Pressure, spatial frame diffusion and the already accumulated
original moment cannot be discarded at a history boundary.

Exact symbolic and complete rational Fourier jets give
`Pi(0)=Pi'(0)=0` and `Pi''(0)=-4a^4/3`, at every positive viscosity.
Consequently `integral_0^tau -2Pi=(4/9)a^4 tau^3+o(tau^3)>0` on a
sufficiently short actual smooth interval. The local-existence/Taylor
passage is analytic, not kernel-certified and not a uniform time window.
This refutes a universal nonrenewing pressure sign. It does not refute
a finite allowance from the full original datum.

The optional dealiased prefixes record the signed pressure payment,
quadratic loss, viscous term, frame strain and frame diffusion at the
same time-integration stages. Full-product pressure is observed on an
enlarged grid; the discarded dynamical outputs have explicit signed
projection residues. A local negative stretching rate does not force
the original moment to decrease: diffusion can bring in deformation
generated elsewhere. These are numerical histories, not continuum
enclosures or arbitrary-data estimates. The remaining theorem is a
full-datum payment for the coupled spatial geometry over all compatible
continuations. One division-free sufficient target is a finite bound on
`integral omega^T Momega`: spatial Cauchy and the analytic original
payment give `||omega||_2^4<=2||grad u_0||_2^2 integral omega^T Momega`,
on either R3 or the torus. Its complete signed production remains
unpaid for arbitrary histories. See the
[pressure renewal and original-frame ledgers](labs/README.md#cyclic-pressure-renewal-and-the-original-frame-history).

### The original tensor splits; its physical compatibility retains pressure

`MettapediaNS.JointTensorSymmetry` identifies exactly what the retained
same-frame quadratic reserve contains. With `W=C^-1`,
`C=E[(F^T F) tensor (F^T F)]` and `M=E[J J^T]`, determinant-one frames give

```text
q_A=q_sym+(1/2) omega^T M^-1 omega,
F_A=F_sym+F_skew.
```

The first identity includes the literal physical curl consumer with its
existing projection and symmetric-curvature hypotheses. The full diffusion
and supplied source-free production also split when the retained spatial
connections preserve transpose. Those connections and every tensor
derivative remain explicit. Thus this quadratic norm has no cross payment
between the symmetric and skew channels. It does not exclude nonlinear
coupling through the velocity, pressure and their complete histories.

A distinct physical quantity is the compatibility defect `E=A-grad u`.
It is symmetric after actual curl identification and starts at zero. With
`D=partial_t+u.grad-nu Delta`, `B=grad u` and `P=Hess p`, its rate is

```text
D E=-B^T E-E B+P-B^T B,
D(vec(E)^T W vec(E))=2 vec(E)^T W vec(P-B^T B)-2nu F_E.
```

Lean certifies the finite defect algebra, complete supplied production,
and the canonical unforced NS gradient-rate bridge. Continuous stochastic
construction and differentiation are separate analytic obligations. No
bound on the signed source over arbitrary histories follows from the ledger.

The [exact symmetry and compatibility lab](labs/joint_tensor_symmetry.py)
rejects a nonpositive-matrix shortcut. For the actual periodic datum
`u_0=(a sin y,c sin z,b sin x)`, at `x*=(pi/2,pi/2,0)` and `z=(1,-1,0)`,
the complete canonical PDE jets give `z^T E_t(0)z=0` and
`z^T E_tt(0)z=4abc-2nu(a^2+b^2)`. At `a=b=c=1,nu=1/10`,
`z^T E(t,x*)z=(9/5)t^2+o(t^2)>0` on a sufficiently short smooth interval.
That time passage is analytic, not Lean-certified or uniform. It refutes
preservation of `E<=0`, not a full-datum history payment or global regularity.
The remaining estimate must pay the physical compatibility/geometry through
its coupled pressure and parents; neither normalization nor a fresh resource
at a composition boundary supplies that payment. See the
[full channel and source checks](labs/README.md#same-frame-tensor-channels-and-the-physical-compatibility-source).

### Complete pressure cotangent and a paid history with nonzero pressure

`MettapediaNS.JointPressureCotangent` retains all nine tensor coordinates
and all three spatial connections. For `e=vec(E)`, `W_j=-W K_j`,
`r_j=partial_j e-K_j e` and `Z=unflatten(W e)`, the exact receiver is

```text
(div Z)_i=sum_j (W r_j)_(i,j),
R(W)_il=sum_j W_(i,j),(l,j),
2 v.div Z <= nu F_E + nu^-1 v^T R(W)v,  nu>0.
```

Lean certifies the complete receiver identity, its agreement with the
existing diffusion cost, the positive induced pressure metric, and the
completed-square absorption. Taking `v=-grad p` and weakly integrating
by parts pays half the original `2nu F_E` diffusion. It leaves the literal
cost `Gamma=integral grad p^T R(W)grad p`. Weak integration and continuous
stochastic identification remain analytic. This is not an unweighted
Helmholtz contraction. Even for one frame, `W=H tensor H` gives
`R(W)=tr(H)H`, so volume preservation alone cannot remove its anisotropy.

There is a positive analytic consumer on the normalized period-2*pi torus:

```text
u=a exp(-2nu t)(sin x cos y,-cos x sin y,0),
p=(a^2/4)exp(-4nu t)(cos 2x+cos 2y),  a>=0, nu>0.
```

The full nonlinear advection is cancelled by this pressure, and the
remaining velocity evolves by heat. Its complete parent integral is
`D=a/(2nu)`, fixed by the original datum. Original stochastic frames
give `exp(-4D)I<=W<=exp(4D)I`, and
`mean(|grad p|^2)=a^4 exp(-8nu t)/4`. Together with the complete quadratic
parent source, these imply

```text
mean(q_E(T))+nu integral_0^T mean(F_E) <= K,
K=exp(2a/nu)[3a^4/(32nu^2)+(a^3/nu)(exp(a/nu)+2/3)].
```

The remaining allowance `R_TG(t)` is explicitly nonnegative and decreasing.
For every `s<=t`, the cost `mean(q_E(t))-mean(q_E(s))+nu integral_s^t F_E`
is at most `R_TG(s)-R_TG(t)`; its original labels and reserve are not reset
at seams. The original `q_A` payment and frame comparison also give the
physical bound `mean(|grad u|^2)<=2exp(4D)(a^2+K)`. These stochastic and
space-time inequalities are analytic; the lab checks their scalar
identities and the literal all-time unforced velocity and pressure.
This class has nonzero pressure but no reciprocally amplifying parent.
Obtaining a datum-fixed metric/source payment for arbitrary parents remains
open; assuming a bound on their unknown future strain would not resolve it.

Weighted pressure orthogonality also requires care. For the original metric,
`J_p=mean(vec(B)^T W vec(P))` starts at zero, but
`J_p'(0)=4 mean(S^2:P)`, with `S=(B+B^T)/2`. Complete canonical 3D jets give
`-391507472/10405395`; an asymmetric annular planar swirl gives the opposite
sign after smooth approximation. Thus neither ordinary pressure
orthogonality nor a universal favorable sign discards the weighted work.
This is a physical-gradient pressure test, distinct from the defect source
work above. The smooth passage is analytic, with no certified uniform
window, recurrence, singularity or whole-space lift. See the
[full cotangent and paid-history calculation](labs/README.md#joint-pressure-cotangent-and-a-complete-paid-history).

### Causal joint-source transfer and reciprocal pressure generation

`MettapediaNS.JointSourceHistory` keeps the combined source
`S_E=Hess p-B^T B` in the original joint metric. Its finite production
estimate retains the complete covariant diffusion and the pressure-parent
cross term in `S_E^T W S_E`. The scalar physical-time theorem states:

```text
q(0)=0,  q'+d<=2 sqrt(q)b,  q,b,d>=0
    => q(T)+integral_0^T d <= (integral_0^T b)^2.
```

For the compatibility defect, weak spatial integration and Cauchy--Schwarz
give `q=integral E:W E`, `d=2nu integral F_E` and
`b=sqrt(integral S_E:W S_E)`, analytically. The time comparison is
kernel-certified, including vanishing energies and all compatible intervals.
Writing `B_source(t)=integral_0^t b`, every interval keeps the square
increment `B_source(t)^2-B_source(s)^2`. A fresh source square would lose
the cross cost with prior history. A proved original-datum cap `L` would
give the nonnegative reserve `L^2-B_source(t)^2`; the cap is still open.

The [exact reciprocal-source lab](labs/joint_source_history.py) tests actual
unforced initial data `u0=(a sin y,b sin z,c sin x)`. Pressure starts at zero,
but `p_t(0)=-2abc cos x cos y cos z`. With all original moment and packet
jets retained, the defect's mean pressure work satisfies

```text
2mean(E:W Hess p)=(9/2)a^2 b^2 c^2 t^3+o(t^3).
```

This positive feedback vanishes when any parent is removed. The complete
fourth energy jet keeps the generated pressure, parent work, changing metric
and all diffusion. The causal pressure-history input square is sharp at its
first nonzero order, proportional to `t^4`; the earlier cotangent absorption
instead charges `t^3/nu` at that order. The causal comparison uses a weighted
Hessian source norm, so it is a different estimate, not a free reduction of
the derivative requirements.

The exact algebra checks and fixed-datum short-time analytic passage do not
prove a uniform turnover window, indefinite renewal or singularity. The
source-norm cap may overpay cancellations between different times; a weaker
signed correction remains possible. Both an original-datum history payment
and sufficient actual curl-direction geometry remain open. This comparison
does not identify an arbitrary-fluid Schrödinger-bridge optimizer, supply an
independent physical force, or assume a bound on unknown future strain.
See [the complete source and history tests](labs/README.md#causal-joint-source-history-and-reciprocal-pressure-generation).

### Directional cubic renewal and a signed physical continuation target

`MettapediaNS.JointCubicRenewal` observes the original gradient packet only
in the actual vorticity direction. Write `H=omega^T A omega`, retain
`E=A-grad u`, and let `h` solve passive advection--diffusion with original
label `h0=omega0^T grad(u0) omega0`. The dual rates of A and omega cancel
strain before estimating. Lean certifies the finite complete production:

```text
D H = -2nu sum_k [(partial_k omega)^T A(partial_k omega)
       +(partial_k omega)^T(partial_k A)omega
       +omega^T(partial_k A)(partial_k omega)].
chi=h-H,
omega^T grad(u) omega=h-chi-omega^T E omega.
```

The mixed diffusion is signed. Combining its covariance history with the
compatibility history cancels the original-packet derivatives; it retains
the actual directional source `omega^T(Hess p-B^T B)omega` and the complete
physical-gradient diffusion. Same-path transport of the cubic label is
also kernel-certified before averaging. The product of three averaged
fields does not preserve that label. Passive-scalar construction, the
continuous original stochastic identification and spatial mass conservation
remain analytic obligations, not new stochastic Lean theorems.

For actual whole-space smooth unforced evolutions, the module identifies
the continuous stretching mass and proves the exact order-one balance.
It states the following sufficient signed renewal estimate, for every
smooth prefix tau of a prescribed horizon T:

```text
-2 integral_0^tau integral(chi+omega^T E omega)
  <= (2-delta)nu integral_0^tau integral |grad omega|^2+K(u0,nu,T),
0<delta<=2.
```

The kernel theorem uses the literal order-two dissipation and the physical
stretching-mass difference for renewal. With delta=1 and the budget fixed
before all solution prefixes, it supplies the existing whole-space
continuation criterion. The equivalent curl/diffusion interpretation and
the realization by h, chi and E are analytic here. The budget itself is
OPEN: the identity rewrites the remaining crux, not a proof of its payment.
Unlike the source-norm benchmark, this formulation need not separately pay
the full weighted Hessian norm or a uniform metric comparison. It retains
the actual vorticity geometry and both signed histories jointly.

The [exact cubic-renewal lab](labs/cubic_parent_renewal.py) checks all
canonical NS outputs and mixed derivatives. Two different scales can have
zero initial signed cubic mass but either sign of covariance production
at every positive viscosity. This excludes a universal favorable covariance
sign or payment from that signed mass alone. The unsigned original label
mass remains finite for the stated smooth class and does not vanish merely
because signed mass cancels. A datum-paid bound on coupled renewal is not
refuted. Reciprocal-parent tests also retain the generated pressure and the
compatibility work. A zero-kinetic-work diagnostic force contributes an
explicit curl-source leg; it is not the imported blowup example or an
internally realized force. No uniform time window, indefinite renewal,
singularity or whole-space finite-energy lift follows from these tests.
The joined budget has paid analytic consumers. The established triangular
mixing class has the all-time allowance `a^2 b^2/(6nu^2)` and decreasing
reserve `a^2 b^2[4exp(-3nu t)-3exp(-4nu t)]/(6nu^2)`. For any mean-zero
periodic divergence-free monochromatic Beltrami field, the full heat-decaying NS evolution
has zero mean stretching and hence zero joined renewal allowance, despite
nonzero pressure and possible three-dimensional pointwise stretching.
The original-frame interpretation remains analytic. Neither class
supplies a bound for arbitrary mutually amplifying parents.
The complete original cubic label is also insufficient as the only initial
resource. Periodic triangular data `u0=(A sin y,0,A sin x)` have `h0=0`
pointwise for every A. At fixed positive viscosity, a linear parabolic
difference estimate at one turnover gives an enstrophy increase of at
least `A^2/8` for sufficiently large A. The half-dissipation renewal excess
is larger still. Thus no finite allowance depending only on this common
label, viscosity and a prescribed positive horizon covers these data.
Their full initial resources grow with A, and the full-datum mixing
allowance above pays them. This is an analytic periodic result; the lab
checks the exact limiting equations and integrals, not the convergence
proof. No full-datum reserve or regularity claim is refuted.
See [the full directional calculation](labs/README.md#directional-cubic-renewal-and-original-labels).

### Generated modes can return work to their original parents

The [returned-parent lab](labs/parent_return_history.py) tests complete
unforced histories starting with empty unobserved modes. An original parent
can receive positive nonlinear work later, after earlier transfers generated
those modes. Consequently a universal assertion that every return damps its
original parent is too strong. This does not refute a signed history payment.

For actual triangular data `u0=(A sin y,0,A sin x)`, `A>0`, put
`sigma=A t`, `kappa=nu/A`. A scalar parabolic contraction comparison with
`sin(x-sigma sin y)` proves that whenever `0<kappa<=1/1000`, the original
vertical sine mode has nonlinear kinetic work at least `A^3/96` on
`47/16<=sigma<=49/16`. Its integrated returned work is at least `A^2/768`.
The phase evolution changes the parent's sign; the returned work is paid by
energy previously stored in the generated modes. The original shear gives
an all-time absolute kinetic-work allowance `A^3/(6nu)`. This kinetic
allowance is distinct from the actual cubic stretching required for
continuation. The interval and its positive-viscosity passage are analytic;
the checker verifies rational margins and complete finite identities.

Three nonzero cyclic sine parents generate pressure and reciprocal
feedback. Complete canonical jets retain the first returned work and a
three-parent correction absent from the sum of the two-parent limits.
The generic returned-work third derivative has a positive correction
`(3/2)a^2 b^2 c^2`. It is not a time-interval or indefinite-renewal theorem.
Dealiased three-dimensional prefixes with a third parent `epsilon=1/20`
show positive returned work near the same phase interval, with spatial
and time refinement and retained pressure. These are numerical prefixes,
not continuum enclosures or certified all-time evolutions.

There is a paid analytic neighborhood with genuine reciprocal feedback.
The triangular reference's fourth derivatives are bounded from its original
integrated shear `|a|/nu` by explicit polynomials. A datum-fixed H3
smallness threshold on a solenoidal perturbation then absorbs its own
nonlinearity into viscosity, using the complete NS pressure orthogonality.
The resulting all-time H3 envelope gives a decreasing nonnegative reserve
paying actual cubic stretching on every compatible interval. The third
parent can be nonzero. This is a perturbative calibration, with a potentially
very small threshold; the numerical `epsilon=1/20` is not certified to
satisfy it. Scalar recurrence and reserve identities are checked exactly;
the continuous estimates are analytic, not new Lean declarations.

The physical distinction is between return from retained old storage and
independently supplied new work. Empty initial hidden modes do not eliminate
later returns. The arbitrary-data question is whether full original
resources can pay the derivative-level signed renewal when the mutually
affecting parents no longer remain in a controlled neighborhood. Neither
the finite kinetic-energy ledger nor these paid classes settles that
question. No internal realization or exclusion of the imported forced
blowup construction is established here.
See [the return interval, three-parent test and paid neighborhood](labs/README.md#returned-parent-work-and-a-paid-reciprocal-neighborhood).

### Complete reciprocal stretching histories and higher loops

The [paired-stretching lab](labs/paired_stretching_history.py) compares the
actual cubic stretching of a three-parent evolution with the sum of its
three complete two-parent evolutions. It includes all interference terms,
canonical pressure and generated modes. This observable differs from the
self-stretching of the velocity remainder after pair subtraction.

For original cyclic sine data, the first mixed time jet is negative even
though its original-parent kinetic-return correction is positive. An
independent generic radius calculation extends this depletion across
scales. The mean-zero profile version has first mixed third derivative
`-12 ||f'||_2^2 ||g'||_2^2 ||h'||_2^2` for data `(f(y),g(z),h(x)`.
This generalization uses Fourier phase and amplitude-degree balance; it
is analytic, with complete finite-profile checks, not a Lean PDE theorem.

The first complete viscous amplitude loop also stays favorable. For
`u0=alpha*(sin y,sin z,sin x)`, write `tau=nu*t`. Its sixth-degree mixed
stretching is `alpha^6/nu^3` times

```text
gamma6(tau) = (3/32) exp(-4tau) [1-2tau+(2tau^2-1)exp(-2tau)] <= 0.
```

`MettapediaNS.PairCycleHistory` certifies this explicit rate, its common
primitive, payment on every compatible interval, and the complete signed
enstrophy/dissipation balance. The identification with continuous NS
amplitude derivatives remains analytic. A single coefficient supplies no
bound on the full nonlinear remainder. The next, eighth-degree loop has
positive complete integrated stretching, so termwise favorable loop signs
cannot supply the missing payment. Each tested coefficient has a finite
original-amplitude reserve; convergence and payment of the full sequence
remain open.

The signed diffusion difference changes the comparison. The sixth-degree
enstrophy difference is positive at `tau=2`, despite nonpositive stretching
throughout that coefficient history. Lean certifies the scalar inequality.
A finite-time analytic solution-map expansion gives actual small-data
examples violating the stronger pairwise enstrophy ordering; that passage
is analytic here. Numerical full nonlinear histories at `nu=1/5` also
change the mixed stretching sign near `t=5.5`, with spatial/time refinement.
They are Galerkin evidence, not continuum sign enclosures.

The remaining target is a reserve for the complete signed renewal sequence,
retaining its pressure, geometry, diffusion and spent initial resources.
The original cubic label has zero mean for these cyclic data and their
pair limits. Thus the mixed joined chi/E renewal cost is precisely
`2 integral Delta G`; this is a physical calibration of the existing
continuation observable, rather than a kinetic-work surrogate.
The exact first loop and the finite coefficient reserves are calibrations
for that target. Neither gives the arbitrary-data continuation allowance
or a realization of the imported forced blowup construction.
See [the full viscous-loop calculation and comparison tests](labs/README.md#complete-pair-stretching-and-viscous-reciprocal-loops).

The [anisotropic history calculation](labs/anisotropic_pair_history.py)
extends the entire first mixed amplitude history to arbitrary positive
parent frequencies, with their cyclic ordering retained. For squared
frequencies `a,b,c>0`, its rate satisfies the quantitative bound

```text
gamma6(a,b,c,tau) <= -(abc/4) tau^3 exp[-2(a+b+c)tau] <= 0.
```

This is an all-time coefficient estimate, not just an initial-time jet.
The exact symbolic recurrence keeps canonical pressure and every generated
mode, and independent rational recurrences check literal curl stretching,
both energy ledgers and unequal-scale resonances.
`MettapediaNS.AnisotropicCycleHistory` certifies the scalar bound, payment
on every nonnegative interval, agreement with the unit-frequency formula,
and preservation under finite nonnegative spectral sums.

For mean-zero separated profiles `(f(y),g(z),h(x))`, Fourier phase balance
expresses this first mixed history as such a sum. Consequently its sign
persists for arbitrary smooth separated profiles; that physical
identification and the smooth limit are analytic, with an exact complete
multiharmonic fixture. Higher reciprocal orders can be positive, so the
result does not yet pay the full nonlinear history, even within this
family. See [the scale-uniform formula and its physical scope](labs/README.md#first-reciprocal-history-at-arbitrary-parent-scales).

There is also a complete analytic example of paid positive renewal.
The horizontal cellular field `exp(-nu*t)*(a sin y,b sin x)` has explicit
pressure and transports a vertical component initially
`c*(cos x+sigma cos y)`. For `sigma=+1`, `a,b>0` and `c!=0`, its full stretching
minus the three complete pair stretchings has derivative `abc^2/2` at
time zero. The actual cumulative difference is therefore positive on a
short interval. These unforced 2.5D flows are globally smooth and admit
an explicit decreasing reserve fixed by the original amplitudes and
viscosity. The opposite receiver phase reverses the initial mixed sign
while preserving initial energy and horizontal pressure.

This analytically refutes a zero-allowance comparison over arbitrary
parent geometries while exhibiting the finite payment that a repaired
history budget needs. The complete parent strain here decays autonomously;
renewal of that parent strain remains open. In the distinct three-axis
cyclic class, refined numerical tests of amplitudes `(1,1,5)` also give
positive cumulative mixed stretching. Those numerical signs have no
continuum enclosure. See [the exact cellular calculation, original
reserve and numerical refinements](labs/README.md#positive-mixed-renewal-with-a-finite-original-allowance).

The next [planar parent reserve](labs/README.md#a-strain-paying-reserve-for-interacting-planar-parents)
allows arbitrary smooth mean-zero horizontal two-dimensional NS data,
including nonlinear parent interactions and initial gradient growth.
Writing `Z=||omega||_2^2` and `Y=||grad omega||_2^2` on the normalized
`2*pi` torus, its explicit original-state reserve is

```text
r = (8/nu) sqrt(Y) exp(64 Z/nu^2),     -r' >= ||grad v||_infty.
V = ||grad theta||_2^2 (exp(2r)-1),   -V' >= 2 |G_theta|.
```

Here `theta` is an arbitrary advected vertical component, and the full
flow remains independent of the vertical coordinate. The continuum
identification and periodic Sobolev estimates are analytic.
`MettapediaNS.PlanarParentReserve` certifies the scalar derivative,
absorption, receiver composition and interval-payment inequalities with
their explicit hypotheses. The reserve is not an arbitrary 3D Lyapunov
function: the averaged equations of a general 3D flow introduce actual
Reynolds sources. Both signed source works remain in the formal
inequality, and exact complete Fourier checks exhibit an increasing
parent reserve under internal, unforced transfer. Paying those sources
together with the unresolved field is the remaining physical obligation.

The [full-energy parent reserve](labs/README.md#full-energy-bellman-payment-and-the-high-strain-remainder)
pays bounded strain observations even when hidden fluid repeatedly
feeds them. For the complete energy `E=||u||_2^2`, dissipation
`d=||grad u||_2^2` and an observation `q<=C sqrt(d)`, the finite-horizon
reserve is `R=C sqrt((H-t)E/(2nu))`. Its Bellman square completion gives
`R'+q<=0`. `MettapediaNS.FullEnergyParentReserve` proves the exact
whole-space NS kinetic rate and payment on every compatible subinterval,
using a fixed positive energy cushion at zero energy. No future bound on
the parent or its hidden suppliers is assumed. The spatial observer
identification is analytic: a Fourier selection of at most `M` modes has
`C=sqrt(M)`, even when its frequencies and geometry change with the history,
and heat smoothing at length `ell` on R3 has `C=(8pi)^(-3/4)ell^(-3/2)`.

This pays the low-strain part of the full vorticity equation; it does not
pay the high-strain remainder. The latter is retained in an explicit
weighted enstrophy inequality. Exact Fourier data show that the growth
of the observer constant with resolution is unavoidable in the stated
pointwise norm bound. Changing resolution adds its own reserve derivative.
An adaptive anisotropic hidden-energy correction also fails an exact
test because its evolving coefficients introduce positive quartic work.
Both observations guide the outstanding geometric high-strain estimate.

The [heat-gradient observation test](labs/README.md#heat-gradient-observations-and-physical-evolution-compatibility)
isolates another obligation in a heat/HJB lift: its observed velocity
must satisfy the actual fluid evolution, beyond matching the initial
velocity. An explicit positive heat profile and tight solenoidal frame
give zero initial observed velocity and a later nonzero shear with a
solenoidal force. Both composition conventions retain this obstruction.
An analytic family matches arbitrarily many initial velocity derivatives
before its source becomes visible. `MettapediaNS.HeatGradientObserver`
certifies the scalar heat/log-gradient calculation, the explicit fluid
residual and one delayed case. The group and spatial identifications
remain analytic. The unrestricted push-down implication fails; an
invariant physically compatible class of lifts remains a separate task.

The [physical covector HJB calculation](labs/README.md#a-physical-covector-hjb-equation-and-its-mean-action-payment)
uses the existing fluid reconstruction directly. On each smooth periodic
unforced prefix, `m=u-grad S` has the actual covector evolution when
`D S=|u|^2/2-p`. Its HJB source is `|m|^2/2-p`; the positive heat transform
retains that internal potential. The auxiliary control does not force the
fluid. With zero-mean pressure, `(mean S)'=||u||_2^2/2`, paid on every
compatible interval by `(H-t)||u(t)||_2^2/2`. This analytic identification
and payment survive interacting parents, with exact shear and full 3D-jet
checks. They control the signed spatial mean; the gradient/pressure work
and the sufficient physical stretching budget remain open.

The [HJB curvature-completion test](labs/README.md#hjb-curvature-completion-and-the-physical-curl-quotient)
then retains the tensor `K=A-grad m`. Its equation cancels the explicit
pressure Hessian but retains `sum_l m_l Hess(u_l)`. Adding its positive
joint-metric energy to the original tensor energy and a fixed multiple
of the mean-action reserve fails the signed renewal supersolution test
on actual viscous shears. Explicit Brownian-moment bounds give a
positive-viscosity interval counterexample, analytically with exact checks.
This symmetric curvature is invisible to the physical curl; its payment
is not required for curl reconstruction. The directional frame geometry
and arbitrary-history signed budget remain open.

The [rotational curl reserve](labs/README.md#a-rotational-curl-reserve-and-its-internal-source)
uses classical axisymmetric no-swirl estimates to pay a physical,
spatially changing direction. A bound c on `|u_r/r|`, fixed by the original
vorticity quotient, makes `Z(t)(exp(2c(H-t))-1)` pay absolute stretching
on every smooth prefix. The existing `PlanarParentReserve` theorem supplies
the scalar payment; the geometric PDE and continuation application are
analytic. Swirl restores the internal source `partial_z((u_theta/r)^2)`;
asymmetry and moving geometric choices have additional exact defects.
Even with swirl, pairing that source with the meridional streamfunction
is paid by the actual swirl kinetic energy, with signed transfer retained
across every seam. The continuation cost needs a higher derivative
pairing. The checker retains these distinctions and tests smooth
whole-space data. Payment for arbitrary interacting histories remains open.

The [joint rotational enstrophy calculation](labs/README.md#joint-rotational-enstrophy-and-the-remaining-directional-work)
then retains both vorticity channels. Their balances cancel the higher
swirl source exactly, leaving the meridional strain acting on the swirl
gradient. The remaining term is identified with the literal full
three-dimensional stretching, including its boundary flux. Two smooth
Schwartz data have identical energy, enstrophy, dissipation and zero source
pairings but opposite stretching; one has increasing enstrophy at positive
viscosity while its meridional stretching is negative. The complete signed
geometric history is still needed. The local density equation retains the
internal boundary flux, and spatial reserve weights have an explicit
compatibility defect. Weights depending on `r^3 partial_r chi` preserve
that cancellation, but their evolving parent cost remains unpaid. These
analytic identities and exact checks supply no arbitrary-data allowance
or new Lean continuation theorem.

The [generated-parent test](labs/README.md#generated-parents-and-an-initially-empty-geometric-reserve)
computes the full evolution of those compatible weights. A smooth
whole-space pure swirl has zero initial meridional parent and stretching,
but its actual pressure-corrected acceleration generates strictly positive
stretching production. Exact heat-resolvent integration and a uniform
local Taylor bound give a short positive-viscosity interval of enstrophy
growth and positive signed renewal excess. Consequently no nonnegative
reserve that starts at zero on these data can pay that cost, including
the tested bounded parent-weight family with arbitrary datum-dependent
parameters. A repaired reserve must charge the swirl's existing ability
to generate a parent before the parent is present. This finite-burst
obstruction does not refute a positive full-datum allowance or regularity.
The identities are symbolically checked; the interval proof is analytic.

The [source-funded forecast reserve](labs/README.md#a-source-funded-reserve-pays-the-first-generated-interval)
then pays that actual first burst. It combines the current parent with
the response to the current swirl source, using coefficients fixed from
the original datum and a sufficiently short horizon H. Its initial
allowance is `14gamma H^2/3`. The complete derivative retains the new
nonlocal and boundary-flux defects. `RotationalForecastReserve` certifies
the scalar derivative, strict polynomial margin and tolerance for five
errors; local weighted transport-diffusion estimates supply those errors
analytically for the physical calibration. Both earlier Gaussian phases
also admit a local payment. Reinitializing the reserve after each interval
would give fresh resources; no bound on repeated renewal or arbitrary
prescribed horizons is established.

The [circulation source reserve](labs/README.md#circulation-pays-source-histories-with-a-radial-weight)
provides a different payment on every available smooth axisymmetric
whole-space prefix. If `C4(0)=integral (r u_theta(0))^4 dx` is finite,
`C4/(3nu)` pays the complete history of `r^6 S^2` in the lifted measure.
With a smooth cutoff zero inside radius rho and one beyond 2rho, it pays
the filtered source and the full Hessian of its nonlocal response, with cost
`C4(0)/(3nu rho^6)`. Removing that radius weight restores signed radial
compression; shrinking rho also adds a positive payment defect. Exact
Gaussian tests separate decreasing circulation stock from growing
source-scale stock. These analytic estimates do not pay full stretching,
the complementary axis source, or the angular defects of general 3D flow.
For the full source norm, the actual weighted quartic equation identifies
a sufficient compression potential: `W>=1` and
`W_t+v.grad W+nu L5 W-6(u_r/r)W<=0`. Its logarithm has the quadratic HJB
Hamiltonian, with actual fluid coefficients held fixed. Bounding its
initial weighted cost from the original datum remains open; auxiliary
sampling drifts do not become forces on the fluid.
The same source payment and the actual scalar vorticity propagator also
bound accumulated `u_r/r` from all initial meridional vorticity and all
subsequent sources generated at r>=2rho. Both history components travel
under the full interacting velocity. The remaining component comes from
generation in r<=2rho and retains its nonlocal response. A finite,
datum-controlled exponential factor removes the paid radial history from
the conditional HJB weight without restarting its allowance.

The [physical-measure compression criterion](labs/README.md#physical-compression-weight-and-its-continuation-consumer)
now connects a uniformly funded weight to full gradient-energy continuation
for smooth axisymmetric whole-space data. In physical measure its condition
is `W>=1` and `W_t+v.grad W+nu Lminus W-8(u_r/r)W<=0`, with
`Lminus=partial_rr-partial_r/r+partial_zz` and a favorable, nonzero axis
boundary term. A bound on the initial weighted fourth-power swirl slope,
uniform over all available prefixes, pays the full source history. Analytic
propagator, maximum-principle and energy estimates then produce the bound
consumed by `hasNSEvolution_of_orderOne_bound`. The weight's initial funding
remains open; the physical implication is not yet a Lean theorem.
The associated sampling process has an absorbing radial coordinate and
continuing axial motion. Its axis trace must dominate stopped fourth
moments of stochastic axial deformation. Every smooth positive static
radius-only weight fails the pointwise criterion on the compressive
Gaussian calibration. Evolving weights and full-datum integrated allowances
are not refuted. The actual pressure curvature and lateral diffusion that
can sustain axial stretching remain in the next physical estimate.

The [axial deformation pressure test](labs/README.md#axial-deformation-retains-its-actual-pressure-suppliers)
derives the complete stochastic acceleration of the required deformation
moment, including its positive quadratic variation. Smooth unforced
whole-space Gaussian data realize an expanding state that defeats every
frozen positive quadratic metric squared on deformation and its rate.
Surrounding-fluid variations leave the initial axis velocity, strain and
diffusion trace fixed while changing their canonical pressure acceleration.
The same metric obstruction occurs in the source-free no-swirl class;
it does not refute a finite datum-dependent history allowance.
The existing energy-paid distant-pressure estimate supplies an explicit
whole-horizon factor for this new observable. Signed nearby-pressure work,
full viscous acceleration and stochastic quadratic variation remain in
the unpaid core cost. The symbolic checks pass; physical history and
stopping arguments are analytic, with no new Lean theorem claimed.
The stronger pathwise factorization `J^4<=exp(8M_H)J_core^4` removes the
already paid initial and outside-source parents without differentiating
them or factoring expectations. A pure-swirl calculation then produces
strictly positive residual axial deformation after this removal. It
refutes a zero-cost residual comparison, while leaving positive source
prefunding and its arbitrary-horizon renewal open.

The [residual parent transport calculation](labs/README.md#residual-source-funding-retains-parent-transport)
derives the residual's actual transport--elliptic commutator, including
the nonzero divergence of the five-dimensional lifted drift. A direct
source contribution separated from the observation by a fixed distance
has an original-energy bound. Together with the paid-parent factor, this
gives an explicit initial allowance for those terms of the residual
deformation metric. Nearby source work, transport, viscous acceleration
and quadratic variation remain in one signed history cost.
A compact smooth test pair has identical initial source, canonical
pressure, axis velocity, energy and scalar paid-parent bound, but opposite
signs of the next residual deformation coefficient. Thus the scalar
payment does not determine the transport of newly generated parents.
The equations and moment coefficients are symbolically checked; elliptic
identification and the interval conclusions remain analytic. This tests
a source-only closure, not a full-datum history allowance or regularity.

The [smooth-receiver history estimate](labs/README.md#smooth-receivers-and-the-complete-generated-parent-history)
pays the full residual's source and actual transport when paired with a
smooth axial receiver whose first two axial derivatives have prescribed
bounds, in the stated axisymmetric whole-space class. Integrating the heat
response over its history leaves a logarithmic source concentration,
paid by the actual full-energy law. Renormalizing
the receiver by r^2 retains the correct physical measure and axis flux.
The transport correction is then bounded using the full physical vorticity
and the already paid parent history, without assuming either is absent.
The source identification, duality and transport estimate remain
analytic, with exact symbolic checks. `MettapediaNS.LogSourceReserve`
certifies the scalar reserve along the actual whole-space `NSEvolution`,
including payment on every compatible subinterval and the initial
allowance. Its seven theorems and three definitions use only the
permitted foundational axioms; the spatial source comparison and
stochastic receiver identification are not formalized by that adapter.
For the actual deformation-weighted receiver, its derivative bounds remain
uncontrolled by the original datum; smooth averaged observations do not
give the uniform point-started moment required by the compression criterion.
An exact Fisher-information identity retains full diffusion and permits
a finite old-parent allowance for mass plus weighted Fisher information;
the signed generated-strain cost is still open.
The heat-referenced variant starts every normalized Gaussian receiver
with allowance two, uniformly in its width. It gives an explicit signed
cost whose uniform payment would control the point-started axis moment;
that payment and the further interior-weight construction remain open.
This is a partial physical bound, not an arbitrary-data continuation result.

The [pure-swirl return test](labs/README.md#positive-return-from-a-swirl-to-its-own-source)
excludes an unconditional nonpositive sign for generated nonlinear feedback.
An explicit smooth finite-energy whole-space datum starts with no meridional
velocity. Its actual unforced evolution generates strain whose contribution
to the quartic swirl balance becomes positive on a short interval, for every
fixed positive viscosity. Exact radial moments and an analytic localization
error bound establish the sign; the functional analysis and time evolution
are not Lean-certified. Arbitrarily slow axial variation retains a positive
return with a quadratic depletion factor. This does not establish growth of
the complete viscous norm or repeated renewal, and it does not directly
evaluate the deformation receiver's signed cost. The kinetic-energy-weighted
return has a favorable sign; an exact commutator isolates the additional
cost introduced by the quartic concentration weight. Controlling that cost
along the evolution, including diffusion, remains the target.

The [circulation-envelope entropy reserve](labs/README.md#an-actual-source-law-with-funded-action-and-entropy)
identifies a probability law transported by the actual lifted meridional
drift. Original circulation, source mass and kinetic energy pay its entire
drift action. Relative entropy to a heat Gaussian plus a remaining-energy
allowance is nonnegative and pays its relative Fisher information. This
includes interacting parents and sign-changing axisymmetric swirl through
a positive passive envelope, under the stated moment assumptions. The law
is an actual-flow stochastic observer, not an optimal Schrödinger bridge
or the law of three-dimensional fluid particles. The derivation is analytic.
A concentrated family has uniformly bounded entropy/action reserves but
unbounded integrated third-moment diffusion cost on actual short unforced
prefixes. Its cubic initial source moment grows at the required scale.
Thus a transfer to deformation moments must retain higher initial resources
and the signed work replenishing them. The [source-reference tests](labs/README.md#source-moments-and-the-axis-receiver)
also retain the stochastic moment correction and transverse diffusion;
neither a power of an averaged source nor its axis trace closes that transfer.

The [critical cubic-source clock](labs/README.md#a-critical-cubic-source-clock-and-its-internally-generated-rebound)
gives a separate continuation consumer in the axisymmetric whole-space
class. For the actual source stock `S=integral_R5 |u_theta/r|^3`, the
circulation maximum and physical energy pay `integral S`. A bound on
`integral S^2` gives the swirl `L8_t L4_x` criterion of
[Wang, Theorem 1.1](https://ejde.math.txstate.edu/Volumes/2015/250/wang.pdf).
Five-dimensional Sobolev interpolation identifies the nonnegative candidate
`R=(E S)^(6/5)` and its exact signed parent cost, retaining both kinetic and
source diffusion. R and the sufficient clock have invariant NS scaling.
The required original-datum bound on that signed cost is open. An explicit
localized pure swirl generates feedback that raises R above its initial
value on an actual short unforced interval at every fixed positive viscosity,
so this candidate is not automatically monotone. The interval proof uses
uniform local estimates after amplitude/time rescaling; exact identities,
localization constants and scaling pass symbolic checks. These results are
analytic, not new Lean theorems, and do not supply general 3D/periodic
continuation or refute a full-datum allowance for repeated renewal.

The [separate-channel test](labs/README.md#swirl-channel-transfer-spatial-composition-and-a-critical-source-moment)
retains the signed transfer from swirl kinetic energy to meridional motion.
Its global product with the cubic stock still fails automatic monotonicity:
a distant weak source changes the product's weighting of active feedback,
and a controlled actual interval retains the failure at positive viscosity.
The spatially additive critical moment `M=integral_R5 |u_theta/r|^(5/2)`
has a precise alternative signed diffusion budget sufficient for the
axisymmetric continuation clock. The earlier paid-parent history removes
all initial meridional parents and outside-created sources with one
original-horizon factor; signed renewal by the remaining parents is open.
An independent family of many initially concentrated swirl packets has
uniformly bounded source entropy/action allowances but unbounded physical `L8_t L4_x` swirl
norms on actual short intervals. Its initial critical moment records the
growing multiplicity. These are analytic arguments with exact algebraic
checks; they neither establish indefinite renewal nor rule out full-datum
regularity, and no new Lean certification is claimed.

The [axial-order history test](labs/README.md#axial-ordering-signed-parent-histories-and-its-dynamical-defect)
keeps the full interacting drift in a positive half-space propagator.
For reflection-symmetric flows, persistent axial ordering of the swirl
magnitude makes the generated-parent contribution to the critical moment
nonpositive, giving the conditional continuation allowance explicitly.
An actual smooth pure swirl shows that initial ordering need not persist:
internally generated pressure reverses a flat axial slope on a short
positive-viscosity interval. An exact signed decomposition identifies the
opposite-sign source/receiver histories left to pay, while retaining the
favorable terms. This refutes automatic persistence of that geometric
condition, not the possibility of signed compensation or regularity.
In fact, the same example retains negative net parent production on a
short interval while its axial ordering has already failed.
These physical statements are analytic with symbolic checks; the general
three-dimensional/periodic history estimate remains open.

The [critical parent-energy test](labs/README.md#critical-parent-exchange-and-the-initial-allowance-it-requires)
adds the actual meridional kinetic channel at the critical exponent.
Its complete identity has positive diffusion and explicitly retains the
pressure-weight and transport commutators; at exponent two it recovers
ordinary kinetic dissipation. A smooth localized pure swirl increases the
critical moment on actual unforced intervals at fixed positive viscosity.
Thus a dominating reserve that assigns no extra initial allowance to pure
swirl cannot be nonincreasing, even if it includes nonnegative energy of
subsequently generated parents. A fixed rescaled interval requires an
initial excess at least a fixed positive constant times A^(5/2) when the
datum's velocity is amplified by A.
This is a finite burst of the same amplitude order as the initial critical
moment, not an obstruction to a finite full-datum allowance or a claim of
indefinite renewal. The signed critical history budgets remain open.

The [funded history test](labs/README.md#a-funded-critical-history-test-with-bounded-coarse-resources)
also rules out a nonzero extra allowance based only on the displayed
energy, circulation and scalar entropy/action resources. Finitely many
separated copies of the critical burst are concentrated on one fixed
Gaussian background. Actual NS stability retains their positive critical
cost, while the coarse initial resources converge to the background's
values. The signed excess grows with the packet count even though its
ledger already includes the full initial critical moment. The original
paid-parent subtraction tends to zero on these short prefixes, so the
same obstruction reaches the signed core-history target.
Continuous state corrections using only those coarse resources also cannot
make the critical moment nonincreasing. These are analytic arguments with
exact scaling checks, not new Lean theorems. The initial critical moment
grows with packet count; an allowance depending on that or finer initial
geometry remains possible. The examples do not show indefinite renewal
from a fixed datum or disprove regularity.

A [critical caloric allowance](labs/README.md#a-critical-allowance-for-the-original-caloric-parent-history)
pays one complete prepared source/receiver history from the original datum:
heat-diffuse the initial swirl quotient, retain all parents generated by
its squared source, and reconstruct their pressure. Their absolute work
against that diffusing receiver is bounded over all positive times by
`C nu^(-2) M0^(9/5)`, where `M0=int_R5 |b0|^(5/2)`. Its remaining-work
integral is a nonnegative reserve, with a proved finite initial bound and
one original clock across compatible segments. The actual fluid's exact
Duhamel decomposition retains two unpaid terms: the changed receiver and
the changed source/full parent transport. A bound on their joint signed
work would close the existing core budget. The prepared allowance is an
analytic partial payment, not control of that nonlinear remainder.

The [complete caloric-parent strain bound](labs/README.md#paying-the-caloric-parent-against-the-actual-receiver)
removes the separate receiver defect using initial swirl energy and
enstrophy. Write `F=||b0||_2(R5)`, `G=||grad b0||_2(R5)` and
`d=||grad beta||_infinity`. Two time-integrated Fourier heat estimates give

```text
integral_0^infinity ||q1(t)||_infinity dt
  <= A_cal=F sqrt(G(d F+2G))/(6 pi^2 nu^2).
```

Here `F^2=pi E_swirl(0)` and `G^2=pi Z_swirl(0)`, with no factor 1/2 in
E. No smallness or future-flow norm is required for this prepared-parent
bound. Its integrating factor pays q1 against the actual changing receiver
on every available smooth prefix. The remaining signed budget contains
only qR: the strain generated by source deformation and full transport
of the generated parents. That budget is still open. The result and its
conditional axisymmetric continuation consequence are analytic, with exact
constant and scaling checks; they are not new Lean-certified PDE results
or an arbitrary-data three-dimensional regularity theorem.

The [relative parent balance](labs/README.md#a-relative-parent-balance-with-paid-supplied-terms)
retains the joint critical moment of the actual swirl and the residual
parent after that subtraction. Its prepared source, outside source and
transport of the prepared parent by the full actual velocity have finite
initial-data payments. The last uses physical kinetic energy paired with
weighted derivatives of the known heat history; no future velocity-gradient
bound is assumed. The complete residual exchange and transport are still
open. In particular, the residual parent does not inherit the full field's
quadratic kinetic cancellation: transport by the subtracted parents leaves
a cross pairing. The exact checker verifies a compatible Gaussian pair
where that pairing is nonzero, without asserting realization by the actual
history split. The new payments and conditional continuation bound remain
analytic, not Lean-certified.

The [prepared-transport estimate](labs/README.md#prepared-transport-and-the-complete-residual-parent)
pays the homogeneous commutator generated by the explicitly prepared
velocity, with a finite coefficient fixed by the original datum and
horizon. A second decomposition keeps ALL unprepared parents together,
including the initial meridional field. This restores their quadratic
self-transport cancellation; it does not give a critical-power sign.
The critical balance retains the changing spatial weight, both residual
commutators and the full diffusion. Its signed absorption estimate remains
open. These are analytic results in the smooth, decaying axisymmetric
whole-space class, with exact algebra checks and no new Lean declarations.

The [critical-parent transport test](labs/README.md#critical-parent-transport-and-nodal-costs)
keeps the complete signed defect. An explicit smooth unforced no-swirl
datum has positive critical production exceeding diffusion after amplitude
rescaling, although its quadratic kinetic cancellation holds. A second
regular datum shows that separately applying Young's inequality to the
weight-gradient term creates an infinite auxiliary cost at parent nodes.
The actual signed work remains finite; smoothing the weight does not give
a uniform bound for that separated cost. These analytic tests exclude
direct absorption and that particular split estimate, not a finite
full-datum history allowance. The continuation observation is swirl, so
growth of a parent norm alone must not be mistaken for dangerous renewal.
The full convex observer retains a positive repair: its weighted gradient
cost is at most three fifths of the complete diffusion. An exact form of
the signed defect keeps this regular observer intact, with its nonlocal
coefficients and time-integrated payment still open.

The [complete far-parent payment](labs/README.md#paying-the-complete-far-parent-flux-from-a-spatial-moment)
bounds an actual nonlinear contribution from the original fluid's energy
and second kinetic moment. The latter propagates by the unforced energy
identity, with no assumed future stretching bound. A Cartesian stress
identity retains both parent transport and the pressure-related correction;
moving its derivative onto a fixed far kernel, including the cutoff
derivative, gives a uniform original-data flux bound. The regular observer
then pays this part by a quarter of diffusion, a fixed linear coefficient
and an additive allowance. The explicitly prepared parent is also retained
in the weighted stocks. Nearby parent interactions and local swirl transport
remain in a signed sufficient history estimate. This is an analytic result
for the axisymmetric R3 track with the stated finite initial moment, not
a bound uniform in the kernel cutoff or arbitrary R3/T3 closure.

An [actual no-swirl reference](labs/README.md#an-actual-no-swirl-reference-and-swirl-seeded-parent-histories)
provides an alternative that does not charge for the reference's harmless
meridional motion. It starts from the same meridional datum and uses
established global no-swirl theory. All residual parents then start at
zero, with their actual swirl source and subsequent feedback retained.
Both reference transport operators have finite critical-norm coefficients;
the physical deviation's energy and spatial moment are paid from its
initial swirl resources. These sharpen the complete far-parent estimate
and vanish when the initial swirl vanishes. The reference coefficient is
a proved-finite functional of that known reference, not a closed formula
in initial seminorms or an assumed bound on the future target flow.
The exact stochastic representation keeps the actual drift and source
together. A sufficient signed budget for the remaining nearby generated
parents is still open. These new arguments are analytic, not Lean-certified.

The [first generated-parent return](labs/README.md#the-first-nonlinear-return-from-an-actual-swirl-seed)
has a favorable sign for an entire radial seed class. Starting from pure
swirl, the first nonlinear feedback into its generated meridional parent
is strictly negative in the canonical kinetic pairing. Every viscous term
is retained in comparison with the original caloric forecast; this gives
an actual short-time parent-energy comparison. The joint critical moment
also initially lies below its caloric forecast for these seeds. An exact
anisotropic family retains the negative parent return. However, the actual
second source jet already leaves radial symmetry, so this comparison cannot
be restarted or iterated without a new estimate. Its role is a concrete
geometric depletion test; it supplies no arbitrary-history allowance.
The identities have exact symbolic checks; the local-history passage is
analytic and no new Lean theorem is claimed.

A [heat-smoothed circulation entropy](labs/README.md#angular-history-and-a-heat-smoothed-circulation-entropy)
retains the geometry generated by this return. A critical angular contrast
can increase under literal diffusion, including at the initial time of
actual smooth pure-swirl flows. Its first generated angular departure is
nevertheless bounded by initial gradient resources and the depleted first
return. The alternative entropy uses a fixed heat-smoothed cylindrical
volume weight. Its complete diffusion is nonnegative, and its transport
and strain cancel except for a precisely weighted near-axis production.
The known no-swirl reference and complete far-parent contribution are
paid from original resources. A stated bound on the remaining near-parent
history implies the existing axisymmetric continuation criterion; that
bound remains open. These are analytic results with exact algebra checks,
not new Lean-certified PDE estimates or arbitrary R3/T3 closure.

The [cellular cycle construction](labs/README.md#arbitrarily-many-finite-cellular-pattern-cycles)
allows any prescribed finite number of approximate two-state, three-state,
or longer whole-pattern returns in an actual unforced periodic class.
The original datum varies with the number of returns and their accuracy.
The parent decays autonomously; its total strain clock and a receiver
reserve give finite original-data payments. A finite-horizon vorticity
bound excludes blowup for this class. The full parabolic construction,
phase coordinates and pattern-tracking estimate are analytic. Lean checks
the horizontal equations, pressure, clock, gradient reaction and explicit
reserve calculus. It also checks separately that an actual whole-space
evolution with positive interior gradient energy cannot return exactly
to its original full velocity. None of these statements excludes a
concentrating cascade with mutually replenishing parents.

The [reciprocal extension](labs/README.md#actual-three-dimensional-pattern-cycles-with-reciprocal-feedback)
now constructs actual global three-dimensional flows following those
finite cycles, with a nonzero internal transfer into the parent. A
Sobolev stability estimate controls the complete evolution from a small
but nonzero 3D perturbation of the original reference. The parent may
receive work; the hidden field pays its opposite, and a single original
reserve bounds all subsequent absolute replenishment. This proves an
analytic perturbative class, with potentially very small thresholds.
It does not require the parent to remain autonomous or reset its budget.
The full-cycle PDE construction remains analytic; the exact checker
retains canonical pressure and every generated initial output.

The [transfer reversal](labs/README.md#reversing-internal-transfer-along-an-actual-cyclic-history)
then identifies both directions of internal energy exchange along one
such actual history. A complete degree-eight Fourier residual estimate,
including viscosity, the evolving receiver and nonlinear feedback, proves
positive initial parent transfer and negative transfer later in the first
turn. The parent remains positive, so its nonlinear energy-exchange power
also reverses. This strengthens the initial-time phase comparison to an
analytic interval result. It requires small receiver and perturbation
amplitudes and does not assert that every turn repeats the reversal.

The [four-mode refeeding example](labs/README.md#parent-refeeding-with-a-paid-energy-exchange-loop)
realizes a positive--negative--positive sequence of parent power along
one actual unforced flow. The complete residual bounds retain all
nonlinear modes. The full kinetic energy strictly decreases between
the three observations, and a single original reserve pays the absolute
modal power over the entire history. Thus the repeated qualitative
transfer label does not imply a repeated full state or a replenished
budget. This analytic, small-perturbation example can be combined with
the prescribed finite pattern cycles; arbitrary-history control is open.

The [stretching comparison](labs/README.md#stretching-through-the-parent-refeeding-loop)
tests the continuation-relevant cubic production on that SAME history.
While the parent receives, returns, and again receives nonlinear energy,
the stretching excess over the original evolving reference has signs
negative, positive, positive. A complete H1 residual estimate and the
evolution of the generated vertical mean control the receiver corrections;
no hidden mean is supplied freely. With zero receiver amplitude these
are signs of total cubic production; with a nonzero receiver its own
production is retained in the reference. Neither positive production nor
positive parent power implies enstrophy growth after viscosity. This
analytic interval result shows that transfer direction alone cannot
decide geometric depletion. Its payment still uses a small H3 stability
neighborhood; arbitrary mutually amplifying histories remain open.

The [generated-mean controller](labs/README.md#bellman-control-of-the-actual-generated-mean)
now gives a closed-form Bellman upper bound for a physical part of that
stretching history. Its state keeps the generated mean and original
remaining clock. An adjoint weight pays both the mean already present
and its allowed future source; it also yields a complete interval budget
for the stretching excess in the controlled class. Exact composition
retains a cross-interval memory term that disappears under an incorrect
reset. Actual NS segments map into the scalar relaxation, whose maximizer
need not itself be a fluid. The analytic cost domination fits the existing
`Bounds.of_domination`, `Bounds.comp` and `Bounds.iterate` interface while
full endpoint velocities remain required for physical gluing. The source
allowance still relies on the proved small H3 neighborhood; that physical
restriction, not the Bellman algebra, is the arbitrary-data obstruction.

The [reference-stretching reserve](labs/README.md#reference-stretching-paid-without-perturbative-smallness)
removes that smallness restriction for ALL mixed cubic stretching terms
involving a known smooth reference U. The actual difference d=u-U retains
every generated mode. Its relative kinetic energy pays the source of a
negative-Sobolev observation, while viscosity pays the quadratic mixed
terms. A backward two-state reserve bounds the absolute mixed stretching
on every available smooth prefix, with no future target derivative bound.
For a matched periodic vertical mean, the initial allowance is a known
reference coefficient times the original relative kinetic energy.
Pure g(d) remains unpaid, including its generated parents; this is not an
arbitrary-data regularity theorem. `ReferenceStretchingReserve` certifies
nine scalar reserve and composition ingredients. The PDE identification,
negative-Sobolev estimate and absolutely-continuous norm calculus remain
analytic.

The [evolving-mean estimate](labs/README.md#the-evolving-planar-mean-has-a-finite-amplification-price)
instead retains M=average_z u from the actual periodic flow, including its
Reynolds source. Two-dimensional interpolation and a horizontal-mean
cancellation control all mean-containing stretching by a viscous share
plus a coefficient times total enstrophy. The coefficient's entire time
integral is bounded by a domain constant times initial kinetic energy
divided by nu squared. This yields an explicit exponential energy
compensation, without smallness or an independently known reference.
It is a multiplicative enstrophy estimate, not an absolute stretching
allowance independent of enstrophy. The mean-free self-stretching budget
remains open; a positive first nonlinear return on the actual refeeding
history shows it cannot be discarded. `GeneratedMeanEnstrophy` certifies
six scalar compensation ingredients. The anisotropic PDE estimate and
short-time sign argument remain analytic, and no whole-space vertical
average is asserted.

The [geometric cascade ledger](labs/README.md#a-finite-energy-finite-time-cascade-ledger-with-unbounded-stretching)
formally separates that remaining question from energy conservation.
It has summable positive energy costs and durations, a decreasing reserve
paying every stage, and unbounded accumulated vorticity scale. This is
exact sequence arithmetic; no NS realization is asserted.

| Module | Reused mathematics | Exact remaining boundary |
| --- | --- | --- |
| `MettapediaNS.CellularCycleReserve` | Explicit decaying cellular parent and pressure; finite advection clock, seam payment and turn-count bound; complete scalar gradient reaction; the existing planar receiver reserve pays absolute stretching under its stated energy-law hypotheses. | Passive parabolic existence, the maximum-principle identification, annular phase construction and arbitrary finite approximate-cycle theorem are analytic. No mutually replenishing parent estimate. |
| `MettapediaNS.WholeSpaceEnergyReturn` | The actual whole-space NS kinetic derivative and scalar monotonicity. Equal endpoint energy forces zero interior dissipation; positive interior gradient energy excludes an exact full-velocity return. | Smooth whole-space L2 evolutions, positive viscosity. It does not classify torus steady states or exclude approximate, observed or rescaled cycles. |
| `MettapediaNS.GeometricCascadeLedger` | Geometric series, a decreasing per-stage reserve, exact viscous-time scaling and unbounded stretching partial sums. | An abstract scaling sequence, with no field, pressure, geometric compatibility or NS evolution asserted. |
| `MettapediaNS.WholeSpaceBKM` | OpenAI's actual vorticity norm, norm-path continuity, and logarithmic gradient estimate. The adapter proves equality with the existing spatial essential supremum, including its extended value, and applies the estimate to the existing transported-velocity interface. | Euclidean smooth fields with actual L² jets; the physical-time vorticity budget and the required realization of the velocity remain obligations. A nonzero periodic lift is not a whole-space L² field. |
| `MettapediaNS.WholeSpaceViscousFlow` | OpenAI's smoothing operators, bounded regularized transport, global Lipschitz Picard theorem, time integrals and smooth-field algebra; the Laplacian and dissipation identity of `WholeSpaceViscousEnergy`. A bounded quadratic field conserving energy plus a bounded dissipative linear field has a global forward flow with nonincreasing norm (truncation by a ball retraction, which keeps the energy balance). For every smoothing operator `S` the regularized viscous term `ν S Δ S` is bounded on `L²` with `⟪u, ν S Δ S u⟫ = -ν ∑ᵢ ‖∂ᵢ S u‖²`, so the regularized Navier–Stokes equation has global forward `L²` solutions, and smooth regularized evolutions with all `L²` jets exist from every smooth solenoidal datum on every interval. The viscous term contributes `-2ν` times the smoothed dissipation to every integer-order energy production, so the upstream tame estimate gives `H³` and all-order bounds on the regularized Euler lifespan of the datum, uniform in the smoothing and the viscosity (`regularizedViscous_all_order`). On solenoidal fields `‖S Δ S A − Δ A‖ ≤ 6 ε M` with the upstream regularization error `ε` (`viscous_error`), and the regularized viscous evolutions are Cauchy in continuous `L²` as the smoothing is removed (`regularizedViscous_cauchy`). Along OpenAI's smooth limit the Laplacians converge with the second-order word paths, the regularized derivatives converge to `P(-(u·∇)u) + ν Δu`, and the limit satisfies the Navier–Stokes equations at every point with the constructed pressure: every smooth solenoidal field with all derivatives in `L²` starts a smooth Navier–Stokes evolution on `ℝ³`, for every `ν ≥ 0`, on the regularized Euler time of its `H³` energy (`exists_local_nsEvolution`). Two such evolutions separate in `L²` at most like `exp (K t)` with `K` a gradient bound (the viscous term only helps; `NSEvolution.l2_stability`), so evolutions with the same initial velocity agree (`NSEvolution.velocity_eq_of_initial`). | Local existence and uniqueness. Maximal lifespans and the continuation criteria are in the two rows below; nothing here bounds a solution beyond its local interval. |
| `MettapediaNS.WholeSpaceNSContinuation` | OpenAI's Helmholtz projection, derivative-word constraints, interval concatenation, strong-time lifting, variable-coefficient Gronwall estimate and `H³` transport estimate. The Laplacian of a solenoidal field is solenoidal, so the `L²` time derivative of every smooth evolution is `-P((u·∇)u) + ν Δu`, a function of its velocity alone, and its pressure is the canonical Helmholtz pressure (`NSEvolution.derivative_toLp_projected`, `NSEvolution.pressureForce_eq`). Evolutions restrict to shorter intervals, two evolutions that meet glue to one (`NSEvolution.concatenate`), and every evolution extends by the local existence time of its final velocity (`NSEvolution.exists_extension`). Data therefore have smooth evolutions on every finite interval or a finite maximal lifespan (`global_or_lifespan`), and the evolutions on shorter intervals agree (`NSLifespan.evolution_agrees`). The gradient supremum is a continuous path and its time integral controls the `H³` energy, the viscous term only helping (`NSEvolution.h3_energy_gradientIntegral`). The local existence time depends only on the `H³` energy, so a bounded gradient integral would give a uniform restart time and an evolution past a finite maximal time: at a finite maximal time the gradient integrals are unbounded, and so is the gradient on every final segment (`NSLifespan.gradientIntegral_unbounded`, `NSLifespan.gradient_unbounded_near_endpoint`). No rescaling is used, so the viscosity is never changed. | Whole-space `SmoothL2Field` data with all derivatives in `L²`, `ν ≥ 0`. This is continuation, not a bound: nothing here controls the gradient of any solution. |
| `MettapediaNS.WholeSpaceNSBlowup` | OpenAI's transport cancellation, pressure pairing, vorticity norms, whole-space logarithmic gradient estimate, logarithmic Gronwall argument and nonnegative improper integrals; the spatial essential-supremum identification of `MettapediaNS.WholeSpaceBKM`. The kinetic energy of every smooth evolution does not increase (`NSEvolution.l2_norm_le`), so the logarithmic estimate bounds the gradient integral by the vorticity integral (`NSEvolution.gradientIntegral_of_vorticity_bound`) and the vorticity integrals are unbounded at a finite maximal time (`NSLifespan.vorticityIntegral_unbounded`). The evolutions on shorter intervals define one smooth solution on the half-open maximal interval, with continuous jets (`NSLifespan.maximalField_eq_evolution`, `NSLifespan.maximalField_jet_continuous`), and the route's spatial essential-supremum integrand of its curl has infinite extended integral over that interval (`NSLifespan.spatialEssentialSupNorm_lintegral_eq_top`). Hence data have smooth evolutions on every finite interval or blow up in this sense at a finite time (`global_or_vorticity_blowup`), and bounds on the vorticity integrals on every finite horizon give global existence (`hasNSEvolution_of_vorticityIntegral_bound`). | The Beale–Kato–Majda criterion on `ℝ³` for the smooth `L²` class. The finite-horizon vorticity bound for arbitrary data is the open estimate; this module supplies none. |
| `MettapediaNS.WholeSpaceTimeSmooth` | OpenAI's strong-time lifting (a pointwise time derivative with continuous jets gives the `L²` derivative of every derivative word, and an `L²` derivative gives pointwise derivatives up to the endpoints), jet continuity of products with Sobolev-embedded coefficients, and the Helmholtz projection. The time-derivative relation is preserved by sums, linear maps, directional derivatives, the Leray projection and the Laplacian, and the advection field obeys the product rule (`TimeDeriv.advection`). The velocity of every smooth evolution has the pressure-free right-hand side as its time derivative, so by induction it has time derivatives of every order, each a path of smooth fields with continuous jets (`NSEvolution.isTimeSmooth`); so does the pressure force. | Time regularity of a given evolution; it bounds nothing. |
| `MettapediaNS.WholeSpaceJointSmooth` | The mean value inequality and Sobolev embedding. A path with a time derivative defines a function of space and time whose derivative within `ℝ³ × [0, T]`, at every point including the endpoints, is the spatial derivative plus the time derivative (`hasFDerivWithinAt_joint`). In coordinates this derivative is built from paths that are again smooth in time, and induction gives `C^∞` on `ℝ³ × [0, T]` (`contDiffOn_joint_infty`). The velocity and the pressure force of every smooth evolution are `C^∞` in space and time (`NSEvolution.velocity_contDiffOn`). | Smoothness of a given evolution on its interval. |
| `MettapediaNS.WholeSpacePressurePotential` | OpenAI's radial potential of smooth gradient fields. Time derivatives of gradient paths are gradients, since the gradient fields form a closed subspace. The radial potential has an explicit derivative within `ℝ³ × [0, T]`; its time part is paid uniformly along the radial segment by the mean value inequality. The scalar pressure of every smooth evolution is `C^∞` in space and time, with gradient the pressure force (`NSEvolution.scalarPressure_contDiffOn`, `NSEvolution.scalarPressure_gradient`). | Smoothness of a given evolution's pressure. |
| `MettapediaNS.WholeSpaceOfficialStatement` | The official whole-space statement (A) with zero force, `OfficialWholeSpaceProblem.WholeSpaceStatementA`, adapted from Formal Conjectures like the periodic target. Rapidly decaying data are smooth `L²` fields, since every derivative is bounded by a multiple of `(1 + |x|)⁻⁴` (`memLp_of_decay`). Evolutions on `[0, n + 1]` agree by uniqueness and glue into a velocity and a scalar pressure that are `C^∞` on `ℝ³ × [0, ∞)`, solve the equation with the one-sided time derivative at time zero (`global_navier_stokes`), and have kinetic energy at most that of the data. Global existence of the smooth evolutions therefore gives statement (A) (`wholeSpaceStatementA_of_global`), and so do finite-horizon bounds on the vorticity integrals (`wholeSpaceStatementA_of_vorticityIntegral_bound`). | Conditional. The finite-horizon vorticity bound for arbitrary data is the open estimate. |
| `MettapediaNS.WholeSpaceOrderEnergy` | OpenAI's derivative words, transport-commutator recursion, transport cancellation and pressure orthogonality (`eulerRhs_pairing`), the `L⁶` Sobolev inequality for smooth `L²` fields and `L⁴` interpolation; mathlib's Hölder inequality. The energy `Eₙ = Σ_{|w|=n} ‖∂_w u‖²` of the derivatives of order exactly `n` has, for the literal Navier–Stokes right-hand side, the exact production `-2 Σ ⟪[∂_w, u·∇]u, ∂_w u⟫ - 2ν Eₙ₊₁` (`orderProduction_navierStokesRhs`). The commutators of words of length two and three are expanded into three and seven advection terms (`transportCommutator_two`, `transportCommutator_three`), each paired by Hölder's inequality with exponents `4, 4, 2` in the order that keeps the estimate linear (`advection_bound_442`, `advection_bound_424`, `advection_bound_244`). With `‖f‖₄⁴ ≤ ‖f‖₂ ‖f‖₆³` and `‖f‖₆² ≤ 3S² Σᵢ ‖∂ᵢf‖₂²`, the squared `L⁴` norms of order `n` sum to at most `(9ⁿ · 27 S⁶ Eₙ Eₙ₊₁³)^(1/4)` (`quarticEnergy_pow_four_le`), and a fourth-power absorption gives, when `E₁ ≤ Z`, `production₂ ≤ -ν E₃ + M(ν, Z) E₂` and `production₃ ≤ -ν E₄ + (M₃(ν, Z) + G (1 + E₂)(1 + E₃)) E₃` with explicit constants (`orderProduction_two_le`, `orderProduction_three_le`). | Inequalities for one smooth solenoidal field; they bound no evolution by themselves. |
| `MettapediaNS.WholeSpaceEnstrophyContinuation` | OpenAI's variable-coefficient Grönwall estimate and interval integrals; the lifespans and restart argument of `MettapediaNS.WholeSpaceNSContinuation`. Along a smooth evolution with `ν > 0` whose gradient energy `E₁ = ‖∇u‖₂²` stays below `Z`, the energy does not increase, `E₂` grows at most like `exp(M t)` (`NSEvolution.orderEnergy_two_le`), `ν ∫ E₃` is bounded (`NSEvolution.dissipation_three_le`), `E₃` obeys Grönwall's inequality with a rate whose integral these two facts bound (`NSEvolution.orderEnergy_three_le`), and the `H³` energy is bounded on every finite horizon by an explicit constant (`NSEvolution.wordEnergy_three_le`). The local existence time depends only on the `H³` energy, so at a finite maximal time the gradient energies are unbounded (`NSLifespan.not_orderOne_bounded`, `NSLifespan.orderOne_unbounded`), which is Leray's criterion. Finite-horizon bounds on the gradient energy give global evolutions (`hasNSEvolution_of_orderOne_bound`) and the official statement (A) (`WholeSpaceOfficial.wholeSpaceStatementA_of_orderOne_bound`). | Conditional, with `ν > 0`. The target is subcritical: a finite-horizon bound on `‖∇u‖₂` for arbitrary data, the quantity the enstrophy identity controls. No such bound is proved. |
| `MettapediaNS.WholeSpaceBetchov` | OpenAI's integration by parts for smooth `L²` fields, advection product rule and solenoidal derivative words; the trace algebra and middle-eigenvalue inequality of `MiddleEigenvalueAlgebra`. For a smooth solenoidal field with all derivatives in `L²` and gradient `A a b = ∂_b u_a`, the square and cube traces are divergences of fluxes that are sums of products of two smooth `L²` fields, so `∫ tr(A²) = 0` and `∫ tr(A³) = 0` (`integral_trSq_eq_zero`, `integral_trCube_eq_zero`; Betchov's identity on `ℝ³`). The order-one production is `-2 ∫ Σ A_ji A_kj A_ki - 2ν E₂` (`orderProduction_one_eq`); with Betchov's identity it equals `-(8/3) ∫ tr(S³) - 2ν E₂`, and `-(4/3) tr(S³) ≤ 2 max(λ₁, 0) |S|²` gives production at most `2 K E₁` whenever `K ≥ 0` bounds the middle strain eigenvalue (`orderProduction_one_le`). Along evolutions the gradient energy is at most `E₁(0) exp(2 ∫ K)` (`NSEvolution.orderEnergy_one_le_of_middle`), so continuous majorants of the positive middle eigenvalue with bounded time integrals give global evolutions (`hasNSEvolution_of_middle_bound`) and the official statement (A) (`WholeSpaceOfficial.wholeSpaceStatementA_of_middle_bound`). | Conditional, with `ν > 0`: the same sheet-forming strain criterion as `MiddleEigenvalueCriterion` on the torus. The criterion is stated with continuous majorants of the middle eigenvalue on each closed interval. No bound on the middle eigenvalue is proved. |
| `MettapediaNS.WholeSpaceViscousEnergy` | OpenAI's derivative-word fields, whole-space integration by parts, and nonlinear H³ energy estimate. The constructed Laplacian is identified with mathlib's actual Laplacian; its production is exactly minus twice the derivative-word dissipation. The full unforced NS right-hand side therefore retains the same nonlinear bound with dissipation on the left. | These are spatial right-hand-side identities and estimates. A time-dependent solution must still supply its actual evolution and regularity, and the gradient/vorticity coefficient must be controlled. |
| `MettapediaNS.AlmostOrthogonality` | Direct semantic aliases of Alpöge–Buckmaster's C*-ring and Hilbert-space Cotlar–Stein theorems. Neither proof is copied or reimplemented. | Both adjoint cross-product bounds and the row/column majorant bounds must be established for the actual localized operators. |
| `MettapediaNS.QuadraticSingularIntegral` | Alpöge–Buckmaster's sharp-truncation, smooth-truncation, and principal-value `L^p` bounds. The adapter constructs the angular hypotheses for the explicit kernels `x_i*x_j / ‖x‖^5` (`i ≠ j`) and `(x_i² - x_j²) / ‖x‖^5`, using mathlib's orthogonal changes of variables and compactness. | Whole-space inputs: bounded compactly supported fields for the truncations, smooth compactly supported fields for the principal value, finite `p > 1`. The constants are independent of the truncation radii; the smooth version also permits every cutoff satisfying the stated support/range conditions. The modules below identify and assemble the actual whole-space strain on smooth compactly supported sources. Periodic transfer, weighted costs, and physical-time control remain separate obligations. |
| `MettapediaNS.WholeSpaceBiotSavart` | Alpöge–Buckmaster's proved `potential_theory_R3` and actual Newtonian Biot–Savart construction. Its velocity is smooth and in `L²`; for divergence-free vorticity, its divergence vanishes and its curl recovers that vorticity in both OpenAI's and the pancake route's APIs. The actual velocity-gradient entries are represented using the imported Newtonian gradient kernel on source derivatives. | Smooth compactly supported vorticity on `ℝ³`. The modules below supply the trace-free Hessian identification, derivative-free component bounds, full strain assembly, and all `L²` velocity jets for divergence-free inputs. General admissible data, physical-time evolution, and the signed budget remain separate obligations. |
| `MettapediaNS.NewtonianHessianPrincipalValue` | The upstream regularized Newtonian potential, integration by parts, convergence against test functions, and principal-value integrability. These identify the actual off-diagonal Newtonian Hessians and differences of diagonal Hessians with the upstream principal-value operators, including the factor `-3/(4π)`. The previously imported `L^p` estimates now bound those actual derivatives by the undifferentiated source norm. | Smooth compactly supported scalar sources on `ℝ³`, finite `p > 1`. Radial cancellation removes the local term for these trace-free components; no such cancellation is asserted for an individual diagonal entry. Full-strain assembly is supplied below. General-data/periodic transfer, weighted projector costs, and signed physical-time control remain open. |
| `MettapediaNS.WholeSpaceStrain` | The existing pancake `strainRateApply` is identified with mathlib's self-adjoint part of the actual Biot–Savart gradient. Its entries are explicit combinations of the imported principal-value operators: local isotropic terms cancel before estimation. All nine entries and the complete operator satisfy `L^p` bounds by the undifferentiated vorticity norm. Assembly uses OpenAI's multilinear coordinate estimate, mathlib's isometric currying, and its finite-sum `L^p` inequality. | Smooth compactly supported vorticity on `ℝ³`, finite `p > 1`; the constant is independent of the source. Actual `MemLp` is also proved. This supplies no `L^∞` endpoint, derivative-weighted projector estimate, general-data/periodic extension, or signed physical-time budget. |
| `MettapediaNS.WholeSpacePressure` | OpenAI's smooth Helmholtz pressure field, normalized radial scalar potential, and preservation of solenoidality by actual derivative words. The constructed pressure is an actual smooth scalar gradient, and the full viscous right-hand side is divergence-free for solenoidal input. The H³ production estimate no longer takes an independently supplied pressure or gradient-space hypothesis. | An actual `SmoothL2Field` input is required. The module constructs a spatial NS right-hand side, not a solution trajectory. No physical-time equation or budget is assumed to follow from the construction. |
| `MettapediaNS.WholeSpaceBiotSavartRegularity` | OpenAI's `smoothL2Field_of_curl_compact` applies directly to the smooth finite-energy Biot–Savart velocity constructed using Alpöge–Buckmaster. Every actual Fréchet derivative is in `L²`, and the closed solenoidal-space condition is proved. The existing spatial BKM estimate and viscous H³ production bound now apply with velocity jets and pressure both constructed from the source. | Smooth compactly supported divergence-free vorticity on `ℝ³`. Compact vorticity is not asserted to persist under viscous evolution. General-data extension, actual time evolution, weighted projector costs, and the signed physical-time bound remain open. The constant time path in the BKM notation represents one spatial slice only. |
| `MettapediaNS.ForcedPathEnergy` | OpenAI's smooth-field time differentiation and variable Grönwall estimate; the whole-space Betchov and order-two energy estimates. The force adds at most `2 √Eₙ(u) √Eₙ(f)` to the order-`n` production. A nonnegative continuous majorant `K` of the middle strain eigenvalue gives `1 + E₁(t) ≤ (1 + E₁(0)) exp ∫(2K + √E₁(f))`; a bound on `E₁` gives the analogous order-two estimate. Uniform integral bounds for `K` and uniform force bounds give energy bounds independent of shorter slab endpoints. | Actual forced smooth `L²` paths with all spatial jets continuous in time. The middle-eigenvalue integral remains a hypothesis. |
| `MettapediaNS.ForcedCandidatePancake`, `MettapediaNS.OpenAISolutionPancake` | OpenAI's compact smooth time fields turn each candidate's actual velocity, pressure and force into a `ForcedPath` on every compact slab starting at `1/2`. Smooth compact forcing has uniformly bounded order-one and order-two energies across time one. A uniform middle-eigenvalue integral would then bound `E₁` and `E₂`; the existing whole-space `H²` embedding and the candidate's kinetic-energy bound would bound speed, contradicting its blow-up (`no_uniform_middle_majorants`). The second module applies this theorem to the actual fields constructed by `NavierStokesR3.theorem_1_1` for every positive viscosity. | No family of nonnegative continuous middle-eigenvalue majorants on the slabs exhausting `[1/2, 1)` has uniformly bounded integrals. The theorem excludes budget derivations that also apply to smooth compactly supported forcing. It proves no unforced budget and does not identify a literal middle-eigenvalue essential-supremum integral. |
| `MettapediaNS.ForcedSignedBudget` | Integration by parts gives the actual gradient-energy force work `-2 ⟪u, Δf⟫`, bounded in absolute value by `6 √E₀(u) √E₂(f)`. The exact integrated energy balance retains signed nonlinear production, viscosity and force work separately. Bounded kinetic energy and smooth compact forcing give a finite force allowance independent of the shorter slab. The constructed candidate has unbounded gradient energy, so even signed nonlinear production minus full viscous dissipation has no uniform upper allowance (`no_uniform_signed_production_budget`). The theorem applies directly to `NavierStokesR3.theorem_1_1` for every positive viscosity. | Full-field statement on the slabs exhausting `[1/2, 1)`. The continuous production path is identified with `-2 ∫ cubicSelf(∇u)`. Its coefficient `c = 2ν` subtracts full dissipation and `c = ν` subtracts half. This module has no frequency projector and supplies no unforced budget. |
| `MettapediaNS.ForcedCandidateVorticity` | Alpöge–Buckmaster's Green representation, Newtonian derivative commutation, and gradient kernel; mathlib's Hölder inequality and local integrability of `‖z‖^(-α)`, `α < 3`. A smooth, compactly supported, divergence-free velocity is proved equal to the Biot–Savart velocity of its own curl. For `p > 3` and compact `K`, one constant gives `‖v(x)‖ ≤ C (∫ ‖curl v‖^p)^(1/p)` for all such velocities supported in `K`. Applied to every whole-space candidate of OpenAI's Theorem 1.1 (`CandidateProperties`), `∫ ‖curl u(t)‖^p` is unbounded for `0 < t < 1`, including the eighth moment. | The statement is proved for every candidate satisfying the problem statement's properties; `MettapediaNS.OpenAISolutionVorticity` applies it to the constructed solution. The candidates are forced. The theorem excludes bounds on these moments, finite up to the singular time, whose derivations also hold for smooth compactly supported forcing. It does not bound any unforced solution. |
| `MettapediaNS.OpenAISolutionVorticity` | OpenAI's `NavierStokesR3.theorem_1_1`, imported with its full construction (rebuilt here; its axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`). | For every positive viscosity, the constructed forced solution has no global finite-energy competitor and an unbounded eighth vorticity moment before time one. This is a statement about forced solutions; it bounds no unforced solution. Importing the construction adds about 520 upstream modules to this target's first build. |
| `MettapediaNS.OpenAIPeriodicWiener` | OpenAI's periodic corollary (`NavierStokes.PeriodicPaper.periodic_corollary`), imported with its construction, and the Fourier inversion of smooth one-periodic fields from the periodic Fourier development. The velocity Wiener norm of the coefficients dominates the real field, so along every periodic candidate the velocity Wiener norm of the time slices is unbounded arbitrarily close to time one. | For the unforced problem, a bound on this norm along tame solutions gives the official periodic statement (`FourierCascadeContraction.periodicStatementB_of_velocityWienerBound`). The forced periodic candidates, whose force is smooth, violate the corresponding bound, so a derivation of that bound must use the absence of forcing. This bounds no unforced solution. Importing the periodic Fourier development adds its modules to this target's first build. |
| `MettapediaNS.OpenAIPulseSeeds` | OpenAI's reference pulse envelope (`NavierStokes.PrimaryPulseBounds.referenceP`) and its Gaussian bounds (`NavierStokes.GaussianEnvelope.reference_gaussian_bounds`). Each primary pulse starts from the seed `referenceP lam u L 0`, which lies between `exp(-u·maxSlope·L/8)` and `exp(-u·minSlope·L/8)`; the amplification from seed to midpoint is at least `exp(u·minSlope·L/8)`, and once the slot length exceeds a multiple of `log(1/Q)` the seed is at most `Q^N`. | The construction's slots have length of order `log²(1/Q)` in a band of scale `Q`, so the seeds it plants are smaller than every power of the band scale. The amplitude equation is linear: by uniqueness of linear solutions, the solution started from any seed `σ e₁` is `σ / P(0)` times the constructed pulse at every time of the slot (`seeded_eq_smul_fundamental`), hence at least `|σ| exp(u·minSlope·L/8)` times its size (`norm_seeded_ge`). A seed that is only polynomially small in the band scale is amplified super-polynomially beyond the constructed pulse. This is a statement about the forced construction; it bounds no unforced solution. |
| `MettapediaNS.SwirlBudget` | OpenAI's Navier–Stokes residual (`NavierStokesR3.ProblemStatement.navierStokesResidual`) and its operators; mathlib's product and chain rules. At every point where the velocity is twice differentiable in space and differentiable in time, the angular momentum density `Γ = x₀u₁ − x₁u₀` about the third axis satisfies `∂ₜΓ + (u·∇)Γ = ν(ΔΓ − 2ω₃) − (x₀∂₁p − x₁∂₀p) + (x₀f₁ − x₁f₀)`, with `f` the residual and `ω₃` the axial vorticity (`swirl_identity`). The angular derivative of a C¹ function is its derivative along the rotations about the axis, so its integral over every circle about the axis vanishes (`integral_angularDeriv_rot`, `integral_angularDerivative_rot`). Mathlib's second-derivative test gives a nonpositive second derivative at every local maximum (`deriv_deriv_nonpos_of_isLocalMax`, `secondDeriv_nonpos_of_isLocalMax`); for an axisymmetric flow the pressure's angular derivative vanishes and, at a critical point of the swirl off the axis, so does the axial vorticity (`axialVorticity_eq_zero_of_critical`), so at every such spatial local maximum `∂ₜΓ ≤ x₀f₁ − x₁f₀` (`deriv_swirl_le_torque_of_isLocalMax`). Maximizing `Γ − εt` over a compact region of space-time gives the maximum principle: for an axisymmetric flow whose force has nonpositive torque and whose swirl is nonpositive outside a compact set, the swirl never exceeds its initial maximum (`swirl_le_of_axisymmetric`). | The pressure drops out of the averaged swirl, and the force enters only through its torque. An axisymmetric unforced flow cannot increase its maximal swirl, so a collapse whose maximal swirl grows must break axisymmetry and draw that growth from the torque of its non-axisymmetric part; `MettapediaNS.AveragedSwirl` treats the averaged swirl of a flow with no symmetry. The identity is pointwise; it bounds no solution. |
| `MettapediaNS.AveragedSwirl` | The swirl identity and angular averaging of `MettapediaNS.SwirlBudget`; mathlib's parametric interval integrals, second-derivative test and compactness bounds. For a flow with no symmetry, integrate the swirl over the circles about the axis. At every spatial local maximum of that circle integral off the axis, `∂ₜ∮Γ ≤ −∮(u·∇)Γ + ∮(x₀f₁ − x₁f₀)` (`deriv_circleInt_swirl_le`). Along the circle the pressure's angular derivative integrates to zero; the Laplacian of the swirl integrates to a nonpositive number, since the second derivatives of the circle integral along the coordinate lines are nonpositive and the trace is invariant under the rotations (`integral_laplacian_nonpos`, `sum_rot_basis`); and the axial vorticity integrates to zero, because `x₀∂₀Γ + x₁∂₁Γ = r²ω₃ + ∂_θ(x₀u₀ + x₁u₁)` holds for every velocity (`fderiv_swirl_horiz`, `integral_axialVorticity_eq_zero`). Maximizing the tilted average over a compact region of space-time gives the swirl budget: if at every spatial maximum the averaged advection and torque are at most `g(t)` for a continuous `g ≥ 0`, the circle integral of the swirl never exceeds its initial maximum plus `∫₀ᵗ g` (`circleInt_swirl_le_budget`). The rotation-equivariant mean velocity `ū` commutes with the rotations (`meanVel_rot`), so at a maximum it carries no net swirl in (`integral_fderiv_meanVel_eq_zero`): only the fluctuation `u − ū` does (`deriv_circleInt_swirl_le_fluct`). The circle integral is differentiable and invariant under the rotations (`hasFDerivAt_circleInt`, `circleInt_rot`), so every point of a maximizing circle is a maximum (`isLocalMax_circleInt_rot`) and the torque at the peak is the fluctuation term `−∮(u′·∇)Γ′`, with `Γ′` the deviation of the swirl from its circle average (`deriv_circleInt_swirl_le_reynolds`). | The circle-averaged swirl can grow at its maxima only through the averaged advection of the swirl and the averaged torque, and its maximum can grow only by the time integral of these at the running maximum. For an axisymmetric flow the averaged advection vanishes at the maximum; in general it is the angular momentum that the non-axisymmetric part carries into the maximum. Hypotheses: a space-time `C²` velocity, a pressure `C¹` in space and a force continuous in space at the given time. It bounds no solution by itself. |
| `MettapediaNS.CirculationFlux` | The circle integrals, rotation-equivariant mean and Reynolds form of `MettapediaNS.AveragedSwirl`; mathlib's parametric interval integrals, fundamental theorem of calculus and `C¹` criterion. The circle integral of the swirl is the circulation around the circle, and it equals the flux of axial vorticity through the disk the circle bounds: `∮Γ = ∫₀¹ s r² (∮ ω₃ over the circle of radius s r) ds` (`circleInt_swirl_eq_flux`), because the radial derivative of the circulation is `s r² ∮ω₃` plus an angular derivative (`fderiv_swirl_ray`, `hasDerivAt_circleInt_ray`). The mean velocity is `C¹` (`hasFDerivAt_meanVel`, `contDiff_meanVel`) and its swirl is the averaged swirl (`swirlSlice_meanVel`). Since `(U·∇)U = ∇(|U|²/2) − U × ω`, the advection of the swirl is an angular derivative minus the swirl of the vortex force (`fderiv_swirl_self`), so around every circle `−∮(U·∇)Γ = ∮Γ(U × ω)`, with `Γ(U × ω) = r (U_z ω_r − U_r ω_z)` the rate at which `U` sweeps vortex lines across the circle (`circleInt_advection_eq_vortexForce`). At every spatial local maximum of the averaged swirl off the axis, `∂ₜ∮Γ ≤ ∮Γ(u × ω) + ∮(x₀f₁ − x₁f₀)` (`deriv_circleInt_swirl_le_vortexForce`) and, with `u′ = u − ū` and `ω′ = curl u′`, `∂ₜ∮Γ ≤ ∮Γ(u′ × ω′) + ∮(x₀f₁ − x₁f₀)` (`deriv_circleInt_swirl_le_eddyFlux`). | The largest axial vortex flux through a disk about the axis grows only as fast as the fluctuation velocity carries fluctuation vorticity across the disk's rim, plus the torque of the force; the axisymmetric part of the flow cannot raise it. Hypotheses as in `MettapediaNS.AveragedSwirl`. It bounds no solution by itself: the sign and size of the eddy vortex flux are the open dynamical question. |
| `MettapediaNS.HelicalPhaseSelection` | Integer phase counts for two parents and their conjugates. With angular indices `2k,2(k+1)` and common positive axial index one, a product with zero angular index and nonzero axial index uses at least `2k+1` factors (`minimum_order_adjacent`). The `(2,4)` and `(6,8)` cases have explicit sharp witnesses of orders three and seven; below order seven, every angular mean from the latter pair has axial index zero (`axial_zero_before_seven`). | Finite arithmetic only. It proves neither that an allowed interaction coefficient is nonzero nor a statement about a PDE solution. The amplitude-derivative application and its restricted-family history estimates are analytic results in the symmetry-defect note, described in the labs README. |
| `MettapediaNS.HelicalHighModeFeedback` | Finite algebraic sign certificates: the circulation heat bracket is positive for real angular index at least five (`circulationHeatBracket_pos`), and the rational negative-pressure allowance is less than one for real angular index at least six (`pressureAllowanceRatio_lt_one`). | The heat-resolvent identities, full signed enstrophy interpretation, and short unforced evolution estimates remain analytic arguments in the symmetry-defect note. This module proves no PDE bound. |
| `MettapediaNS.HelicalParentMomentum` | Pressure cancellation in the tangential/axial scalar equations at a critical circulation circle (`hasDerivAt_momentum`), conservation of the squared modulus for the resulting rotation ODE (`normSq_eq_initial`), and the Gram inequality controlling that momentum by the two velocity components (`momentum_normSq_le`). | Scalar ODE and algebra only. The cylindrical linearized Euler interpretation and the absence of a parent-history bound uniform in time and viscosity are analytic arguments in the symmetry-defect note. No nonlinear remainder or recurrent cascade is controlled. |
| `MettapediaNS.WholeSpacePressureRecovery` | OpenAI's instantaneous weak pressure identities, Fourier `H³` bound, Riesz Poisson identity, and harmonic-functional uniqueness identify the constructed Helmholtz pressure gradient with the double-Riesz pairing of the actual velocity tensor on every compact smooth scalar test. The required instantaneous equation is realized by an explicit affine tangent with the actual constructed viscous right-hand side. | Smooth solenoidal `SmoothL2Field` inputs on `ℝ³`. The tangent satisfies the equation at time one only; no solution on a time interval is asserted. The test identity is not a physical-time estimate. |
| `MettapediaNS.WholeSpacePressureFlux` | The constructed-pressure test identity discharges OpenAI's generic compact-flux identification theorem. Its complete cutoff-flux estimate, including the localized Sobolev term and heat-kernel commutator term, then bounds the actual scalar pressure flux. The `L³` membership and tensor `L¹` bound are supplied using upstream Sobolev estimates and mathlib integrability. | The flux identity permits every compact smooth cutoff. The quantitative application uses the upstream radial weight with `R ≥ 1`; its constant is independent of `R` but depends on the velocity slice's `L²` and `L³` norms. This is neither a uniform physical-time bound nor an estimate for arbitrary anisotropic pancake/projector weights. All-scale summation and the signed misalignment budget remain open. |

`MettapediaNS.RieszDoubleCommutator` applies OpenAI's heat-kernel
commutator twice and its Riesz self-adjointness once. The resulting signed
quadratic localization defect retains the squared difference of the
multiplier `φ²` before taking norms. For `0 ≤ φ ≤ 1` with Lipschitz bound
`L/R`, its kernel has majorant
`C max(2L,1)² |x-y|⁻³ min(|x-y|/R,1)²`.
This is bounded by `C max(2L,1)² R⁻¹` times the **existing upstream radial
kernel to the power `2/3`**. Mathlib's power change of exponent and Hölder
inequality therefore give actual section integrability for `L²` sources
and an `R^(-3/2)` pointwise bound. No radial integration theorem, Fourier
operator, or heat representation is reimplemented.

For Schwartz tests representing `f`, `φ² f`, and `φ⁴ f`, the checked defect is
`∫(φ² f) T(φ² f) - ∫(φ⁴ f) Tf`, where `T` is the actual upstream double
Riesz transform. Its norm is at most
`C max(2L,1)² R^(-3/2) ‖f‖₁ ‖f‖₂` with a source-independent constant.
The identity is bilinear and gives the usual real quadratic-form identity
on real tests. This differs from the single-commutator `L¹`-`L⁴` estimate;
the bounds have different source norms and are not pointwise comparable
without further assumptions. Matching this defect to the full signed NS
residual, extending beyond the test class, controlling moving projectors,
and paying the scale/time coefficients remain obligations.

`MettapediaNS.PressureLocalizationDifference` handles distinct source and
receiver fields. Write `χ = φ²` and `P(g,ψ) = ∫ g Tψ`. For actual Schwartz
tests `ψh = χψ` and `ψhh = χ²ψ`, it proves the exact decomposition

```text
P(χ²g,ψ) - P(g,χ²ψ)
  = [P(g,χ²ψ) - 2P(χg,χψ) + P(χ²g,ψ)]
      - 2[P(g,χ²ψ) - P(χg,χψ)].
```

The first bracket is the double commutator and is bounded by
`C₂(L,R) ‖g‖₁ ‖ψ‖₂`, with `C₂` proportional to `R^(-3/2)`.
The second is a first commutator, bounded using OpenAI's existing theorem
by `C₁(L,R) ‖g‖₁ ‖χψ‖₄`, with `C₁` proportional to `R^(-3/4)`.
The complete bound retains both terms. For `g = u_i u_j`, the localized
source is literally the tensor of `χu`, and the upstream finite-energy
tensor estimate gives `‖g‖₁ ≤ ∫|u|²`. No claim is made that `χu` is
divergence-free or that the first commutator vanishes.

`MettapediaNS.WholeSpaceUnforcedEnergy` supplies the initial-data resource
for this source on an actual unforced `ClassicalH3Solution`. It specializes
OpenAI's `difference_rate_le` with both transported field and transporting
velocity equal to `u`, and zero deformation operator. Its generic pressure
orthogonality theorem removes the pressure work; pressure-gradient `L²`
membership is derived from the equation. OpenAI's Grönwall theorem then gives
`∫|u(t)|² ≤ ∫|u₀|²` throughout the given lifespan. Thus the second pressure
difference is bounded by `C₂(L,R) ‖u₀‖₂² ‖ψ‖₂`, including a checked sum over
all nine tensor components. No energy inequality or later-time bound is
assumed in the solution class. The module neither constructs nor extends
the lifespan. The first commutator, the actual material pressure-Hessian
receiver tests, adaptive cutoff costs, periodic transfer, and the signed
all-scale/time budget remain obligations.

`MettapediaNS.WholeSpaceStretchingFlux` constructs the cubic flux and its
gradient projection from an actual `SmoothL2Field` velocity, using upstream
vorticity, field products, advection, and the genuine Helmholtz projection.
Writing `ω = curl u` and `s = (ω·∇)u`, the flux is `J_ja = -ω_j s_a`.
Projection acts on the spatial index `j`: each column is the complement of
the upstream solenoidal projection. The resulting field `F` and the receiver
`B_ab = ω_b Σ_j ω_j F_ja` have all actual `L²` jets by the imported field
algebra. Neither is an independently supplied estimate or field.

`MettapediaNS.PressureHessianReceiver` identifies the corresponding complete
spatial pressure work with canonical Riesz pairings of `u_i u_j` against
`∂a∂b(η B_ab)`. It uses the upstream compact integration-by-parts theorem
and the previously identified constructed Helmholtz pressure. Every index is
included. For a smooth compact cutoff, the differentiated test is exactly

```text
∂a∂b(η B) = η ∂a∂b B + (∂aη)(∂b B) + (∂bη)(∂a B) + B ∂a∂bη.
```

`MettapediaNS.PressureHessianLocalization` constructs the difference between
this actual test and `η ∂a∂b B` in the upstream Schwartz space. With
`η = φ⁴`, the full localization difference is **twice the first commutator
minus the second difference plus the cutoff-derivative pressure pairing**.
Both multiplier relations required by the earlier estimates are proved for
the constructed Hessian tests. The initial-energy estimate therefore applies
to the second difference with its actual Hessian-test `L²` norm; it does not
bound that norm, remove the first commutator, or pay the three derivative
remainder terms. These are whole-space spatial identities, not an evolution
theorem or an identification of the auxiliary-heat/periodic receiver. The
input-scale heat weights, moving geometry, signed physical-time budget, and
unconditional continuation remain open.

`MettapediaNS.GaussianHeatCovariance` identifies OpenAI's literal Gaussian
product defect `R_ij = Hτ(u_i u_j) - (Hτu)_i (Hτu)_j` with mathlib's
covariance bilinear form, for arbitrary ordinary whole-space `L²` velocities.
Its quadratic form is nonnegative. `GaussianHeatEnergy` applies OpenAI's
parameter-integral theorem to obtain the global `L²` contraction and mathlib's
convolution integral theorem to prove the exact identity

```text
∫ trace(Rτ) = ∫ |u|² - ∫ |Hτu|² ≤ ∫ |u|².
```

`GaussianHeatIncrement` uses mathlib's variance bound after subtraction of a
constant, OpenAI's actual `L²` translation increment, its Bochner realization,
and its widened-Gaussian quadratic majorant. For actual `SmoothL2Field`
velocities it proves

```text
∫ trace(Rτ) ≤ (2τ) 2^(3/2) ‖A.derivative.toLp‖².
```

This derivative norm is the `L²` norm of the actual Fréchet derivative with
its operator norm. No spatial supremum of that derivative is used. The
separate energy bound is composed with `WholeSpaceUnforcedEnergy` to bound
the stress trace by initial energy along every given unforced H³ lifespan,
uniformly in `τ > 0`. The Gaussian convention has generator `Δ/4`; physical
heat time `νσ` corresponds to `τ = 4νσ`. Although the translation theorem is
imported from `OrdinaryMollifier`, its statement is about ordinary translations;
the compact mollifier from that module is not substituted for the Gaussian.
`GaussianHeatPairing` identifies the full signed contraction with the
Gaussian expectation of a quadratic form on centered velocity. Consequently

```text
Rτ : M = E[⟨u - Hτu, M(u - Hτu)⟩],
Rτ : M = Rτ : sym(M),
|∫ Rτ : M| ≤ sup_x ‖M(x)‖ ∫ trace(Rτ).
```

The pointwise one-sided quadratic bound is also retained, including a
negative upper bound when applicable. There is no component-count factor.
`GaussianHeatWeakStress` constructs the weak action of `-P div Rτ` by
applying OpenAI's actual solenoidal projection to the receiver first. It
proves integrability and bounds this signed action using the energy or
heat-scale trace bounds above. Only the symmetric derivative contributes;
the actual projected receiver derivative remains an explicit cost. No
`L∞` boundedness of the Leray projection is asserted.

`GaussianHeatFourier` directly applies OpenAI's
`fourierIntegral_gaussian_real` and the existing MeTTapedia
`UnitTorusPeriodization.mFourierCoeff_periodize`. The result identifies the
periodized Gaussian's exact multiplier at **every** lattice frequency:
`exp(-π²τ|n|²)`. It also proves the literal Gaussian averaging identity for
plane waves, which are not whole-space `L²` functions. Neither Gaussian
Fourier analysis nor periodization is reimplemented.

`GaussianHeatTorus` identifies the literal whole-space Gaussian average of
a continuous periodic lift with convolution by that periodized kernel.
It then applies the existing integrable-convolution theorem and mathlib's
Fourier reconstruction to obtain the exact series for inputs with summable
Fourier coefficients. No whole-space `L²` assumption is imposed on a periodic
lift. The shared periodization proof now handles arbitrary invariant scalar
tests with integrable weighted kernels; its previous unit-character theorem
is a specialization, not a second unfolding proof. Periodization integrability
also uses the existing mass bound instead of requiring Schwartz regularity.

These results do not pay the evolving projected receiver derivative,
establish a physical-time dissipation bound in this interface, or identify
the full periodic/input-scale Gram work with the spatial stress action.
The existing canonical Fourier heat-source split, heat-commutator
energy/enstrophy bounds, and signed coefficient-adjoint/Duhamel
representation are retained, not reimplemented. Their migration to this
toolchain is a separate compatibility task.

A 21-file shared compatibility slice now passes selected-module builds on both
Lean 4.31.0 and Lean 4.34.0-rc2. It covers angular-curl continuity, radial
kernel moments and correlations, the exact Fourier triad, normalized
Schwartz-kernel decay, annular charts, dyadic rescaling, and frozen-frame
kernel transfer. It also covers buffered annular transfer, quadratic Fourier
support, the physical forcing-continuity lemma, and the physical Laplacian.
The two generalized periodization modules are also checked on both versions.
The compatibility adjustments concern elaboration and mathlib lemma names;
theorem statements are unchanged. This does not yet certify the
entire `ExchangedFluxHeatAdjoint` dependency chain on the newer toolchain.

`WholeSpaceBKM.h3_energyProduction_add_dissipation_le_spatialBKMIntegrand`
combines the first two applications: the actual viscous energy production
is controlled by the existing spatial BKM integrand and the actual higher
velocity norm. This does not establish integrability up to a singular time.

`NS.Lit.CZ.truncated_Lp_uniform`, `pvOp_Lp`, and
`smoothTruncate_Lp_uniform` in `Lit/CZ/CZCore/Homogeneous.lean` are now
checked imports and used by the quadratic-kernel applications above.
Their proofs cover general positive dimension; the current concrete
applications use dimension three. None of these estimates provides an
`L^∞` endpoint or the global signed time-integrated misalignment budget.

## Reuse policy

Before a new general-analysis proof, check mathlib, the existing MeTTapedia
development, and the relevant OpenAI and Alpöge–Buckmaster developments.
Prefer direct application, then a representation adapter or a generalization
of an existing proof. Record the exact missing hypothesis before undertaking
new mathematics. Toolchain differences are migration tasks, not a reason to
reprove an available theorem.

Ben's coherence/pancake mechanism remains the research target. Auxiliary
norms, functionals, and interfaces may be improved to use established theory.

## Reproducible Fourier calculations

The [exact Fourier interaction lab](labs/README.md) checks explicit
trigonometric data using the complete Leray-projected quadratic source and
rational arithmetic. It covers equal initial sources with opposite cubic
corrections to later production, mixed interactions escaping a generated
frequency chain, and a cyclic-shear cancellation that ends at the next
order. These are executable algebra checks, not Lean certificates or
physical-time budget estimates.

## Build

```sh
lake update
lake exe cache get
bash scripts/prepare-upstreams.sh
lake build MettapediaNS
lake env lean MettapediaNS/UpstreamAudit.lean
```

This target checks the imported theorem surface and adapters listed above. The
arbitrary-data dynamical budget and unconditional continuation theorem remain
separate mathematical obligations.

The selected target has been checked on Lean 4.34.0-rc2. OpenAI's source
tree is unchanged. EulerBlowup declares Lean 4.32.2 and mathlib 4.32.0;
the Cotlar–Stein dependency chain compiles unchanged on the newer toolchain.
The larger homogeneous-kernel dependency chain needs exactly five order-
lemma name updates in `Marcinkiewicz.lean` and `Homogeneous.lean`, recorded
in `patches/euler-blowup-lean-4.34.patch`. The potential-theory dependency
chain additionally needs one scoped elaboration setting around the existing
`Cm24.L2_6_III_Fc` proof in `Cm24/S2/Master.lean`, recorded in
`patches/euler-blowup-potential-lean-4.34.patch`. No statement or mathematical
argument is changed. `scripts/prepare-upstreams.sh` checks the pinned
revision and applies these patches idempotently, refusing a conflicting patch.
Run it after dependency setup; it never resets upstream files. The upstream
files and their Apache-2.0 license remain in their original package.
This does not certify the entire EulerBlowup development.
Upstream and existing local sources emit deprecation/unused-variable
warnings; these are not proof failures.

The shared `SpatialBKMIntegrand` source needs only a compatibility adjustment
to six continuity/measurability applications. Its mathematical statements
are unchanged; no new supremum construction is introduced.
The adjusted source also passes its original Lean 4.31.0 target. The
235-declaration integration audit reports only `propext`, `Classical.choice`,
and `Quot.sound`; there are no additional analytic axioms in those proofs.
