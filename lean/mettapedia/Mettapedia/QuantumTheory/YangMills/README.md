# Yang-Mills Lean Lane

This directory records the current formal proof surface for Ben's Yang-Mills
route. It is not a claimed Millennium solution.

Manuscript route (v14): start from finite Wilson lattice gauge theory; run an
extended-extraction RG bootstrap intended to contract irrelevant activities;
obtain stopping-scale clustering from a Kotecký–Preiss polymer expansion;
transport clustering back to fine scales; and use Osterwalder–Schrader
reconstruction to construct the continuum Hilbert space, Hamiltonian, and mass
gap. The formalization keeps those layers separate so that finite arithmetic or
a toy spectral gap cannot silently stand for the continuum construction.

OUR finite-coordinate repairs continue this same proof programme. They retain
the Wilson-lattice, extended-extraction, KP, glue, and OS architecture while
replacing false finite-coordinate bridges by quotient-compatible hypercubic and
boundary-cochain constructions. They are not claims about content already
present in v14.

Current status:

- `CompletionSteelman.lean` steelmans the five completion inputs from the
  Ben-facing report.
- The v14 extraction/recombination constant is not derived as written.
  `WilsonBlockMajorant.lean` proves norm-one canonical truncation on concrete
  gauge-invariant finite Wilson observables; `ExtendedExtractionTransfer.lean`
  gives both the basis/dual-jet transfer theorem and a range-only projection
  counterexample; `WilsonPolymerRecombination.lean` proves norm-one regrouping
  by union and refutes the literal total-contact reading of the factor `14`.
- `Dimension16WilsonExtractionCertificate.lean` records the decisive outcome
  of attempting the manuscript-facing coordinate construction. F.4 uses an
  on-shell relation policy while O.9 explicitly selects an off-shell census;
  v14 gives no dimension-16 lattice representatives, quotient basis, dual
  jets, biorthogonality matrix, or conditioning certificate. Appendix I's
  explicit jets belong to the distinct dimension-4 observable sector. Thus
  the source as written cannot instantiate the positive transfer theorem.
- Under Appendix O's other proposed factors, substituting the proved
  extraction factor `1` gives the conditional ledger `C = 5544/5`; depth `15`
  is the least unrestricted two-source depth and `16` the least even depth.
  This is not an actual Wilson RG constant until the remaining analytic factor
  bounds are proved in the same norm.
- OUR repaired finite relation target is now the coordinate-free
  `jointInvariantRelationSubmodule` inside the signed hypercubic invariant
  orbit space. Its off-shell relation submodule embeds in the on-shell one.
  The exact field-eight trace family, a seven-to-eight commutator relation,
  and a field-five commutator separator certify rank at least `11558` for
  either policy. This is a lower bound only: it neither supplies the complete
  relation census nor the joint quotient dimension or conditioning.
- The covariant-commutator row of `HypercubicDimension16CovariantCommutator`
  is a field identity only when the commutator's field has no derivative
  outside the pair. `HypercubicDimension16CommutatorRowEvaluation.lean`
  evaluates rows on gauge backgrounds and shows that the four-field row used by
  the separator has value `64` on a constant `SU(2)` background.
  `HypercubicDimension16LeibnizCommutator.lean` defines the Leibniz-correct row,
  `HypercubicDimension16LeibnizRelationOperator.lean` the corrected operator and
  `leibnizJointInvariantRelationSubmodule`, and
  `HypercubicDimension16LeibnizJointRank.lean` proves rank at least `11558` for
  it. Every row of the corrected operator vanishes after integration on every
  gauge background (the equation-of-motion rows on on-shell backgrounds), and
  the evaluation descends to the corrected joint scalar quotient
  (`HypercubicDimension16LeibnizCommutatorSoundness`,
  `HypercubicDimension16RelationRowSoundness`,
  `HypercubicDimension16RelationEvaluationDescent`). The earlier joint
  submodule is not a space of relations: it contains the Reynolds-averaged
  four-field row, whose averaged background value is `32/3`
  (`HypercubicDimension16RelationEvaluationEquivariance`). The cochain bridge
  and the source-band reduction of the profile correction hold for the
  corrected operator, and the two operators agree on the source bands seven and
  eight (`HypercubicDimension16LeibnizFDIBPCochainBridge`,
  `HypercubicDimension16LeibnizSourceSix`).
- The stopping-scale step. `FreeMaxwellNonClustering.lean` proves that the
  field-strength two-point function of the free lattice Maxwell field is not
  absolutely summable and has no exponential bound, in every dimension `d ≥ 3`.
  `CrossingInput.lean` states the input the stopping-scale step needs (at one
  block scale, uniformly in the volume, a Kotecký–Preiss-small polymer gas over a
  block-product reference measure), proves that it implies exponential
  clustering of bounded block observables uniformly in the volume, and proves
  that it fails for families whose bounded two-point functions approach the free
  field. `FreeFieldNoCrossing.lean` makes this concrete: the periodic Gaussian
  `F₀₁` field of the free Maxwell theory admits no crossing representation that
  reproduces its phase correlations on the tori; that weakly coupled `U(1)`
  approaches this field as `β → ∞` is not formalized. The polymer-gas theory
  these modules use is general and lives in
  `Mettapedia/Combinatorics/PolymerGas/` (Dobrushin and Kotecký–Preiss criteria,
  spatial decay, polymer representations of product measures, the truncated
  two-point function, lattice geometry, exponential clustering), without a
  cluster expansion. `CouplingDrift.lean` checks v14's drift constant (it is `N`
  times too small). `TwistDiagnostic.lean` adds a calibration that can be tested
  at finite coupling: a crossing family whose twisted and untwisted polymer
  representations differ only on polymers winding around the torus has twist
  free energy tending to zero (`PolymerGas/Twist.lean`), so a family whose twist
  free energy stays away from zero is not crossing; the winding hypothesis is
  stated, not derived. `MarginalBlindness.lean` proves that one-site marginal
  criteria admitting a nonzero one-site covariance cannot by themselves imply
  clustering. `TwistCost.lean` and
  `TwistEater.lean` compare the classical cost of a centre twist: at least
  `2βL^{d-4}` for every `U(1)` configuration, zero for `SU(2)`, where the
  anticommuting `iσ₁`, `iσ₂` absorb it. `StrongCouplingCrossing.lean` proves
  the crossing input at strong coupling: for Wilson-type measures on the tori
  `(ℤ/(n+3))^d` with any measurable plaquette potential in `[0, 2]` and
  `0 ≤ β ≤ β₀(d)`, the connected plaquette activities are Kotecký–Preiss small
  uniformly in the volume, and the Wilson expectations cluster exponentially
  (`PolymerGas/PlaquetteExpansion.lean`, `ConnectedCount.lean`,
  `PlaquetteSmallness.lean`). `StrongCouplingTwist.lean` verifies the twist
  diagnostic in that regime: for a central involution (the centre element `-1`
  of `SU(2)`) the twisted and untwisted activities form a twist-compatible
  crossing family, and the twist free energy of the Wilson measure tends to zero
  as the volume grows. `WilsonReflectionPositivity.lean` proves site reflection
  positivity of the Wilson-type measure at every real coupling, for class
  functions even under inversion and inversion-invariant reference measures.
  `StrongCouplingTransferGap.lean` proves, for every finite gauge group, a
  transfer-matrix gap at strong coupling that is uniform in the spatial volume.
  Proving the crossing input for four-dimensional `SU(2)` at weak coupling is
  open.
- `HypercubicDimension16FDIBPCochainJointBridge.lean` now proves that OUR
  finite derivative-alpha-reduced `F,D`/IBP relation cochains, after the
  physical operator and signed-hypercubic Reynolds average, surject onto that
  same joint relation submodule for either policy, with range equal to the
  whole submodule. Shared off-shell cochains retain their ambient invariant
  semantics on shell. This identifies the finite relation object; it does not
  yet provide the full
  noncommutative Wilson-functional-to-cochain dual jets.
- `HypercubicDimension16WilsonCartanJointMismatch.lean` now gives the exact
  boundary of the existing Cartan Wilson chart. Its raw Cartan restriction
  forgets trace order, so OUR raw restriction of the actual eighth-jet
  coefficient kills the signed incoming commutator pair even though the
  corresponding ordinary trace class is certified nonzero. Independently, no
  map from that `98`-dimensional trace quotient into a `17`-coordinate Cartan
  chart can be injective. This does not rule out the Wilson route; a full
  construction must retain noncommutative trace order and the coupled
  lower-field commutator data.
- `HypercubicDimension16WilsonTraceOrderRepair.lean` proves the first local
  repair requirement. On the concrete seven/eight-field commutator quotient,
  the canonical eight-field trace coordinate cannot descend by itself; every
  descended trace-order correction has a forced, nonzero seven-field value.
  The explicit compensator realizes that value, kills the complete physical
  commutator for either policy, and still detects its isolated eight-field
  trace component. OUR repair data retain this rational coordinate alongside
  the exact Cartan Wilson coefficient packet without identifying the pair
  with a completed noncommutative Wilson functional.
- The support recurrence is reduced to a manuscript branch choice:
  coarsen-then-thicken is uniformly bounded, while thicken-only is unbounded.
- The two-marked centered correlation identity is a named API; a canary proves
  one-marked pushforward does not imply it.
- KP convergence and Wilson reflection positivity are represented as
  classical-import APIs that plug into the OS scaffold. Their route-specific
  instantiation—actual stopping-scale activities, uniform smallness and source
  summability, decaying remainders, and compatibility for the same Wilson
  family and RG kernels—remains open mathematics.
- The first load-bearing remaining theorem is
  `FirstLoadBearingYangMillsCompletionInput`, the actual Wilson Yang-Mills RG
  map recursion producing the lattice gap/clustering bridge consumed by OS
  reconstruction.

Main status files:

- `ProofState.lean` records route nodes and current endpoint blockers.
- `Roadmap.lean` records the checked roadmap entries.
- `CompletionSteelmanRegression.lean` protects the five-input classification.
- `ContinuumOSReconstruction.lean` contains the conditional OS/Kirk endpoint.

The continuum mass-gap endpoint remains open until the actual Wilson RG
recursion, support branch, two-marked identity, KP convergence, Wilson
reflection positivity, and OS/subsequential-limit machinery are all instantiated
for the same route.

The incomplete extraction-side mathematics is to extend this local
trace-order-aware cross-sector coordinate to the full repaired joint quotient,
then establish its policy-indexed relation census, sparse rank/conditioning
certificates, and analytic dual jets in the same norm. The recombination-side
mathematics remains the weighted connected-cumulant/tree/KP estimate for the
actual Wilson activities in that same norm.

## Quantitative Wilson boundary contracts

`WilsonEliminationRoutes.lean` carries the actual positive density, reference
probability law, partition normalization and continuous moment functions
through order three. Concrete product integrations define `HaarTransition`;
spatial bounds are separate OSLF predicates. The native diamond asserts the
existence of a successor satisfying the predicate. Its right adjoint is
predecessor-universal, as specified by `haarBox_contract_iff`.

`SU2WilsonAssemblyLocality.uniform_responseContract` proves one common
second/third response contract for both actual Haar stages and every bounded
singleton-collar-local mark family. Its constants precede the volume, marks
and retained boundary values. `uniform_responseContract_reachable` supplies
the concrete integration witnesses. `SU2WilsonEffectiveInteraction` specializes
these statements to original Wilson scores in `uniform_scoreResponseContract`
and `uniform_scoreContract_reachable`.

For `0 ≤ β ≤ beta0 4`, `SU2BoundaryResponse.uniform_scoreThirdArray_envelope`
gives a positive rate `κ`, uniform before all volumes, plaquette masks, pinned
values and three independent rotation frames. If `τ` is the minimum
spanning-tree length of the three links, the bound is
`|Cum₃| ≤ 9 · 256³ · exp(2304 + 2κ) · exp(-(κ/2)τ)`.
Taking `η = κ/4` gives the tree-weighted row budget
`9 · 256³ · exp(2304 + 2κ) · exponentialVolumeBound 4 (κ/8)²`.
Both assembly levels are covered by `uniform_weightedThirdRow`, including
coincident and nearby triples. These are score cumulants. The true third
derivative equals `-β³ Cum₃` for three pairwise plaquette-separated patches.
For arbitrary patches, `thirdDerivative_eq_cumulant_contacts` in both
`SU2BoundaryResponse` and `SU2WilsonEffectiveInteraction` proves the full
ordered derivative at every real coupling. Writing `A_S` for a score and
`J_ST = D_T A_S`, its correction is
`β²[Cov(J_ST,A_V) + Cov(J_SV,A_T) + Cov(A_S,J_TV)] - β E[D_V J_ST]`.
The direct action contact is `thirdContact`, with bound `4096 · |S|` and
support inside the original plaquette collar. Ordered repeated-slot matrix
insertions cover overlapping and coincident links. Its left and right
disjointness lemmas recover the relevant contact cancellations.

`WilsonBoundaryResponse.hasDerivAt_thirdCumulant` identifies the first
higher response required on differentiating this calculus: three third
cumulants containing the derivatives of the marks, minus `beta` times their
fourth cumulant with the action score. The fourth conditioning identity in
`WilsonProjectionComposition.fiberFourthCumulant_staged` retains all fifteen
partition terms under the explicit generated integration maps.

`WilsonLocalResponse.fourthCumulant_ball_clustering` proves four-mark decay
from all seven singleton/pair cuts. For marks bounded by `B` in radius-`r`
balls, its envelope is
`66 B^4 exp(12 exp(r) V(1) + 2 kappa r) exp(-(kappa/6) star)`,
where `star` is the sum of the three distances from the first label and
`V(t) = exponentialVolumeBound 4 t`. At rate `eta = kappa/12`, the weighted
row budget is `66 B^4 exp(12 exp(r) V(1) + 2 kappa r) V(kappa/12)^3`.
`uniform_weightedFourthSeminorm` in `SU2BoundaryResponse` and
`SU2WilsonEffectiveInteraction` specializes this to actual Wilson scores
(`B = 256`, `r = 1`) at both assembly levels, including repeated labels and
independent frames. Rates and constants precede volume, active plaquettes,
boundary data and frames. This fourth-order estimate does not imply an
all-order analytic bound or clustering under the product-constrained block law.

`ResponseData.Contract.transport` proves the quantitative rule
`C₂' ≤ C₂ + D₂` and `C₃' ≤ C₃ + D₃ + E₁ + E₂ + E₃`, where the three `E`
budgets control the three mixed covariances. Direct and staged moment data
agree exactly, with the generated first density explicit. Uniform bounds
`B`, `2B²` and `6B³` hold for projected marks, covariance remainders and
third remainders; each mixed correction in the actual two-stage route has
bound `4B³`. `SU2WilsonAssemblyLocality.uniform_mixedCorrection_bounds` now
proves the three individual spatial sums are uniformly finite. Exact
first-stage locality enlarges singleton collars only to radius-four balls.
Inner pair decay and outer mean-versus-pair decay give the tree envelope
`A · exp(-(κ/2)τ)`, with `κ = min κ₁ κ₂` and
`A = 2B · covarianceEnvelope B κ₁ + 6B³ · ballResponseEnvelope 4 κ₂`.
The weighted budget is `A · exponentialVolumeBound 4 (κ/8)²` at rate `κ/4`.
`uniform_transported_response_bounds` supplies the new conditional second
and third budgets under the generated first density.

`uniform_composed_responseContract` instantiates the transport theorem with
these proved estimates, yielding budgets `C₂ + D₂` and `C₃ + D₃ + 3E` at a
common positive rate. `uniform_scoreCompositionContract` specializes this
certificate to actual Wilson scores at both assembly levels. Every rate
and constant precedes volume, boundary values and rotation frames.

`WilsonPinnedIntegral` proves exact density and mark transport through every
finite nested sequence of retained coordinate sets. The generated density is
averaged at each step; direct and staged normalized integrals agree, and the
partition is preserved. `WilsonProjectionComposition.coordinateRoute` realizes
these maps as existing GSLT routes. In `WilsonDyadicObservableFlow`,
`uniform_nestedResponseContract` bounds the stored original-label pair and
third moments independently of elimination depth, using one direct pinned
Wilson law. Its constants precede the volume, retained sets, mark family,
boundary values and depth. This theorem keeps the original lattice metric;
it does not identify stored moments with derivatives of coarse link products.

`WilsonDyadicGeometry.blockField` defines an actual scale-two map from side
`2(n+3)` to side `n+3`: every coarse link is the ordered product of its two
fine links. `blockField_gaugeAct` proves gauge equivariance;
`blockEdge_injective` proves these pairs share no fine edges, including at
the periodic seam. `dist_blockEdge_zero` proves exact factor-two rescaling
of the circle sup metric at the even base points.

`SU2WilsonAssembly.ScaleTwo` constructs the product-Haar block chart: first
halves and unused edges remain fluctuation variables, while second halves
are recovered from the prescribed coarse products. Its positive
`coarseDensity` preserves the full Wilson partition and marked expectations.
It is gauge invariant at every real coupling, and `integrationStep` is an
actual existing GSLT weighted step. `projected_blockObservable` proves that
all coarse-product observables survive exactly, including nonconstant ones.

`SU2WilsonEffectiveInteraction.ScaleTwo` differentiates that same generated
weight under its explicit conditional density `fiberDensity`.
`blockThirdDerivative_eq_cumulant_contacts` retains the score third cumulant,
all three contact covariances and the direct third contact. It holds for
arbitrary real coupling and arbitrary overlapping or coincident patches.
The score and two direct contact bounds are `256 |S|`, `1024 |S|` and
`4096 |S|`, uniformly in volume, boundary and frame. Coarse rotations lift to
second fine links with fluctuation-dependent unitary frames. Their bounded
shift from even anchors costs `exp(2η)` and `exp(4η)` for second and third
spatial arrays while doubling the rate. These metric comparisons do not
assert clustering of the product-constrained law from individual-link pinning.

`WilsonConditionalProjection.PairedHaar.strict_linear_gain` gives an actual
strict gain for centered local interactions under the unweighted block-Haar
average. The norm is the maximum over links of
`sum_(S containing l) exp(a |S|) ||Phi_S||_sup`. A local term can depend after
averaging only on coarse pairs whose two fine edges both belong to `S`.
Consequently its regrouped norm decreases by `exp(-a) < 1` for every `a > 0`,
independently of volume. Locality, Haar centering and the full averaged action
are preserved, and the empty-support component is zero.

`SU2WilsonAssembly.wilsonInteraction` is the actual centered Wilson action,
with norm at most `64 |beta| exp(4a)` for `a >= 0`. Its exponential, multiplied
by the explicitly recorded vacuum factor, is exactly the full Wilson density.
Thus `|beta| <= rho / (64 exp(4a))` puts the starting family in radius `rho`,
uniformly in volume. `ScaleTwo.blocked_wilsonInteraction_zero` proves that its
entire linear blocked interaction vanishes. The operator is nontrivial:
`retainedWilsonObservable` is a gauge-invariant ordered two-by-two Wilson loop,
with Haar mean zero, whose normalized projection is the nonzero coarse
plaquette trace at every real coupling.

The full observable space still has norm-one projection because constants
survive (`WilsonBlockElimination.one_le_project_uniform_bound`). The strict
interaction estimate is for the linear Haar average. The nonlinear logarithm
now has an all-order polymer majorant:
`PolymerGas.sum_weighted_log_coefficients_le` bounds the weighted absolute
subset-coefficient sum through each polymer by its Dobrushin removal weight.
The proof uses the full exponential and logarithm series. Weighted site
incidence controls connected families of arbitrary support size, without a
maximum-degree assumption. Applying these bounds to the generated interaction
norm remains the nonlinear contraction obligation.

The paired chart has explicit independent fluctuation coordinates: its two
fine halves share one coordinate. `ScaleTwo.fluctuationPlaquetteSupport` has
diameter at most 3, site incidence at most 128 and overlap degree at most 512,
uniformly in the torus size. `blockedDensity_gauge` transports gauge invariance
for every continuous generated fine density. The labelled polymer integration
identity keeps these dependency supports distinct from the retained coarse
supports, which contain only complete fine pairs.

The coordinate-rescaling lemmas in `WilsonBoundaryResponse.lean` prove that
an injective coordinate map with `d_fine = s · d_coarse` changes the admissible
exponent to `η_coarse = sη_fine`, without a volume factor. The current assembly
uses the original link metric. The concrete scale-two map and its first
three ordered response identities are now proved. Repeated scale changes
still require the relevant interaction extraction and preservation of the
analytic budgets under the generated product constraints in the same rescaled norm.

A precise all-order target is a uniform bound
`sup_l sum_(l₂,...,lᵣ) exp(η τᵣ) |Cumᵣ| ≤ A · r! · R^(-r)` for every `r ≥ 2`,
with positive `η,R` before volume and boundary data, together with the
corresponding differentiated contact bounds and exact partition-indexed
conditioning identities: sum over every partition of the source marks the
outer cumulant of the conditional cumulants associated to its blocks, using
the generated marginal for the outer law. Proving preservation after extraction
and rescaling
with gain below one remains open. The weak-to-strong trajectory and the
continuum construction remain further obligations.
