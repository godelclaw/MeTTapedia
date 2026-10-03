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
  clustering. Its `SU2Blocking` calibration also uses the actual scale-two
  Haar map: a positive gauge-invariant fine density has a constant complete
  coarse density, nondegenerate retained plaquettes and nondecaying distant
  fine plaquette correlations. This engineered density is not the Wilson
  action. `TwistCost.lean` and
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
survive (`WilsonBlockElimination.one_le_project_uniform_bound`). The nonlinear logarithm
has an all-order polymer majorant:
`PolymerGas.sum_weighted_log_coefficients_le` bounds the weighted absolute
subset-coefficient sum through each polymer by its Dobrushin removal weight.
The proof uses the full exponential and logarithm series.
`sum_weighted_norm_log_coefficients_le` controls the sum of uniform norms for
continuous activities, using one boundary-independent negative-activity
majorant. Weighted site incidence controls connected families of arbitrary support size, without a
maximum-degree assumption. `PairedHaar.nonlinear_block_contraction` applies these estimates to the actual
conditional Haar activities. For arbitrary finite nonempty supports and
continuous local interactions with per-link `exp(8 |S|)` budget `R <= 1/2`,
it constructs the full generated interaction `Psi` and an explicit vacuum
constant, reconstructs the blocked density exactly as `exp(vacuum + sum Psi)`,
and proves `interactionNorm 8 Psi <= 4 exp(-2) R`, with `4 exp(-2) < 1`.
Every output term is local and Haar-centered, and its empty-support term is
zero. `effectiveInteraction` is the canonical support-indexed version of the
same construction. These constants precede all volumes and boundary values.
The proof sums the full exponential and logarithm series. Its spatial extension,
`effectiveInteraction_spatial_norm_le`, uses the complete interaction norm

`sup_l sum_(S containing l) exp(8 |S| + eta treeLength(S)) ||Phi_S||_sup`.

`PolymerGas.treeLength` is the infimum of costs of recursive metric networks
spanning the support; auxiliary vertices are allowed. It dominates diameter
and is subadditive along connected overlaps. The actual `halfLink` projection
identifies both halves of each block pair and is nonexpanding, so the same
spatial rate is retained. Disconnected logarithmic coefficients vanish exactly.
For every fixed `eta >= 0`, the same radius `1/2` and gain `4 exp(-2)` apply,
independently of volume and coarse fields. These are bounds on interaction
functions; higher derivative estimates remain separate.
`ScaleTwo.effectiveInteraction_gauge` proves that each extracted term retains
gauge invariance for the actual ordered SU(2) block map.

`ScaleTwo.InteractionState` carries the full local interaction, its vacuum
constant, Haar centering, gauge symmetry and the invariant radius `1/2`.
Its `density_block` theorem identifies the next state's density with the actual
conditional Haar integral. In `WilsonDyadicObservableFlow`, `iterate n j`
performs `j` such steps from torus side `2^j (n+3)` to side `n+3`.
`spatial_norm_iterate_le` gives `R_j <= (4 exp(-2))^j R_0`. The Wilson input has
spatial norm at most `64 |beta| exp(32+4 eta)`, so

`spatialIterationBeta eta = 1 / (128 exp(32+4 eta))`

supplies the radius for every volume and depth. The choice `eta = 1` gives an
explicit positive interval. At `eta = 0`, this recovers the earlier cardinality
threshold `iterationBeta`. All these constants precede volume and depth.

The same radius suffices for spatial clustering. For the complete generated
interaction, `interactionDensity_eq_polymerDensity` is an exact polymer
identity and `polymer_expectation_eq_realExpectation` identifies normalized
expectations. `interactionActivity_small` gives `ActivitySmall` with rate `eta`
and smallness `exp(-3)`. `crossingInput_wilson_iterates` supplies one crossing
input for every pair `(volume, depth)`. For continuous real marks supported on
`S,T`, with `S` nonempty and bounds `B,C`, the generated covariance is at most
`3 B C exp(3|S|+3|T|) exp(-eta polymerDist S T)` in absolute value. The vacuum
factor cancels exactly. `wilson_scaleLift_clustering` proves the same estimate
for the corresponding ordered-product pullbacks under the original Wilson law.

`ScaleFiber` is the explicit product of all Haar fluctuations in the finite
chain. `density_iterate_direct` and `action_route_eq_direct` identify the
staged generated density and marks with one integral over that product under
the original density. The partition is unchanged. `integral_directDensity`, `directProject_succ`
and `expectation_directProject` also hold for every positive continuous input
density, with no input smallness assumption. Every continuous mark, including
every finite product of marks, retains its original expectation. For general
marks, `covariance_directProject` keeps the exact correction
`E_generated[P(FG) - PF PG]`. Its unconditional bound is only `2 B C`, with no
spatial decay. `covariance_scaleLift` removes this correction exactly for
coarse-product pullbacks.
`retainedWilsonLoop_nonzero` proves that a nonzero coarse plaquette trace
survives every finite chain through its ordered-product pullback, which is
gauge invariant and Haar-centered.

`radiusSequence_step` instantiates `AffineRGStepBound` with the actual
interaction norms, gain `4 exp(-2)`, and zero error. The sequence is explicitly
padded by zero after its finite lattice chain ends; it does not posit further
scales on a fixed finite torus. `haarDiamond_interactionContract` supplies a
successor satisfying the strict bound in the existing OSLF forward modality;
`haarDiamond_spatialInteractionContract` supplies the spatial version.
The paired-Haar rewrite constructor itself contains no smallness condition.
This is a contraction of complete interaction functions with exact vacuum
extraction; no finite-coordinate dimension-16 extraction certificate or
analytic comparison with such a certificate is assumed.

The paired chart has explicit independent fluctuation coordinates: its two
fine halves share one coordinate. `ScaleTwo.fluctuationPlaquetteSupport` has
diameter at most 3, site incidence at most 128 and overlap degree at most 512,
uniformly in the torus size. `blockedDensity_gauge` transports gauge invariance
for every continuous generated fine density. The labelled polymer integration
identity keeps these dependency supports distinct from the retained coarse
supports, which contain only complete fine pairs.

The actual one-step Wilson conditional law now has a spatial bound.
`conditionalWilsonInteraction_spatial_norm_le` gives
`128 |beta| exp(4 a + 12 eta)` for its interaction norm with support weight
`a >= 0` and spatial rate `eta >= 0`, uniformly in volume and every retained
field. Thus `conditionalCovarianceBeta eta = 1/(256 exp(32+12 eta))` is a
positive sufficient threshold. If `|beta| <= conditionalCovarianceBeta eta`,
`conditionalCovariance_spatial_le` proves, for nonempty supports and continuous
local marks bounded by `B,C`,

`|P(FG)-PF PG| <= 3 B C exp(3|S|+3|T|) exp(-eta(dist(S,T)-2))`.

The same bound holds after averaging under the exact generated coarse density.
`wilsonPlaquetteMark` centers a plaquette under the original Wilson law and
retains its normalization `z` explicitly. It is gauge invariant, local and
bounded by `2|z|`; for two such marks the prefactor is
`12 |z| |w| exp(24)`. Coincident and nearby plaquettes are included. This is
an estimate for the first actual Wilson step; later steps have generated
interactions and transported marks, and require their own estimates.

The coordinate-rescaling lemmas in `WilsonBoundaryResponse.lean` prove that
an injective coordinate map with `d_fine = s · d_coarse` changes the admissible
exponent to `η_coarse = sη_fine`, without a volume factor. The two-separator assembly
uses the original link metric; scale-two iteration uses the successive coarse
metrics. The concrete scale-two map and its first
three ordered response identities are now proved. Finite repeated scale changes
now preserve the full interaction-function contract with a strict gain. Preservation of spatially weighted derivative
budgets under the successive generated product constraints is a separate
obligation.

A precise all-order target is a uniform bound
`sup_l sum_(l₂,...,lᵣ) exp(η τᵣ) |Cumᵣ| ≤ A · r! · R^(-r)` for every `r ≥ 2`,
with positive `η,R` before volume and boundary data, together with the
corresponding differentiated contact bounds and exact partition-indexed
conditioning identities: sum over every partition of the source marks the
outer cumulant of the conditional cumulants associated to its blocks, using
the generated marginal for the outer law. For this stronger all-order derivative
contract, preservation after extraction and rescaling with gain below one remains open. It does not follow
from the complete interaction-function norm bound. The weak-to-strong
trajectory and the continuum construction remain further obligations.

`StoppingScaleEntrance` records a quantitative entrance obligation on the
actual integrated Wilson density. Fixed `eta > 0` and `0 < rMin <= rMax` precede
the cutoff and volume. At cutoff `k`, the finite depth `j(k)` is independent of
volume, the stopped interaction has spatial norm at most `1/2`, and its physical
spacing satisfies `rMin <= 2^j(k) a(k) <= rMax`. The density identity includes
vacuum normalization. `coarseSpacing` and `physical_anchor_distance` give the
exact units conversion: the rate is `eta/r`, hence at least `m = eta/rMax`.
`uniform_pullback_clustering` makes its rate and prefactor uniform in cutoff
and volume when support sizes and amplitudes are uniformly bounded.

General transported observables can have spatial tails. `AnchoredObservableBound`
records an exact decomposition `F = sum_S f_S`, each piece supported on its
nonempty `S`, with budget

`sum_S exp(3|S| + eta treeLength(S union {x})) ||f_S||_sup <= B`.

`covariance_of_anchoredBounds` proves the bound `3 B C exp(-eta dist x y)`
for two such decompositions under the actual generated law. The number and
sizes of the pieces may depend on volume; their total budgets must be uniform.
`StoppingScaleEntrance.TransportControl` requires these budgets for `PF,PG`,
a physical anchor separation at least `D-delta`, and the independent bound
`|E_generated[P(FG)-PF PG]| <= epsilon exp(-m D)`. Its checked consequence is

`|Cov_original(F,G)| <= (3 B C exp(m delta) + epsilon) exp(-m D)`.

Every constant precedes cutoff and volume. Exact pullbacks satisfy the
conditional-covariance obligation with error zero (`transportControl_pullbacks`).
`covariance_le_of_local_approximation` also quantifies errors from approximating
projected marks by single local functions; those localization errors are charged
explicitly rather than discarded.

`covariance_eq_direct_add_scaleContributions` expands the original covariance
at every finite blocking depth into the final coarse covariance and the sum of
all discarded conditional-covariance contributions. Each contribution uses the
actual generated density and the transported original marks at that scale.
`wilsonPlaquette_covariance_scales` specializes this identity to centered,
gauge-invariant plaquettes at arbitrary positions and any real coupling.

The complete first generated logarithm is identified by
`log_coarseDensity_eq_generated`: its vacuum is
`-beta #plaquettes + effectiveVacuum`, and every extracted interaction
`effectiveInteraction S` remains in the sum. The normalized original mark is
the ratio of the marked and unmarked Haar integrals (`projected_integral`).
Neither the generated action nor its projected marks are replaced by a Wilson
ansatz. This reconstruction identifies the full interaction; it does not by
itself prove that a specified non-Wilson coefficient is nonzero.

There is also a decomposition retaining original plaquette labels:
`log_coarseDensity_eq_plaquetteLogFamily` includes the exact Wilson vacuum
factor and the complete logarithmic cluster family. Fix `eta >= 0` and
`|beta| <= 1/(128 exp(32+4 eta))`. For every volume and designated original
plaquette `p`, `plaquetteLogFamily_marked_spatial_budget` proves

`sum_(A containing p) exp(8|T_A| + eta treeLength(T_A union halfLink(supp p))) ||f_A||`
`<= 2 |beta| exp(24+4 eta)`.

Here `A` is a family of connected plaquette clusters, `p` belongs to its union,
`T_A` is its retained coarse support, and `f_A` is its exact logarithmic
coefficient. The norm is uniform over retained configurations. The tree length
allows ambient connecting vertices. The designated plaquette's location is
kept even when absent from `T_A`. The general compact-group theorem retains
`2 ||Phi_p|| exp(6|supp p|+eta treeLength(supp p))` on the right. These are
one-step coefficient bounds. Identifying and bounding source derivatives as
transported observables remains an additional step.

The second conditional law is now controlled as well. Fix `eta >= 0` and

`beta2(eta) = 1/(256 exp(64+56 eta)) > 0`.

At `|beta| <= beta2(eta)`, the two independent Haar fibers have plaquette
supports of size at most eight, diameter at most seven, incidence at most 128,
and separation at least the original separation minus six. Their complete
conditional interaction satisfies
`spatialInteractionNorm a eta <= 128 |beta| exp(8a+56 eta)`.
The signed identity is `R_direct2 = Q(R_first) + R_second(PF,PG)`, where `Q`
uses the full first generated density. For centered original plaquettes with
normalizations `z,w`, `secondGeneratedCovariance_wilsonPlaquette_le` proves

`|R_second(PF,PG;c)| <= 24 |z| |w| exp(48) exp(-eta (dist-6))`.

The same bound holds after averaging against the second exact marginal.
It is uniform over volume, positions and retained fields, including contacts.
The joint two-step remainder has the sharper prefactor `12 |z| |w| exp(48)`;
bounding it directly preserves cancellation between the two contributions.
These are fixed two-step spatial theorems. The threshold does not assert
arbitrary-depth spatial control of transported original marks.

There is also an unconditional depth-independent budget. For every positive
continuous density and every finite depth,
`sum_i |c_i(F,G)| <= (Var(F)+Var(G))/2`.
`sum_abs_wilsonPlaquette_scales_le` makes this at most `(z^2+w^2)/2` for
the original centered Wilson plaquettes, at every real beta and every volume.
This rules out unbounded absolute accumulation for uniformly bounded marks.
It supplies no decay with separation and no uniform bound for growing
cutoff normalizations.

The remainder can be bounded independently of depth if its per-scale spatial
estimate is uniform. Write `r_i = 2^i a`, `m = eta/rMax`, and `c_i` for the
contribution at scale `i`, ordered from fine to coarse. Fix `A >= 0` and
`D0 > 0` before cutoff and volume. The sufficient hypothesis is

`D >= D0  ==>  |c_i| <= A exp(-eta D/r_i)` for every eliminated scale.

`coarseSpacing_rev` proves the exact relation between each `r_i` and the
stopping spacing. `directRemainder_le_of_physicalScaleBounds` sums the estimates
without a depth factor: away from the diagonal its prefactor is
`A exp(-m D0)/(1-exp(-m D0))`. If the original marks are uniformly bounded by
`B0,C0`, `StoppingScaleEntrance.covarianceRemainder_le_of_scaleBounds` covers
near and coincident points as well, with

`epsilon = 2 B0 C0 exp(m D0) + A exp(-m D0)/(1-exp(-m D0))`.

For the two proved Wilson steps, the common amplitude is explicitly
`A = 24 |z| |w| exp(48+6 eta)` and `D = a dist(supp p,supp q)`.
`twoScaleCovariance_wilsonPlaquette_physical_le` discharges both per-scale
inequalities, and `twoStepRemainder_wilsonPlaquette_physical_le` applies the
depth-sum theorem at `j=2`, `4a <= rMax`, and `D >= D0 > 0`.
The general depth-sum theorem remains conditional beyond those two steps.

This supplies the remainder field of `TransportControl` once the per-scale
inequality is proved. The hypothesis is on the averaged covariance, so a
bound for every retained configuration is sufficient but unnecessary. Uniform
anchored budgets for the final projected marks remain a separate requirement.
The separate absolute-value bounds may lose cancellations between scales;
they are sufficient conditions, not necessary consequences of clustering.
Cutoff-dependent plaquette normalizations are not absorbed into uniform constants.
The contact estimate requires bounded original amplitudes. For renormalized
point fields with growing normalization, uniform contact control is not asserted;
the theorem at positive physical separation does not require those contact bounds.

The necessity of the remainder control is concrete. In
`MarginalBlindness.SU2Blocking`, let `F,G` be Haar-centered plaquette traces
at support distance greater than one and take `W = 1 + epsilon F G`,
`|epsilon| < 1`. Under the actual paired Haar map, `B(W)=1`, `PF=PG=0`,
but `P(FG)=epsilon v^2` and `Cov_W(F,G)=epsilon v^2`, where the fixed
four-link Haar variance `v` is strictly positive. Opposite transverse
plaquettes have distance at least `n+3` on side `2(n+3)`;
`no_uniform_covariance_bound` rules out a volume-uniform exponential bound
at `epsilon=1/2`. Retained coarse Wilson plaquettes still have variance `v`.
This rules out reliance on the coarse density and transported means alone.
The calibration family cannot satisfy the uniform positive-rate small
fine-interaction hypotheses: those would force the exponential bound just
ruled out. It does not refute the actual Wilson trajectory.

`strongCouplingEntrance` constructs an actual entrance family with fixed small
Wilson coupling, `a(k)=2^(-k)`, depth `k`, and stopping spacing one. This proves
the stopping interface is nonempty. `WeakCouplingEntranceObligation` separately
states the unproved target with `a(k) -> 0` and `beta(k) -> infinity`. Its
existence, the needed observable budgets and the uniform per-scale inequality
above along such a trajectory are open. The generated conditional law at scale
`i` has density `W_i(chart(c,f))/W_(i+1)(c)` against fluctuation Haar measure;
its outer average uses the normalized generated density `W_(i+1)`.
Smallness of the final density alone gives neither this bound nor control of
the transported observables. Nonzero observables at each finite cutoff do not
establish a nontrivial continuum limit. Construction, Euclidean covariance,
reflection compatibility and quantum-field reconstruction remain separate.

The reproducible [planar SU(2) diagnostic](../../../../../tools/yang-mills/su2_planar_block_diagnostic.py)
examines a two-dimensional open patch through exact character-convolution
formulas, quadrature and sampled direct/staged Haar integrals. It tests couplings
from zero to 16, checks ordered-product gauge identities, and records generated
non-Wilson logarithmic components. Mode and quadrature refinements and sampling
errors are reported. These finite computations do not certify four-dimensional
uniform bounds. The `--covariance` mode records both terms of the covariance
identity, original and retained variances, and the two-scale contribution sum.
For independent original plaquettes, the nonzero coarse covariance cancels the
averaged conditional covariance; either term alone misrepresents the original
correlation. The planar setting is the open-boundary Euclidean example in
[Kanwar and Wagman](https://arxiv.org/abs/2103.02602); the spatial polymer estimates
are proved separately in Lean. [Ueltschi's cluster-expansion criteria](https://arxiv.org/abs/math-ph/0304003)
likewise require strengthened weighted hypotheses to obtain spatial decay.
For a rigorous example of loss of locality under blocking,
[van Enter, Fernandez and Sokal](https://arxiv.org/abs/hep-lat/9210032),
Theorem 4.1, treats scale-two decimation of the two-dimensional nearest-neighbour
Ising model at zero field and coupling greater than
`arcosh(1+sqrt(2))/2`. Its image has no quasilocal specification. These hypotheses
do not establish a corresponding pathology for compact SU(2); they distinguish
existence of an exact marginal from the uniform locality needed for iteration.

The `--weak-coupling` diagnostic tests beta from 1 to 128 with two discarded
scales, 128/256-node quadrature, character-tail envelopes and independent exact-law
rejection sampling in real arithmetic. It records floating-point and sampling
diagnostics separately; these are not certified error bounds. The raw absolute
discarded sum peaks near beta 2 and falls on the later tested couplings, whereas
its ratio to the original variance rises to about 0.437 at beta 128. Rescaling
the two marks by beta gives a budget about 0.653 at that coupling. Thus small
unrescaled covariance alone does not establish control of renormalized marks.
This two-dimensional, two-step experiment tests neither long-distance decay
nor uniformity over arbitrary blocking depths in four dimensions.
