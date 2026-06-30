import Mettapedia.QuantumTheory.YangMills.Clustering
import Mettapedia.QuantumTheory.YangMills.ExtractionConstantBreak

/-!
# Yang-Mills Continuum OS Reconstruction Scaffold

This module isolates the honest continuum endpoint after the extraction
constant erratum: the extended-extraction contraction stands, but the
continuum Yang-Mills mass gap is not proved here.

The scaffold follows the Kirk-style route:

* lattice positive mass gap,
* OS reflection positivity,
* exponential clustering,
* subsequential Schwinger-function limits and OS reconstruction,

then a continuum Hamiltonian with a positive spectral gap.  The heavy
constructive-QFT theorem is a structure field.  The central open bridge for
Ben's route is also explicit: the standing `Lambda < 1` contraction must still
be shown to imply the lattice gap and exponential clustering required by the
OS reconstruction framework.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- Lattice mass-gap input in the form needed by the continuum reconstruction
scaffold.  It is deliberately separate from the continuum Hamiltonian gap. -/
structure LatticeMassGapInput where
  gap : ℝ
  positive : 0 < gap

/-- Lattice exponential clustering input for one correlation kernel. -/
structure LatticeExponentialClusteringInput (corr : SpatialCorrelation) where
  rate : ℝ
  ratePositive : 0 < rate
  clusteringAtRate : HasExponentialClusteringAtRate corr rate

/-- OS reflection positivity data.  For Ben's Wilson-measure route this is an
open input unless both the functional and cone interfaces are represented. -/
structure OSReflectionPositivityInput where
  reflectionPositiveFunctional : Prop
  reflectionPositiveCone : Prop
  reflectionPositive : reflectionPositiveFunctional ∧ reflectionPositiveCone

/-- Subsequence and regularity data needed before applying OS reconstruction
to the limiting Schwinger functions. -/
structure ContinuumSchwingerLimitInput where
  subsequentialLimits : Prop
  temperedness : Prop
  euclideanCovarianceRestored : Prop
  limitReady :
    subsequentialLimits ∧ temperedness ∧ euclideanCovarianceRestored

/-- Output packet of the carried OS reconstruction theorem: a reconstructed
continuum Wightman theory with a positive-energy Hamiltonian and a mass gap. -/
structure ContinuumWightmanMassGapPacket
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) (Δ : ℝ) where
  osHilbertSpaceConstructed : Prop
  wightmanQFTConstructed : Prop
  positiveEnergySpectrum : HasPositiveEnergySpectrum A
  continuumMassGap : HasSpectralMassGap A Δ

/-- Abstract Kirk-style OS reconstruction machine.

The two function fields are exactly the analytic/constructive-QFT work not
formalized in Mathlib here: extraction of subsequential Schwinger-function
limits from the lattice hypotheses, then OS reconstruction plus Hamiltonian
gap transfer. -/
structure KirkOSReconstructionMachine
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) (Δ : ℝ) (corr : SpatialCorrelation) where
  schwingerLimits :
    LatticeMassGapInput →
      OSReflectionPositivityInput →
        LatticeExponentialClusteringInput corr →
          ContinuumSchwingerLimitInput
  osReconstruction :
    (massGap : LatticeMassGapInput) →
      (reflectionPositive : OSReflectionPositivityInput) →
        (clustering : LatticeExponentialClusteringInput corr) →
          ContinuumSchwingerLimitInput →
            ContinuumWightmanMassGapPacket A Δ

/-- The carried OS machinery produces the full continuum packet from the three
Kirk-side inputs. -/
def continuumPacket_of_latticeMassGap_reflectionPositive_clustering
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (machine : KirkOSReconstructionMachine A Δ corr)
    (massGap : LatticeMassGapInput)
    (reflectionPositive : OSReflectionPositivityInput)
    (clustering : LatticeExponentialClusteringInput corr) :
    ContinuumWightmanMassGapPacket A Δ :=
  machine.osReconstruction massGap reflectionPositive clustering
    (machine.schwingerLimits massGap reflectionPositive clustering)

/-- Checked conditional: lattice mass gap, OS reflection positivity, and
exponential clustering imply a continuum spectral mass gap, provided the
Kirk-style OS reconstruction machine is supplied. -/
theorem continuumMassGap_of_latticeMassGap_reflectionPositive_clustering
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (machine : KirkOSReconstructionMachine A Δ corr)
    (massGap : LatticeMassGapInput)
    (reflectionPositive : OSReflectionPositivityInput)
    (clustering : LatticeExponentialClusteringInput corr) :
    HasSpectralMassGap A Δ :=
  (continuumPacket_of_latticeMassGap_reflectionPositive_clustering
    machine massGap reflectionPositive clustering).continuumMassGap

/-- Positivity of the continuum gap follows from the checked conditional
rather than being an extra advertised endpoint claim. -/
theorem continuumGapPositive_of_latticeMassGap_reflectionPositive_clustering
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (machine : KirkOSReconstructionMachine A Δ corr)
    (massGap : LatticeMassGapInput)
    (reflectionPositive : OSReflectionPositivityInput)
    (clustering : LatticeExponentialClusteringInput corr) :
    0 < Δ :=
  (continuumMassGap_of_latticeMassGap_reflectionPositive_clustering
    machine massGap reflectionPositive clustering).positive

/-- The standing numerical endpoint after the extraction-constant erratum. -/
def BenStandingExtendedExtractionContraction : Prop :=
  HasExtendedExtractionContraction benCauchyC1UpperBound 2 16

/-- The standing contraction theorem is checked arithmetic, not a continuum
mass-gap theorem. -/
theorem benStandingExtendedExtractionContraction_checked :
    BenStandingExtendedExtractionContraction :=
  benCauchyC1UpperBound_contraction_two_sixteen

/-- Central open input for Ben's continuum route: prove that the standing
`Lambda < 1` extended-extraction contraction supplies the lattice mass gap and
exponential clustering required by the OS reconstruction framework. -/
structure BenLambdaToKirkOpenInput (corr : SpatialCorrelation) where
  latticeGapAndClustering_of_contraction :
    BenStandingExtendedExtractionContraction →
      LatticeMassGapInput × LatticeExponentialClusteringInput corr

/-- If the open bridge is supplied, the standing contraction provides the
Kirk-side lattice inputs. -/
def BenLambdaToKirkOpenInput.latticeInputs
    {corr : SpatialCorrelation}
    (bridge : BenLambdaToKirkOpenInput corr) :
    LatticeMassGapInput × LatticeExponentialClusteringInput corr :=
  bridge.latticeGapAndClustering_of_contraction
    benStandingExtendedExtractionContraction_checked

/-- Ben-specific conditional endpoint package.

This is intentionally stronger than the current route ledger: it assumes the
open bridge from contraction to lattice gap/clustering, the Wilson-measure OS
reflection-positivity input, and the Kirk-style OS reconstruction machine. -/
structure BenYMContinuumOSConditional
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) (Δ : ℝ) (corr : SpatialCorrelation) where
  lambdaBridge : BenLambdaToKirkOpenInput corr
  reflectionPositivity : OSReflectionPositivityInput
  reconstructionMachine : KirkOSReconstructionMachine A Δ corr

/-- Conditional continuum endpoint for Ben's route.

The proof genuinely uses the checked standing contraction through the explicit
open bridge before invoking the carried OS reconstruction machine. -/
theorem BenYMContinuumOSConditional.continuumMassGap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (D : BenYMContinuumOSConditional A Δ corr) :
    HasSpectralMassGap A Δ := by
  let inputs := D.lambdaBridge.latticeInputs
  exact
    continuumMassGap_of_latticeMassGap_reflectionPositive_clustering
      D.reconstructionMachine inputs.1 D.reflectionPositivity inputs.2

/-- Regression-friendly packet showing the conditional is not a bare restatement:
the standing contraction is used to obtain Kirk-side inputs, then the continuum
gap follows. -/
theorem BenYMContinuumOSConditional.reductionPacket
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (D : BenYMContinuumOSConditional A Δ corr) :
    BenStandingExtendedExtractionContraction ∧
      HasSpectralMassGap A Δ ∧
        0 < Δ := by
  have hgap := D.continuumMassGap
  exact
    ⟨benStandingExtendedExtractionContraction_checked,
      hgap,
      hgap.positive⟩

/-- Named open inputs that remain after the conditional scaffold is checked. -/
def benContinuumEndpointOpenInputs : List String :=
  [ "Ben Lambda<1 contraction implies lattice mass gap and exponential clustering"
  , "Ben Wilson-measure OS reflection positivity: functional plus cone"
  , "Kirk-style subsequential Schwinger limits and OS reconstruction machinery"
  ]

theorem benContinuumEndpointOpenInputs_records_lambda_bridge :
    "Ben Lambda<1 contraction implies lattice mass gap and exponential clustering" ∈
      benContinuumEndpointOpenInputs := by
  simp [benContinuumEndpointOpenInputs]

theorem benContinuumEndpointOpenInputs_records_reflection_positivity :
    "Ben Wilson-measure OS reflection positivity: functional plus cone" ∈
      benContinuumEndpointOpenInputs := by
  simp [benContinuumEndpointOpenInputs]

/-- Verdict tags for the requested side-check on claimed incompatibility
between a continuum mass gap and asymptotic freedom. -/
inductive ContinuumIncompatibilityVerdict where
  | notRouteBlocking
  | unresolved
  | routeBlocking
deriving DecidableEq, Repr

/-- Side-check verdict for the reported preprints.org/202504.1268 claim.

Verdict: not route-blocking.  As reported, the claimed contradiction relies on
expanding the Kallen-Lehmann integral as an `O(1/p^2)` term using finite
spectral moments and a too-rigid subtraction-polynomial analysis for a
composite `Tr(F^2)` two-point function.  That does not refute the OS/Kirk
conditional route, so no additional formal obstruction is introduced here. -/
def preprints2025041268Verdict : ContinuumIncompatibilityVerdict :=
  .notRouteBlocking

theorem preprints2025041268Verdict_notRouteBlocking :
    preprints2025041268Verdict = .notRouteBlocking := by
  rfl

end YangMills
end QuantumTheory
end Mettapedia
