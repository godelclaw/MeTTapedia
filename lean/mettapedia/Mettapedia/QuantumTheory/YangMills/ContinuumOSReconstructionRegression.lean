import Mettapedia.QuantumTheory.YangMills.ContinuumOSReconstruction

/-!
# Regression checks for the Yang-Mills continuum OS reconstruction scaffold
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace ContinuumOSReconstructionRegression

def continuum_os_packet_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (machine : KirkOSReconstructionMachine A Δ corr)
    (massGap : LatticeMassGapInput)
    (reflectionPositive : OSReflectionPositivityInput)
    (clustering : LatticeExponentialClusteringInput corr) :
    ContinuumWightmanMassGapPacket A Δ :=
  continuumPacket_of_latticeMassGap_reflectionPositive_clustering
    machine massGap reflectionPositive clustering

theorem continuum_os_mass_gap_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (machine : KirkOSReconstructionMachine A Δ corr)
    (massGap : LatticeMassGapInput)
    (reflectionPositive : OSReflectionPositivityInput)
    (clustering : LatticeExponentialClusteringInput corr) :
    HasSpectralMassGap A Δ :=
  continuumMassGap_of_latticeMassGap_reflectionPositive_clustering
    machine massGap reflectionPositive clustering

theorem continuum_os_gap_positive_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (machine : KirkOSReconstructionMachine A Δ corr)
    (massGap : LatticeMassGapInput)
    (reflectionPositive : OSReflectionPositivityInput)
    (clustering : LatticeExponentialClusteringInput corr) :
    0 < Δ :=
  continuumGapPositive_of_latticeMassGap_reflectionPositive_clustering
    machine massGap reflectionPositive clustering

theorem ben_carried_actual_wilson_contraction_regression
    {corr : SpatialCorrelation}
    (bridge : BenLambdaToKirkOpenInput corr) :
    HasTwoSourceBootstrapSlack bridge.Ctrue 2 16 :=
  bridge.actualWilsonTwoSourceContraction

def ben_lambda_bridge_lattice_inputs_regression
    {corr : SpatialCorrelation}
    (bridge : BenLambdaToKirkOpenInput corr) :
    LatticeMassGapInput × LatticeExponentialClusteringInput corr :=
  bridge.latticeInputs

theorem ben_continuum_os_conditional_mass_gap_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (D : BenYMContinuumOSConditional A Δ corr) :
    HasSpectralMassGap A Δ :=
  D.continuumMassGap

theorem ben_continuum_os_conditional_packet_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (D : BenYMContinuumOSConditional A Δ corr) :
    HasTwoSourceBootstrapSlack D.lambdaBridge.Ctrue 2 16 ∧
      HasSpectralMassGap A Δ ∧
        0 < Δ :=
  D.reductionPacket

theorem ben_open_inputs_lambda_bridge_regression :
    "Actual Wilson contraction implies lattice mass gap and exponential clustering" ∈
      benContinuumEndpointOpenInputs :=
  benContinuumEndpointOpenInputs_records_lambda_bridge

theorem ben_open_inputs_reflection_positivity_regression :
    "Ben Wilson-measure OS reflection positivity: functional plus cone" ∈
      benContinuumEndpointOpenInputs :=
  benContinuumEndpointOpenInputs_records_reflection_positivity

theorem preprints_verdict_regression :
    preprints2025041268Verdict = .notRouteBlocking :=
  preprints2025041268Verdict_notRouteBlocking

end ContinuumOSReconstructionRegression
end YangMills
end QuantumTheory
end Mettapedia
