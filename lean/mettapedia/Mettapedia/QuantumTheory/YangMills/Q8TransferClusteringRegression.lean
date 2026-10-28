import Mettapedia.QuantumTheory.YangMills.Q8TransferClustering

/-!
# `Q₈` transfer clustering regression checks

Pins the non-abelian instantiation of the transfer-gap clustering theorem:
the packaged system has mass gap exactly `1`, its truncated two-point
function decays at that rate, the induced spatial kernel clusters at every
rate below `1`, and the lattice mass-gap/reflection-positivity/clustering
inputs of the Kirk continuum gate are discharged (the OS reconstruction
machine remains the open input).  Axiom audits are guarded so any future
`sorry` or extra axiom fails the build.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace Q8TransferClusteringRegression

theorem q8_system_massGap_eq_one_regression :
    transferMassGap q8TransferGapSystem = 1 := by
  rw [q8TransferGapSystem_massGap_eq, q8StrongCouplingGap_eq_one]

theorem q8_gap_contraction_regression
    (f : FiniteObservable Q8OneLinkConfig)
    (horth : osBilinearForm q8NormalizedKernel q8ConstantObservable f = 0) :
    osBilinearForm q8NormalizedKernel
        (q8StrongCouplingTransfer f) (q8StrongCouplingTransfer f)
      ≤ q8SpinRatio ^ 2 *
        osBilinearForm q8NormalizedKernel f f :=
  q8_gapContraction f horth

theorem q8_decay_at_gap_rate_regression
    (f g : FiniteObservable Q8OneLinkConfig) (n : ℕ) :
    |truncatedTwoPoint q8TransferGapSystem f g n|
      ≤ clusteringPrefactor q8TransferGapSystem f g
        * Real.exp (-q8StrongCouplingGap * n) :=
  q8_truncatedTwoPoint_decay_at_gap_rate f g n

theorem q8_spatial_clustering_half_rate_regression
    (f g : FiniteObservable Q8OneLinkConfig) :
    HasExponentialClusteringAtRate (q8SpatialCorrelation f g) (1 / 2) :=
  q8SpatialCorrelation_clustering f g (by norm_num)

theorem q8_continuum_gate_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (f g : FiniteObservable Q8OneLinkConfig)
    (machine : KirkOSReconstructionMachine A Δ (q8SpatialCorrelation f g)) :
    HasSpectralMassGap A Δ :=
  q8_continuumMassGap_of_reconstructionMachine f g machine

/--
info: 'Mettapedia.QuantumTheory.YangMills.q8_gapContraction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms q8_gapContraction

/--
info: 'Mettapedia.QuantumTheory.YangMills.q8_truncatedTwoPoint_decay_at_gap_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms q8_truncatedTwoPoint_decay_at_gap_rate

/--
info: 'Mettapedia.QuantumTheory.YangMills.q8SpatialCorrelation_clustering' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms q8SpatialCorrelation_clustering

/--
info: 'Mettapedia.QuantumTheory.YangMills.q8_continuumMassGap_of_reconstructionMachine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms q8_continuumMassGap_of_reconstructionMachine

end Q8TransferClusteringRegression
end YangMills
end QuantumTheory
end Mettapedia
