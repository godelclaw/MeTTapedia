import Mettapedia.QuantumTheory.YangMills.Z2TransferClustering

/-!
# Z₂ transfer clustering regression checks

Pins the `Z₂` single-link instantiation: the packaged transfer-gap system has
mass gap exactly `1`, its truncated two-point function decays at that rate,
the induced spatial kernel clusters at every rate below `1`, and the lattice
mass-gap/reflection-positivity/clustering inputs of the Kirk continuum gate
are discharged (the OS reconstruction machine remains the open input).
Axiom audits are guarded so any future `sorry` or extra axiom fails the
build.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace Z2TransferClusteringRegression

theorem z2_system_massGap_eq_one_regression :
    transferMassGap z2TransferGapSystem = 1 := by
  rw [z2TransferGapSystem_massGap_eq, z2StrongCouplingGap_eq_one]

theorem z2_decay_at_gap_rate_regression
    (f g : FiniteObservable Z2OneLinkConfig) (n : ℕ) :
    |truncatedTwoPoint z2TransferGapSystem f g n|
      ≤ clusteringPrefactor z2TransferGapSystem f g
        * Real.exp (-z2StrongCouplingGap * n) :=
  z2_truncatedTwoPoint_decay_at_gap_rate f g n

theorem z2_spatial_clustering_half_rate_regression
    (f g : FiniteObservable Z2OneLinkConfig) :
    HasExponentialClusteringAtRate (z2SpatialCorrelation f g) (1 / 2) :=
  z2SpatialCorrelation_clustering f g (by norm_num)

theorem z2_gate_inputs_discharged_regression
    (f g : FiniteObservable Z2OneLinkConfig) :
    z2LatticeMassGapInput.gap = z2StrongCouplingGap ∧
      (z2LatticeClusteringInput f g).rate = 1 / 2 ∧
      z2OSReflectionPositivityInput.reflectionPositiveFunctional :=
  ⟨rfl, rfl, z2NormalizedKernel_reflectionPositive⟩

theorem z2_continuum_gate_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (f g : FiniteObservable Z2OneLinkConfig)
    (machine : KirkOSReconstructionMachine A Δ (z2SpatialCorrelation f g)) :
    HasSpectralMassGap A Δ :=
  z2_continuumMassGap_of_reconstructionMachine f g machine

/--
info: 'Mettapedia.QuantumTheory.YangMills.z2_truncatedTwoPoint_decay_at_gap_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms z2_truncatedTwoPoint_decay_at_gap_rate

/--
info: 'Mettapedia.QuantumTheory.YangMills.z2SpatialCorrelation_clustering' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms z2SpatialCorrelation_clustering

/--
info: 'Mettapedia.QuantumTheory.YangMills.z2_continuumMassGap_of_reconstructionMachine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms z2_continuumMassGap_of_reconstructionMachine

end Z2TransferClusteringRegression
end YangMills
end QuantumTheory
end Mettapedia
