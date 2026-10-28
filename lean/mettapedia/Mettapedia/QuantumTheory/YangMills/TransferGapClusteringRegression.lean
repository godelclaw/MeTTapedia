import Mettapedia.QuantumTheory.YangMills.TransferGapClustering

/-!
# Transfer gap/clustering regression checks

Pins the abstract finite OS statements: gap implies truncated two-point
clustering at rate `q` (squared, absolute-value, and exponential forms);
per-vector moment decay forces the eigenvalue bound; an additive `+ δ` term
defeats the moment argument; and prefactor absorption into a rate slack.
Axiom audits are guarded so any future `sorry` or extra axiom fails the
build.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace TransferGapClusteringRegression

universe u

variable {Ω : Type u} [Fintype Ω]

theorem gap_implies_clustering_sq_regression
    (S : NormalizedTransferGapSystem Ω)
    (f g : FiniteObservable Ω) (n : ℕ) :
    truncatedTwoPoint S f g n ^ 2
      ≤ (S.q ^ n) ^ 2 *
        (osBilinearForm S.K (vacuumSubtract S f) (vacuumSubtract S f) *
          osBilinearForm S.K (vacuumSubtract S g) (vacuumSubtract S g)) :=
  truncatedTwoPoint_sq_le S f g n

theorem gap_implies_clustering_abs_regression
    (S : NormalizedTransferGapSystem Ω)
    (f g : FiniteObservable Ω) (n : ℕ) :
    |truncatedTwoPoint S f g n|
      ≤ clusteringPrefactor S f g * S.q ^ n :=
  abs_truncatedTwoPoint_le S f g n

theorem gap_implies_clustering_exp_regression
    (S : NormalizedTransferGapSystem Ω) (hq : 0 < S.q)
    (f g : FiniteObservable Ω) (n : ℕ) :
    |truncatedTwoPoint S f g n|
      ≤ clusteringPrefactor S f g
        * Real.exp (-transferMassGap S * n) :=
  abs_truncatedTwoPoint_le_exp S hq f g n

theorem moment_decay_eigenvalue_regression
    {K : Ω → Ω → ℝ}
    {T : FiniteObservable Ω → FiniteObservable Ω}
    {v : FiniteObservable Ω} {μ q Cv : ℝ}
    (hq : 0 ≤ q)
    (heig : T v = μ • v)
    (hTsmul : ∀ (a : ℝ) (w : FiniteObservable Ω), T (a • w) = a • T w)
    (hvpos : 0 < osBilinearForm K v v)
    (hmom : ∀ n : ℕ, osBilinearForm K v (T^[n] v) ≤ Cv * q ^ n) :
    |μ| ≤ q :=
  eigenvalue_abs_le_of_moment_decay hq heig hTsmul hvpos hmom

theorem additive_defeat_regression :
    ∃ (K : Fin 1 → Fin 1 → ℝ)
      (T : FiniteObservable (Fin 1) → FiniteObservable (Fin 1))
      (v : FiniteObservable (Fin 1)) (μ q Cv δ : ℝ),
      0 ≤ q ∧ 0 < δ ∧
      T v = μ • v ∧
      (∀ (a : ℝ) (w : FiniteObservable (Fin 1)), T (a • w) = a • T w) ∧
      0 < osBilinearForm K v v ∧
      (∀ n : ℕ, osBilinearForm K v (T^[n] v) ≤ Cv * q ^ n + δ) ∧
      q < |μ| :=
  moment_decay_additive_defeat

theorem prefactor_absorption_regression
    {corr : SpatialCorrelation} {A m C : ℝ}
    (hCm : C < m)
    (hbound : ∀ x y : Space, |corr x y| ≤ A * Real.exp (-m * dist x y)) :
    HasExponentialClusteringAtRate corr C :=
  hasExponentialClusteringAtRate_of_uniform_exp_bound hCm hbound

/--
info: 'Mettapedia.QuantumTheory.YangMills.truncatedTwoPoint_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms truncatedTwoPoint_sq_le

/--
info: 'Mettapedia.QuantumTheory.YangMills.abs_truncatedTwoPoint_le_exp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms abs_truncatedTwoPoint_le_exp

/--
info: 'Mettapedia.QuantumTheory.YangMills.eigenvalue_abs_le_of_moment_decay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms eigenvalue_abs_le_of_moment_decay

/--
info: 'Mettapedia.QuantumTheory.YangMills.moment_decay_additive_defeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms moment_decay_additive_defeat

/--
info: 'Mettapedia.QuantumTheory.YangMills.hasExponentialClusteringAtRate_of_uniform_exp_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms hasExponentialClusteringAtRate_of_uniform_exp_bound

end TransferGapClusteringRegression
end YangMills
end QuantumTheory
end Mettapedia
