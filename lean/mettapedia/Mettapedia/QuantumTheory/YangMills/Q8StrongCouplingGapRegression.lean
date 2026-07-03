import Mettapedia.QuantumTheory.YangMills.Q8StrongCouplingGap

/-!
# `Q₈` strong-coupling gap regression checks

Pins the non-abelian canary: group axioms and the non-commutativity witness,
the character-form kernel equals the genuine `Q₈` convolution kernel, the
spectral self-pairing identity, reflection positivity, the complete
eigensystem action on spectral coefficients, and the gap value `1`.
Axiom audits are guarded so any future `sorry` or extra axiom fails the
build.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace Q8StrongCouplingGapRegression

theorem q8_group_regression :
    (∀ a b c : Fin 8, q8Mul (q8Mul a b) c = q8Mul a (q8Mul b c)) ∧
      (∀ a : Fin 8, q8Mul 0 a = a) ∧
      (∀ a : Fin 8, q8Mul (q8Inv a) a = 0) ∧
      q8Mul 2 4 ≠ q8Mul 4 2 :=
  ⟨q8Mul_assoc, q8_one_mul, q8_inv_mul, q8_noncommutative⟩

theorem q8_convolution_grounding_regression
    (x y : Q8OneLinkConfig) :
    q8StrongCouplingKernel x y = q8HeatClassFunction (q8Mul x (q8Inv y)) :=
  q8StrongCouplingKernel_eq_heat_convolution x y

theorem q8_reflection_positive_regression :
    OSReflectionPositive q8StrongCouplingKernel :=
  q8StrongCouplingKernel_reflectionPositive

theorem q8_spectral_action_regression
    (f : FiniteObservable Q8OneLinkConfig) :
    q8S0 (q8StrongCouplingTransfer f) = q8S0 f ∧
      q8Si (q8StrongCouplingTransfer f) = q8SignRatio * q8Si f ∧
      q8DR (q8StrongCouplingTransfer f) = q8SpinRatio * q8DR f :=
  ⟨q8S0_transfer f, q8Si_transfer f, q8DR_transfer f⟩

theorem q8_gap_value_regression :
    q8StrongCouplingGap = 1 ∧ 0 < q8StrongCouplingGap :=
  ⟨q8StrongCouplingGap_eq_one, q8StrongCouplingGap_positive⟩

theorem q8_gap_in_spin_sector_regression :
    q8SignRatio ≤ q8SpinRatio :=
  q8SignRatio_le_spinRatio

theorem q8_landmark_regression :
    ∃ _ : Q8StrongCouplingGapCanary,
      q8Mul 2 4 ≠ q8Mul 4 2 ∧
        OSReflectionPositive q8StrongCouplingKernel ∧
        q8StrongCouplingGap = 1 ∧
        0 < q8StrongCouplingGap :=
  q8StrongCoupling_nonabelian_massGap_landmark

/--
info: 'Mettapedia.QuantumTheory.YangMills.q8StrongCouplingKernel_eq_heat_convolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms q8StrongCouplingKernel_eq_heat_convolution

/--
info: 'Mettapedia.QuantumTheory.YangMills.q8StrongCouplingKernel_self_pairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms q8StrongCouplingKernel_self_pairing

/--
info: 'Mettapedia.QuantumTheory.YangMills.q8StrongCouplingKernel_reflectionPositive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms q8StrongCouplingKernel_reflectionPositive

/--
info: 'Mettapedia.QuantumTheory.YangMills.q8StrongCoupling_nonabelian_massGap_landmark' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms q8StrongCoupling_nonabelian_massGap_landmark

end Q8StrongCouplingGapRegression
end YangMills
end QuantumTheory
end Mettapedia
