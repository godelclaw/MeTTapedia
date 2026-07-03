import Mettapedia.QuantumTheory.YangMills.ToyRGMap

/-!
# Toy RG dynamics regression checks

Pins the toy realization of the two-source bootstrap: exact orbit recursion,
slack-implies-invariant-ball for the dynamics, the manuscript-constant
instantiation at depth `16`, the one-step ball escape at depth `15` (the
dynamical sharpness of the `1/3` threshold), and the nonlinearity witness.
Axiom audits are guarded so any future `sorry` or extra axiom fails the
build.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace ToyRGMapRegression

theorem orbit_recursion_regression (a q σu σv : ℝ) (s0 : ToyRGState) (j : ℕ) :
    (toyRGOrbit a q σu σv s0 (j + 1)).x
      = a * (toyRGOrbit a q σu σv s0 j).x
        + q * (toyRGOrbit a q σu σv s0 j).x ^ 2
        + (toyRGOrbit a q σu σv s0 j).u
        + (toyRGOrbit a q σu σv s0 j).v :=
  toyRGOrbit_x_recursion a q σu σv s0 j

theorem invariant_ball_of_slack_regression
    {C : ℝ} {b dmax : ℕ} {σu σv : ℝ}
    (hC : 0 < C)
    (hslack : HasTwoSourceBootstrapSlack C b dmax)
    (hσu0 : 0 ≤ σu) (hσu1 : σu ≤ 1) (hσv0 : 0 ≤ σv) (hσv1 : σv ≤ 1)
    {s0 : ToyRGState} (hx0 : 0 ≤ s0.x) (hu0 : 0 ≤ s0.u) (hv0 : 0 ≤ s0.v)
    (hx : s0.x ≤ twoSourceEpsilonStar C (rgGain C b dmax))
    (hu : s0.u ≤ twoSourceEpsilonStar C (rgGain C b dmax) / 4)
    (hv : s0.v ≤ twoSourceEpsilonStar C (rgGain C b dmax) / 4)
    (j : ℕ) :
    (toyRGOrbit (rgGain C b dmax) C σu σv s0 j).x
      ≤ twoSourceEpsilonStar C (rgGain C b dmax) :=
  toyRG_invariant_ball_of_slack hC hslack hσu0 hσu1 hσv0 hσv1
    hx0 hu0 hv0 hx hu hv j

theorem ben_realization_regression :
    ToyRGBootstrapRealization 2224 2 16 :=
  benToyRGBootstrapRealization

theorem escape_two_fifteen_regression (σu σv : ℝ) :
    twoSourceEpsilonStar 2224 (rgGain 2224 2 15) <
      (toyRGOrbit (rgGain 2224 2 15) 2224 σu σv
        ⟨twoSourceEpsilonStar 2224 (rgGain 2224 2 15),
          twoSourceEpsilonStar 2224 (rgGain 2224 2 15) / 4,
          twoSourceEpsilonStar 2224 (rgGain 2224 2 15) / 4⟩ 1).x :=
  toyRG_ball_escape_two_fifteen σu σv

theorem nonlinearity_regression (a σu σv : ℝ) :
    (toyRGStep a 2224 σu σv ⟨2, 0, 0⟩).x
        - 2 * (toyRGStep a 2224 σu σv ⟨1, 0, 0⟩).x
        + (toyRGStep a 2224 σu σv ⟨0, 0, 0⟩).x
      ≠ 0 :=
  toyRGStep_not_affine_at_manuscript_constants a σu σv

/--
info: 'Mettapedia.QuantumTheory.YangMills.toyRG_invariant_ball_of_slack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toyRG_invariant_ball_of_slack

/--
info: 'Mettapedia.QuantumTheory.YangMills.benToyRGBootstrapRealization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms benToyRGBootstrapRealization

/--
info: 'Mettapedia.QuantumTheory.YangMills.toyRG_ball_escape_two_fifteen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toyRG_ball_escape_two_fifteen

/--
info: 'Mettapedia.QuantumTheory.YangMills.toyRGStep_not_affine_at_manuscript_constants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toyRGStep_not_affine_at_manuscript_constants

end ToyRGMapRegression
end YangMills
end QuantumTheory
end Mettapedia
