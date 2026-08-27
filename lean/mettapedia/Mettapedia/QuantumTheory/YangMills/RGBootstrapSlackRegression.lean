import Mettapedia.QuantumTheory.YangMills.RGBootstrapSlack

/-!
# RG bootstrap slack regression checks

Pins the two-source bootstrap layer: the `1/3` closure theorem, the
linear-vs-bootstrap least-depth separation at `dmax = 15`, and the concrete
closure at the advertised constants.  Axiom audits are guarded so any future
`sorry` or extra axiom fails the build.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace RGBootstrapSlackRegression

theorem slack_sixteen_regression :
    HasTwoSourceBootstrapSlack 2224 2 16 :=
  twoSourceBootstrapSlack_2224_two_sixteen

theorem linear_yes_bootstrap_no_fifteen_regression :
    HasExtendedExtractionContraction 2224 2 15 ∧
      ¬ HasTwoSourceBootstrapSlack 2224 2 15 :=
  ⟨rgContraction_2224_two_fifteen,
    not_twoSourceBootstrapSlack_2224_two_fifteen⟩

theorem least_depth_separation_regression :
    (HasExtendedExtractionContraction 2224 2 15 ∧
      ∀ dmax : ℕ, dmax ≤ 14 → ¬ HasExtendedExtractionContraction 2224 2 dmax) ∧
    (HasTwoSourceBootstrapSlack 2224 2 16 ∧
      ∀ dmax : ℕ, dmax ≤ 15 → ¬ HasTwoSourceBootstrapSlack 2224 2 dmax) :=
  leastDepth_2224_two_packet

theorem epsilon_star_value_regression :
    benTwoSourceEpsilonStar = (373 : ℝ) / 4554752 :=
  benTwoSourceEpsilonStar_eq

/--
info: 'Mettapedia.QuantumTheory.YangMills.scalar_bootstrap_two_sources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scalar_bootstrap_two_sources

/--
info: 'Mettapedia.QuantumTheory.YangMills.ben_scalar_bootstrap_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ben_scalar_bootstrap_closure

/--
info: 'Mettapedia.QuantumTheory.YangMills.leastDepth_2224_two_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms leastDepth_2224_two_packet

end RGBootstrapSlackRegression
end YangMills
end QuantumTheory
end Mettapedia
