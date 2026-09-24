import Mettapedia.Analysis.OcticCurlCancellation

/-!
# Gradient-removal and layered-jet regressions

These are exact local-jet checks, not assertions of Navier--Stokes
trajectories or dynamical coherence. A radial test on a tangential
layered jet has positive raw transverse square but zero remainder.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.OcticCurlCancellationTests

open scoped RealInnerProductSpace
open OcticCurlCancellation WeightedCurlCancellation EuclideanCrossProduct RadialPower
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def e (i : Fin 3) : R3 := EuclideanSpace.single i 1
def layeredJet (j : Fin 3) : R3 := e 0 j • e 1

theorem raw_transverse_eq :
    cross (e 1) (curlJet (fun j ↦ evenRadialRate 2 (e 1) (layeredJet j))) = (7 : ℝ) • e 0 := by
  ext i
  fin_cases i <;> norm_num [cross, cross_apply, curlJet, evenRadialRate, layeredJet, e,
    EuclideanSpace.inner_single_left, PiLp.single_apply, Pi.single_apply, Matrix.cons_val_two,
    show (2 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 0 by decide]

theorem raw_transverse_square :
    ‖cross (e 1) (curlJet (fun j ↦ evenRadialRate 2 (e 1) (layeredJet j)))‖ ^ 2 = 49 := by
  rw [raw_transverse_eq]
  norm_num [norm_smul, e]

theorem gradient_removed_eq_zero :
    cross (e 1) (curlJet (fun j ↦ evenRadialRate 2 (e 1) (layeredJet j))) -
      potentialGradient (e 1) layeredJet = 0 := by
  rw [cross_curlJet_radial]
  have h := longitudinalRate_layered (e 1) (e 0) (e 1)
    (by norm_num [e, EuclideanSpace.inner_single_left, PiLp.single_apply])
  change -longitudinalRate (e 1) (fun j ↦ e 0 j • e 1) = 0
  rw [h, neg_zero]

theorem arbitrary_normal_gradient_removed (a n v : R3) (h : ⟪a, n⟫ = 0) :
    cross a (curlJet (fun j ↦ evenRadialRate 2 a (n j • v))) -
      potentialGradient a (fun j ↦ n j • v) = 0 := by
  rw [cross_curlJet_radial, longitudinalRate_layered a n v h, neg_zero]

/-- The canonical gradient is not an orthogonal projection of an
arbitrary test: it can increase the norm when the test vanishes. -/
theorem zero_test_subtracted_square :
    ‖cross (e 1) (curlJet (fun _ ↦ (0 : R3))) - potentialGradient (e 1) layeredJet‖ ^ 2 = 49 := by
  have hg := sub_eq_zero.mp gradient_removed_eq_zero
  rw [← hg, raw_transverse_eq]
  have hc : curlJet (fun _ ↦ (0 : R3)) = 0 := by ext i; fin_cases i <;> simp [curlJet]
  rw [hc, cross_zero, zero_sub, norm_neg]
  norm_num [norm_smul, e]

theorem zero_amplitude (D E : Fin 3 → R3) :
    cross (0 : R3) (curlJet E) - potentialGradient 0 D = 0 := by
  ext i
  simp [potentialGradient, potentialRate]

end Mettapedia.Analysis.OcticCurlCancellationTests
