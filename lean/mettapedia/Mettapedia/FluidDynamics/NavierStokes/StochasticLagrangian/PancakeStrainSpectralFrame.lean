import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAlignmentDynamics
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Ordered spectral frames for three-dimensional strain

This module constructs, rather than assumes, the ordered orthonormal
eigenframe used by the invariant pancake-alignment argument.  Mathlib's
finite-dimensional spectral theorem supplies an orthonormal eigenbasis for a
symmetric real operator, with eigenvalues in decreasing order.

The two route-facing identities are then proved from that basis:

* Parseval: the three squared vorticity coordinates sum to one;
* Rayleigh: `<xi,S xi>` is the eigenvalue-weighted coordinate sum.

Together these discharge the spectral-coordinate premises of the gap
coercivity and near-degeneracy lemmas in `PancakeAlignmentDynamics`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeStrainSpectralFrame

open scoped RealInnerProductSpace BigOperators
open PancakeAlignmentDynamics

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- An orthonormal strain eigenbasis whose eigenvalues are ordered from
largest to smallest. -/
structure OrderedEigenframe (S : R3 →L[ℝ] R3) where
  eigenvalue : Fin 3 → ℝ
  eigenbasis : OrthonormalBasis (Fin 3) ℝ R3
  antitone_eigenvalue : Antitone eigenvalue
  apply_eigenbasis : ∀ i,
    S (eigenbasis i) = eigenvalue i • eigenbasis i

/-- A symmetric three-dimensional strain operator has an ordered orthonormal
eigenframe. -/
def orderedEigenframe (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    OrderedEigenframe S := by
  let hT : S.toLinearMap.IsSymmetric := fun u v ↦ (hSsymm u v).symm
  have hfin : Module.finrank ℝ R3 = 3 := by simp
  exact
    { eigenvalue := hT.eigenvalues hfin
      eigenbasis := hT.eigenvectorBasis hfin
      antitone_eigenvalue := hT.eigenvalues_antitone hfin
      apply_eigenbasis := fun i ↦ hT.apply_eigenvectorBasis hfin i }

/-- Parseval's identity expanded at the three concrete frame indices. -/
theorem parseval_three (b : OrthonormalBasis (Fin 3) ℝ R3)
    (xi : R3) (hxi : ‖xi‖ = 1) :
    (inner ℝ xi (b 0)) ^ 2 + (inner ℝ xi (b 1)) ^ 2 +
      (inner ℝ xi (b 2)) ^ 2 = 1 := by
  have h := b.sum_inner_mul_inner xi xi
  simpa [Fin.sum_univ_succ, real_inner_comm, pow_two,
    real_inner_self_eq_norm_sq, hxi, add_assoc] using h

/-- The Rayleigh quotient expanded in an orthonormal eigenbasis. -/
theorem rayleigh_three (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (lambda : Fin 3 → ℝ) (b : OrthonormalBasis (Fin 3) ℝ R3)
    (heigen : ∀ i, S (b i) = lambda i • b i) (xi : R3) :
    inner ℝ xi (S xi) =
      lambda 0 * (inner ℝ xi (b 0)) ^ 2 +
        lambda 1 * (inner ℝ xi (b 1)) ^ 2 +
        lambda 2 * (inner ℝ xi (b 2)) ^ 2 := by
  calc
    inner ℝ xi (S xi) =
        ∑ i : Fin 3, inner ℝ xi (b i) * inner ℝ (b i) (S xi) :=
      (b.sum_inner_mul_inner xi (S xi)).symm
    _ = ∑ i : Fin 3, lambda i * (inner ℝ xi (b i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hSsymm (b i) xi, heigen i, real_inner_smul_left,
        real_inner_comm (b i) xi]
      ring
    _ = lambda 0 * (inner ℝ xi (b 0)) ^ 2 +
          lambda 1 * (inner ℝ xi (b 1)) ^ 2 +
          lambda 2 * (inner ℝ xi (b 2)) ^ 2 := by
      simp only [Fin.sum_univ_succ]
      norm_num
      ring

/-- The constructed ordered eigenframe supplies both exact coordinate
identities for every unit vorticity direction. -/
theorem orderedEigenframe_coordinates
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (xi : R3) (hxi : ‖xi‖ = 1) :
    let F := orderedEigenframe S hSsymm
    (inner ℝ xi (F.eigenbasis 0)) ^ 2 +
          (inner ℝ xi (F.eigenbasis 1)) ^ 2 +
          (inner ℝ xi (F.eigenbasis 2)) ^ 2 = 1 ∧
      inner ℝ xi (S xi) =
        F.eigenvalue 0 * (inner ℝ xi (F.eigenbasis 0)) ^ 2 +
          F.eigenvalue 1 * (inner ℝ xi (F.eigenbasis 1)) ^ 2 +
          F.eigenvalue 2 * (inner ℝ xi (F.eigenbasis 2)) ^ 2 := by
  let F := orderedEigenframe S hSsymm
  exact ⟨parseval_three F.eigenbasis xi hxi,
    rayleigh_three S hSsymm F.eigenvalue F.eigenbasis
      F.apply_eigenbasis xi⟩

/-- The constructed eigenvalues are ordered at the concrete indices. -/
theorem orderedEigenframe_gaps_nonnegative
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    let F := orderedEigenframe S hSsymm
    0 ≤ F.eigenvalue 0 - F.eigenvalue 1 ∧
      0 ≤ F.eigenvalue 0 - F.eigenvalue 2 := by
  let F := orderedEigenframe S hSsymm
  have h01 : F.eigenvalue 1 ≤ F.eigenvalue 0 :=
    F.antitone_eigenvalue (by decide)
  have h02 : F.eigenvalue 2 ≤ F.eigenvalue 0 :=
    F.antitone_eigenvalue (by decide)
  exact ⟨sub_nonneg.mpr h01, sub_nonneg.mpr h02⟩

/-- The constructed frame discharges the coordinate hypotheses in the
alignment coercivity theorem. -/
theorem OrderedEigenframe.gap_alignmentEnergy_le_strainDefect
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (F : OrderedEigenframe S) (xi : R3) (hxi : ‖xi‖ = 1)
    (gap : ℝ)
    (hgap₁ : gap ≤ F.eigenvalue 0 - F.eigenvalue 1)
    (hgap₂ : gap ≤ F.eigenvalue 0 - F.eigenvalue 2) :
    gap * alignmentEnergy xi (F.eigenbasis 0) ≤
      F.eigenvalue 0 - inner ℝ xi (S xi) := by
  exact gap_mul_alignmentEnergy_le_strainDefect
    S xi (F.eigenbasis 0) (F.eigenbasis 1) (F.eigenbasis 2)
      (F.eigenvalue 0) (F.eigenvalue 1) (F.eigenvalue 2) gap
      (parseval_three F.eigenbasis xi hxi)
      (rayleigh_three S hSsymm F.eigenvalue F.eigenbasis
        F.apply_eigenbasis xi)
      hgap₁ hgap₂

/-- The actual spectral frame of a symmetric strain obeys the gap
coercivity estimate; no eigenbasis or Parseval identity is supplied by the
caller. -/
theorem constructedFrame_gap_alignmentEnergy_le_strainDefect
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (xi : R3) (hxi : ‖xi‖ = 1) (gap : ℝ)
    (hgap₁ : gap ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 1)
    (hgap₂ : gap ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 2) :
    gap * alignmentEnergy xi
        ((orderedEigenframe S hSsymm).eigenbasis 0) ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        inner ℝ xi (S xi) := by
  exact (orderedEigenframe S hSsymm).gap_alignmentEnergy_le_strainDefect
    S hSsymm xi hxi gap hgap₁ hgap₂

/-- For the constructed frame, every threshold gives the exact alternative:
a small top spectral gap, or coercive damping of line misalignment. -/
theorem constructedFrame_smallGap_or_alignmentEnergy_coercive
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (xi : R3) (hxi : ‖xi‖ = 1) (gap : ℝ) :
    let F := orderedEigenframe S hSsymm
    (F.eigenvalue 0 - F.eigenvalue 1 < gap ∨
        F.eigenvalue 0 - F.eigenvalue 2 < gap) ∨
      gap * alignmentEnergy xi (F.eigenbasis 0) ≤
        F.eigenvalue 0 - inner ℝ xi (S xi) := by
  let F := orderedEigenframe S hSsymm
  by_cases hgap₁ : gap ≤ F.eigenvalue 0 - F.eigenvalue 1
  · by_cases hgap₂ : gap ≤ F.eigenvalue 0 - F.eigenvalue 2
    · exact Or.inr (F.gap_alignmentEnergy_le_strainDefect
        S hSsymm xi hxi gap hgap₁ hgap₂)
    · exact Or.inl (Or.inr (lt_of_not_ge hgap₂))
  · exact Or.inl (Or.inl (lt_of_not_ge hgap₁))

end PancakeStrainSpectralFrame
end NavierStokes
end FluidDynamics
end Mettapedia
