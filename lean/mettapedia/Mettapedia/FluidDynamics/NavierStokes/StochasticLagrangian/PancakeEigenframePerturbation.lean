import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.DirectionEvolutionTilting
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Spatial eigenframe perturbation and the spectral-gap denominator

The actual pancake cone is defined relative to an eigendirection of the
low-frequency strain.  Freezing that direction over a spatial cell requires
a quantitative perturbation theorem.  This module proves the elementary
self-adjoint eigenvector identity underlying the Davis--Kahan estimate.

For self-adjoint `B`, an eigenvector `e` of `A` with eigenvalue `lambda`, and
an eigenvector `f` of `B` with eigenvalue `mu`,

`(lambda - mu) * <f,e> = <f,(A-B)e>`.

For unit vectors, the overlap is therefore at most
`||A-B|| / |lambda-mu|`.  This is the precise spatial analogue of the
eigenvalue-gap denominator already found in the time-dependent tilting
calculation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeEigenframePerturbation

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Rank-one orthogonal-line projector associated with a unit direction. -/
def lineProjector (e : E) : E →L[ℝ] E :=
  InnerProductSpace.rankOne ℝ e e

/-- Difference of line projectors decomposed into two rank-one terms. -/
theorem lineProjector_sub (e f : E) :
    lineProjector e - lineProjector f =
      InnerProductSpace.rankOne ℝ (e - f) e +
        InnerProductSpace.rankOne ℝ f (e - f) := by
  ext v
  simp only [lineProjector, sub_apply, add_apply,
    InnerProductSpace.rankOne_apply, inner_sub_left, sub_smul]
  module

/-- Lipschitz dependence of an orthogonal-line projector on its unit
direction.  Since a line projector is sign-invariant, a later application may
choose the sign of either eigenvector before using this estimate. -/
theorem norm_lineProjector_sub_le (e f : E)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    ‖lineProjector e - lineProjector f‖ ≤ 2 * ‖e - f‖ := by
  rw [lineProjector_sub]
  calc
    ‖InnerProductSpace.rankOne ℝ (e - f) e +
        InnerProductSpace.rankOne ℝ f (e - f)‖ ≤
        ‖InnerProductSpace.rankOne ℝ (e - f) e‖ +
          ‖InnerProductSpace.rankOne ℝ f (e - f)‖ := norm_add_le _ _
    _ = 2 * ‖e - f‖ := by rw [InnerProductSpace.norm_rankOne,
      InnerProductSpace.norm_rankOne, he, hf]; ring

/-- Exact cross-eigenvector perturbation identity. -/
theorem eigenvector_overlap_identity
    (A B : E →L[ℝ] E) (e f : E) (lambda mu : ℝ)
    (hBsymm : ∀ (u v : E), inner ℝ u (B v) = inner ℝ (B u) v)
    (hAe : A e = lambda • e) (hBf : B f = mu • f) :
    (lambda - mu) * ⟪f, e⟫ = ⟪f, (A - B) e⟫ := by
  rw [sub_apply, inner_sub_right, hAe,
    real_inner_smul_right, hBsymm, hBf, real_inner_smul_left]
  ring

/-- Unit-eigenvector overlap bound in product form. -/
theorem abs_gap_mul_abs_overlap_le
    (A B : E →L[ℝ] E) (e f : E) (lambda mu : ℝ)
    (hBsymm : ∀ (u v : E), inner ℝ u (B v) = inner ℝ (B u) v)
    (hAe : A e = lambda • e) (hBf : B f = mu • f)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    |lambda - mu| * |⟪f, e⟫| ≤ ‖A - B‖ := by
  calc
    |lambda - mu| * |⟪f, e⟫| =
        |(lambda - mu) * ⟪f, e⟫| := (abs_mul _ _).symm
    _ = |⟪f, (A - B) e⟫| := by
      rw [eigenvector_overlap_identity A B e f lambda mu
        hBsymm hAe hBf]
    _ ≤ ‖f‖ * ‖(A - B) e‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖f‖ * (‖A - B‖ * ‖e‖) := by
      exact mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.le_opNorm (A - B) e) (norm_nonneg f)
    _ = ‖A - B‖ := by rw [he, hf, one_mul, mul_one]

/-- **Gap-divided eigenframe perturbation estimate.** -/
theorem abs_overlap_le_opNorm_div_gap
    (A B : E →L[ℝ] E) (e f : E) (lambda mu gap : ℝ)
    (hBsymm : ∀ (u v : E), inner ℝ u (B v) = inner ℝ (B u) v)
    (hAe : A e = lambda • e) (hBf : B f = mu • f)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hgap : gap ≤ |lambda - mu|) (hgapPos : 0 < gap) :
    |⟪f, e⟫| ≤ ‖A - B‖ / gap := by
  have hmain := abs_gap_mul_abs_overlap_le A B e f lambda mu
    hBsymm hAe hBf he hf
  have hoverlap : 0 ≤ |⟪f, e⟫| := abs_nonneg _
  have hscaled : gap * |⟪f, e⟫| ≤ ‖A - B‖ :=
    (mul_le_mul_of_nonneg_right hgap hoverlap).trans hmain
  exact (le_div_iff₀ hgapPos).2 (by simpa [mul_comm] using hscaled)

/-- **Gap/near-degeneracy dichotomy.**  At every positive threshold, either
the two eigenvalues are near-degenerate, or the transverse overlap obeys the
gap-divided perturbation estimate at that threshold. -/
theorem nearDegenerate_or_abs_overlap_le
    (A B : E →L[ℝ] E) (e f : E) (lambda mu threshold : ℝ)
    (hBsymm : ∀ (u v : E), inner ℝ u (B v) = inner ℝ (B u) v)
    (hAe : A e = lambda • e) (hBf : B f = mu • f)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hthreshold : 0 < threshold) :
    |lambda - mu| < threshold ∨
      |⟪f, e⟫| ≤ ‖A - B‖ / threshold := by
  by_cases hnear : |lambda - mu| < threshold
  · exact Or.inl hnear
  · exact Or.inr (abs_overlap_le_opNorm_div_gap A B e f lambda mu threshold
      hBsymm hAe hBf he hf (le_of_not_gt hnear) hthreshold)

/-- **Square-root-balanced gap dichotomy.**  If the strain operators differ by
at most `epsilon`, choosing the gap threshold `sqrt epsilon` makes both sides
of the alternative small at the same rate. -/
theorem nearDegenerate_or_abs_overlap_le_sqrt
    (A B : E →L[ℝ] E) (e f : E) (lambda mu epsilon : ℝ)
    (hBsymm : ∀ (u v : E), inner ℝ u (B v) = inner ℝ (B u) v)
    (hAe : A e = lambda • e) (hBf : B f = mu • f)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hepsilon : 0 < epsilon) (hAB : ‖A - B‖ ≤ epsilon) :
    |lambda - mu| < Real.sqrt epsilon ∨
      |⟪f, e⟫| ≤ Real.sqrt epsilon := by
  have hsqrt : 0 < Real.sqrt epsilon := Real.sqrt_pos.2 hepsilon
  rcases nearDegenerate_or_abs_overlap_le A B e f lambda mu
      (Real.sqrt epsilon) hBsymm hAe hBf he hf hsqrt with hnear | hfar
  · exact Or.inl hnear
  · apply Or.inr
    refine hfar.trans ?_
    calc
      ‖A - B‖ / Real.sqrt epsilon ≤
          epsilon / Real.sqrt epsilon := by
        exact div_le_div_of_nonneg_right hAB (le_of_lt hsqrt)
      _ = Real.sqrt epsilon := by
        apply (div_eq_iff hsqrt.ne').2
        nlinarith [Real.sq_sqrt (le_of_lt hepsilon)]

/-! ## From cross-eigenvector overlaps to the matched eigenline -/

/-- Choose the sign of `f` whose inner product with `e` is nonnegative.  The
line projector is insensitive to this choice. -/
def alignedRepresentative (e f : E) : E :=
  if 0 ≤ inner ℝ e f then f else -f

theorem norm_alignedRepresentative (e f : E) :
    ‖alignedRepresentative e f‖ = ‖f‖ := by
  unfold alignedRepresentative
  split_ifs <;> simp

theorem inner_alignedRepresentative (e f : E) :
    inner ℝ e (alignedRepresentative e f) = |inner ℝ e f| := by
  unfold alignedRepresentative
  by_cases h : 0 ≤ inner ℝ e f
  · simp [h, abs_of_nonneg h]
  · have hneg : inner ℝ e f < 0 := lt_of_not_ge h
    simp [h, abs_of_neg hneg]

theorem lineProjector_alignedRepresentative (e f : E) :
    lineProjector (alignedRepresentative e f) = lineProjector f := by
  unfold alignedRepresentative
  by_cases h : 0 ≤ inner ℝ e f
  · simp [h]
  · rw [if_neg h]
    ext v
    simp [lineProjector, InnerProductSpace.rankOne_apply]

/-- If the squared mass of a unit vector transverse to a unit line is at most
`2 r²`, then their rank-one line projectors differ by at most `4r`.  The sign
of the representative line is chosen internally. -/
theorem norm_lineProjector_sub_le_of_transverseEnergy
    (e f : E) (r : ℝ)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hr : 0 ≤ r)
    (htransverse : 1 - (inner ℝ e f) ^ 2 ≤ 2 * r ^ 2) :
    ‖lineProjector e - lineProjector f‖ ≤ 4 * r := by
  let f' := alignedRepresentative e f
  have hf' : ‖f'‖ = 1 := by
    rw [show f' = alignedRepresentative e f from rfl,
      norm_alignedRepresentative, hf]
  have hinner : inner ℝ e f' = |inner ℝ e f| := by
    exact inner_alignedRepresentative e f
  have habs : |inner ℝ e f| ≤ 1 := by
    calc
      |inner ℝ e f| ≤ ‖e‖ * ‖f‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [he, hf, one_mul]
  have hfactor :
      1 - |inner ℝ e f| ≤ 1 - (inner ℝ e f) ^ 2 := by
    have habsnonneg : 0 ≤ |inner ℝ e f| := abs_nonneg _
    have hsquare : |inner ℝ e f| ^ 2 = (inner ℝ e f) ^ 2 := sq_abs _
    nlinarith
  have hdistSq : ‖e - f'‖ ^ 2 = 2 * (1 - |inner ℝ e f|) := by
    rw [norm_sub_sq_real, he, hf', hinner]
    ring
  have hdistSqLe : ‖e - f'‖ ^ 2 ≤ (2 * r) ^ 2 := by
    rw [hdistSq]
    nlinarith
  have hdist : ‖e - f'‖ ≤ 2 * r := by
    have hnorm : 0 ≤ ‖e - f'‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖e - f'‖ + 2 * r)]
  calc
    ‖lineProjector e - lineProjector f‖ =
        ‖lineProjector e - lineProjector f'‖ := by
      rw [lineProjector_alignedRepresentative e f]
    _ ≤ 2 * ‖e - f'‖ :=
      norm_lineProjector_sub_le e f' he hf'
    _ ≤ 4 * r := by nlinarith

/-- A three-dimensional matched-eigenline perturbation theorem.  The two
cross-eigenvector estimates are combined through the displayed Parseval
identity for the eigenbasis of `B`. -/
theorem norm_matchedEigenline_sub_le
    (A B : E →L[ℝ] E) (e f₀ f₁ f₂ : E)
    (lambda mu₁ mu₂ epsilon gap : ℝ)
    (hBsymm : ∀ (u v : E), inner ℝ u (B v) = inner ℝ (B u) v)
    (hAe : A e = lambda • e)
    (hBf₁ : B f₁ = mu₁ • f₁) (hBf₂ : B f₂ = mu₂ • f₂)
    (he : ‖e‖ = 1) (hf₀ : ‖f₀‖ = 1)
    (hf₁ : ‖f₁‖ = 1) (hf₂ : ‖f₂‖ = 1)
    (hparseval : (inner ℝ e f₀) ^ 2 + (inner ℝ e f₁) ^ 2 +
      (inner ℝ e f₂) ^ 2 = 1)
    (hgap₁ : gap ≤ |lambda - mu₁|)
    (hgap₂ : gap ≤ |lambda - mu₂|)
    (hgapPos : 0 < gap) (hepsilon : 0 ≤ epsilon)
    (hAB : ‖A - B‖ ≤ epsilon) :
    ‖lineProjector e - lineProjector f₀‖ ≤ 4 * (epsilon / gap) := by
  have hcross₁ := abs_overlap_le_opNorm_div_gap
    A B e f₁ lambda mu₁ gap hBsymm hAe hBf₁ he hf₁ hgap₁ hgapPos
  have hcross₂ := abs_overlap_le_opNorm_div_gap
    A B e f₂ lambda mu₂ gap hBsymm hAe hBf₂ he hf₂ hgap₂ hgapPos
  have hεgap : 0 ≤ epsilon / gap := div_nonneg hepsilon hgapPos.le
  have hcross₁' : |inner ℝ e f₁| ≤ epsilon / gap := by
    rw [real_inner_comm]
    exact hcross₁.trans (div_le_div_of_nonneg_right hAB hgapPos.le)
  have hcross₂' : |inner ℝ e f₂| ≤ epsilon / gap := by
    rw [real_inner_comm]
    exact hcross₂.trans (div_le_div_of_nonneg_right hAB hgapPos.le)
  apply norm_lineProjector_sub_le_of_transverseEnergy e f₀
    (epsilon / gap) he hf₀ hεgap
  have hsq₁ : (inner ℝ e f₁) ^ 2 ≤ (epsilon / gap) ^ 2 := by
    calc
      (inner ℝ e f₁) ^ 2 = |inner ℝ e f₁| ^ 2 := (sq_abs _).symm
      _ ≤ (epsilon / gap) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hcross₁' 2
  have hsq₂ : (inner ℝ e f₂) ^ 2 ≤ (epsilon / gap) ^ 2 := by
    calc
      (inner ℝ e f₂) ^ 2 = |inner ℝ e f₂| ^ 2 := (sq_abs _).symm
      _ ≤ (epsilon / gap) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hcross₂' 2
  nlinarith [hparseval]

/-- Gap/near-degeneracy alternative for the matched eigenline in a
three-dimensional eigenbasis. -/
theorem nearDegenerate_or_norm_matchedEigenline_sub_le
    (A B : E →L[ℝ] E) (e f₀ f₁ f₂ : E)
    (lambda mu₁ mu₂ epsilon threshold : ℝ)
    (hBsymm : ∀ (u v : E), inner ℝ u (B v) = inner ℝ (B u) v)
    (hAe : A e = lambda • e)
    (hBf₁ : B f₁ = mu₁ • f₁) (hBf₂ : B f₂ = mu₂ • f₂)
    (he : ‖e‖ = 1) (hf₀ : ‖f₀‖ = 1)
    (hf₁ : ‖f₁‖ = 1) (hf₂ : ‖f₂‖ = 1)
    (hparseval : (inner ℝ e f₀) ^ 2 + (inner ℝ e f₁) ^ 2 +
      (inner ℝ e f₂) ^ 2 = 1)
    (hthreshold : 0 < threshold) (hepsilon : 0 ≤ epsilon)
    (hAB : ‖A - B‖ ≤ epsilon) :
    |lambda - mu₁| < threshold ∨
      |lambda - mu₂| < threshold ∨
        ‖lineProjector e - lineProjector f₀‖ ≤
          4 * (epsilon / threshold) := by
  by_cases hnear₁ : |lambda - mu₁| < threshold
  · exact Or.inl hnear₁
  by_cases hnear₂ : |lambda - mu₂| < threshold
  · exact Or.inr (Or.inl hnear₂)
  · exact Or.inr (Or.inr (norm_matchedEigenline_sub_le
      A B e f₀ f₁ f₂ lambda mu₁ mu₂ epsilon threshold
        hBsymm hAe hBf₁ hBf₂ he hf₀ hf₁ hf₂ hparseval
        (le_of_not_gt hnear₁) (le_of_not_gt hnear₂)
        hthreshold hepsilon hAB))

/-- Square-root-balanced matched-eigenline alternative.  Away from either
near-collision band, the line projector varies by at most
`4 * sqrt epsilon`. -/
theorem nearDegenerate_or_norm_matchedEigenline_sub_le_sqrt
    (A B : E →L[ℝ] E) (e f₀ f₁ f₂ : E)
    (lambda mu₁ mu₂ epsilon : ℝ)
    (hBsymm : ∀ (u v : E), inner ℝ u (B v) = inner ℝ (B u) v)
    (hAe : A e = lambda • e)
    (hBf₁ : B f₁ = mu₁ • f₁) (hBf₂ : B f₂ = mu₂ • f₂)
    (he : ‖e‖ = 1) (hf₀ : ‖f₀‖ = 1)
    (hf₁ : ‖f₁‖ = 1) (hf₂ : ‖f₂‖ = 1)
    (hparseval : (inner ℝ e f₀) ^ 2 + (inner ℝ e f₁) ^ 2 +
      (inner ℝ e f₂) ^ 2 = 1)
    (hepsilon : 0 < epsilon) (hAB : ‖A - B‖ ≤ epsilon) :
    |lambda - mu₁| < Real.sqrt epsilon ∨
      |lambda - mu₂| < Real.sqrt epsilon ∨
        ‖lineProjector e - lineProjector f₀‖ ≤
          4 * Real.sqrt epsilon := by
  have hsqrt : 0 < Real.sqrt epsilon := Real.sqrt_pos.2 hepsilon
  rcases nearDegenerate_or_norm_matchedEigenline_sub_le
      A B e f₀ f₁ f₂ lambda mu₁ mu₂ epsilon (Real.sqrt epsilon)
      hBsymm hAe hBf₁ hBf₂ he hf₀ hf₁ hf₂ hparseval hsqrt
      hepsilon.le hAB with hnear₁ | hnear₂ | hfar
  · exact Or.inl hnear₁
  · exact Or.inr (Or.inl hnear₂)
  · apply Or.inr (Or.inr ?_)
    refine hfar.trans ?_
    have hsqrtEq : epsilon / Real.sqrt epsilon = Real.sqrt epsilon := by
      apply (div_eq_iff hsqrt.ne').2
      nlinarith [Real.sq_sqrt hepsilon.le]
    rw [hsqrtEq]

end PancakeEigenframePerturbation
end NavierStokes
end FluidDynamics
end Mettapedia
