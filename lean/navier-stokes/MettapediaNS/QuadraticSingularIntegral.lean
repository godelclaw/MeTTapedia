import EulerBlowup.Lit.CZ.CZCore.Homogeneous

/-!
# Quadratic cancellation kernels and upstream singular-integral bounds

The off-diagonal products and differences of coordinate squares generate
the trace-free quadratic angular factors of the three-dimensional strain
kernel. Only their angular hypotheses are established here. The singular-
integral estimates themselves are imported from Alpöge–Buckmaster.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace Mettapedia.Analysis.QuadraticSingularIntegral

open NS.Lit.CZ

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Smooth angular factors satisfy the two sphere bounds by compactness. -/
theorem exists_angularPart_of_contDiff {Ω : Space → ℂ}
    (hΩ : ContDiff ℝ ∞ Ω)
    (hzero : ∫ z in {z : Space | 1 < ‖z‖ ∧ ‖z‖ < 2}, homKer Ω z = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ AngularPart L Ω := by
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : Space) 1).exists_bound_of_continuousOn
    hΩ.continuous.continuousOn
  obtain ⟨D, hD⟩ := (isCompact_sphere (0 : Space) 1).exists_bound_of_continuousOn
    (hΩ.continuous_fderiv (by simp)).continuousOn
  refine ⟨max 0 (max B D), le_max_left _ _, ?_⟩
  refine ⟨(hΩ.of_le (by simp)).contDiffOn, ?_, ?_, hzero⟩
  · intro z hz
    exact (hB z (by simpa using hz)).trans ((le_max_left B D).trans (le_max_right _ _))
  · intro z hz
    exact (hD z (by simpa using hz)).trans ((le_max_right B D).trans (le_max_right _ _))

/-- Orthogonal antisymmetry cancels a homogeneous kernel against any radial
weight on any radial set. The change of variables needs no integrability. -/
theorem integral_radial_mul_homKer_eq_zero_of_isometry {Ω : Space → ℂ}
    (e : Space ≃ₗᵢ[ℝ] Space) (hΩ : ∀ z, Ω (e z) = -Ω z)
    (a : ℝ → ℂ) (s : Set ℝ) :
    ∫ z in {z : Space | ‖z‖ ∈ s}, a ‖z‖ * homKer Ω z = 0 := by
  have hkernel (z : Space) : homKer Ω (e z) = -homKer Ω z := by
    by_cases hz : z = 0
    · simp [hz, homKer]
    · rw [homKer_smul_aux Ω (by simpa using hz), homKer_smul_aux Ω hz,
        e.norm_map, ← e.map_smul, hΩ, neg_mul]
  have hpre : e ⁻¹' {z : Space | ‖z‖ ∈ s} =
      {z : Space | ‖z‖ ∈ s} := by ext z; simp
  have h := e.measurePreserving.setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding (fun z ↦ a ‖z‖ * homKer Ω z)
    {z : Space | ‖z‖ ∈ s}
  rw [hpre] at h
  simp_rw [e.norm_map, hkernel, mul_neg, integral_neg] at h
  exact neg_eq_self.mp h

/-- The annular cancellation required by the upstream angular hypotheses. -/
theorem integral_homKer_eq_zero_of_isometry {Ω : Space → ℂ}
    (e : Space ≃ₗᵢ[ℝ] Space) (hΩ : ∀ z, Ω (e z) = -Ω z) :
    ∫ z in {z : Space | 1 < ‖z‖ ∧ ‖z‖ < 2}, homKer Ω z = 0 := by
  simpa only [Set.mem_Ioo, one_mul] using
    integral_radial_mul_homKer_eq_zero_of_isometry e hΩ (fun _ ↦ 1) (Set.Ioo 1 2)

def coordinateSquareDifference (i j : Fin 3) (z : Space) : ℂ :=
  ((z i) ^ 2 - (z j) ^ 2 : ℝ)

theorem contDiff_coordinateSquareDifference (i j : Fin 3) :
    ContDiff ℝ ∞ (coordinateSquareDifference i j) := by
  have hi : ContDiff ℝ ∞ (fun z : Space ↦ z i) := by fun_prop
  have hj : ContDiff ℝ ∞ (fun z : Space ↦ z j) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp ((hi.pow 2).sub (hj.pow 2))

theorem integral_homKer_coordinateSquareDifference (i j : Fin 3) :
    ∫ z in {z : Space | 1 < ‖z‖ ∧ ‖z‖ < 2},
      homKer (coordinateSquareDifference i j) z = 0 := by
  apply integral_homKer_eq_zero_of_isometry
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j))
  intro z
  simp [coordinateSquareDifference, Equiv.piCongrLeft', sub_eq_neg_add, add_comm]

theorem exists_angularPart_coordinateSquareDifference (i j : Fin 3) :
    ∃ L : ℝ, 0 ≤ L ∧ AngularPart L (coordinateSquareDifference i j) :=
  exists_angularPart_of_contDiff (contDiff_coordinateSquareDifference i j)
    (integral_homKer_coordinateSquareDifference i j)

def coordinateProduct (i j : Fin 3) (z : Space) : ℂ := ((z i) * (z j) : ℝ)

theorem contDiff_coordinateProduct (i j : Fin 3) :
    ContDiff ℝ ∞ (coordinateProduct i j) := by
  have hi : ContDiff ℝ ∞ (fun z : Space ↦ z i) := by fun_prop
  have hj : ContDiff ℝ ∞ (fun z : Space ↦ z j) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp (hi.mul hj)

theorem integral_homKer_coordinateProduct (i j : Fin 3) (hij : i ≠ j) :
    ∫ z in {z : Space | 1 < ‖z‖ ∧ ‖z‖ < 2},
      homKer (coordinateProduct i j) z = 0 := by
  let e : Space ≃ₗᵢ[ℝ] Space := LinearIsometryEquiv.piLpCongrRight 2
    (fun k : Fin 3 ↦ if k = i then LinearIsometryEquiv.neg ℝ else .refl ℝ ℝ)
  apply integral_homKer_eq_zero_of_isometry e
  intro z
  simp [e, coordinateProduct, hij.symm]

theorem exists_angularPart_coordinateProduct (i j : Fin 3) (hij : i ≠ j) :
    ∃ L : ℝ, 0 ≤ L ∧ AngularPart L (coordinateProduct i j) :=
  exists_angularPart_of_contDiff (contDiff_coordinateProduct i j)
    (integral_homKer_coordinateProduct i j hij)

/-- The actual homogeneous kernel, including its totalized value at the origin. -/
theorem homKer_coordinateProduct (i j : Fin 3) (z : Space) :
    homKer (coordinateProduct i j) z = (((z i) * (z j) / ‖z‖ ^ 5 : ℝ) : ℂ) := by
  by_cases hz : z = 0
  · simp [hz, homKer]
  · rw [homKer_smul_aux _ hz]
    simp only [coordinateProduct, PiLp.smul_apply, smul_eq_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp

theorem homKer_coordinateSquareDifference (i j : Fin 3) (z : Space) :
    homKer (coordinateSquareDifference i j) z =
      ((((z i) ^ 2 - (z j) ^ 2) / ‖z‖ ^ 5 : ℝ) : ℂ) := by
  by_cases hz : z = 0
  · simp [hz, homKer]
  · rw [homKer_smul_aux _ hz]
    simp only [coordinateSquareDifference, PiLp.smul_apply, smul_eq_mul,
      ← Complex.ofReal_mul]
    congr 1
    field_simp

/-- Cutoff-uniform bounds are an application of the imported theorem, not a
new Calderón–Zygmund proof. -/
theorem exists_truncated_lpBound_coordinateProduct (i j : Fin 3) (hij : i ≠ j)
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε R : ℝ, 0 < ε → ε < R →
      LpBound (ENNReal.ofReal p) C (truncate (homKer (coordinateProduct i j)) ε R) := by
  obtain ⟨L, hL, hΩ⟩ := exists_angularPart_coordinateProduct i j hij
  obtain ⟨C, hC, hbound⟩ := truncated_Lp_uniform 3 (by decide) L p hL hp
  exact ⟨C, hC, hbound _ hΩ⟩

theorem exists_truncated_lpBound_coordinateSquareDifference (i j : Fin 3)
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε R : ℝ, 0 < ε → ε < R →
      LpBound (ENNReal.ofReal p) C
        (truncate (homKer (coordinateSquareDifference i j)) ε R) := by
  obtain ⟨L, hL, hΩ⟩ := exists_angularPart_coordinateSquareDifference i j
  obtain ⟨C, hC, hbound⟩ := truncated_Lp_uniform 3 (by decide) L p hL hp
  exact ⟨C, hC, hbound _ hΩ⟩

/-- The principal-value limit is the upstream operator on actual smooth,
compactly supported inputs, with cancellation built into its near integral. -/
theorem exists_pv_eLpNorm_bound_coordinateProduct (i j : Fin 3) (hij : i ≠ j)
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Space → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      eLpNorm (pvOp (coordinateProduct i j) φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm φ (ENNReal.ofReal p) volume := by
  obtain ⟨L, hL, hΩ⟩ := exists_angularPart_coordinateProduct i j hij
  obtain ⟨C, hC, hbound⟩ := pvOp_Lp 3 (by decide) L p hL hp
  exact ⟨C, hC, hbound _ hΩ⟩

theorem exists_pv_eLpNorm_bound_coordinateSquareDifference (i j : Fin 3)
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Space → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      eLpNorm (pvOp (coordinateSquareDifference i j) φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm φ (ENNReal.ofReal p) volume := by
  obtain ⟨L, hL, hΩ⟩ := exists_angularPart_coordinateSquareDifference i j
  obtain ⟨C, hC, hbound⟩ := pvOp_Lp 3 (by decide) L p hL hp
  exact ⟨C, hC, hbound _ hΩ⟩

/-- The same bound is uniform over the admissible cutoff functions, not just
over the two truncation radii. -/
theorem exists_smoothTruncated_lpBound_coordinateProduct (i j : Fin 3) (hij : i ≠ j)
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ χ : Space → ℝ, Continuous χ →
      (∀ z, ‖z‖ ≤ 1 / 2 → χ z = 1) → (∀ z, 1 ≤ ‖z‖ → χ z = 0) →
      (∀ z, χ z ∈ Icc (0 : ℝ) 1) → ∀ ε R : ℝ, 0 < ε → ε < R →
      LpBound (ENNReal.ofReal p) C
        (smoothTruncate χ (homKer (coordinateProduct i j)) ε R) := by
  obtain ⟨L, hL, hΩ⟩ := exists_angularPart_coordinateProduct i j hij
  obtain ⟨C, hC, hbound⟩ := smoothTruncate_Lp_uniform 3 (by decide) L p hL hp
  exact ⟨C, hC, hbound _ hΩ⟩

theorem exists_smoothTruncated_lpBound_coordinateSquareDifference (i j : Fin 3)
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ χ : Space → ℝ, Continuous χ →
      (∀ z, ‖z‖ ≤ 1 / 2 → χ z = 1) → (∀ z, 1 ≤ ‖z‖ → χ z = 0) →
      (∀ z, χ z ∈ Icc (0 : ℝ) 1) → ∀ ε R : ℝ, 0 < ε → ε < R →
      LpBound (ENNReal.ofReal p) C
        (smoothTruncate χ (homKer (coordinateSquareDifference i j)) ε R) := by
  obtain ⟨L, hL, hΩ⟩ := exists_angularPart_coordinateSquareDifference i j
  obtain ⟨C, hC, hbound⟩ := smoothTruncate_Lp_uniform 3 (by decide) L p hL hp
  exact ⟨C, hC, hbound _ hΩ⟩

end Mettapedia.Analysis.QuadraticSingularIntegral
