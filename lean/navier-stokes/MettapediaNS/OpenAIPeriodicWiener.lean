import NavierStokes.PeriodicPaperTheorem
import MettapediaNS.ForcedCandidateVorticity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierCascadeContraction

/-!
# The periodic forced breakdown has an unbounded velocity Wiener norm

The velocity Wiener norm `V(a) = ∑_k ‖a_k‖` of the Fourier coefficients of a
smooth one-periodic velocity dominates its supremum, since the Fourier series
converges absolutely and each character has modulus one.

Every periodic candidate of OpenAI's periodic corollary has unbounded speed
arbitrarily close to time one. Its time slices before time one are smooth and
one-periodic, so the velocity Wiener norm of their coefficients is unbounded
before time one as well.

For the unforced problem, a bound on this norm along every tame solution
gives the official periodic statement
(`FourierCascadeContraction.periodicStatementB_of_velocityWienerBound`). The
forced solutions of the periodic corollary, whose force is smooth, violate
the corresponding bound. A derivation of the bound that remains valid in the
presence of a smooth force is therefore impossible: it must use the absence
of forcing. The imported construction is used as proved; nothing in it is
reimplemented.
-/

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.OpenAIPeriodicWiener

open Set
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator
open FourierSpatialCalculus FourierInitialData FourierShellFeeding FourierPhysicalFields
open scoped ContDiff

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The Euclidean norms of rapid coefficients are summable. -/
theorem summable_norm_coefficientVec {a : FourierVelocity} (ha : Rapid a) :
    Summable (fun k ↦ ‖coefficientVec (a k)‖) :=
  (ha.summable_norm.mul_left 3).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    fun k ↦ FourierRelaxation.norm_coefficientVec_le_three (a k)

/-- **The velocity Wiener norm dominates the real field.** -/
theorem norm_realField_le_velocityWiener {a : FourierVelocity} (ha : Rapid a) (x : ℝ³) :
    ‖realField a x‖ ≤ velocityWiener a := by
  have hs : Summable (fun k ↦ coefficientVec (character k x • a k)) :=
    (summable_norm_coefficientVec ha).of_norm_bounded fun k ↦ by
      rw [FourierVorticitySource.norm_cv_smul, FourierPhysicalFields.norm_character, one_mul]
  have hn : Summable (fun k ↦ ‖coefficientVec (character k x • a k)‖) :=
    (summable_norm_coefficientVec ha).congr fun k ↦ by
      rw [FourierVorticitySource.norm_cv_smul, FourierPhysicalFields.norm_character, one_mul]
  have e : coefficientVec (field a x) = ∑' k, coefficientVec (character k x • a k) :=
    (EuclideanSpace.equiv (Fin 3) ℂ).symm.map_tsum
  unfold realField
  rw [PancakeDyadicDirectionEvolution.complexRealPartEuclideanCLM_apply]
  refine (PancakeExteriorReconstructionTail.norm_realPart_le_coefficientVec _).trans ?_
  rw [e]
  refine (norm_tsum_le_tsum_norm hn).trans (le_of_eq ?_)
  unfold velocityWiener
  refine tsum_congr fun k ↦ ?_
  rw [FourierVorticitySource.norm_cv_smul, FourierPhysicalFields.norm_character, one_mul]

open NavierStokes.ProblemStatement NavierStokes.PeriodicPaper

/-- Along every periodic candidate, the velocity Wiener norm of the time
slices is unbounded arbitrarily close to time one. -/
theorem candidate_velocityWiener_unbounded {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties ν u p f K) (M δ : ℝ)
    (hδ : 0 < δ) :
    ∃ t ∈ Ioo (0 : ℝ) 1, 1 - δ < t ∧ M < velocityWiener (coeffVec (fun y ↦ u (t, y))) := by
  obtain ⟨t, x, ht, htδ, hlt⟩ := h.speed_unbounded (max M 0 + 1) (by positivity) δ hδ
  have hs : ContDiff ℝ ∞ (fun y : Space ↦ u (t, y)) :=
    ForcedCandidateVorticity.slice_contDiff h.velocity_smooth ht
  have hp : OfficialPeriodicProblem.IsOnePeriodic (fun y : Space ↦ u (t, y)) :=
    fun y i ↦ h.velocity_periodic t (Ioo_subset_Ico_self ht) y i
  have hx : u (t, x) = realField (coeffVec (fun y ↦ u (t, y))) x :=
    (realField_coeffVec hs hp x).symm
  have hle := norm_realField_le_velocityWiener (rapid_coeffVec hs hp) x
  rw [← hx] at hle
  exact ⟨t, ht, htδ, by linarith [le_max_left M 0]⟩

/-- **The periodic forced breakdown violates the velocity-Wiener bound.** For
every positive viscosity, OpenAI's periodic candidate has no global smooth
periodic competitor, and the velocity Wiener norm of its time slices is
unbounded before time one. -/
theorem openAI_periodic_velocityWiener_unbounded (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧ ¬ Nonempty (GlobalSmoothSolution ν f) ∧
      ∀ M δ : ℝ, 0 < δ →
        ∃ t ∈ Ioo (0 : ℝ) 1, 1 - δ < t ∧ M < velocityWiener (coeffVec (fun y ↦ u (t, y))) := by
  obtain ⟨u, p, f, K, hc, hg⟩ := periodic_corollary ν hν
  exact ⟨u, p, f, K, hc, hg, fun M δ hδ ↦ candidate_velocityWiener_unbounded hc M δ hδ⟩

end Mettapedia.FluidDynamics.NavierStokes.OpenAIPeriodicWiener
