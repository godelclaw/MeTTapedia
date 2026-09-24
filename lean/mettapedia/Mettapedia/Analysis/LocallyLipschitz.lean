import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Uniform

/-! # Finite constructions of locally Lipschitz maps -/

set_option autoImplicit false

namespace LocallyLipschitz

variable {X : Type*} [PseudoMetricSpace X]

theorem finsetSum {ι E : Type*} [SeminormedAddCommGroup E]
    (s : Finset ι) (f : ι → X → E) (hf : ∀ i ∈ s, LocallyLipschitz (f i)) :
    LocallyLipschitz (fun x ↦ ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using LocallyLipschitz.const (0 : E)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

/-- Finitely many local Lipschitz neighborhoods admit a common refinement. -/
theorem pi {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, PseudoMetricSpace (E i)]
    (f : X → ∀ i, E i) (hf : ∀ i, LocallyLipschitz (fun x ↦ f x i)) :
    LocallyLipschitz f := by
  classical
  intro x
  choose C s hs hC using fun i ↦ hf i x
  refine ⟨∑ i, C i, ⋂ i, s i, Filter.iInter_mem.mpr hs, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  exact ((hC i).dist_le_mul y (Set.mem_iInter.mp hy i) z (Set.mem_iInter.mp hz i)).trans
    (mul_le_mul_of_nonneg_right (by
      exact_mod_cast Finset.single_le_sum (fun j _ ↦ (zero_le : 0 ≤ C j)) (Finset.mem_univ i)) dist_nonneg)

theorem mul_algebra {E : Type*} [NormedRing E] [NormedAlgebra ℝ E]
    {f g : X → E} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x ↦ f x * g x) := by
  have hm : ContDiff ℝ 1 (fun z : E × E ↦ z.1 * z.2) := contDiff_fst.mul contDiff_snd
  exact hm.locallyLipschitz.comp (hf.prodMk hg)

theorem smul_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → ℝ} {g : X → E} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x ↦ f x • g x) := by
  have hm : ContDiff ℝ 1 (fun z : ℝ × E ↦ z.1 • z.2) := contDiff_fst.smul contDiff_snd
  exact hm.locallyLipschitz.comp (hf.prodMk hg)

end LocallyLipschitz
