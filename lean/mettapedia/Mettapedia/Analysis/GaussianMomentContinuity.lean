import Mettapedia.Analysis.GaussianAmplitudeOverlap

/-! Continuity of finite Gaussian distance moments, including two-point costs. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.GaussianPartitionEnergy

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [NormedAddCommGroup E]

@[fun_prop] theorem continuous_distanceMoment (center : ι → E) (tau : ℝ) :
    Continuous (distanceMoment center tau) := by
  have he : distanceMoment center tau = fun x ↦
      ∑ i, gaussianAmplitude center tau x i ^ 2 * ‖x - center i‖ ^ 2 := by
    funext x
    exact (sum_sq_mul_distance_eq center tau x).symm
  rw [he]
  exact continuous_finsetSum _ (fun i _ ↦ ((continuous_gaussianAmplitude center tau i).pow 2).mul
    ((continuous_id.sub continuous_const).norm.pow 2))

variable [InnerProductSpace ℝ E]

@[fun_prop] theorem continuous_twoPointDistanceMoment (center : ι → E) (tau : ℝ) :
    Continuous (fun p : E × E ↦ twoPointDistanceMoment center tau p.1 p.2) := by
  have hmid : Continuous (fun p : E × E ↦ (1 / 2 : ℝ) • (p.1 + p.2)) := by fun_prop
  exact ((continuous_distanceMoment center tau).comp continuous_fst).add
    (continuous_const.mul ((continuous_distanceMoment center tau).comp hmid)) |>.add
      (continuous_const.mul ((continuous_fst.sub hmid).norm.pow 2))

end Mettapedia.Analysis.GaussianPartitionEnergy
