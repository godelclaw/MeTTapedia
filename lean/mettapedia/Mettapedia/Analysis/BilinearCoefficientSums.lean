import Mettapedia.Analysis.EuclideanBilinearCoordinates
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Convergent coordinate series reconstruct a convergent series of bilinear operators. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.EuclideanBilinearCoordinates

variable {𝕜 I J K ι : Type*} [RCLike 𝕜]
variable [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K]

local notation "U" => EuclideanSpace 𝕜 I
local notation "V" => EuclideanSpace 𝕜 J
local notation "W" => EuclideanSpace 𝕜 K
local notation "Op" => U →L[𝕜] V →L[𝕜] W

local instance : NormedAddCommGroup (V →L[𝕜] W) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace 𝕜 (V →L[𝕜] W) := ContinuousLinearMap.toNormedSpace
local instance : NormedSpace 𝕜 Op := ContinuousLinearMap.toNormedSpace

omit [DecidableEq I] [DecidableEq J] in
theorem hasSum_reconstruct (f : ι → K → I → J → 𝕜) (b : K → I → J → 𝕜)
    (h : ∀ i j l, HasSum (fun n ↦ f n i j l) (b i j l)) :
    HasSum (fun n ↦ reconstruct (f n)) (reconstruct b) := by
  unfold reconstruct
  exact hasSum_sum (fun i _ ↦ hasSum_sum (fun j _ ↦ hasSum_sum (fun l _ ↦
    (h i j l).smul_const (elementary i j l))))

end Mettapedia.Analysis.EuclideanBilinearCoordinates
