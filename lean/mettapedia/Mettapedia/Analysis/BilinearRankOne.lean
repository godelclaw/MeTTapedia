import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Rank-one continuous bilinear maps and their exact norm -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearRankOne

variable {𝕜 U V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup U] [NormedSpace 𝕜 U]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

def rankOne (f : U →L[𝕜] 𝕜) (g : V →L[𝕜] 𝕜) (w : W) : U →L[𝕜] V →L[𝕜] W :=
  f.smulRight (g.smulRight w)

@[simp] theorem rankOne_apply (f : U →L[𝕜] 𝕜) (g : V →L[𝕜] 𝕜) (w : W) (u : U) (v : V) :
    rankOne f g w u v = (f u * g v) • w := by
  simp [rankOne, smul_smul]

@[simp] theorem norm_rankOne (f : U →L[𝕜] 𝕜) (g : V →L[𝕜] 𝕜) (w : W) :
    ‖rankOne f g w‖ = ‖f‖ * ‖g‖ * ‖w‖ := by
  simp [rankOne, mul_assoc]

end Mettapedia.Analysis.BilinearRankOne
