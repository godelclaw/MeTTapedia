import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltSymbol

/-!
# Elliptic product identity for the pressure-tilt commutator

Factoring the pressure potential rather than its Laplacian exposes one
cutoff derivative in each mixed term and two in the remaining terms.
The identity includes zero input and output frequencies. No spectral
support or angular hypothesis is used.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTiltEllipticIdentity

open scoped RealInnerProductSpace
open PancakeAnisotropyDepletion PressureTiltSymbol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sq_smul_tiltSymbol_sub (e p k : E) :
    ‖k‖ ^ 2 • (tiltSymbol e k - tiltSymbol e (p + k)) =
      (2 * ⟪p, k⟫ + ‖p‖ ^ 2) • tiltSymbol e (p + k) -
        (⟪k, e⟫ • lineRemainder e p + ⟪p, e⟫ • lineRemainder e k +
          ⟪p, e⟫ • lineRemainder e p) := by
  have hq := norm_sq_smul_tiltSymbol e (p + k)
  have hnorm : ‖p + k‖ ^ 2 = ‖p‖ ^ 2 + 2 * ⟪p, k⟫ + ‖k‖ ^ 2 := by
    rw [norm_add_sq_real]
  have hrem : lineRemainder e (p + k) = lineRemainder e p + lineRemainder e k := by
    simp only [lineRemainder, inner_add_right, add_smul]
    module
  rw [hnorm, inner_add_left, hrem] at hq
  rw [smul_sub, norm_sq_smul_tiltSymbol]
  have hm : (2 * ⟪p, k⟫ + ‖p‖ ^ 2) • tiltSymbol e (p + k) =
      (⟪p, e⟫ + ⟪k, e⟫) • (lineRemainder e p + lineRemainder e k) -
        ‖k‖ ^ 2 • tiltSymbol e (p + k) := by
    calc
      _ = (‖p‖ ^ 2 + 2 * ⟪p, k⟫ + ‖k‖ ^ 2) • tiltSymbol e (p + k) -
          ‖k‖ ^ 2 • tiltSymbol e (p + k) := by module
      _ = _ := by rw [hq]
  rw [hm]
  module

end Mettapedia.FluidDynamics.NavierStokes.PressureTiltEllipticIdentity
