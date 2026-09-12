import Mettapedia.Analysis.RadialRieszRegularization

/-!
# The radial regularized Riesz kernel is a potential Hessian

Each entry is the inverse Fourier transform of the constructed compact
Riesz symbol. Two ordinary directional derivatives of the radial Schwartz
potential recover that entry, with the Fourier normalization explicit.
This connects radiality of a constructed scalar potential to the actual
matrix kernel, rather than assuming a radial tensor decomposition.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialRieszRegularization

open SchwartzMap LineDeriv
open scoped SchwartzMap FourierTransform ContDiff RealInnerProductSpace

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

def symbol (N : ℕ) (i j : Fin d) : 𝓢(Rd, ℂ) :=
  smulLeftCLM ℂ (fun x : Rd ↦ x i * x j) (potentialSymbol N)

theorem symbol_apply (N : ℕ) (i j : Fin d) (x : Rd) :
    symbol N i j x = (entry N i j x : ℂ) := by
  have ht : (fun x : Rd ↦ x i * x j).HasTemperateGrowth :=
    (EuclideanSpace.proj i).hasTemperateGrowth.mul (EuclideanSpace.proj j).hasTemperateGrowth
  simp only [symbol, smulLeftCLM_apply_apply ht]
  change (x i * x j) • (potentialEntry N x : ℂ) = (entry N i j x : ℂ)
  simp only [entry, Complex.real_smul, Complex.ofReal_mul]

def kernel (N : ℕ) (i j : Fin d) : 𝓢(Rd, ℂ) := 𝓕⁻ (symbol N i j)

theorem fourier_kernel (N : ℕ) (i j : Fin d) : 𝓕 (kernel N i j) = symbol N i j :=
  FourierTransform.fourier_fourierInv_eq _

theorem fourier_kernel_apply (N : ℕ) (i j : Fin d) (x : Rd) :
    (𝓕 (kernel N i j)) x =
      ((weight N x * AnnularRieszKernel.rieszEntry i j x : ℝ) : ℂ) := by
  rw [fourier_kernel, symbol_apply, entry_eq_weight_mul]

theorem lineDerivOp_lineDerivOp_potential (N : ℕ) (i j : Fin d) :
    ∂_{EuclideanSpace.single i (1 : ℝ)}
      (∂_{EuclideanSpace.single j (1 : ℝ)} (potential (d := d) N) : 𝓢(Rd, ℂ)) =
      (-(2 * Real.pi) ^ 2 : ℂ) • kernel N i j := by
  have hi : (fun x : Rd ↦ ⟪x, EuclideanSpace.single i (1 : ℝ)⟫).HasTemperateGrowth := by fun_prop
  have hj : (fun x : Rd ↦ ⟪x, EuclideanSpace.single j (1 : ℝ)⟫).HasTemperateGrowth := by fun_prop
  have he : (2 * Real.pi * Complex.I) •
      smulLeftCLM ℂ (fun x : Rd ↦ ⟪x, EuclideanSpace.single i (1 : ℝ)⟫)
        ((2 * Real.pi * Complex.I) •
          smulLeftCLM ℂ (fun x : Rd ↦ ⟪x, EuclideanSpace.single j (1 : ℝ)⟫) (potentialSymbol N)) =
      (-(2 * Real.pi) ^ 2 : ℂ) • symbol N i j := by
    ext x
    simp only [smul_apply]
    rw [smulLeftCLM_apply_apply hi]
    simp only [smul_apply]
    rw [smulLeftCLM_apply_apply hj, symbol_apply]
    simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul, entry,
      Complex.real_smul, Complex.ofReal_mul, smul_eq_mul]
    change (2 * ↑Real.pi * Complex.I) * (↑(x i) *
      ((2 * ↑Real.pi * Complex.I) * (↑(x j) * ↑(potentialEntry N x)))) = _
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [potential, lineDerivOp_fourierInv_eq, lineDerivOp_fourierInv_eq, he,
    FourierTransform.fourierInv_smul, kernel]

end Mettapedia.Analysis.RadialRieszRegularization
