import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorFamilyPairing
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Checked finite F2 kernel certificates

This module gives the finite certificate shape consumed by the CAP5/F2 route gate.  A
certificate provides an explicit finite left-inverse matrix for a linear map after choosing a
finite basis of the domain.  The check is the finite product equation saying that the matrix
product is the identity on basis vectors; Lean then reconstructs a left inverse and proves the
kernel is trivial.
-/

namespace Mettapedia.GraphTheory.FourColor

open scoped BigOperators

variable {X ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [AddCommGroup X] [Module F2 X]

/--
A checked finite F2 left-inverse/kernel certificate for `f`.

The rows are indexed by a chosen basis `B : Module.Basis ι F2 X`, the columns by the finite
output coordinate type `κ`, and `product_eq` is the finite matrix-product check.  In the CAP5
route this is the Lean landing point for emitted RREF/kernel data.
-/
structure F2LeftInverseKernelCertificate
    (B : Module.Basis ι F2 X) (f : X →ₗ[F2] (κ → F2)) where
  coeff : ι → κ → F2
  product_eq :
    ∀ i j : ι, (∑ k : κ, coeff i k * f (B j) k) = if i = j then 1 else 0

namespace F2LeftInverseKernelCertificate

/-- The coordinate map represented by the finite certificate matrix. -/
noncomputable def coordinateMap {B : Module.Basis ι F2 X} {f : X →ₗ[F2] (κ → F2)}
    (cert : F2LeftInverseKernelCertificate B f) : (κ → F2) →ₗ[F2] (ι → F2) where
  toFun y := fun i => ∑ k : κ, cert.coeff i k * y k
  map_add' := by
    intro y z
    funext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a y
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ac_rfl

/-- The left inverse reconstructed from a checked finite certificate. -/
noncomputable def leftInverse {B : Module.Basis ι F2 X} {f : X →ₗ[F2] (κ → F2)}
    (cert : F2LeftInverseKernelCertificate B f) : (κ → F2) →ₗ[F2] X :=
  (B.equivFun.symm : (ι → F2) →ₗ[F2] X).comp cert.coordinateMap

theorem leftInverse_apply_basis {B : Module.Basis ι F2 X} {f : X →ₗ[F2] (κ → F2)}
    (cert : F2LeftInverseKernelCertificate B f) (j : ι) :
    cert.leftInverse (f (B j)) = B j := by
  apply (B.equivFun : X ≃ₗ[F2] (ι → F2)).injective
  funext i
  simp [leftInverse, coordinateMap, cert.product_eq]

theorem leftInverse_comp {B : Module.Basis ι F2 X} {f : X →ₗ[F2] (κ → F2)}
    (cert : F2LeftInverseKernelCertificate B f) :
    cert.leftInverse.comp f = (LinearMap.id : X →ₗ[F2] X) := by
  exact B.ext (fun j => by
    exact cert.leftInverse_apply_basis j)

/-- A checked finite left-inverse certificate proves the kernel of `f` is trivial. -/
theorem ker_eq_bot {B : Module.Basis ι F2 X} {f : X →ₗ[F2] (κ → F2)}
    (cert : F2LeftInverseKernelCertificate B f) :
    LinearMap.ker f = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hcomp := congrArg (fun g : X →ₗ[F2] X => g x) cert.leftInverse_comp
  have hfx : f x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hleftZero : cert.leftInverse (f x) = 0 := by
    rw [hfx]
    simp
  simpa [LinearMap.comp_apply, hleftZero] using hcomp.symm

end F2LeftInverseKernelCertificate

end Mettapedia.GraphTheory.FourColor
