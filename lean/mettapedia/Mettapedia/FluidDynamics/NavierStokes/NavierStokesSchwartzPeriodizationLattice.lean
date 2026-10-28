import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationBoxes
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Submodule

/-!
# Navier-Stokes: Schwartz Periodization Lattice

Semantic layer split from `NavierStokesSchwartzPeriodizationConvergence`.
-/


set_option autoImplicit false

noncomputable section

open Filter

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped BigOperators

/-- The standard integer lattice `ℤ^3 ⊂ ℝ^3` inside the fixed concrete space. -/
abbrev NSCoordinateLattice : Submodule ℤ NSSpace :=
  Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis))

/-- The standard Euclidean basis, restricted from `ℝ`-coefficients to the
integer lattice it spans, gives a concrete `ℤ`-basis of `ℤ^3 ⊂ ℝ^3`. -/
noncomputable abbrev nsCoordinateLatticeBasis : Module.Basis (Fin 3) ℤ NSCoordinateLattice :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.restrictScalars ℤ

/-- Coordinate-lattice points are equivalent to the raw index type `Fin 3 → ℤ`
used by the periodization boxes. -/
noncomputable abbrev nsCoordinateLatticeEquiv :
    NSCoordinateLattice ≃ₗ[ℤ] NSLatticeIndex :=
  (nsCoordinateLatticeBasis.repr).trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin 3))

/-- The raw lattice-index type `ℤ^3` viewed as the concrete coordinate lattice
subtype. -/
noncomputable abbrev nsCoordinateLatticePointEquiv : NSLatticeIndex ≃ NSCoordinateLattice :=
  (nsCoordinateLatticeEquiv : NSCoordinateLattice ≃ₗ[ℤ] NSLatticeIndex).toEquiv.symm

instance : DiscreteTopology NSCoordinateLattice := by
  refine DiscreteTopology.of_continuous_injective
    (f := (nsCoordinateLatticeEquiv : NSCoordinateLattice → NSLatticeIndex))
    continuous_of_discreteTopology nsCoordinateLatticeEquiv.injective

/-- The concrete lattice point associated to an index `n : ℤ^3`. -/
noncomputable def nsCoordinateLatticePoint (n : NSLatticeIndex) : NSCoordinateLattice :=
  nsCoordinateLatticePointEquiv n

/-- The concrete lattice point corresponding to `n` has the expected real
coordinates. -/
theorem nsCoordinateLatticePoint_coe_apply
    (n : NSLatticeIndex) (i : Fin 3) :
    ((nsCoordinateLatticePoint n : NSCoordinateLattice) : NSSpace) i = (n i : ℝ) := by
  have hrepr :
      nsCoordinateLatticeBasis.repr (nsCoordinateLatticePoint n) i = n i := by
    have hpoint : nsCoordinateLatticeEquiv (nsCoordinateLatticePoint n) = n := by
      simp [nsCoordinateLatticePoint]
    simpa [nsCoordinateLatticeEquiv] using congrFun hpoint i
  have hcast :
      ((nsCoordinateLatticeBasis.repr (nsCoordinateLatticePoint n) i : ℤ) : ℝ) =
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr
          (((nsCoordinateLatticePoint n : NSCoordinateLattice) : NSSpace)) i) := by
    exact
      Module.Basis.restrictScalars_repr_apply
        (R := ℤ) ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
        (nsCoordinateLatticePoint n) i
  simpa [EuclideanSpace.basisFun_repr, hrepr] using hcast.symm

/-- The periodization shift is exactly scalar multiplication of the associated
concrete lattice point. -/
theorem periodizationShift_eq_smul_nsCoordinateLatticePoint
    (L : ℝ) (n : NSLatticeIndex) :
    periodizationShift L n =
      (2 * Real.pi * L) • ((nsCoordinateLatticePoint n : NSCoordinateLattice) : NSSpace) := by
  ext i
  simp [periodizationShift, nsCoordinateLatticePoint_coe_apply]

/-- Every lattice index lies in some centered cubic box. -/
theorem exists_mem_centeredLatticeBox (n : NSLatticeIndex) :
    ∃ N : ℕ, n ∈ centeredLatticeBox N := by
  let M : ℤ := max (|n 0|) (max (|n 1|) (|n 2|))
  have hM : ∀ i : Fin 3, |n i| ≤ M := by
    intro i
    fin_cases i <;> simp [M]
  have hMnonneg : 0 ≤ M := by
    exact le_trans (abs_nonneg (n 0)) (hM 0)
  refine ⟨Int.toNat M, ?_⟩
  rw [mem_centeredLatticeBox_iff_abs_le]
  intro i
  simpa [Int.toNat_of_nonneg hMnonneg] using hM i

/-- The centered lattice boxes exhaust the raw index type `ℤ^3`. -/
theorem centeredLatticeBox_tendsto_atTop :
    Tendsto centeredLatticeBox Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_finset_of_monotone
    (fun _ _ hNM => centeredLatticeBox_mono hNM)
    exists_mem_centeredLatticeBox

end NavierStokes
end FluidDynamics
end Mettapedia
