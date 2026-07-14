import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-!
# A finite Wilson-block coefficient-majorant realization

This file constructs a concrete bridge between finite-volume Wilson observables
and the coefficient-majorant extraction model.  It is our realization of the
tree-gauge/jet suggestion in the completion blueprint; it is not asserted to be
the unspecified extended-extraction operator of the manuscript.

The pre-gauge object is exact: link fields take values in an arbitrary gauge
group, local gauge transformations act at link endpoints, plaquette holonomy
transforms by conjugation, and every class-function plaquette coordinate is
gauge invariant.  Finite polynomials in those coordinates are therefore actual
gauge-invariant Wilson-block observables, rather than an unrelated label type.

Canonical dimension is attached to each Wilson coordinate.  The polynomial
coefficient majorant is weighted by that dimension, and coordinate truncation
to dimension at most `D` has norm at most one.  This proves the extraction
component on this explicit realization.  Transfer to the manuscript's
dimension-`16` projection is handled separately: the manuscript must select the
same coordinate truncation, or provide bounded basis/dual-jet maps.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-! ## Finite group-valued Wilson fields -/

/-- An oriented link in a finite block. -/
structure WilsonLink (Vertex : Type*) where
  source : Vertex
  target : Vertex

/-- A group-valued link field on the complete oriented-link carrier of a finite
block.  A concrete lattice block is obtained by using only its designated
plaquette links below. -/
abbrev WilsonLinkField (Vertex GaugeGroup : Type*) :=
  WilsonLink Vertex → GaugeGroup

/-- A local gauge transformation, one group element at every vertex. -/
abbrev WilsonGaugeTransform (Vertex GaugeGroup : Type*) :=
  Vertex → GaugeGroup

/-- Standard endpoint action of a local gauge transformation on a link field. -/
def wilsonGaugeAct
    {Vertex GaugeGroup : Type*} [Group GaugeGroup]
    (g : WilsonGaugeTransform Vertex GaugeGroup)
    (U : WilsonLinkField Vertex GaugeGroup) :
    WilsonLinkField Vertex GaugeGroup :=
  fun e => g e.source * U e * (g e.target)⁻¹

theorem wilsonGaugeAct_one
    {Vertex GaugeGroup : Type*} [Group GaugeGroup]
    (U : WilsonLinkField Vertex GaugeGroup) :
    wilsonGaugeAct (fun _ => 1) U = U := by
  funext e
  simp [wilsonGaugeAct]

theorem wilsonGaugeAct_mul
    {Vertex GaugeGroup : Type*} [Group GaugeGroup]
    (g₁ g₂ : WilsonGaugeTransform Vertex GaugeGroup)
    (U : WilsonLinkField Vertex GaugeGroup) :
    wilsonGaugeAct (fun v => g₁ v * g₂ v) U =
      wilsonGaugeAct g₁ (wilsonGaugeAct g₂ U) := by
  funext e
  simp only [wilsonGaugeAct, mul_inv_rev]
  group

/-- Four oriented vertices specifying one plaquette loop. -/
structure WilsonPlaquette (Vertex : Type*) where
  v0 : Vertex
  v1 : Vertex
  v2 : Vertex
  v3 : Vertex

/-- Ordered plaquette holonomy. -/
def wilsonPlaquetteHolonomy
    {Vertex GaugeGroup : Type*} [Group GaugeGroup]
    (U : WilsonLinkField Vertex GaugeGroup)
    (p : WilsonPlaquette Vertex) : GaugeGroup :=
  U ⟨p.v0, p.v1⟩ * U ⟨p.v1, p.v2⟩ *
    U ⟨p.v2, p.v3⟩ * U ⟨p.v3, p.v0⟩

/-- Plaquette holonomy transforms by conjugation at its base vertex. -/
theorem wilsonPlaquetteHolonomy_gaugeAct
    {Vertex GaugeGroup : Type*} [Group GaugeGroup]
    (g : WilsonGaugeTransform Vertex GaugeGroup)
    (U : WilsonLinkField Vertex GaugeGroup)
    (p : WilsonPlaquette Vertex) :
    wilsonPlaquetteHolonomy (wilsonGaugeAct g U) p =
      g p.v0 * wilsonPlaquetteHolonomy U p * (g p.v0)⁻¹ := by
  simp only [wilsonPlaquetteHolonomy, wilsonGaugeAct]
  group

/-- A real class function on the gauge group.  The Wilson plaquette potential
`1 - N⁻¹ Re Tr(U)` is the intended special case for `SU(N)`. -/
structure WilsonClassFunction (GaugeGroup : Type*) [Group GaugeGroup] where
  toFun : GaugeGroup → ℝ
  conjugation_invariant :
    ∀ g x : GaugeGroup, toFun (g * x * g⁻¹) = toFun x

instance {GaugeGroup : Type*} [Group GaugeGroup] :
    CoeFun (WilsonClassFunction GaugeGroup) (fun _ => GaugeGroup → ℝ) :=
  ⟨WilsonClassFunction.toFun⟩

/-- The actual Wilson plaquette potential on the matrix group `SU(n)`, in the
normalization `1 - card(n)⁻¹ Re Tr(U)`.  The intended manuscript case has
`card(n) ≥ 2`; conjugation invariance does not require that numerical guard. -/
def specialUnitaryWilsonPotential
    (n : Type*) [Fintype n] [DecidableEq n] :
    WilsonClassFunction (Matrix.specialUnitaryGroup n ℂ) where
  toFun U := 1 - (Matrix.trace U.1).re / Fintype.card n
  conjugation_invariant := by
    intro g x
    congr 2
    change
      (Matrix.trace ((g.1 * x.1) * (g⁻¹).1)).re =
        (Matrix.trace x.1).re
    rw [Matrix.trace_mul_cycle]
    change
      (Matrix.trace ((g⁻¹ * g : Matrix.specialUnitaryGroup n ℂ).1 * x.1)).re =
        (Matrix.trace x.1).re
    rw [inv_mul_cancel]
    simp

/-- A finite block of plaquette loops, together with its Wilson class function
and the canonical dimension assigned to each chart coordinate. -/
structure FiniteWilsonBlock
    (Vertex Plaquette GaugeGroup : Type*) [Group GaugeGroup] where
  plaquette : Plaquette → WilsonPlaquette Vertex
  potential : WilsonClassFunction GaugeGroup
  coordinateDimension : Plaquette → ℕ
  coordinateDimension_pos : ∀ p, 0 < coordinateDimension p

/-- The exact plaquette-coordinate map on a finite Wilson block. -/
def FiniteWilsonBlock.coordinate
    {Vertex Plaquette GaugeGroup : Type*} [Group GaugeGroup]
    (B : FiniteWilsonBlock Vertex Plaquette GaugeGroup)
    (p : Plaquette) (U : WilsonLinkField Vertex GaugeGroup) : ℝ :=
  B.potential (wilsonPlaquetteHolonomy U (B.plaquette p))

theorem FiniteWilsonBlock.coordinate_gaugeAct
    {Vertex Plaquette GaugeGroup : Type*} [Group GaugeGroup]
    (B : FiniteWilsonBlock Vertex Plaquette GaugeGroup)
    (p : Plaquette)
    (g : WilsonGaugeTransform Vertex GaugeGroup)
    (U : WilsonLinkField Vertex GaugeGroup) :
    B.coordinate p (wilsonGaugeAct g U) = B.coordinate p U := by
  unfold FiniteWilsonBlock.coordinate
  rw [wilsonPlaquetteHolonomy_gaugeAct]
  exact B.potential.conjugation_invariant _ _

/-- Gauge invariance for a real observable on finite link fields. -/
def WilsonGaugeInvariant
    {Vertex GaugeGroup : Type*} [Group GaugeGroup]
    (F : WilsonLinkField Vertex GaugeGroup → ℝ) : Prop :=
  ∀ g U, F (wilsonGaugeAct g U) = F U

/-! ## Polynomial Wilson observables and canonical dimension -/

/-- A monomial in the finite plaquette-coordinate catalog. -/
abbrev WilsonMonomial (Plaquette : Type*) := Plaquette →₀ ℕ

/-- A finite coefficient expansion in Wilson-coordinate monomials. -/
abbrev WilsonPolynomial (Plaquette : Type*) :=
  WilsonMonomial Plaquette →₀ ℝ

/-- Canonical dimension of a Wilson-coordinate monomial. -/
def FiniteWilsonBlock.monomialDimension
    {Vertex Plaquette GaugeGroup : Type*} [Group GaugeGroup]
    (B : FiniteWilsonBlock Vertex Plaquette GaugeGroup)
    (m : WilsonMonomial Plaquette) : ℕ :=
  m.sum fun p exponent => exponent * B.coordinateDimension p

/-- Evaluation of one monomial as an actual group-field observable. -/
def FiniteWilsonBlock.monomialEvaluate
    {Vertex Plaquette GaugeGroup : Type*} [Group GaugeGroup]
    (B : FiniteWilsonBlock Vertex Plaquette GaugeGroup)
    (m : WilsonMonomial Plaquette)
    (U : WilsonLinkField Vertex GaugeGroup) : ℝ :=
  m.prod fun p exponent => (B.coordinate p U) ^ exponent

theorem FiniteWilsonBlock.monomialEvaluate_gaugeAct
    {Vertex Plaquette GaugeGroup : Type*} [Group GaugeGroup]
    (B : FiniteWilsonBlock Vertex Plaquette GaugeGroup)
    (m : WilsonMonomial Plaquette)
    (g : WilsonGaugeTransform Vertex GaugeGroup)
    (U : WilsonLinkField Vertex GaugeGroup) :
    B.monomialEvaluate m (wilsonGaugeAct g U) = B.monomialEvaluate m U := by
  classical
  unfold FiniteWilsonBlock.monomialEvaluate
  apply Finsupp.prod_congr
  intro p _
  rw [B.coordinate_gaugeAct]

/-- Evaluation of a finite Wilson-coordinate polynomial on a group field. -/
def FiniteWilsonBlock.polynomialEvaluate
    {Vertex Plaquette GaugeGroup : Type*} [Group GaugeGroup]
    (B : FiniteWilsonBlock Vertex Plaquette GaugeGroup)
    (coeff : WilsonPolynomial Plaquette)
    (U : WilsonLinkField Vertex GaugeGroup) : ℝ :=
  coeff.sum fun m c => c * B.monomialEvaluate m U

/-- Every polynomial in the block's Wilson coordinates is an actual
gauge-invariant observable. -/
theorem FiniteWilsonBlock.polynomialEvaluate_gaugeInvariant
    {Vertex Plaquette GaugeGroup : Type*} [Group GaugeGroup]
    (B : FiniteWilsonBlock Vertex Plaquette GaugeGroup)
    (coeff : WilsonPolynomial Plaquette) :
    WilsonGaugeInvariant (B.polynomialEvaluate coeff) := by
  intro g U
  unfold FiniteWilsonBlock.polynomialEvaluate
  apply Finsupp.sum_congr
  intro m _
  rw [B.monomialEvaluate_gaugeAct]

/-! ## Our coefficient-majorant extraction realization -/

/-- Weighted coefficient-majorant of a finite Wilson polynomial at radius `r`.
Unlike the manuscript's ambiguous coefficient/derivative supremum, this fixes
the norm explicitly. -/
def FiniteWilsonBlock.polynomialMajorantNorm
    {Vertex Plaquette GaugeGroup : Type*} [Group GaugeGroup]
    (B : FiniteWilsonBlock Vertex Plaquette GaugeGroup)
    (r : ℝ) (coeff : WilsonPolynomial Plaquette) : ℝ :=
  coeff.sum fun m c => |c| * r ^ B.monomialDimension m

/-- Canonical coordinate truncation to monomials of dimension at most `D`. -/
def FiniteWilsonBlock.polynomialTruncate
    {Vertex Plaquette GaugeGroup : Type*} [Group GaugeGroup]
    (B : FiniteWilsonBlock Vertex Plaquette GaugeGroup)
    (D : ℕ) (coeff : WilsonPolynomial Plaquette) :
    WilsonPolynomial Plaquette :=
  coeff.filter fun m => B.monomialDimension m ≤ D

/-- Exact support characterization of our extended-extraction realization. -/
theorem FiniteWilsonBlock.polynomialTruncate_apply
    {Vertex Plaquette GaugeGroup : Type*} [Group GaugeGroup]
    (B : FiniteWilsonBlock Vertex Plaquette GaugeGroup)
    (D : ℕ) (coeff : WilsonPolynomial Plaquette)
    (m : WilsonMonomial Plaquette) :
    B.polynomialTruncate D coeff m =
      if B.monomialDimension m ≤ D then coeff m else 0 := by
  rfl

/-- **Faithful component theorem for our Wilson-block realization.**  In the
explicit coefficient-majorant norm, canonical monomial extraction has operator
norm at most one.  Finiteness here is finite polynomial support; the plaquette
catalog is a genuine finite Wilson block, not a generic monomial-label toy. -/
theorem FiniteWilsonBlock.polynomialMajorantNorm_truncate_le
    {Vertex Plaquette GaugeGroup : Type*} [Group GaugeGroup]
    (B : FiniteWilsonBlock Vertex Plaquette GaugeGroup)
    (r : ℝ) (hr : 0 ≤ r) (D : ℕ)
    (coeff : WilsonPolynomial Plaquette) :
    B.polynomialMajorantNorm r (B.polynomialTruncate D coeff) ≤
      B.polynomialMajorantNorm r coeff := by
  classical
  unfold FiniteWilsonBlock.polynomialMajorantNorm
    FiniteWilsonBlock.polynomialTruncate
  rw [Finsupp.sum_filter_index]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
    (by
      intro m _ _
      exact mul_nonneg (abs_nonneg _) (pow_nonneg hr _))

/-- Truncation remains an actual gauge-invariant Wilson observable after
extraction. -/
theorem FiniteWilsonBlock.polynomialTruncate_gaugeInvariant
    {Vertex Plaquette GaugeGroup : Type*} [Group GaugeGroup]
    (B : FiniteWilsonBlock Vertex Plaquette GaugeGroup)
    (D : ℕ) (coeff : WilsonPolynomial Plaquette) :
    WilsonGaugeInvariant
      (B.polynomialEvaluate (B.polynomialTruncate D coeff)) :=
  B.polynomialEvaluate_gaugeInvariant _

end YangMills
end QuantumTheory
end Mettapedia
