import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticBasis

/-!
# Wilson and O(4) bridge for the certified H(4) quartic census

This module identifies the pure-fourth H(4) orbit coordinate with the actual
`SU(2)` Wilson fourth Cartan jet.  It also defines the honest O(4)-invariant
function subspace and proves that the pure-fourth orbit polynomial gives a
nonzero class in the Lorentz-breaking quotient.

The result closes only the derivative-free Cartan quartic rung.  It does not
transfer this coordinate or its identity conditioning to the noncommutative
dimension-sixteen `F,D` quotient.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicQuarticWilsonBridge

open SU2LatticeFDCensusNoGo
open V14HypercubicQuarticCensus

/-! ## The Wilson pure-fourth coordinate -/

/-- The rational coefficient vector of the actual Wilson fourth jet in the
certified quartic census: six times the pure-fourth orbit basis. -/
def wilsonQuarticCensusCoefficient (monomial : QuarticMonomial) : ℚ :=
  6 * quarticOrbitBasis 0 monomial

theorem wilsonQuarticCensusCoefficient_invariant :
    IsHypercubicQuarticCoefficient wilsonQuarticCensusCoefficient := by
  intro h monomial
  rw [wilsonQuarticCensusCoefficient,
    quarticOrbitBasis_invariant 0 h monomial,
    wilsonQuarticCensusCoefficient]
  ring

/-- The exact dual-coordinate vector is `(6,0,0,0)`. -/
theorem wilsonQuarticCensusCoefficient_dual
    (coordinate : Fin 4) :
    quarticDual coordinate wilsonQuarticCensusCoefficient =
      if coordinate = 0 then 6 else 0 := by
  simp [quarticDual, wilsonQuarticCensusCoefficient,
    quarticOrbitBasis_at_representative, eq_comm]

/-- Polynomial realization of the pure-fourth orbit coordinate.  The orbit of
`quarticPureFourth` runs through the six oriented coordinate planes, and the
fourth power removes its tensor sign. -/
def pureFourthOrbitPolynomial (coefficient : ℝ)
    (F : CartanCurvature) : ℝ :=
  coefficient * hypercubicQuarticJet F

theorem pureFourthOrbitPolynomial_one_eq_planeSum (F : CartanCurvature) :
    pureFourthOrbitPolynomial 1 F =
      ∑ plane : OrientedPlane,
        F plane.first plane.second ^ 4 := by
  simp [pureFourthOrbitPolynomial, hypercubicQuarticJet,
    OrientedPlane.first, OrientedPlane.second, Fin.sum_univ_six]

/-- The fourth derivative of the exact gauge-invariant Wilson observable is
the polynomial realization of census coordinate `6 · e₀`. -/
theorem actualWilsonFourthJet_eq_pureFourthCoordinate
    (F : CartanCurvature) :
    iteratedDeriv 4
        (fun t : ℝ =>
          su2HypercubicQuarticWilsonObservable (cartanLinkChart t F)) 0 =
      pureFourthOrbitPolynomial 6 F := by
  simpa [pureFourthOrbitPolynomial] using
    su2HypercubicQuarticWilsonObservable_fourthCartanJet F

/-! ## O(4)-invariant subspace and the artifact quotient -/

/-- Curvature observables invariant under every orthogonal spacetime matrix.
The distinguished representative below is homogeneous quartic, but the
ambient function type is intentionally not restricted to polynomial syntax. -/
def o4InvariantQuarticSubspace :
    Submodule ℝ (CartanCurvature → ℝ) where
  carrier := {observable | ∀ R : Matrix (Fin 4) (Fin 4) ℝ,
    R.transpose * R = 1 → ∀ F,
      observable (rotateCurvature R F) = observable F}
  zero_mem' := by
    intro R _ F
    rfl
  add_mem' := by
    intro left right hleft hright R horthogonal F
    simp only [Pi.add_apply]
    rw [hleft R horthogonal F, hright R horthogonal F]
  smul_mem' := by
    intro scalar observable hobservable R horthogonal F
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hobservable R horthogonal F]

theorem hypercubicQuarticJet_not_mem_o4InvariantSubspace :
    hypercubicQuarticJet ∉ o4InvariantQuarticSubspace := by
  intro hinvariant
  exact hypercubicQuarticJet_not_lorentzInvariant
    (hinvariant mixingRotation mixingRotation_orthogonal
      planeZeroOneCurvature)

/-- The O(4)-invariant curvature-observable subspace is strictly smaller than
the ambient function space. -/
theorem o4InvariantQuarticSubspace_strict :
    o4InvariantQuarticSubspace < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro heq
  apply hypercubicQuarticJet_not_mem_o4InvariantSubspace
  rw [heq]
  trivial

theorem hypercubicQuarticJet_nonzero :
    hypercubicQuarticJet ≠ 0 := by
  intro hzero
  have hvalue := congrArg
    (fun observable : CartanCurvature → ℝ =>
      observable planeZeroOneCurvature) hzero
  rw [hypercubicQuarticJet_planeZeroOne] at hvalue
  norm_num at hvalue

/-- The pure-fourth Wilson coordinate defines a nonzero Lorentz-breaking
artifact class modulo all O(4)-invariant curvature observables. -/
theorem pureFourthArtifactClass_nonzero :
    o4InvariantQuarticSubspace.mkQ hypercubicQuarticJet ≠ 0 := by
  change Submodule.Quotient.mk hypercubicQuarticJet ≠ 0
  intro hzero
  exact hypercubicQuarticJet_not_mem_o4InvariantSubspace
    ((Submodule.Quotient.mk_eq_zero o4InvariantQuarticSubspace).mp hzero)

/-- Same-object completion packet for the quartic rung: census coordinates,
the exact Wilson realization, strict O(4) inclusion, and a nonzero artifact
class are all simultaneous theorems. -/
theorem quarticWilson_hypercubicArtifact_packet :
    IsHypercubicQuarticCoefficient wilsonQuarticCensusCoefficient ∧
    (∀ coordinate : Fin 4,
      quarticDual coordinate wilsonQuarticCensusCoefficient =
        if coordinate = 0 then 6 else 0) ∧
    (∀ F : CartanCurvature,
      iteratedDeriv 4
          (fun t : ℝ =>
            su2HypercubicQuarticWilsonObservable (cartanLinkChart t F)) 0 =
        pureFourthOrbitPolynomial 6 F) ∧
    o4InvariantQuarticSubspace < ⊤ ∧
    o4InvariantQuarticSubspace.mkQ hypercubicQuarticJet ≠ 0 := by
  exact ⟨wilsonQuarticCensusCoefficient_invariant,
    wilsonQuarticCensusCoefficient_dual,
    actualWilsonFourthJet_eq_pureFourthCoordinate,
    o4InvariantQuarticSubspace_strict,
    pureFourthArtifactClass_nonzero⟩

end V14HypercubicQuarticWilsonBridge
end YangMills
end QuantumTheory
end Mettapedia
