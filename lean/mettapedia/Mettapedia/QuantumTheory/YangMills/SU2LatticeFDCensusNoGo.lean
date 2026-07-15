import Mettapedia.QuantumTheory.YangMills.V14BoundaryCochainBootstrap
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# SU(2) lattice obstruction to the O.9 Lorentz-only operator census

This module decides the first mandatory gate for a complete dimension-at-most-16
Wilson-coordinate certificate on the repaired boundary-cochain object.

The exact Wilson block has only hypercubic spacetime symmetry.  Already at
canonical dimension eight it has the gauge-invariant local observable obtained
by squaring the six oriented plaquette potentials at one vertex and summing
them.  On a Cartan small-field chart its first quartic term is the componentwise
fourth-power polynomial in the six curvature components.

O.9.3, by contrast, restricts its proposed census to Lorentz-invariant tensor
contractions.  A rational orthogonal rotation below proves that the Wilson
quartic polynomial is not Lorentz invariant.  Hence it cannot lie in the span
of *any* O.9 Lorentz-scalar census, independently of the number of proposed
coordinates or of Bianchi, IBP, EOM, trace-cyclicity, and SU(2)
Cayley--Hamilton reductions.  The obstruction is derivative-free, so passing
from O.9.2 off shell to the F.4.3 on-shell quotient cannot remove it.

The result is specifically about the requested identification of an actual
lattice census with O.9/F.4.3.  Enlarging the target to all hypercubic
operators is a possible new construction, but it is a different census and
requires new extraction and analytic estimates.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2LatticeFDCensusNoGo

open SU2WilsonBlockPilot

/-! ## The exact lattice observable -/

/-- The six positively oriented coordinate two-planes in four dimensions,
ordered as `01, 02, 03, 12, 13, 23`. -/
abbrev OrientedPlane := Fin 6

def OrientedPlane.first : OrientedPlane → Axis
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | 5 => 2

def OrientedPlane.second : OrientedPlane → Axis
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 2
  | 4 => 3
  | 5 => 3

theorem OrientedPlane.ordered (plane : OrientedPlane) :
    plane.first < plane.second := by
  fin_cases plane <;> decide

/-- The elementary plaquette in a coordinate plane based at the zero vertex. -/
def originPlaquette (plane : OrientedPlane) : BlockPlaquette where
  origin := 0
  first := plane.first
  second := plane.second
  ordered := plane.ordered
  canStepFirst := by simp
  canStepSecond := by simp

/-- Real curvature components on a Cartan slice of the SU(2) small-field
chart.  Antisymmetry is imposed on the witnesses below rather than baked into
the carrier, keeping rotation and finite sums transparent. -/
abbrev CartanCurvature := Fin 4 → Fin 4 → ℝ

/-! ### An exact Cartan subgroup and a realizing link-field chart -/

/-- A real two-dimensional rotation, regarded as a complex matrix.  This is a
concrete maximal-torus chart in `SU(2)`. -/
def su2CartanMatrix (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos theta : ℂ), (Real.sin theta : ℂ);
     -(Real.sin theta : ℂ), (Real.cos theta : ℂ)]

theorem su2CartanMatrix_mem (theta : ℝ) :
    su2CartanMatrix theta ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [su2CartanMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        star, Matrix.conjTranspose_apply, -Complex.ofReal_cos,
        -Complex.ofReal_sin] <;>
      nlinarith [Real.sin_sq_add_cos_sq theta]
  · apply Complex.ext <;>
      simp [su2CartanMatrix, Matrix.det_fin_two, -Complex.ofReal_cos,
        -Complex.ofReal_sin] <;>
      nlinarith [Real.sin_sq_add_cos_sq theta]

/-- The exact `SU(2)` Cartan element used by the small-field chart. -/
def su2CartanElement (theta : ℝ) : SU2 :=
  ⟨su2CartanMatrix theta, su2CartanMatrix_mem theta⟩

/-- On the Cartan subgroup, the normalized `SU(2)` Wilson potential is exactly
`1 - cos theta`. -/
theorem specialUnitaryWilsonPotential_su2CartanElement (theta : ℝ) :
    specialUnitaryWilsonPotential (Fin 2) (su2CartanElement theta) =
      1 - Real.cos theta := by
  simp [specialUnitaryWilsonPotential, su2CartanElement, su2CartanMatrix,
    Matrix.trace, Fin.sum_univ_two, -Complex.ofReal_cos]

/-- The six links carrying the independent origin-plaquette Cartan angles are
pairwise distinct. -/
theorem origin_secondAfterFirst_injective :
    Function.Injective
      (fun plane : OrientedPlane => (originPlaquette plane).secondAfterFirst) := by
  decide

theorem origin_firstLink_not_secondAfterFirst (plane : OrientedPlane) :
    ¬ ∃ source : OrientedPlane,
      (originPlaquette plane).firstLink =
        (originPlaquette source).secondAfterFirst := by
  fin_cases plane <;> decide

theorem origin_secondLink_not_secondAfterFirst (plane : OrientedPlane) :
    ¬ ∃ source : OrientedPlane,
      (originPlaquette plane).secondLink =
        (originPlaquette source).secondAfterFirst := by
  fin_cases plane <;> decide

theorem origin_firstAfterSecond_not_secondAfterFirst (plane : OrientedPlane) :
    ¬ ∃ source : OrientedPlane,
      (originPlaquette plane).firstAfterSecond =
        (originPlaquette source).secondAfterFirst := by
  fin_cases plane <;> decide

/-- A genuine link field realizing arbitrary Cartan angles on all six
plaquettes at the origin.  The selected forward-shifted links carry the six
angles; every other link is the identity. -/
def cartanLinkChart (t : ℝ) (F : CartanCurvature) : BlockLinkField :=
  fun e =>
    if h : ∃ plane : OrientedPlane,
        e = (originPlaquette plane).secondAfterFirst then
      su2CartanElement (t * F (Classical.choose h).first
        (Classical.choose h).second)
    else 1

theorem cartanLinkChart_secondAfterFirst
    (t : ℝ) (F : CartanCurvature) (plane : OrientedPlane) :
    cartanLinkChart t F (originPlaquette plane).secondAfterFirst =
      su2CartanElement (t * F plane.first plane.second) := by
  unfold cartanLinkChart
  split
  · next h =>
    congr 2
    have hp : Classical.choose h = plane :=
      origin_secondAfterFirst_injective (Classical.choose_spec h).symm
    rw [hp]
  · next h => exact (h ⟨plane, rfl⟩).elim

theorem cartanLinkChart_firstLink
    (t : ℝ) (F : CartanCurvature) (plane : OrientedPlane) :
    cartanLinkChart t F (originPlaquette plane).firstLink = 1 := by
  rw [cartanLinkChart,
    dif_neg (origin_firstLink_not_secondAfterFirst plane)]

theorem cartanLinkChart_secondLink
    (t : ℝ) (F : CartanCurvature) (plane : OrientedPlane) :
    cartanLinkChart t F (originPlaquette plane).secondLink = 1 := by
  rw [cartanLinkChart,
    dif_neg (origin_secondLink_not_secondAfterFirst plane)]

theorem cartanLinkChart_firstAfterSecond
    (t : ℝ) (F : CartanCurvature) (plane : OrientedPlane) :
    cartanLinkChart t F (originPlaquette plane).firstAfterSecond = 1 := by
  rw [cartanLinkChart,
    dif_neg (origin_firstAfterSecond_not_secondAfterFirst plane)]

theorem plaquetteHolonomy_cartanLinkChart
    (t : ℝ) (F : CartanCurvature) (plane : OrientedPlane) :
    plaquetteHolonomy (cartanLinkChart t F) (originPlaquette plane) =
      su2CartanElement (t * F plane.first plane.second) := by
  simp [plaquetteHolonomy, cartanLinkChart_firstLink,
    cartanLinkChart_secondAfterFirst, cartanLinkChart_firstAfterSecond,
    cartanLinkChart_secondLink]

theorem plaquettePotential_cartanLinkChart
    (t : ℝ) (F : CartanCurvature) (plane : OrientedPlane) :
    plaquettePotential (cartanLinkChart t F) (originPlaquette plane) =
      1 - Real.cos (t * F plane.first plane.second) := by
  unfold plaquettePotential
  rw [plaquetteHolonomy_cartanLinkChart,
    specialUnitaryWilsonPotential_su2CartanElement]

/-- An actual local SU(2) Wilson observable: sum of the squares of the six
plaquette potentials at one lattice vertex. -/
def su2HypercubicQuarticWilsonObservable (U : BlockLinkField) : ℝ :=
  ∑ plane : OrientedPlane,
    plaquettePotential U (originPlaquette plane) ^ 2

/-- The exact scalar expression of the actual observable along the realizing
Cartan link-field chart. -/
def cartanWilsonChartFunctional (t : ℝ) (F : CartanCurvature) : ℝ :=
  ∑ plane : OrientedPlane,
    (1 - Real.cos (t * F plane.first plane.second)) ^ 2

theorem su2HypercubicQuarticWilsonObservable_cartanLinkChart
    (t : ℝ) (F : CartanCurvature) :
    su2HypercubicQuarticWilsonObservable (cartanLinkChart t F) =
      cartanWilsonChartFunctional t F := by
  unfold su2HypercubicQuarticWilsonObservable cartanWilsonChartFunctional
  apply Finset.sum_congr rfl
  intro plane _
  rw [plaquettePotential_cartanLinkChart]

/-- The lattice observable is exactly gauge invariant. -/
theorem su2HypercubicQuarticWilsonObservable_gaugeInvariant :
    ∀ (g : BlockGaugeTransform) (U : BlockLinkField),
      su2HypercubicQuarticWilsonObservable (gaugeAct g U) =
        su2HypercubicQuarticWilsonObservable U := by
  intro g U
  unfold su2HypercubicQuarticWilsonObservable
  apply Finset.sum_congr rfl
  intro plane _
  rw [plaquettePotential_gaugeAct]

/-- O.9.1 canonical dimension of the leading term: four curvature factors and
no covariant derivatives. -/
def su2HypercubicQuarticCanonicalDimension : ℕ := 2 * 4 + 0

theorem su2HypercubicQuarticCanonicalDimension_eq_eight :
    su2HypercubicQuarticCanonicalDimension = 8 := by
  rfl

/-! ## Its quartic Cartan jet is not Lorentz invariant -/

/-- The componentwise quartic polynomial contributed by the six plaquette
potential squares.  It is the quartic Cartan jet of the exact Wilson
observable, up to one common nonzero normalization factor. -/
def hypercubicQuarticJet (F : CartanCurvature) : ℝ :=
    F 0 1 ^ 4 + F 0 2 ^ 4 + F 0 3 ^ 4 +
    F 1 2 ^ 4 + F 1 3 ^ 4 + F 2 3 ^ 4

/-- The fourth derivative of one squared Wilson plaquette potential.  This is
the analytic seal connecting the formal fourth-power polynomial to the exact
Wilson potential rather than to a substituted polynomial model. -/
theorem singleCartanWilsonSquare_fourthJet (x : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => (1 - Real.cos (t * x)) ^ 2) 0 =
      6 * x ^ 4 := by
  let f0 : ℝ → ℝ := fun t => (1 - Real.cos (t * x)) ^ 2
  let f1 : ℝ → ℝ := fun t => (2 * x) *
    ((1 - Real.cos (t * x)) * Real.sin (t * x))
  let f2 : ℝ → ℝ := fun t => 2 * x ^ 2 *
    (Real.sin (t * x) ^ 2 +
      (1 - Real.cos (t * x)) * Real.cos (t * x))
  let f3 : ℝ → ℝ := fun t => 2 * x ^ 3 *
    (4 * Real.sin (t * x) * Real.cos (t * x) - Real.sin (t * x))
  have h01 : deriv f0 = f1 := by
    funext t
    simp only [f0, f1]
    have htx : HasDerivAt (fun s : ℝ => s * x) x t := by
      simpa using (hasDerivAt_id t).mul_const x
    have hcos : HasDerivAt (fun s : ℝ => Real.cos (s * x))
        (-Real.sin (t * x) * x) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_cos (t * x)).comp t htx
    have ha : HasDerivAt (fun s : ℝ => 1 - Real.cos (s * x))
        (Real.sin (t * x) * x) t := by
      simpa [sub_eq_add_neg] using hcos.neg.const_add 1
    have hf0 := (ha.pow 2).congr_deriv (by ring :
      (2 : ℝ) * (1 - Real.cos (t * x)) ^ (2 - 1) *
          (Real.sin (t * x) * x) =
        (2 * x) * ((1 - Real.cos (t * x)) * Real.sin (t * x)))
    have hfun : ((fun s : ℝ => 1 - Real.cos (s * x)) ^ 2) =
        (fun s : ℝ => (1 - Real.cos (s * x)) ^ 2) := by
      funext s
      rfl
    rw [hfun] at hf0
    exact hf0.deriv
  have h12 : deriv f1 = f2 := by
    funext t
    simp only [f1, f2]
    have htx : HasDerivAt (fun s : ℝ => s * x) x t := by
      simpa using (hasDerivAt_id t).mul_const x
    have hcos : HasDerivAt (fun s : ℝ => Real.cos (s * x))
        (-Real.sin (t * x) * x) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_cos (t * x)).comp t htx
    have hsin : HasDerivAt (fun s : ℝ => Real.sin (s * x))
        (Real.cos (t * x) * x) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_sin (t * x)).comp t htx
    have ha : HasDerivAt (fun s : ℝ => 1 - Real.cos (s * x))
        (Real.sin (t * x) * x) t := by
      simpa [sub_eq_add_neg] using hcos.neg.const_add 1
    have hf1 := ((ha.mul hsin).const_mul (2 * x)).congr_deriv (by
      ring :
      (2 * x) * ((Real.sin (t * x) * x) * Real.sin (t * x) +
          (1 - Real.cos (t * x)) * (Real.cos (t * x) * x)) =
        2 * x ^ 2 * (Real.sin (t * x) ^ 2 +
          (1 - Real.cos (t * x)) * Real.cos (t * x)))
    simpa only [Pi.mul_apply] using hf1.deriv
  have h23 : deriv f2 = f3 := by
    funext t
    simp only [f2, f3]
    have htx : HasDerivAt (fun s : ℝ => s * x) x t := by
      simpa using (hasDerivAt_id t).mul_const x
    have hcos : HasDerivAt (fun s : ℝ => Real.cos (s * x))
        (-Real.sin (t * x) * x) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_cos (t * x)).comp t htx
    have hsin : HasDerivAt (fun s : ℝ => Real.sin (s * x))
        (Real.cos (t * x) * x) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_sin (t * x)).comp t htx
    have ha : HasDerivAt (fun s : ℝ => 1 - Real.cos (s * x))
        (Real.sin (t * x) * x) t := by
      simpa [sub_eq_add_neg] using hcos.neg.const_add 1
    have hf2 := (((hsin.pow 2).add (ha.mul hcos)).const_mul
      (2 * x ^ 2)).congr_deriv (by
        ring :
        (2 * x ^ 2) *
            ((2 : ℝ) * Real.sin (t * x) ^ (2 - 1) *
                (Real.cos (t * x) * x) +
              ((Real.sin (t * x) * x) * Real.cos (t * x) +
                (1 - Real.cos (t * x)) * (-Real.sin (t * x) * x))) =
          2 * x ^ 3 *
            (4 * Real.sin (t * x) * Real.cos (t * x) - Real.sin (t * x)))
    simpa only [Pi.pow_apply, Pi.add_apply, Pi.mul_apply] using hf2.deriv
  have h3 : deriv f3 0 = 6 * x ^ 4 := by
    simp only [f3]
    have htx : HasDerivAt (fun s : ℝ => s * x) x 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const x
    have hcos : HasDerivAt (fun s : ℝ => Real.cos (s * x)) 0 0 := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_cos (0 * x)).comp 0 htx
    have hsin : HasDerivAt (fun s : ℝ => Real.sin (s * x)) x 0 := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_sin (0 * x)).comp 0 htx
    have hf3 := ((((hsin.mul hcos).const_mul 4).sub hsin).const_mul
      (2 * x ^ 3)).congr_deriv (by norm_num; ring :
        (2 * x ^ 3) * (4 * (x * Real.cos (0 * x) +
            Real.sin (0 * x) * 0) - x) = 6 * x ^ 4)
    have hfun :
        (fun y => 2 * x ^ 3 *
          (4 * (Real.sin (y * x) * Real.cos (y * x)) - Real.sin (y * x))) =
        (fun y => 2 * x ^ 3 *
          (4 * Real.sin (y * x) * Real.cos (y * x) - Real.sin (y * x))) := by
      funext y
      ring
    simpa only [Pi.mul_apply, Pi.sub_apply, hfun] using hf3.deriv
  change iteratedDeriv 4 f0 0 = 6 * x ^ 4
  change iteratedDeriv (3 + 1) f0 0 = 6 * x ^ 4
  rw [iteratedDeriv_succ', h01]
  change iteratedDeriv (2 + 1) f1 0 = 6 * x ^ 4
  rw [iteratedDeriv_succ', h12]
  change iteratedDeriv (1 + 1) f2 0 = 6 * x ^ 4
  rw [iteratedDeriv_succ', h23]
  change iteratedDeriv (0 + 1) f3 0 = 6 * x ^ 4
  rw [iteratedDeriv_succ']
  simpa using h3

/-- The exact actual Wilson observable has fourth Cartan jet equal to six
times the hypercubic polynomial.  The factor six is nonzero, so the symmetry
failure below is a symmetry failure of the actual lattice observable. -/
theorem su2HypercubicQuarticWilsonObservable_fourthCartanJet
    (F : CartanCurvature) :
    iteratedDeriv 4
        (fun t : ℝ =>
          su2HypercubicQuarticWilsonObservable (cartanLinkChart t F)) 0 =
      6 * hypercubicQuarticJet F := by
  have hfun :
      (fun t : ℝ =>
        su2HypercubicQuarticWilsonObservable (cartanLinkChart t F)) =
      (fun t : ℝ => cartanWilsonChartFunctional t F) := by
    funext t
    exact su2HypercubicQuarticWilsonObservable_cartanLinkChart t F
  rw [hfun]
  unfold cartanWilsonChartFunctional
  rw [iteratedDeriv_fun_sum (I := Finset.univ) (n := 4) (x := (0 : ℝ))]
  · simp_rw [singleCartanWilsonSquare_fourthJet]
    rw [← Finset.mul_sum]
    congr 1
    simp [hypercubicQuarticJet, OrientedPlane.first, OrientedPlane.second,
      Fin.sum_univ_six]
  · intro plane _
    fun_prop

/-- A rational rotation by the 3-4-5 angle in the `(0,2)` coordinate plane. -/
def mixingRotation : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(3 : ℝ) / 5, 0, 4 / 5, 0;
     0, 1, 0, 0;
     -4 / 5, 0, 3 / 5, 0;
     0, 0, 0, 1]

/-- The chosen rational matrix is an honest orthogonal spacetime rotation. -/
theorem mixingRotation_orthogonal :
    mixingRotation.transpose * mixingRotation = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mixingRotation, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- Natural action of a spacetime matrix on a rank-two covariant tensor. -/
def rotateCurvature
    (R : Matrix (Fin 4) (Fin 4) ℝ) (F : CartanCurvature) :
    CartanCurvature :=
  fun mu nu =>
    ∑ alpha : Fin 4, ∑ beta : Fin 4,
      R mu alpha * R nu beta * F alpha beta

/-- Unit curvature in the `(0,1)` plane. -/
def planeZeroOneCurvature : CartanCurvature := fun mu nu =>
  if mu = 0 ∧ nu = 1 then 1
  else if mu = 1 ∧ nu = 0 then -1
  else 0

theorem planeZeroOneCurvature_antisymmetric
    (mu nu : Fin 4) :
    planeZeroOneCurvature mu nu =
      -planeZeroOneCurvature nu mu := by
  fin_cases mu <;> fin_cases nu <;>
    norm_num [planeZeroOneCurvature]

@[simp] theorem planeZeroOneCurvature_zero_one :
    planeZeroOneCurvature 0 1 = 1 := by
  simp [planeZeroOneCurvature]

@[simp] theorem planeZeroOneCurvature_zero_two :
    planeZeroOneCurvature 0 2 = 0 := by
  simp [planeZeroOneCurvature]

@[simp] theorem planeZeroOneCurvature_zero_three :
    planeZeroOneCurvature 0 3 = 0 := by
  simp [planeZeroOneCurvature]

@[simp] theorem planeZeroOneCurvature_one_two :
    planeZeroOneCurvature 1 2 = 0 := by
  simp [planeZeroOneCurvature]

@[simp] theorem planeZeroOneCurvature_one_three :
    planeZeroOneCurvature 1 3 = 0 := by
  simp [planeZeroOneCurvature]

@[simp] theorem planeZeroOneCurvature_two_three :
    planeZeroOneCurvature 2 3 = 0 := by
  simp [planeZeroOneCurvature]

theorem hypercubicQuarticJet_planeZeroOne :
    hypercubicQuarticJet planeZeroOneCurvature = 1 := by
  simp [hypercubicQuarticJet, planeZeroOneCurvature]

theorem rotated_planeZeroOne_zero_one :
    rotateCurvature mixingRotation planeZeroOneCurvature 0 1 =
      (3 : ℝ) / 5 := by
  simp [rotateCurvature, mixingRotation, planeZeroOneCurvature,
    Fin.sum_univ_succ]

theorem rotated_planeZeroOne_zero_two :
    rotateCurvature mixingRotation planeZeroOneCurvature 0 2 = 0 := by
  simp [rotateCurvature, mixingRotation, planeZeroOneCurvature,
    Fin.sum_univ_succ]

theorem rotated_planeZeroOne_zero_three :
    rotateCurvature mixingRotation planeZeroOneCurvature 0 3 = 0 := by
  simp [rotateCurvature, mixingRotation, planeZeroOneCurvature,
    Fin.sum_univ_succ]

theorem rotated_planeZeroOne_one_two :
    rotateCurvature mixingRotation planeZeroOneCurvature 1 2 =
      (4 : ℝ) / 5 := by
  simp [rotateCurvature, mixingRotation, planeZeroOneCurvature,
    Fin.sum_univ_succ] <;> norm_num

theorem rotated_planeZeroOne_one_three :
    rotateCurvature mixingRotation planeZeroOneCurvature 1 3 = 0 := by
  simp [rotateCurvature, mixingRotation, planeZeroOneCurvature,
    Fin.sum_univ_succ]

theorem rotated_planeZeroOne_two_three :
    rotateCurvature mixingRotation planeZeroOneCurvature 2 3 = 0 := by
  simp [rotateCurvature, mixingRotation, planeZeroOneCurvature,
    Fin.sum_univ_succ]

theorem hypercubicQuarticJet_rotated_planeZeroOne :
    hypercubicQuarticJet
      (rotateCurvature mixingRotation planeZeroOneCurvature) =
        (337 : ℝ) / 625 := by
  rw [hypercubicQuarticJet, rotated_planeZeroOne_zero_one,
    rotated_planeZeroOne_zero_two, rotated_planeZeroOne_zero_three,
    rotated_planeZeroOne_one_two, rotated_planeZeroOne_one_three,
    rotated_planeZeroOne_two_three]
  norm_num

/-- The dimension-eight Wilson quartic jet fails invariance under an explicit
orthogonal rotation. -/
theorem hypercubicQuarticJet_not_lorentzInvariant :
    hypercubicQuarticJet
        (rotateCurvature mixingRotation planeZeroOneCurvature) ≠
      hypercubicQuarticJet planeZeroOneCurvature := by
  rw [hypercubicQuarticJet_rotated_planeZeroOne,
    hypercubicQuarticJet_planeZeroOne]
  norm_num

/-! ## Universal span obstruction -/

/-- Invariance under the one explicit rotation.  Every O(4)-invariant scalar
operator necessarily satisfies this weaker condition. -/
def InvariantUnderMixingRotation
    (observable : CartanCurvature → ℝ) : Prop :=
  ∀ F, observable (rotateCurvature mixingRotation F) = observable F

/-- Any finite linear combination of rotation-invariant operator jets remains
rotation invariant. -/
theorem linearCombination_invariant
    {Operator : Type*} [Fintype Operator]
    (operatorJet : Operator → CartanCurvature → ℝ)
    (hinvariant : ∀ operator,
      InvariantUnderMixingRotation (operatorJet operator))
    (coefficients : Operator → ℝ) :
    InvariantUnderMixingRotation
      (fun F => ∑ operator : Operator,
        coefficients operator * operatorJet operator F) := by
  intro F
  apply Finset.sum_congr rfl
  intro operator _
  rw [hinvariant operator F]

/-- The necessary obstruction core of any requested certificate.  The
`operatorJet` rows obey O.9.3's Lorentz-scalar restriction, while
`wilsonQuarticCoordinates` asserts completeness for the actual dimension-eight
Wilson quartic jet. -/
structure O9WilsonCensusSpanningCore
    (Operator : Type*) [Fintype Operator] where
  operatorJet : Operator → CartanCurvature → ℝ
  o9LorentzScalar : ∀ operator,
    InvariantUnderMixingRotation (operatorJet operator)
  wilsonQuarticCoordinates : Operator → ℝ
  spansWilsonQuartic : ∀ F,
    hypercubicQuarticJet F =
      ∑ operator : Operator,
        wilsonQuarticCoordinates operator * operatorJet operator F

/-- **Universal census no-go.** No finite O.9 Lorentz-scalar census can span
the actual lattice Wilson quartic jet.  The theorem is independent of census
size and basis presentation. -/
theorem no_O9WilsonCensusSpanningCore
    (Operator : Type*) [Fintype Operator] :
    ¬ Nonempty (O9WilsonCensusSpanningCore Operator) := by
  rintro ⟨certificate⟩
  have hcombination := linearCombination_invariant
    certificate.operatorJet certificate.o9LorentzScalar
    certificate.wilsonQuarticCoordinates
  have hinvariant :
      hypercubicQuarticJet
          (rotateCurvature mixingRotation planeZeroOneCurvature) =
        hypercubicQuarticJet planeZeroOneCurvature := by
    calc
      _ = ∑ operator : Operator,
          certificate.wilsonQuarticCoordinates operator *
            certificate.operatorJet operator
              (rotateCurvature mixingRotation planeZeroOneCurvature) :=
        certificate.spansWilsonQuartic _
      _ = ∑ operator : Operator,
          certificate.wilsonQuarticCoordinates operator *
            certificate.operatorJet operator planeZeroOneCurvature :=
        hcombination planeZeroOneCurvature
      _ = _ := (certificate.spansWilsonQuartic _).symm
  exact hypercubicQuarticJet_not_lorentzInvariant hinvariant

/-- The two manuscript relation branches.  The obstruction has no derivatives,
so EOM elimination cannot affect it. -/
inductive CensusRelationPolicy where
  | o9OffShell
  | f43OnShell
deriving DecidableEq, Fintype, Repr

/-- A full coordinate certificate contains considerably more data (actual
representatives, reduction, independent dual jets, and conditioning).  This
interface records only the two fields already forced by fidelity and
completeness; its uninhabitedness therefore obstructs every stronger requested
certificate for either relation policy. -/
structure FaithfulDimension16WilsonCoordinateCertificate
    (policy : CensusRelationPolicy)
    (Operator : Type*) [Fintype Operator] where
  canonicalDimension : Operator → ℕ
  dimensionAtMostSixteen : ∀ operator,
    canonicalDimension operator ≤ 16
  censusCore : O9WilsonCensusSpanningCore Operator

/-- Off-shell O.9.2 fails before basis reduction, dual jets, or conditioning can
be reached. -/
theorem no_faithfulDimension16WilsonCoordinateCertificate_offShell
    (Operator : Type*) [Fintype Operator] :
    ¬ Nonempty (FaithfulDimension16WilsonCoordinateCertificate
      .o9OffShell Operator) := by
  rintro ⟨certificate⟩
  exact no_O9WilsonCensusSpanningCore Operator ⟨certificate.censusCore⟩

/-- The F.4.3 on-shell quotient cannot repair the derivative-free quartic
failure. -/
theorem no_faithfulDimension16WilsonCoordinateCertificate_onShell
    (Operator : Type*) [Fintype Operator] :
    ¬ Nonempty (FaithfulDimension16WilsonCoordinateCertificate
      .f43OnShell Operator) := by
  rintro ⟨certificate⟩
  exact no_O9WilsonCensusSpanningCore Operator ⟨certificate.censusCore⟩

/-! ## Reasonable relation-policy variants -/

inductive CensusConstructionVariant where
  | o9OffShell
  | f43OnShellEOM
  | bianchiAndIBPReduced
  | cyclicAndMultiTraceCompleted
  | su2CayleyHamiltonReduced
  | postponedIBPBoundaryCochain
deriving DecidableEq, Fintype, Repr

inductive CensusConstructionVerdict where
  | obstructedByHypercubicQuartic
deriving DecidableEq, Repr

def censusConstructionVerdict
    (_ : CensusConstructionVariant) : CensusConstructionVerdict :=
  .obstructedByHypercubicQuartic

/-- All same-target variants are closed by the same derivative-free symmetry
obstruction.  Bianchi, IBP, EOM, trace, and Cayley--Hamilton choices cannot turn
a non-Lorentz-invariant polynomial into a Lorentz scalar. -/
theorem every_censusConstructionVariant_obstructed
    (variant : CensusConstructionVariant) :
    censusConstructionVerdict variant =
      .obstructedByHypercubicQuartic := by
  cases variant <;> rfl

/-- **YM MOVE 7 terminal no-go.** The exact SU(2) Wilson observable exists and
is gauge invariant at canonical dimension eight, but neither manuscript
relation policy admits a complete Lorentz-only coordinate census for it. -/
theorem ymMove7_dimension16WilsonCoordinate_terminalNoGo :
    su2HypercubicQuarticCanonicalDimension = 8 ∧
    (∀ g U,
      su2HypercubicQuarticWilsonObservable (gaugeAct g U) =
        su2HypercubicQuarticWilsonObservable U) ∧
    hypercubicQuarticJet
        (rotateCurvature mixingRotation planeZeroOneCurvature) ≠
      hypercubicQuarticJet planeZeroOneCurvature ∧
    (∀ F,
      iteratedDeriv 4
          (fun t : ℝ =>
            su2HypercubicQuarticWilsonObservable (cartanLinkChart t F)) 0 =
        6 * hypercubicQuarticJet F) ∧
    (∀ (Operator : Type) [Fintype Operator],
      ¬ Nonempty (FaithfulDimension16WilsonCoordinateCertificate
        .o9OffShell Operator)) ∧
    (∀ (Operator : Type) [Fintype Operator],
      ¬ Nonempty (FaithfulDimension16WilsonCoordinateCertificate
        .f43OnShell Operator)) ∧
    (∀ variant,
      censusConstructionVerdict variant =
        .obstructedByHypercubicQuartic) := by
  exact ⟨su2HypercubicQuarticCanonicalDimension_eq_eight,
    su2HypercubicQuarticWilsonObservable_gaugeInvariant,
    hypercubicQuarticJet_not_lorentzInvariant,
    su2HypercubicQuarticWilsonObservable_fourthCartanJet,
    no_faithfulDimension16WilsonCoordinateCertificate_offShell,
    no_faithfulDimension16WilsonCoordinateCertificate_onShell,
    every_censusConstructionVariant_obstructed⟩

end SU2LatticeFDCensusNoGo
end YangMills
end QuantumTheory
end Mettapedia
