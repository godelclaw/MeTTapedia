import Mettapedia.QuantumTheory.YangMills.SU2LatticeFDCensusNoGo
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# A certificate surface for the finite-spacing hypercubic `F,D` census

The exact Wilson lattice has hypercubic rather than orthogonal spacetime
symmetry.  This module starts the replacement forced by
`SU2LatticeFDCensusNoGo`: a finite raw `F,D` syntax acted on by the signed
coordinate permutations in four dimensions.

The raw syntax records every field-strength index, every covariant-derivative
index, derivative ownership and ordering, and the cycle permutation encoding
single- and multitraces.  Invariant coefficient tensors on this finite syntax
therefore include delta, epsilon, and genuinely lattice-only contractions;
none is hidden behind a preselected Lorentz-scalar list.

Relations are rows of an exact rational matrix.  Bianchi, EOM, IBP,
postponed-IBP, cyclicity, multitrace identities, and `SU(2)`
Cayley--Hamilton are separate named families.  The on-shell and off-shell
policies differ only by whether EOM rows are enabled.  This file proves the
mechanical finiteness and action laws.  It does not claim that merely naming a
relation family supplies all of its rows, nor that a datatype enumeration is a
spanning or independence certificate.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicFDCensus

abbrev Axis := Fin 4

/-! ## The signed permutation group, presented constructively -/

/-- A signed coordinate permutation.  `reflected i = true` means that the
source basis vector `i` acquires a minus sign before being sent to `perm i`. -/
structure Hypercubic4 where
  perm : Equiv.Perm Axis
  reflected : Axis → Bool
deriving DecidableEq, Fintype

namespace Hypercubic4

@[ext] theorem ext (left right : Hypercubic4)
    (hperm : ∀ i, left.perm i = right.perm i)
    (hreflected : ∀ i, left.reflected i = right.reflected i) :
    left = right := by
  cases left with
  | mk leftPerm leftReflected =>
      cases right with
      | mk rightPerm rightReflected =>
          simp only [mk.injEq]
          exact ⟨Equiv.ext hperm, funext hreflected⟩

def one : Hypercubic4 where
  perm := Equiv.refl Axis
  reflected := fun _ => false

/-- `compose left right` acts first by `right`, then by `left`. -/
def compose (left right : Hypercubic4) : Hypercubic4 where
  perm := right.perm.trans left.perm
  reflected := fun i => right.reflected i ^^ left.reflected (right.perm i)

def inverse (h : Hypercubic4) : Hypercubic4 where
  perm := h.perm.symm
  reflected := fun i => h.reflected (h.perm.symm i)

@[simp] theorem one_perm_apply (i : Axis) : one.perm i = i := rfl

@[simp] theorem one_reflected (i : Axis) : one.reflected i = false := rfl

@[simp] theorem compose_perm_apply (left right : Hypercubic4) (i : Axis) :
    (compose left right).perm i = left.perm (right.perm i) := rfl

@[simp] theorem compose_reflected (left right : Hypercubic4) (i : Axis) :
    (compose left right).reflected i =
      (right.reflected i ^^ left.reflected (right.perm i)) := rfl

theorem compose_assoc (first second third : Hypercubic4) :
    compose first (compose second third) =
      compose (compose first second) third := by
  ext i
  · rfl
  · simp [compose, Bool.xor_assoc]

@[simp] theorem compose_one (h : Hypercubic4) : compose h one = h := by
  ext i <;> simp [compose]

@[simp] theorem one_compose (h : Hypercubic4) : compose one h = h := by
  ext i <;> simp [compose]

@[simp] theorem inverse_compose (h : Hypercubic4) :
    compose (inverse h) h = one := by
  ext i
  · simp [compose, inverse]
  · simp [compose, inverse]

@[simp] theorem compose_inverse (h : Hypercubic4) :
    compose h (inverse h) = one := by
  ext i
  · simp [compose, inverse]
  · simp [compose, inverse]

/-- Rational sign carried by one source coordinate. -/
def axisSign (h : Hypercubic4) (i : Axis) : ℚ :=
  if h.reflected i then -1 else 1

@[simp] theorem axisSign_one (i : Axis) : axisSign one i = 1 := by
  simp [axisSign, one]

theorem axisSign_compose (left right : Hypercubic4) (i : Axis) :
    axisSign (compose left right) i =
      axisSign right i * axisSign left (right.perm i) := by
  cases hri : right.reflected i <;>
    cases hli : left.reflected (right.perm i) <;>
    simp [axisSign, compose, hri, hli]

/-- Determinant character of the signed permutation, used to distinguish
ordinary scalars from epsilon/pseudoscalar contractions. -/
def orientationSign (h : Hypercubic4) : ℚ :=
  ((Equiv.Perm.sign h.perm : ℤ) : ℚ) * ∏ i, axisSign h i

theorem orientationSign_mem (h : Hypercubic4) :
    orientationSign h = 1 ∨ orientationSign h = -1 := by
  classical
  have hperm : ((Equiv.Perm.sign h.perm : ℤ) : ℚ) = 1 ∨
      ((Equiv.Perm.sign h.perm : ℤ) : ℚ) = -1 := by
    have hu := Int.units_eq_one_or h.perm.sign
    rcases hu with hu | hu
    · left
      simpa using congrArg (fun u : ℤˣ => ((u : ℤ) : ℚ)) hu
    · right
      simpa using congrArg (fun u : ℤˣ => ((u : ℤ) : ℚ)) hu
  have haxis : (∏ i, axisSign h i) = 1 ∨
      (∏ i, axisSign h i) = -1 := by
    classical
    induction (Finset.univ : Finset Axis) using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi]
        have hs : axisSign h i = 1 ∨ axisSign h i = -1 := by
          unfold axisSign
          split <;> simp
        rcases hs with hs | hs <;> rcases ih with ih | ih <;>
          simp [hs, ih]
  rcases hperm with hp | hp <;> rcases haxis with ha | ha <;>
    simp [orientationSign, hp, ha]

/-- The concrete signed-permutation carrier has the expected order
`2^4 · 4! = 384`. -/
theorem card_hypercubic4 : Fintype.card Hypercubic4 = 384 := by
  set_option maxRecDepth 10000 in
    decide

/-- Determinant parity is multiplicative.  This finite theorem is checked by
normalization over all `384^2` pairs of signed permutations. -/
theorem orientationSign_compose (left right : Hypercubic4) :
    orientationSign (compose left right) =
      orientationSign left * orientationSign right := by
  classical
  have haxis :
      (∏ i, axisSign (compose left right) i) =
        (∏ i, axisSign right i) * (∏ i, axisSign left i) := by
    calc
      (∏ i, axisSign (compose left right) i) =
          ∏ i, (axisSign right i * axisSign left (right.perm i)) := by
            apply Finset.prod_congr rfl
            intro i _
            exact axisSign_compose left right i
      _ = (∏ i, axisSign right i) *
          (∏ i, axisSign left (right.perm i)) :=
            Finset.prod_mul_distrib
      _ = (∏ i, axisSign right i) * (∏ i, axisSign left i) := by
            rw [Equiv.prod_comp right.perm (fun i => axisSign left i)]
  unfold orientationSign
  rw [haxis]
  change
    ((↑((Equiv.Perm.sign (right.perm.trans left.perm) : ℤ)) : ℚ) *
        ((∏ i, axisSign right i) * (∏ i, axisSign left i))) =
      (((↑((Equiv.Perm.sign left.perm : ℤ)) : ℚ) *
          ∏ i, axisSign left i) *
        ((↑((Equiv.Perm.sign right.perm : ℤ)) : ℚ) *
          ∏ i, axisSign right i))
  rw [Equiv.Perm.sign_trans]
  simp only [Units.val_mul, Int.cast_mul]
  ring

end Hypercubic4

/-! ## Finite raw `F,D` syntax through canonical dimension sixteen -/

/-- Numbers of field strengths and covariant derivatives.  The bounds are
structural: at dimension at most sixteen there are at most eight `F` factors
and at most sixteen derivative factors. -/
structure FDShape where
  fieldCount : Fin 9
  derivativeCount : Fin 17
  dimension_le : 2 * fieldCount.1 + derivativeCount.1 ≤ 16
deriving DecidableEq, Fintype

def FDShape.canonicalDimension (shape : FDShape) : ℕ :=
  2 * shape.fieldCount.1 + shape.derivativeCount.1

theorem FDShape.canonicalDimension_le_sixteen (shape : FDShape) :
    shape.canonicalDimension ≤ 16 :=
  shape.dimension_le

/-- Fixed-width trace-cycle data. -/
structure PaddedTraceLayout where
  traceSuccessor : Fin 8 → Fin 8
  tracePredecessor : Fin 8 → Fin 8
deriving DecidableEq, Fintype

/-- Fixed-width derivative ownership and ordering data. -/
structure PaddedDerivativeLayout where
  derivativeOwner : Fin 16 → Fin 8
  derivativeSuccessor : Fin 16 → Fin 16
  derivativePredecessor : Fin 16 → Fin 16
deriving DecidableEq, Fintype

/-- Fixed-width concrete spacetime-index data. -/
structure PaddedAxisAssignment where
  fieldFirst : Fin 8 → Axis
  fieldSecond : Fin 8 → Axis
  derivativeAxis : Fin 16 → Axis
deriving DecidableEq, Fintype

/-- A fixed-width encoding of a raw monomial.  Slots beyond the counts in
`shape` are padding.  Fixed widths make the enumerated carrier manifestly
finite; `PaddedRawFDMonomial.WellFormed` below prevents padding from being
mistaken for mathematical syntax. -/
structure PaddedRawFDMonomial where
  shape : FDShape
  trace : PaddedTraceLayout
  derivatives : PaddedDerivativeLayout
  axes : PaddedAxisAssignment
deriving DecidableEq, Fintype

/-- Active trace cycles and derivative data stay inside the active prefixes.
This also excludes derivative-only expressions with no field strength. -/
def PaddedRawFDMonomial.WellFormed
    (monomial : PaddedRawFDMonomial) : Prop :=
  (Function.LeftInverse monomial.trace.tracePredecessor
    monomial.trace.traceSuccessor) ∧
  (Function.RightInverse monomial.trace.tracePredecessor
    monomial.trace.traceSuccessor) ∧
  (Function.LeftInverse monomial.derivatives.derivativePredecessor
    monomial.derivatives.derivativeSuccessor) ∧
  (Function.RightInverse monomial.derivatives.derivativePredecessor
    monomial.derivatives.derivativeSuccessor) ∧
  (∀ i : Fin 8, i.1 < monomial.shape.fieldCount.1 →
    (monomial.trace.traceSuccessor i).1 < monomial.shape.fieldCount.1) ∧
  (∀ j : Fin 16, j.1 < monomial.shape.derivativeCount.1 →
    (monomial.derivatives.derivativeOwner j).1 <
      monomial.shape.fieldCount.1) ∧
  (∀ j : Fin 16, j.1 < monomial.shape.derivativeCount.1 →
    (monomial.derivatives.derivativeSuccessor j).1 <
      monomial.shape.derivativeCount.1)

/-- One completely indexed and well-formed raw monomial.

The active cycles of `traceSuccessor` encode its trace words.
`derivativeOwner` and `derivativeOrder` retain which covariant derivatives act
on which field and in which order.  Axis assignments are intentionally
concrete: invariant linear combinations of them are the contraction tensors. -/
abbrev RawFDMonomial :=
  {monomial : PaddedRawFDMonomial // monomial.WellFormed}

noncomputable instance : Fintype RawFDMonomial := Fintype.ofFinite _

namespace RawFDMonomial

def shape (monomial : RawFDMonomial) : FDShape := monomial.1.shape
def traceSuccessor (monomial : RawFDMonomial) : Fin 8 → Fin 8 :=
  monomial.1.trace.traceSuccessor
def tracePredecessor (monomial : RawFDMonomial) : Fin 8 → Fin 8 :=
  monomial.1.trace.tracePredecessor
def derivativeOwner (monomial : RawFDMonomial) : Fin 16 → Fin 8 :=
  monomial.1.derivatives.derivativeOwner
def derivativeSuccessor (monomial : RawFDMonomial) : Fin 16 → Fin 16 :=
  monomial.1.derivatives.derivativeSuccessor
def derivativePredecessor (monomial : RawFDMonomial) : Fin 16 → Fin 16 :=
  monomial.1.derivatives.derivativePredecessor
def fieldFirst (monomial : RawFDMonomial) : Fin 8 → Axis :=
  monomial.1.axes.fieldFirst
def fieldSecond (monomial : RawFDMonomial) : Fin 8 → Axis :=
  monomial.1.axes.fieldSecond
def derivativeAxis (monomial : RawFDMonomial) : Fin 16 → Axis :=
  monomial.1.axes.derivativeAxis

end RawFDMonomial

def RawFDMonomial.canonicalDimension (monomial : RawFDMonomial) : ℕ :=
  monomial.shape.canonicalDimension

theorem RawFDMonomial.canonicalDimension_le_sixteen
    (monomial : RawFDMonomial) : monomial.canonicalDimension ≤ 16 :=
  monomial.shape.canonicalDimension_le_sixteen

/-- Signed coordinate permutation of a raw monomial.  Trace and derivative
order data are unchanged; every visible spacetime index is renamed. -/
def RawFDMonomial.act (h : Hypercubic4)
    (monomial : RawFDMonomial) : RawFDMonomial :=
  ⟨{ shape := monomial.1.shape
     trace := monomial.1.trace
     derivatives := monomial.1.derivatives
     axes :=
       { fieldFirst := fun i => h.perm (monomial.1.axes.fieldFirst i)
         fieldSecond := fun i => h.perm (monomial.1.axes.fieldSecond i)
         derivativeAxis := fun i => h.perm (monomial.1.axes.derivativeAxis i) } },
   monomial.property⟩

@[simp] theorem RawFDMonomial.act_shape
    (h : Hypercubic4) (monomial : RawFDMonomial) :
    (monomial.act h).shape = monomial.shape := rfl

@[simp] theorem RawFDMonomial.act_fieldFirst
    (h : Hypercubic4) (monomial : RawFDMonomial) (i : Fin 8) :
    (monomial.act h).fieldFirst i = h.perm (monomial.fieldFirst i) := rfl

@[simp] theorem RawFDMonomial.act_fieldSecond
    (h : Hypercubic4) (monomial : RawFDMonomial) (i : Fin 8) :
    (monomial.act h).fieldSecond i = h.perm (monomial.fieldSecond i) := rfl

@[simp] theorem RawFDMonomial.act_derivativeAxis
    (h : Hypercubic4) (monomial : RawFDMonomial) (i : Fin 16) :
    (monomial.act h).derivativeAxis i =
      h.perm (monomial.derivativeAxis i) := rfl

@[simp] theorem RawFDMonomial.act_one (monomial : RawFDMonomial) :
    monomial.act Hypercubic4.one = monomial := by
  apply Subtype.ext
  cases monomial with
  | mk value property =>
      cases value
      rfl

theorem RawFDMonomial.act_compose
    (left right : Hypercubic4) (monomial : RawFDMonomial) :
    monomial.act (Hypercubic4.compose left right) =
      (monomial.act right).act left := by
  apply Subtype.ext
  cases monomial with
  | mk value property =>
      cases value
      rfl

/-- Tensor sign contributed by every concrete spacetime index.  This is the
sign that accompanies index renaming under coordinate reflections. -/
def RawFDMonomial.tensorSign (h : Hypercubic4)
    (monomial : RawFDMonomial) : ℚ :=
  (∏ i : Fin 8, if i.1 < monomial.shape.fieldCount.1 then
      Hypercubic4.axisSign h (monomial.fieldFirst i) else 1) *
    (∏ i : Fin 8, if i.1 < monomial.shape.fieldCount.1 then
      Hypercubic4.axisSign h (monomial.fieldSecond i) else 1) *
    ∏ j : Fin 16, if j.1 < monomial.shape.derivativeCount.1 then
      Hypercubic4.axisSign h (monomial.derivativeAxis j) else 1

@[simp] theorem RawFDMonomial.tensorSign_one (monomial : RawFDMonomial) :
    monomial.tensorSign Hypercubic4.one = 1 := by
  simp [RawFDMonomial.tensorSign]

theorem RawFDMonomial.tensorSign_compose
    (left right : Hypercubic4) (monomial : RawFDMonomial) :
    monomial.tensorSign (Hypercubic4.compose left right) =
      monomial.tensorSign right *
        (monomial.act right).tensorSign left := by
  classical
  have hfirst :
      (∏ i : Fin 8, if i.1 < monomial.shape.fieldCount.1 then
        Hypercubic4.axisSign (Hypercubic4.compose left right)
          (monomial.fieldFirst i) else 1) =
      (∏ i : Fin 8, if i.1 < monomial.shape.fieldCount.1 then
        Hypercubic4.axisSign right (monomial.fieldFirst i) else 1) *
      (∏ i : Fin 8, if i.1 < monomial.shape.fieldCount.1 then
        Hypercubic4.axisSign left (right.perm (monomial.fieldFirst i)) else 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i.1 < monomial.shape.fieldCount.1 <;>
      simp [hi, Hypercubic4.axisSign_compose]
  have hsecond :
      (∏ i : Fin 8, if i.1 < monomial.shape.fieldCount.1 then
        Hypercubic4.axisSign (Hypercubic4.compose left right)
          (monomial.fieldSecond i) else 1) =
      (∏ i : Fin 8, if i.1 < monomial.shape.fieldCount.1 then
        Hypercubic4.axisSign right (monomial.fieldSecond i) else 1) *
      (∏ i : Fin 8, if i.1 < monomial.shape.fieldCount.1 then
        Hypercubic4.axisSign left (right.perm (monomial.fieldSecond i)) else 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i.1 < monomial.shape.fieldCount.1 <;>
      simp [hi, Hypercubic4.axisSign_compose]
  have hderivative :
      (∏ j : Fin 16, if j.1 < monomial.shape.derivativeCount.1 then
        Hypercubic4.axisSign (Hypercubic4.compose left right)
          (monomial.derivativeAxis j) else 1) =
      (∏ j : Fin 16, if j.1 < monomial.shape.derivativeCount.1 then
        Hypercubic4.axisSign right (monomial.derivativeAxis j) else 1) *
      (∏ j : Fin 16, if j.1 < monomial.shape.derivativeCount.1 then
        Hypercubic4.axisSign left
          (right.perm (monomial.derivativeAxis j)) else 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j.1 < monomial.shape.derivativeCount.1 <;>
      simp [hj, Hypercubic4.axisSign_compose]
  simp only [RawFDMonomial.tensorSign, hfirst, hsecond, hderivative,
    RawFDMonomial.act_shape, RawFDMonomial.act_fieldFirst,
    RawFDMonomial.act_fieldSecond, RawFDMonomial.act_derivativeAxis]
  ring

inductive ContractionParity where
  | scalar
  | pseudoscalar
deriving DecidableEq, Fintype, Repr

def ContractionParity.character
    (parity : ContractionParity) (h : Hypercubic4) : ℚ :=
  match parity with
  | .scalar => 1
  | .pseudoscalar => h.orientationSign

theorem ContractionParity.character_compose
    (parity : ContractionParity) (left right : Hypercubic4) :
    parity.character (Hypercubic4.compose left right) =
      parity.character left * parity.character right := by
  cases parity
  · simp [ContractionParity.character]
  · exact Hypercubic4.orientationSign_compose left right

/-- Exact rational coefficient tensors on the finite raw syntax. -/
abbrev RawFDCoefficients := RawFDMonomial → ℚ

/-- Transformation law for an ordinary scalar or epsilon/pseudoscalar
coefficient tensor. -/
def IsHypercubicCoefficientTensor
    (parity : ContractionParity) (coefficients : RawFDCoefficients) : Prop :=
  ∀ h monomial,
    coefficients (monomial.act h) =
      parity.character h * monomial.tensorSign h * coefficients monomial

theorem rawFDCensus_finite : Finite RawFDMonomial := inferInstance

theorem rawFDCensus_card_finite : ∃ count : ℕ,
    Fintype.card RawFDMonomial = count :=
  ⟨Fintype.card RawFDMonomial, rfl⟩

/-! ## Exact relation matrices and separated source policies -/

inductive FDRelationFamily where
  | fieldAntisymmetry
  | bianchi
  | equationOfMotion
  | integrationByParts
  | postponedIBPBoundary
  | cyclicTrace
  | multitrace
  | su2CayleyHamilton
deriving DecidableEq, Fintype, Repr

inductive FDRelationPolicy where
  | o9OffShell
  | f43OnShell
deriving DecidableEq, Fintype, Repr

/-- The source policies share every named relation family except EOM:
O.9.2 retains EOM operators, while F.4.3 eliminates them on shell.  IBP and
postponed-IBP are distinct rows rather than silently identified. -/
def FDRelationPolicy.enables
    (policy : FDRelationPolicy) (family : FDRelationFamily) : Bool :=
  match policy, family with
  | .o9OffShell, .equationOfMotion => false
  | _, _ => true

theorem offShell_disables_eom :
    FDRelationPolicy.o9OffShell.enables .equationOfMotion = false := rfl

theorem onShell_enables_eom :
    FDRelationPolicy.f43OnShell.enables .equationOfMotion = true := rfl

/-- A finite, explicitly indexed set of relation rows.  The matrix entries are
the construction content; the family label alone proves no identity. -/
structure FDRelationMatrix (Row : Type*) [Fintype Row] where
  family : Row → FDRelationFamily
  entries : Matrix Row RawFDMonomial ℚ
  dimension : Row → Fin 17
  homogeneous : ∀ row monomial,
    entries row monomial ≠ 0 →
      monomial.canonicalDimension = (dimension row).1

def FDRelationMatrix.enabledRows
    {Row : Type*} [Fintype Row] (matrix : FDRelationMatrix Row)
    (policy : FDRelationPolicy) :=
  {row : Row // policy.enables (matrix.family row) = true}

noncomputable instance {Row : Type*} [Fintype Row]
    (matrix : FDRelationMatrix Row) (policy : FDRelationPolicy) :
    Fintype (matrix.enabledRows policy) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

theorem relationMatrix_indices_finite
    {Row : Type*} [Fintype Row] (matrix : FDRelationMatrix Row)
    (policy : FDRelationPolicy) :
    Finite (matrix.enabledRows policy) ∧ Finite RawFDMonomial :=
  ⟨inferInstance, inferInstance⟩

/-- A checked finite-dimensional census must supply both directions.  The
left inverse certifies independence; the right inverse certifies spanning.
Nothing in this structure asserts that a proposed basis exists. -/
structure ExactCensusCertificate
    (Coordinate : Type*) [Fintype Coordinate] [DecidableEq Coordinate] where
  basisToRaw : Matrix RawFDMonomial Coordinate ℚ
  rawToBasis : Matrix Coordinate RawFDMonomial ℚ
  leftInverse : rawToBasis * basisToRaw = 1
  rightInverse : basisToRaw * rawToBasis = 1

/-- The checker is the conjunction of the two exact matrix identities. -/
def ExactCensusCertificate.Checks
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : ExactCensusCertificate Coordinate) : Prop :=
  certificate.rawToBasis * certificate.basisToRaw = 1 ∧
    certificate.basisToRaw * certificate.rawToBasis = 1

theorem ExactCensusCertificate.checks
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : ExactCensusCertificate Coordinate) : certificate.Checks :=
  ⟨certificate.leftInverse, certificate.rightInverse⟩

end V14HypercubicFDCensus
end YangMills
end QuantumTheory
end Mettapedia
