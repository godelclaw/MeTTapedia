import Mettapedia.QuantumTheory.YangMills.V14HypercubicFDCensus
import Mathlib.Data.Sym.Card

/-!
# Certified dimension-eight hypercubic quartic census

This module certifies the first non-Lorentz finite-spacing sector forced by
`SU2LatticeFDCensusNoGo`: homogeneous quartic polynomials in the six Cartan
field-strength components.  Four field strengths have canonical dimension
eight under O.9.1.

There are `126` raw quartic monomials.  The signed hypercubic action splits
them into four admissible signed orbits; seven further orbits have a negative
stabilizer and therefore carry zero coefficient in every invariant
polynomial.  The four surviving orbit representatives give an exact census,
not a hand-labelled list: every raw monomial is checked to have either a
transport witness or a killing stabilizer.

This is the complete derivative-free Cartan restriction of the dimension-eight
sector.  It is not yet the complete noncommutative `SU(2)` sector with
covariant derivatives and color-trace relations; that larger transfer remains
separate and cannot be inferred from Cartan restriction.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicQuarticCensus

open SU2LatticeFDCensusNoGo
open V14HypercubicFDCensus

/-! ## The induced signed action on the six two-form components -/

/-- Lookup of the unordered coordinate plane.  Diagonal entries are padding;
all uses below have distinct input axes. -/
def planeLookup : Axis → Axis → OrientedPlane :=
  ![![0, 0, 1, 2],
    ![0, 0, 3, 4],
    ![1, 3, 0, 5],
    ![2, 4, 5, 0]]

/-- Plane permutation induced by an unsigned coordinate permutation.  Keeping
this helper separate prevents the irrelevant `2^4` reflection data from
inflating the finite inverse certificate. -/
def planeActionPerm (permutation : Equiv.Perm Axis)
    (plane : OrientedPlane) : OrientedPlane :=
  planeLookup (permutation plane.first) (permutation plane.second)

/-- Plane permutation induced by the unsigned part of a hypercubic element. -/
def planeAction (h : Hypercubic4) (plane : OrientedPlane) : OrientedPlane :=
  planeActionPerm h.perm plane

/-- Reordering sign needed to put the transformed pair back in increasing
axis order. -/
def planeReorderSign (h : Hypercubic4) (plane : OrientedPlane) : ℤ :=
  if h.perm plane.first < h.perm plane.second then 1 else -1

/-- Full sign of a two-form component under a signed coordinate permutation. -/
def planeTensorSign (h : Hypercubic4) (plane : OrientedPlane) : ℤ :=
  (if h.reflected plane.first then -1 else 1) *
    (if h.reflected plane.second then -1 else 1) *
    planeReorderSign h plane

theorem planeTensorSign_eq_one_or_neg_one
    (h : Hypercubic4) (plane : OrientedPlane) :
    planeTensorSign h plane = 1 ∨ planeTensorSign h plane = -1 := by
  unfold planeTensorSign planeReorderSign
  split <;> split <;> split <;> simp

theorem planeAction_one : ∀ plane,
    planeAction Hypercubic4.one plane = plane := by
  decide

theorem planeActionPerm_inverse_left : ∀ permutation plane,
    planeActionPerm permutation.symm (planeActionPerm permutation plane) = plane := by
  set_option maxRecDepth 10000 in
    decide

theorem planeActionPerm_inverse_right : ∀ permutation plane,
    planeActionPerm permutation (planeActionPerm permutation.symm plane) = plane := by
  set_option maxRecDepth 10000 in
    decide

theorem planeAction_inverse_left (h : Hypercubic4) (plane : OrientedPlane) :
    planeAction (Hypercubic4.inverse h) (planeAction h plane) = plane :=
  planeActionPerm_inverse_left h.perm plane

theorem planeAction_inverse_right (h : Hypercubic4) (plane : OrientedPlane) :
    planeAction h (planeAction (Hypercubic4.inverse h) plane) = plane :=
  planeActionPerm_inverse_right h.perm plane

def planeEquiv (h : Hypercubic4) : Equiv.Perm OrientedPlane where
  toFun := planeAction h
  invFun := planeAction (Hypercubic4.inverse h)
  left_inv := planeAction_inverse_left h
  right_inv := planeAction_inverse_right h

theorem card_orientedPlane : Fintype.card OrientedPlane = 6 := by decide

/-! ## Quartic monomials and their exact signed action -/

/-- A homogeneous degree-four monomial in the six independent two-form
components, represented directly by a four-element multiset.  This is the
stars-and-bars carrier of size 126; it avoids enumerating and then filtering
all `5^6` candidate exponent vectors. -/
abbrev QuarticMonomial := Sym OrientedPlane 4

theorem card_quarticMonomial : Fintype.card QuarticMonomial = 126 := by
  rw [Sym.card_sym_eq_choose]
  decide

/-- Push-forward of exponents by the plane permutation. -/
def QuarticMonomial.act (h : Hypercubic4)
    (monomial : QuarticMonomial) : QuarticMonomial :=
  Sym.map (planeEquiv h) monomial

/-- The unsigned lift of a coordinate permutation. -/
def unsignedHypercubic (permutation : Equiv.Perm Axis) : Hypercubic4 where
  perm := permutation
  reflected := fun _ => false

@[simp] theorem unsignedHypercubic_perm (permutation : Equiv.Perm Axis) :
    (unsignedHypercubic permutation).perm = permutation := rfl

@[simp] theorem unsignedHypercubic_reflected
    (permutation : Equiv.Perm Axis) (axis : Axis) :
    (unsignedHypercubic permutation).reflected axis = false := rfl

@[simp] theorem planeReorderSign_unsigned (h : Hypercubic4)
    (plane : OrientedPlane) :
    planeReorderSign (unsignedHypercubic h.perm) plane =
      planeReorderSign h plane := by
  rfl

/-- Reflections affect tensor signs but not transport of exponent multisets. -/
theorem QuarticMonomial.act_eq_unsigned (h : Hypercubic4)
    (monomial : QuarticMonomial) :
    monomial.act h = monomial.act (unsignedHypercubic h.perm) := by
  rfl

/-- Sign accumulated by the four two-form factors. -/
def QuarticMonomial.tensorSign
    (h : Hypercubic4) (monomial : QuarticMonomial) : ℤ :=
  ((monomial : Multiset OrientedPlane).map (planeTensorSign h)).prod

def IsHypercubicQuarticCoefficient
    (coefficients : QuarticMonomial → ℚ) : Prop :=
  ∀ h monomial,
    coefficients (monomial.act h) =
      (monomial.tensorSign h : ℚ) * coefficients monomial

/-! ## Four admissible orbit representatives -/

def quarticOfPlanes (first second third fourth : OrientedPlane) :
    QuarticMonomial :=
  Sym.ofVector ⟨[first, second, third, fourth], rfl⟩

def quarticPureFourth : QuarticMonomial :=
  quarticOfPlanes 5 5 5 5

def quarticAdjacentSquares : QuarticMonomial :=
  quarticOfPlanes 4 4 5 5

def quarticOppositeSquares : QuarticMonomial :=
  quarticOfPlanes 2 2 3 3

def quarticRectangleProduct : QuarticMonomial :=
  quarticOfPlanes 1 2 3 4

def quarticRepresentative : Fin 4 → QuarticMonomial
  | 0 => quarticPureFourth
  | 1 => quarticAdjacentSquares
  | 2 => quarticOppositeSquares
  | 3 => quarticRectangleProduct

def InSignedOrbit (representative monomial : QuarticMonomial) : Prop :=
  ∃ h : Hypercubic4, representative.act h = monomial

def HasNegativeStabilizer (monomial : QuarticMonomial) : Prop :=
  ∃ h : Hypercubic4,
    monomial.act h = monomial ∧ monomial.tensorSign h = -1

/-- A transparent enumeration of the 24 unsigned coordinate permutations.
Both directions are literal four-entry tables, so certificate checking does not
invoke choice or search for an inverse. -/
def permutationCode : Fin 24 → Equiv.Perm Axis
  | 0 =>
      { toFun := ![0, 1, 2, 3]
        invFun := ![0, 1, 2, 3]
        left_inv := by decide
        right_inv := by decide }
  | 1 =>
      { toFun := ![0, 1, 3, 2]
        invFun := ![0, 1, 3, 2]
        left_inv := by decide
        right_inv := by decide }
  | 2 =>
      { toFun := ![0, 2, 1, 3]
        invFun := ![0, 2, 1, 3]
        left_inv := by decide
        right_inv := by decide }
  | 3 =>
      { toFun := ![0, 2, 3, 1]
        invFun := ![0, 3, 1, 2]
        left_inv := by decide
        right_inv := by decide }
  | 4 =>
      { toFun := ![0, 3, 1, 2]
        invFun := ![0, 2, 3, 1]
        left_inv := by decide
        right_inv := by decide }
  | 5 =>
      { toFun := ![0, 3, 2, 1]
        invFun := ![0, 3, 2, 1]
        left_inv := by decide
        right_inv := by decide }
  | 6 =>
      { toFun := ![1, 0, 2, 3]
        invFun := ![1, 0, 2, 3]
        left_inv := by decide
        right_inv := by decide }
  | 7 =>
      { toFun := ![1, 0, 3, 2]
        invFun := ![1, 0, 3, 2]
        left_inv := by decide
        right_inv := by decide }
  | 8 =>
      { toFun := ![1, 2, 0, 3]
        invFun := ![2, 0, 1, 3]
        left_inv := by decide
        right_inv := by decide }
  | 9 =>
      { toFun := ![1, 2, 3, 0]
        invFun := ![3, 0, 1, 2]
        left_inv := by decide
        right_inv := by decide }
  | 10 =>
      { toFun := ![1, 3, 0, 2]
        invFun := ![2, 0, 3, 1]
        left_inv := by decide
        right_inv := by decide }
  | 11 =>
      { toFun := ![1, 3, 2, 0]
        invFun := ![3, 0, 2, 1]
        left_inv := by decide
        right_inv := by decide }
  | 12 =>
      { toFun := ![2, 0, 1, 3]
        invFun := ![1, 2, 0, 3]
        left_inv := by decide
        right_inv := by decide }
  | 13 =>
      { toFun := ![2, 0, 3, 1]
        invFun := ![1, 3, 0, 2]
        left_inv := by decide
        right_inv := by decide }
  | 14 =>
      { toFun := ![2, 1, 0, 3]
        invFun := ![2, 1, 0, 3]
        left_inv := by decide
        right_inv := by decide }
  | 15 =>
      { toFun := ![2, 1, 3, 0]
        invFun := ![3, 1, 0, 2]
        left_inv := by decide
        right_inv := by decide }
  | 16 =>
      { toFun := ![2, 3, 0, 1]
        invFun := ![2, 3, 0, 1]
        left_inv := by decide
        right_inv := by decide }
  | 17 =>
      { toFun := ![2, 3, 1, 0]
        invFun := ![3, 2, 0, 1]
        left_inv := by decide
        right_inv := by decide }
  | 18 =>
      { toFun := ![3, 0, 1, 2]
        invFun := ![1, 2, 3, 0]
        left_inv := by decide
        right_inv := by decide }
  | 19 =>
      { toFun := ![3, 0, 2, 1]
        invFun := ![1, 3, 2, 0]
        left_inv := by decide
        right_inv := by decide }
  | 20 =>
      { toFun := ![3, 1, 0, 2]
        invFun := ![2, 1, 3, 0]
        left_inv := by decide
        right_inv := by decide }
  | 21 =>
      { toFun := ![3, 1, 2, 0]
        invFun := ![3, 1, 2, 0]
        left_inv := by decide
        right_inv := by decide }
  | 22 =>
      { toFun := ![3, 2, 0, 1]
        invFun := ![2, 3, 1, 0]
        left_inv := by decide
        right_inv := by decide }
  | 23 =>
      { toFun := ![3, 2, 1, 0]
        invFun := ![3, 2, 1, 0]
        left_inv := by decide
        right_inv := by decide }
  | _ => Equiv.refl Axis

/-- Reflection mask; bit i records reflection of source axis i. -/
def reflectionCode (mask : Fin 16) (axis : Axis) : Bool :=
  mask.1.testBit axis.1

/-- Decode the compact signed-permutation witness carried by a certificate. -/
def decodeHypercubic (permutation : Fin 24)
    (reflectionMask : Fin 16) : Hypercubic4 where
  perm := permutationCode permutation
  reflected := reflectionCode reflectionMask

/-- Sparse certificate attached to one quartic monomial.  An admissible
certificate gives a representative and one transporter.  A killed certificate
gives one negative stabilizer. -/
inductive QuarticCertificate where
  | orbit (coordinate : Fin 4) (permutation : Fin 24)
      (reflectionMask : Fin 16)
  | killed (permutation : Fin 24) (reflectionMask : Fin 16)
deriving DecidableEq

def QuarticCertificate.Valid (monomial : QuarticMonomial) :
    QuarticCertificate → Prop
  | .orbit coordinate permutation reflectionMask =>
      (quarticRepresentative coordinate).act
          (decodeHypercubic permutation reflectionMask) = monomial
  | .killed permutation reflectionMask =>
      monomial.act (decodeHypercubic permutation reflectionMask) = monomial ∧
        monomial.tensorSign
          (decodeHypercubic permutation reflectionMask) = -1

instance QuarticCertificate.instDecidableValid
    (monomial : QuarticMonomial) (certificate : QuarticCertificate) :
    Decidable (certificate.Valid monomial) := by
  cases certificate <;> unfold QuarticCertificate.Valid <;> infer_instance

end V14HypercubicQuarticCensus
end YangMills
end QuantumTheory
end Mettapedia
