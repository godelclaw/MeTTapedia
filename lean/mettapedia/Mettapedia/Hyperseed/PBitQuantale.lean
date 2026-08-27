import Mettapedia.Algebra.QuantaleWeakness
import Mettapedia.CategoryTheory.FuzzyFrame

/-!
# The bounded Hyperseed p-bit quantale

This file formalizes the bounded evidence-pair core in Ben Goertzel's
*Hyperseed ontology: formal presentation and theoretical development* (2026).
It keeps positive support and counter-support as independent coordinates in
`[0,1]²`, including the four Belnap-style corners, evidence negation, the
evidence conjunction/disjunction operations, and the canonical commutative
quantale with componentwise joins and multiplication.

This bounded object is distinct from PLN's unbounded evidence-count carrier.
The latter can realize the same four corners, but an identification of the two
whole carriers would require an explicit normalization map and its laws.

The source presents material implication as one convenient, replaceable
choice.  It is intentionally not made part of this algebraic core.
-/

set_option autoImplicit false

namespace Mettapedia.Hyperseed.PBitQuantale

open Mettapedia.CategoryTheory.FuzzyFrame
open Mettapedia.CategoryTheory.FuzzyFrame.UnitInterval
open Mettapedia.Algebra.QuantaleWeakness

/-- A bounded p-bit records independent positive and negative evidence. -/
abbrev PBit := 𝕀 × 𝕀

/-- Positive support. -/
def support (value : PBit) : 𝕀 := value.1

/-- Counter-support. -/
def opposition (value : PBit) : 𝕀 := value.2

/-- Net evidential bias, used only as a readout of the informative pair. -/
def bias (value : PBit) : ℝ := value.1.val - value.2.val

/-- Strength of the stronger evidential channel. -/
def determination (value : PBit) : 𝕀 := value.1 ⊔ value.2

/-- Simultaneous positive and negative evidence. -/
def conflict (value : PBit) : 𝕀 := value.1 ⊓ value.2

/-- Evidential negation swaps the two channels. -/
def neg (value : PBit) : PBit := (value.2, value.1)

/-- Conjunction needs support for both inputs and opposition to either. -/
def conjunction (left right : PBit) : PBit :=
  (left.1 ⊓ right.1, left.2 ⊔ right.2)

/-- Disjunction needs support for either input and opposition to both. -/
def disjunction (left right : PBit) : PBit :=
  (left.1 ⊔ right.1, left.2 ⊓ right.2)

/-- No evidence in either direction. -/
def neither : PBit := (0, 0)

/-- Positive evidence without counter-evidence. -/
def trueOnly : PBit := (1, 0)

/-- Counter-evidence without positive evidence. -/
def falseOnly : PBit := (0, 1)

/-- Maximal evidence in both directions. -/
def both : PBit := (1, 1)

@[simp] theorem neg_neg (value : PBit) : neg (neg value) = value := by
  cases value
  rfl

@[simp] theorem neg_trueOnly : neg trueOnly = falseOnly := rfl

@[simp] theorem neg_falseOnly : neg falseOnly = trueOnly := rfl

@[simp] theorem neg_neither : neg neither = neither := rfl

@[simp] theorem neg_both : neg both = both := rfl

/-- Conflict and ignorance remain different points of the carrier. -/
theorem both_ne_neither : both ≠ neither := by
  intro equality
  have first := congrArg Prod.fst equality
  have oneEqualsZero : (1 : 𝕀) = 0 := by
    simpa [both, neither] using first
  have realOneEqualsZero :=
    congrArg (fun value : 𝕀 => value.val) oneEqualsZero
  change (1 : ℝ) = 0 at realOneEqualsZero
  norm_num at realOneEqualsZero

/-- A fixed unit-interval multiplier is left adjoint to its product
residuum, hence preserves arbitrary joins. -/
noncomputable instance unitIntervalCommQuantale : IsCommQuantale 𝕀 :=
  IsCommQuantale.ofCommSemigroup fun fixed values => by
    let connection : GaloisConnection
        (fun value : 𝕀 => fixed * value)
        (productImp fixed) := fun left right =>
      product_residuation fixed left right
    exact connection.l_sSup

/-- The residual of the canonical componentwise p-bit tensor. -/
noncomputable def residual (left right : PBit) : PBit :=
  (productImp left.1 right.1, productImp left.2 right.2)

/-- Componentwise multiplication is left adjoint to the componentwise
residual. -/
theorem tensor_residuation (left middle right : PBit) :
    left * middle ≤ right ↔ middle ≤ residual left right := by
  change
    (left.1 * middle.1 ≤ right.1 ∧ left.2 * middle.2 ≤ right.2) ↔
      (middle.1 ≤ productImp left.1 right.1 ∧
        middle.2 ≤ productImp left.2 right.2)
  rw [product_residuation, product_residuation]

/-- The canonical bounded p-bit carrier is a commutative quantale under the
knowledge order, componentwise supremum, and componentwise multiplication. -/
noncomputable instance pBitCommQuantale : IsCommQuantale PBit :=
  IsCommQuantale.ofCommSemigroup fun fixed values => by
    let connection : GaloisConnection
        (fun value : PBit => fixed * value)
        (residual fixed) := fun left right =>
      tensor_residuation fixed left right
    exact connection.l_sSup

/-- The quantale unit is maximal evidence in both channels: it is a neutral
information-flow value, not a claim of classical truth. -/
theorem quantale_unit_eq_both : (1 : PBit) = both := rfl

/-- The lattice bottom is the no-evidence corner. -/
theorem lattice_bottom_eq_neither : (⊥ : PBit) = neither := rfl

/-- Quantale composition attenuates the two channels independently. -/
@[simp] theorem tensor_components (left right : PBit) :
    (left * right).1 = left.1 * right.1 ∧
      (left * right).2 = left.2 * right.2 := by
  exact ⟨rfl, rfl⟩

#print axioms Mettapedia.Hyperseed.PBitQuantale.neg_neg
#print axioms Mettapedia.Hyperseed.PBitQuantale.both_ne_neither
#print axioms Mettapedia.Hyperseed.PBitQuantale.tensor_residuation
#print axioms Mettapedia.Hyperseed.PBitQuantale.quantale_unit_eq_both

end Mettapedia.Hyperseed.PBitQuantale
