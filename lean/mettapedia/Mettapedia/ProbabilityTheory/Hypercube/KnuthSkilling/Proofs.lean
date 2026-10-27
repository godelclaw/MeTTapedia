import Mettapedia.ProbabilityTheory.Common.OrderedCombination
import Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets
import Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.ToyFreeMonoid2

/-!
# Representations, shrinking intervals and a toy diagram

The algebraic statements and interval theorem have independent hypotheses.
The final three-vertex graph is an authored diagram: its edges supply no model
translations. In particular, its reachability facts do not construct an additive
representation or a probability measure.
-/

set_option autoImplicit false
namespace Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Proofs

open _root_.KnuthSkilling _root_.KnuthSkilling.KnuthSkillingAlgebraBase
open _root_.KnuthSkilling.Additive
open Mettapedia.ProbabilityTheory.OrderedCombination
open Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets

/-- An associative operation with a witnessed failure of commutativity. -/
structure NoncommutativeModel (α : Type*) where
  op : α → α → α
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  noncomm : ∃ x y, op x y ≠ op y x

/-- A commutative interval-valued algebra, without a representation claim. -/
structure CommutativeCredalModel (α : Type*) where
  credal : CredalAlgebra α
  comm : ∀ x y, credal.op x y = credal.op y x

/-- A supplied canonical ordered representation, without event-measure structure. -/
structure RepresentedModel (α : Type*) where
  algebra : KnuthSkillingMonoidBase α
  representation : @NormalizedRepresentationResult α algebra

def freeMonoidModel : NoncommutativeModel ToyFreeMonoid2.FreeMonoid2 where
  op := ToyFreeMonoid2.op
  assoc := ToyFreeMonoid2.op_assoc
  noncomm := ⟨ToyFreeMonoid2.genA, ToyFreeMonoid2.genB, ToyFreeMonoid2.op_not_comm⟩

/-- Conditional commutativity; representation existence is a separate theorem. -/
theorem commutativity_from_representation
    {α : Type*} [inst : KnuthSkillingAlgebra α] (Θ : α → ℝ)
    (horder : ∀ x y, x ≤ y ↔ Θ x ≤ Θ y)
    (hadd : ∀ x y, Θ (inst.op x y) = Θ x + Θ y) :
    ∀ x y, inst.op x y = inst.op y x :=
  commutative_of_representation ⟨Θ, horder, hadd⟩

/-- Bounds, nesting and vanishing width are supplied by `RefinedCredalAlgebra`. -/
theorem path2_intervals_collapse_to_points {α : Type*} (R : RefinedCredalAlgebra α) :
    ∃ Θ : α → ℝ, ∀ x n, (R.μ n x).lower ≤ Θ x ∧ Θ x ≤ (R.μ n x).upper :=
  collapse_theorem R

/-- Labels of an authored diagram; they carry no semantic model data. -/
inductive ToyPathVertex where
  | V0 | V2 | V3
  deriving DecidableEq, Repr

/-- The two stipulated edges are not interpretations between model categories. -/
inductive ToyPathEdge : ToyPathVertex → ToyPathVertex → Prop where
  | first : ToyPathEdge .V0 .V2
  | second : ToyPathEdge .V2 .V3

def toyPathGraph : ToyPathVertex → ToyPathVertex → Prop := ToyPathEdge

def toyPath : ToyPathVertex → ToyPathVertex → Prop := Relation.ReflTransGen toyPathGraph

theorem toy_first_edge : ToyPathEdge .V0 .V2 := .first

theorem toy_second_edge : ToyPathEdge .V2 .V3 := .second

theorem toy_no_direct_edge : ¬ToyPathEdge .V0 .V3 := by intro h; cases h

theorem toy_composite_path : toyPath .V0 .V3 :=
  Relation.ReflTransGen.head ToyPathEdge.first
    (Relation.ReflTransGen.head ToyPathEdge.second Relation.ReflTransGen.refl)

/-- Associativity alone cannot yield commutativity, even with an identity. -/
theorem commutativity_not_from_associativity_alone :
    ∃ (α : Type) (op : α → α → α),
      (∀ x y z, op (op x y) z = op x (op y z)) ∧ (∃ x y, op x y ≠ op y x) :=
  ⟨ToyFreeMonoid2.FreeMonoid2, ToyFreeMonoid2.op, ToyFreeMonoid2.op_assoc,
    ToyFreeMonoid2.genA, ToyFreeMonoid2.genB, ToyFreeMonoid2.op_not_comm⟩

/-- This conclusion requires a supplied representation, rather than graph reachability. -/
theorem commutative_of_exists_representation {α : Type*} [KSSemigroupBase α]
    (h : ∃ Θ : α → ℝ, (∀ x y, x ≤ y ↔ Θ x ≤ Θ y) ∧
      ∀ x y, Θ (KSSemigroupBase.op x y) = Θ x + Θ y) :
    ∀ x y : α, KSSemigroupBase.op x y = KSSemigroupBase.op y x := by
  obtain ⟨Θ, horder, hadd⟩ := h
  exact commutative_of_representation ⟨Θ, horder, hadd⟩

end Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Proofs
