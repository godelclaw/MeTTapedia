import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierGraphFamilyCode

/-!
# Boolean reflection of a bounded graph family

`BoundedCarrierGraphFamilyCode` is the proof-facing finite carrier used by the
literal Cell construction.  Its graph family is proposition-valued.  This file
adds an explicit Boolean adjacency table on the same dependent carrier, so a
certificate generator and Lean's kernel can evaluate local reachability.

The reflection theorem is exact: reflecting a simple-graph family to Boolean
adjacency and rebuilding the graphs changes neither adjacency nor reachability.
This is finite computational infrastructure only; it does not define a source
alphabet, a reachable-state closure, or a base threshold.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BoundedCarrierBoolGraphFamilyCode

open GoertzelV24BoundedCarrierGraphFamilyCode

universe u

/-- A bounded common carrier whose graph family is stored as Boolean adjacency
tables.  `toGraph` below performs the harmless symmetrization and loop removal
required by `SimpleGraph`. -/
structure BoundedCarrierBoolGraphFamilyCode
    (bound pointCount : Nat) (Family : Type u) where
  vertexCount : Fin (bound + 1)
  point : Fin pointCount → Fin vertexCount.val
  adjacency : Family →
    Fin vertexCount.val → Fin vertexCount.val → Bool

private def boundedCarrierBoolGraphFamilyCodeEquiv
    (bound pointCount : Nat) (Family : Type u) :
    BoundedCarrierBoolGraphFamilyCode bound pointCount Family ≃
      Σ vertexCount : Fin (bound + 1),
        (Fin pointCount → Fin vertexCount.val) ×
          (Family → Fin vertexCount.val → Fin vertexCount.val → Bool) where
  toFun code := ⟨code.vertexCount, code.point, code.adjacency⟩
  invFun code := ⟨code.1, code.2.1, code.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (bound pointCount : Nat) (Family : Type u) :
    DecidableEq (BoundedCarrierBoolGraphFamilyCode bound pointCount Family) :=
  Classical.decEq _

instance (bound pointCount : Nat) (Family : Type u)
    [Fintype Family] [DecidableEq Family] :
    Fintype (BoundedCarrierBoolGraphFamilyCode bound pointCount Family) :=
  Fintype.ofEquiv _
    (boundedCarrierBoolGraphFamilyCodeEquiv bound pointCount Family).symm

/-- Interpret one Boolean table as an undirected loopless graph. -/
def BoundedCarrierBoolGraphFamilyCode.toGraph
    {bound pointCount : Nat} {Family : Type u}
    (code : BoundedCarrierBoolGraphFamilyCode bound pointCount Family)
    (family : Family) : SimpleGraph (Fin code.vertexCount.val) :=
  SimpleGraph.fromRel fun left right =>
    code.adjacency family left right = true

instance {bound pointCount : Nat} {Family : Type u}
    (code : BoundedCarrierBoolGraphFamilyCode bound pointCount Family)
    (family : Family) : DecidableRel (code.toGraph family).Adj :=
  fun left right => by
    change Decidable
      (left ≠ right ∧
        (code.adjacency family left right = true ∨
          code.adjacency family right left = true))
    infer_instance

/-- Executable component membership in one reflected local graph. -/
def BoundedCarrierBoolGraphFamilyCode.reachable
    {bound pointCount : Nat} {Family : Type u}
    (code : BoundedCarrierBoolGraphFamilyCode bound pointCount Family)
    (family : Family) (left right : Fin code.vertexCount.val) : Bool :=
  decide ((code.toGraph family).Reachable left right)

@[simp]
theorem BoundedCarrierBoolGraphFamilyCode.reachable_eq_true_iff
    {bound pointCount : Nat} {Family : Type u}
    (code : BoundedCarrierBoolGraphFamilyCode bound pointCount Family)
    (family : Family) (left right : Fin code.vertexCount.val) :
    code.reachable family left right = true ↔
      (code.toGraph family).Reachable left right := by
  simp only [BoundedCarrierBoolGraphFamilyCode.reachable,
    decide_eq_true_eq]

/-- Reflect a proof-facing graph family into an explicit Boolean table. -/
noncomputable def ofGraphFamilyCode
    {bound pointCount : Nat} {Family : Type u}
    (code : BoundedCarrierGraphFamilyCode bound pointCount Family) :
    BoundedCarrierBoolGraphFamilyCode bound pointCount Family where
  vertexCount := code.vertexCount
  point := code.point
  adjacency family left right := by
    classical
    exact decide ((code.graph family).Adj left right)

@[simp]
theorem ofGraphFamilyCode_vertexCount
    {bound pointCount : Nat} {Family : Type u}
    (code : BoundedCarrierGraphFamilyCode bound pointCount Family) :
    (ofGraphFamilyCode code).vertexCount = code.vertexCount :=
  rfl

@[simp]
theorem ofGraphFamilyCode_point
    {bound pointCount : Nat} {Family : Type u}
    (code : BoundedCarrierGraphFamilyCode bound pointCount Family) :
    (ofGraphFamilyCode code).point = code.point :=
  rfl

/-- Boolean reflection followed by graph reconstruction is literally the
original simple graph. -/
theorem ofGraphFamilyCode_toGraph
    {bound pointCount : Nat} {Family : Type u}
    (code : BoundedCarrierGraphFamilyCode bound pointCount Family)
    (family : Family) :
    (ofGraphFamilyCode code).toGraph family = code.graph family := by
  classical
  change (SimpleGraph.fromRel fun left right =>
      decide ((code.graph family).Adj left right) = true) = code.graph family
  ext left right
  simp only [SimpleGraph.fromRel_adj]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨(code.graph family).ne_of_adj h, Or.inl h⟩

/-- In particular, Boolean reflection preserves every local component
query exactly. -/
theorem ofGraphFamilyCode_reachable_iff
    {bound pointCount : Nat} {Family : Type u}
    (code : BoundedCarrierGraphFamilyCode bound pointCount Family)
    (family : Family) (left right : Fin code.vertexCount.val) :
    ((ofGraphFamilyCode code).toGraph family).Reachable left right ↔
      (code.graph family).Reachable left right := by
  rw [ofGraphFamilyCode_toGraph]
  rfl

/-- The executable Boolean query on a reflected proof-facing code is exact. -/
theorem ofGraphFamilyCode_reachable_eq_true_iff
    {bound pointCount : Nat} {Family : Type u}
    (code : BoundedCarrierGraphFamilyCode bound pointCount Family)
    (family : Family) (left right : Fin code.vertexCount.val) :
    (ofGraphFamilyCode code).reachable family left right = true ↔
      (code.graph family).Reachable left right := by
  rw [BoundedCarrierBoolGraphFamilyCode.reachable_eq_true_iff,
    ofGraphFamilyCode_reachable_iff]

end GoertzelV24BoundedCarrierBoolGraphFamilyCode

end Mettapedia.GraphTheory.FourColor
