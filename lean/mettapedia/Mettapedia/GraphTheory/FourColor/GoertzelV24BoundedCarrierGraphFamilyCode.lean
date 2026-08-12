import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Finite codes for graph families on one bounded carrier

A finite transfer morphism usually carries several relations on the same
local vertices.  Coding the support of each relation independently loses the
common coordinate system and also drops distinguished boundary vertices when
they are isolated in one relation.  This module instead transports a whole
family of ambient graphs through one bounded finite carrier and retains a
fixed family of named points.

The construction is generic finite-graph bookkeeping.  It does not assert
that a corridor profile determines the carrier, its graph family, or its
distinguished points.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BoundedCarrierGraphFamilyCode

universe u v

noncomputable section

/-- A family of finite graphs sharing one carrier of size at most `bound`,
with `pointCount` distinguished coordinates retained in that carrier. -/
structure BoundedCarrierGraphFamilyCode
    (bound pointCount : Nat) (Family : Type u) where
  vertexCount : Fin (bound + 1)
  point : Fin pointCount → Fin vertexCount.val
  graph : Family → SimpleGraph (Fin vertexCount.val)

instance (bound pointCount : Nat) (Family : Type u) :
    DecidableEq (BoundedCarrierGraphFamilyCode bound pointCount Family) :=
  Classical.decEq _

private def boundedCarrierGraphFamilyCodeEquiv
    (bound pointCount : Nat) (Family : Type u) :
    BoundedCarrierGraphFamilyCode bound pointCount Family ≃
      Σ vertexCount : Fin (bound + 1),
        (Fin pointCount → Fin vertexCount.val) ×
          (Family → SimpleGraph (Fin vertexCount.val)) where
  toFun code := ⟨code.vertexCount, code.point, code.graph⟩
  invFun code := ⟨code.1, code.2.1, code.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (bound pointCount : Nat) (Family : Type u)
    [Fintype Family] [DecidableEq Family] :
    Fintype (BoundedCarrierGraphFamilyCode bound pointCount Family) :=
  Fintype.ofEquiv _
    (boundedCarrierGraphFamilyCodeEquiv bound pointCount Family).symm

/-- Canonical finite coordinates on every element of one finite carrier. -/
noncomputable def carrierCoordinate
    {Vertex : Type v} [Fintype Vertex]
    (carrier : Finset Vertex) :
    {vertex // vertex ∈ carrier} ≃ Fin carrier.card :=
  (Fintype.equivFin _).trans (finCongr (Fintype.card_coe carrier))

/-- Transport a family of ambient graphs to one common bounded carrier.
Edges leaving `carrier` are deliberately absent; exactness for a particular
application is supplied by proving that the relevant graph supports lie in
the carrier. -/
noncomputable def boundedCarrierGraphFamilyCode
    {Vertex : Type v} [Fintype Vertex]
    {Family : Type u}
    (carrier : Finset Vertex) (bound pointCount : Nat)
    (hcard : carrier.card ≤ bound)
    (points : Fin pointCount → {vertex // vertex ∈ carrier})
    (graphs : Family → SimpleGraph Vertex) :
    BoundedCarrierGraphFamilyCode bound pointCount Family where
  vertexCount :=
    ⟨carrier.card, Nat.lt_succ_of_le hcard⟩
  point := fun index => carrierCoordinate carrier (points index)
  graph := fun family =>
    ((graphs family).induce (carrier : Set Vertex)).map
      (carrierCoordinate carrier).toEmbedding

/-- The common carrier size stored in the code is its literal cardinality. -/
theorem boundedCarrierGraphFamilyCode_vertexCount_eq_card
    {Vertex : Type v} [Fintype Vertex]
    {Family : Type u}
    (carrier : Finset Vertex) (bound pointCount : Nat)
    (hcard : carrier.card ≤ bound)
    (points : Fin pointCount → {vertex // vertex ∈ carrier})
    (graphs : Family → SimpleGraph Vertex) :
    (boundedCarrierGraphFamilyCode carrier bound pointCount hcard points graphs).vertexCount.val =
      carrier.card := by
  rfl

/-- A named ambient point is transported by the same coordinate equivalence
as every graph in the family. -/
theorem boundedCarrierGraphFamilyCode_point
    {Vertex : Type v} [Fintype Vertex]
    {Family : Type u}
    (carrier : Finset Vertex) (bound pointCount : Nat)
    (hcard : carrier.card ≤ bound)
    (points : Fin pointCount → {vertex // vertex ∈ carrier})
    (graphs : Family → SimpleGraph Vertex) (index : Fin pointCount) :
    (boundedCarrierGraphFamilyCode carrier bound pointCount hcard points graphs).point index =
      carrierCoordinate carrier (points index) := by
  rfl

/-- Adjacency of carrier vertices is represented exactly in every coded
family member. -/
theorem boundedCarrierGraphFamilyCode_adj_iff
    {Vertex : Type v} [Fintype Vertex]
    {Family : Type u}
    (carrier : Finset Vertex) (bound pointCount : Nat)
    (hcard : carrier.card ≤ bound)
    (points : Fin pointCount → {vertex // vertex ∈ carrier})
    (graphs : Family → SimpleGraph Vertex)
    (family : Family) (first second : {vertex // vertex ∈ carrier}) :
    ((boundedCarrierGraphFamilyCode carrier bound pointCount hcard points graphs).graph family).Adj
          (carrierCoordinate carrier first)
          (carrierCoordinate carrier second) ↔
      (graphs family).Adj first.1 second.1 := by
  change
    (((graphs family).induce (carrier : Set Vertex)).map
      (carrierCoordinate carrier).toEmbedding).Adj
        ((carrierCoordinate carrier).toEmbedding first)
        ((carrierCoordinate carrier).toEmbedding second) ↔ _
  rw [SimpleGraph.map_adj_apply]
  rfl

/-- Reachability wholly inside the common carrier is represented exactly in
every coded family member. -/
theorem boundedCarrierGraphFamilyCode_reachable_iff
    {Vertex : Type v} [Fintype Vertex]
    {Family : Type u}
    (carrier : Finset Vertex) (bound pointCount : Nat)
    (hcard : carrier.card ≤ bound)
    (points : Fin pointCount → {vertex // vertex ∈ carrier})
    (graphs : Family → SimpleGraph Vertex)
    (family : Family) (first second : {vertex // vertex ∈ carrier}) :
    ((boundedCarrierGraphFamilyCode carrier bound pointCount hcard points graphs).graph family).Reachable
          (carrierCoordinate carrier first)
          (carrierCoordinate carrier second) ↔
      ((graphs family).induce (carrier : Set Vertex)).Reachable first second := by
  exact SimpleGraph.Iso.reachable_iff
    (φ := SimpleGraph.Iso.map (carrierCoordinate carrier)
      ((graphs family).induce (carrier : Set Vertex)))

end

end GoertzelV24BoundedCarrierGraphFamilyCode

end Mettapedia.GraphTheory.FourColor
