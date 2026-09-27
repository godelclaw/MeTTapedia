import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

namespace Mettapedia.GraphTheory.FourColor

open scoped BigOperators

noncomputable section

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- The rotation-system edges crossing a finite vertex side, computed by
requiring exactly one of the edge's two endpoints to lie in the side. This
definition retains parallel edges because its carrier is the abstract edge
type `E`, not a `SimpleGraph` edge set. -/
def vertexSideEdgeBoundary (side : Finset V) : Finset E :=
  Finset.univ.filter fun e => (RS.endpoints e ∩ side).card = 1

@[simp]
theorem mem_vertexSideEdgeBoundary_iff {side : Finset V} {e : E} :
    e ∈ RS.vertexSideEdgeBoundary side ↔
      (RS.endpoints e ∩ side).card = 1 := by
  simp [vertexSideEdgeBoundary]

/-- Double-counting incidence over a vertex side: an edge color occurs once
for each endpoint of that edge lying in the side. -/
theorem sum_vertexColorSum_eq_sum_endpointMultiplicity
    (C : E → Color) (side : Finset V) :
    ∑ v ∈ side, RS.vertexColorSum C v =
      ∑ e : E, (RS.endpoints e ∩ side).card • C e := by
  classical
  unfold vertexColorSum
  calc
    ∑ v ∈ side, ∑ e ∈ RS.incidentEdges v, C e =
        ∑ v ∈ side, ∑ e : E, if e ∈ RS.incidentEdges v then C e else 0 := by
          apply Finset.sum_congr rfl
          intro v _hv
          rw [← Finset.sum_filter]
          have hfilter :
              (Finset.univ.filter fun e : E => e ∈ RS.incidentEdges v) =
                RS.incidentEdges v := by
            ext e
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hfilter]
    _ = ∑ e : E, ∑ v ∈ side, if e ∈ RS.incidentEdges v then C e else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ e : E, (RS.endpoints e ∩ side).card • C e := by
          apply Finset.sum_congr rfl
          intro e _he
          rw [← Finset.sum_filter]
          have hfilter :
              side.filter (fun v => e ∈ RS.incidentEdges v) =
                side ∩ RS.endpoints e := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_inter]
            rw [← RS.mem_endpoints_iff_mem_incidentEdges]
          rw [hfilter, Finset.sum_const, Finset.inter_comm]

/-- In `V₄`, the twice-counted internal edges cancel, so the endpoint
multiplicity sum is exactly the sum over edges crossing the vertex side. -/
theorem sum_endpointMultiplicity_eq_sum_vertexSideEdgeBoundary
    (C : E → Color) (side : Finset V) :
    ∑ e : E, (RS.endpoints e ∩ side).card • C e =
      ∑ e ∈ RS.vertexSideEdgeBoundary side, C e := by
  classical
  calc
    ∑ e : E, (RS.endpoints e ∩ side).card • C e =
        ∑ e : E, if e ∈ RS.vertexSideEdgeBoundary side then C e else 0 := by
          apply Finset.sum_congr rfl
          intro e _he
          by_cases hcross : (RS.endpoints e ∩ side).card = 1
          · simp [hcross]
          · have hle : (RS.endpoints e ∩ side).card ≤ 2 := by
              calc
                (RS.endpoints e ∩ side).card ≤ (RS.endpoints e).card :=
                  Finset.card_le_card Finset.inter_subset_left
                _ = 2 := RS.endpoints_card_two e
            have hzero_or_two :
                (RS.endpoints e ∩ side).card = 0 ∨
                  (RS.endpoints e ∩ side).card = 2 := by
              omega
            rcases hzero_or_two with hzero | htwo
            · simp [hzero]
            · rw [nsmul_even_eq_zero (c := C e)
                (n := (RS.endpoints e ∩ side).card) ⟨1, htwo⟩]
              simp [htwo]
    _ = ∑ e ∈ RS.vertexSideEdgeBoundary side, C e := by
          rw [← Finset.sum_filter]
          have hfilter :
              (Finset.univ.filter fun e : E =>
                e ∈ RS.vertexSideEdgeBoundary side) =
                  RS.vertexSideEdgeBoundary side := by
            ext e
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hfilter]

/-- A `V₄` Kirchhoff law at the vertices of a side forces the sum of the
colors crossing that side to vanish. -/
theorem vertexSideEdgeBoundary_colorSum_eq_zero
    (C : E → Color) (side : Finset V)
    (hflow : ∀ v ∈ side, RS.vertexColorSum C v = 0) :
    ∑ e ∈ RS.vertexSideEdgeBoundary side, C e = 0 := by
  rw [← RS.sum_endpointMultiplicity_eq_sum_vertexSideEdgeBoundary C side,
    ← RS.sum_vertexColorSum_eq_sum_endpointMultiplicity C side]
  exact Finset.sum_eq_zero fun v hv => by simp [hflow v hv]

/-- Rotation-system cut parity for a Tait coloring. Cubicity and proper
nonzero edge colors supply the vertex Kirchhoff law; no planarity or
no-parallel-edge assumption is used. -/
theorem vertexSideEdgeBoundary_colorSum_eq_zero_of_isTaitEdgeColoring
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) (side : Finset V) :
    ∑ e ∈ RS.vertexSideEdgeBoundary side, C e = 0 := by
  apply RS.vertexSideEdgeBoundary_colorSum_eq_zero C side
  intro v _hv
  exact RS.vertexColorSum_eq_zero_of_isCubic_of_isTaitEdgeColoring
    hCubic C hC v

/-- Two-edge-cut color equation: if the computed boundary of a vertex side
is exactly two distinct edges, every Tait coloring gives those edges the
same color. -/
theorem twoEdgeCut_colors_eq
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) (side : Finset V)
    {e f : E} (hne : e ≠ f)
    (hboundary : RS.vertexSideEdgeBoundary side = {e, f}) :
    C e = C f := by
  have hsum :=
    RS.vertexSideEdgeBoundary_colorSum_eq_zero_of_isTaitEdgeColoring
      hCubic C hC side
  rw [hboundary] at hsum
  simp only [Finset.sum_insert, Finset.mem_singleton, hne,
    not_false_eq_true, Finset.sum_singleton] at hsum
  exact (add_eq_zero_iff_eq (C e) (C f)).1 hsum

/-- Cardinality form of the two-edge-cut color equation, extracting the two
distinct cut edges and their forced common color. -/
theorem exists_twoEdgeCut_colors_eq
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) (side : Finset V)
    (hcard : (RS.vertexSideEdgeBoundary side).card = 2) :
    ∃ e f : E, e ≠ f ∧
      RS.vertexSideEdgeBoundary side = {e, f} ∧ C e = C f := by
  rcases Finset.card_eq_two.mp hcard with ⟨e, f, hne, hboundary⟩
  exact ⟨e, f, hne, hboundary,
    RS.twoEdgeCut_colors_eq hCubic C hC side hne hboundary⟩

end RotationSystem

end

end Mettapedia.GraphTheory.FourColor
