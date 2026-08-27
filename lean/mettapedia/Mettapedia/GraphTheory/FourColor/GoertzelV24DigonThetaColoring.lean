import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonFirstReturn
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# The theta case of a parallel pair

If the exterior edge at `v` returns to `u`, the third edges coincide and the
whole connected cubic map is the theta multigraph: two vertices joined by
three edges.  Three pairwise adjacent edges take the three nonzero colours, so
such a map is Tait colourable and can never be a counterexample.

This is the branch that digon suppression cannot handle — suppressing there
would leave a loop — and it is discharged here by exhibiting the colouring.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

open GoertzelV24FaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable section

namespace DigonPatchData

variable {RS : RotationSystem V E} (D : @DigonPatchData V E)

/-- In the theta case the two exterior edges are the same edge. -/
theorem outerV_eq_outerU_of_theta (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (htheta : D.vFar hD = D.u) : D.outerV = D.outerU := by
  have hmem : D.outerV ∈ RS.incidentEdges D.u :=
    RS.mem_incidentEdges_iff.2 ⟨D.b' hD, D.edgeOf_b' hD, htheta⟩
  rw [hD.2.2.1] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hedges := D.edges_v_pairwise_ne hD hCubic
  rcases hmem with h | h | h
  · exact h
  · exact absurd h hedges.1
  · exact absurd h hedges.2.1

/-- In the theta case the exterior edge at `u` also lands on `v`. -/
theorem uFar_eq_v_of_theta (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (htheta : D.vFar hD = D.u) : D.uFar hD = D.v := by
  have hd : D.a' hD ∈ RS.dartsOn D.outerV :=
    RS.mem_dartsOn.2 (by
      rw [D.edgeOf_a' hD, D.outerV_eq_outerU_of_theta hD hCubic htheta])
  have hq : D.qᵦ hD ∈ RS.dartsOn D.outerV :=
    RS.mem_dartsOn.2 (D.edgeOf_qᵦ hD)
  rw [RS.dartsOn_eq_pair_of_mem hq, D.alpha_qᵦ hD] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with h | h
  · change RS.vertOf (D.a' hD) = D.v
    rw [h]
    exact D.vertOf_qᵦ hD
  · exfalso
    apply D.uFar_ne_u hD
    change RS.vertOf (D.a' hD) = D.u
    rw [h]
    exact htheta

/-! ## The map is exactly the two digon vertices -/

theorem adj_step_of_theta (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (htheta : D.vFar hD = D.u) {x y : V} (hx : x = D.u ∨ x = D.v)
    (hadj : (rotationPrimalGraph RS).Adj x y) : y = D.u ∨ y = D.v := by
  obtain ⟨dart, hdx, hdy⟩ := hadj
  rcases hx with rfl | rfl
  · rcases D.eq_of_vertOf_eq_u hD hCubic hdx with rfl | rfl | rfl
    · exact Or.inr (by rw [← hdy, D.alpha_p₁ hD, D.vertOf_q₁ hD])
    · exact Or.inr (by rw [← hdy, D.alpha_p₂ hD, D.vertOf_q₂ hD])
    · exact Or.inr (by
        rw [← hdy, D.alpha_pₐ hD]
        exact D.uFar_eq_v_of_theta hD hCubic htheta)
  · rcases D.eq_of_vertOf_eq_v hD hCubic hdx with rfl | rfl | rfl
    · exact Or.inl (by rw [← hdy, D.alpha_q₁ hD, D.vertOf_p₁ hD])
    · exact Or.inl (by rw [← hdy, D.alpha_q₂ hD, D.vertOf_p₂ hD])
    · exact Or.inl (by rw [← hdy, D.alpha_qᵦ hD]; exact htheta)

theorem mem_pair_of_theta (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (htheta : D.vFar hD = D.u)
    (hconn : (rotationPrimalGraph RS).Connected)
    (vertex : V) : vertex = D.u ∨ vertex = D.v := by
  have hreach := hconn.preconnected D.u vertex
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact Or.inl rfl
  | tail _ hadj ih => exact D.adj_step_of_theta hD hCubic htheta ih hadj

/-- In the theta case there are exactly the three named edges. -/
theorem edge_eq_of_theta (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (htheta : D.vFar hD = D.u)
    (hconn : (rotationPrimalGraph RS).Connected)
    (edge : E) : edge = D.e ∨ edge = D.f ∨ edge = D.outerU := by
  obtain ⟨dart, hdart⟩ := RS.dartsOn_nonempty edge
  have hedge : RS.edgeOf dart = edge := RS.mem_dartsOn.1 hdart
  have hincident : edge ∈ RS.incidentEdges D.u ∨
      edge ∈ RS.incidentEdges D.v := by
    rcases D.mem_pair_of_theta hD hCubic htheta hconn (RS.vertOf dart) with
      hu | hv
    · exact Or.inl (RS.mem_incidentEdges_iff.2 ⟨dart, hedge, hu⟩)
    · exact Or.inr (RS.mem_incidentEdges_iff.2 ⟨dart, hedge, hv⟩)
  rcases D.eq_of_mem_incident hD hincident with h | h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inr
      (h.trans (D.outerV_eq_outerU_of_theta hD hCubic htheta)))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-! ## The theta map is Tait colourable -/

/-- The three-colouring of the theta map. -/
def thetaColor (edge : E) : Color :=
  if edge = D.e then red else if edge = D.f then blue else purple

/-- **A theta map is Tait colourable**, so a parallel pair whose exterior
edges coincide never occurs in a counterexample. -/
theorem taitColorable_of_theta (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (htheta : D.vFar hD = D.u)
    (hconn : (rotationPrimalGraph RS).Connected) :
    RotationSystemTaitColorable RS := by
  classical
  have hedges := D.edges_u_pairwise_ne hD hCubic
  have hcolor : ∀ edge : E,
      (edge = D.e ∧ D.thetaColor edge = red) ∨
        (edge = D.f ∧ D.thetaColor edge = blue) ∨
        (edge = D.outerU ∧ D.thetaColor edge = purple) := by
    intro edge
    rcases D.edge_eq_of_theta hD hCubic htheta hconn edge with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, by simp [thetaColor]⟩
    · exact Or.inr (Or.inl ⟨rfl, by simp [thetaColor, hedges.2.2.symm]⟩)
    · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      simp [thetaColor, hedges.1, hedges.2.1]
  refine ⟨SimpleGraph.Coloring.mk (D.thetaColor) ?_, ?_⟩
  · intro left right hadjacent
    have hne : left ≠ right := hadjacent.1
    rcases hcolor left with ⟨hl, hlc⟩ | ⟨hl, hlc⟩ | ⟨hl, hlc⟩ <;>
      rcases hcolor right with ⟨hr, hrc⟩ | ⟨hr, hrc⟩ | ⟨hr, hrc⟩ <;>
      first
        | (exact absurd (hl.trans hr.symm) hne)
        | (rw [hlc, hrc]; decide)
  · intro edge
    show D.thetaColor edge ≠ 0
    rcases hcolor edge with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ <;> rw [hc] <;> decide

end DigonPatchData

end

end RotationSystem

end Mettapedia.GraphTheory.FourColor
