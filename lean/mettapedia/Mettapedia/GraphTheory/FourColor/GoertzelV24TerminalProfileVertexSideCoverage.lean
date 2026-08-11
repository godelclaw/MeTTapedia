import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileRegionalCoverage

/-!
# Terminal-profile coverage for an actual vertex-side cut

For a finite vertex side and its complement, the two induced regional edge
sets cover every ambient edge and overlap exactly on the crossing cut.  More
importantly, two adjacent edges share a vertex, so they belong together to at
least one of the two regional factors.  This is the literal geometric
coverage condition required by both coordinates of the relational terminal
profile update.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TerminalProfileVertexSideCoverage

open GoertzelV24FaceDualConnectedness
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileConnectivityUpdate
open GoertzelV24TerminalProfileFaceUpdate
open GoertzelV24TerminalProfileRegionalCoverage

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The regional edge sets induced by opposite vertex sides cover every
ambient edge. -/
theorem vertexSetRegionEdges_union_compl_eq_univ
    (RS : RotationSystem V E) (inside : Finset V) :
    vertexSetRegionEdges RS inside ∪ vertexSetRegionEdges RS insideᶜ =
      Finset.univ := by
  ext edge
  simp only [Finset.mem_union, Finset.mem_univ, iff_true,
    mem_vertexSetRegionEdges_iff, edgeMeetsVertexSet]
  have hpositive : 0 < (RS.endpoints edge).card := by
    rw [RS.endpoints_card_two]
    omega
  rcases Finset.card_pos.mp hpositive with ⟨vertex, hvertex⟩
  by_cases hinside : vertex ∈ inside
  · exact Or.inl ⟨vertex, hvertex, hinside⟩
  · exact Or.inr ⟨vertex, hvertex, by simpa using hinside⟩

/-- An edge lies in both opposite regional edge sets exactly when it crosses
the vertex cut. -/
theorem vertexSetRegionEdges_inter_compl_eq_crossingEdges
    (RS : RotationSystem V E) (inside : Finset V) :
    vertexSetRegionEdges RS inside ∩ vertexSetRegionEdges RS insideᶜ =
      vertexSetCrossingEdges RS inside := by
  ext edge
  simp only [Finset.mem_inter, mem_vertexSetRegionEdges_iff,
    mem_vertexSetCrossingEdges_iff, edgeMeetsVertexSet,
    edgeCrossesVertexSet]
  constructor
  · rintro ⟨⟨inner, hinnerEndpoint, hinner⟩,
      ⟨outer, houterEndpoint, houter⟩⟩
    exact ⟨inner, hinnerEndpoint, hinner,
      outer, houterEndpoint, by simpa using houter⟩
  · rintro ⟨inner, hinnerEndpoint, hinner,
      outer, houterEndpoint, houter⟩
    exact ⟨⟨inner, hinnerEndpoint, hinner⟩,
      ⟨outer, houterEndpoint, by simpa using houter⟩⟩

/-- At an actual vertex-side split, every adjacent edge pair retained by the
union lies wholly in one regional factor.  The union-membership hypotheses
are present to match the generic coverage interface; total coverage above
shows they are automatic here. -/
theorem regionalEdgeAdjacencyCovered_vertexSetRegionEdges_compl
    (RS : RotationSystem V E) (inside : Finset V) :
    RegionalEdgeAdjacencyCovered RS
      (vertexSetRegionEdges RS inside)
      (vertexSetRegionEdges RS insideᶜ) := by
  intro left right hadj _ _
  rcases hadj.2 with ⟨vertex, hleftEndpoint, hrightEndpoint⟩
  by_cases hinside : vertex ∈ inside
  · exact Or.inl ⟨
      (mem_vertexSetRegionEdges_iff RS inside left).2
        ⟨vertex, hleftEndpoint, hinside⟩,
      (mem_vertexSetRegionEdges_iff RS inside right).2
        ⟨vertex, hrightEndpoint, hinside⟩⟩
  · have houtside : vertex ∈ insideᶜ := by simpa using hinside
    exact Or.inr ⟨
      (mem_vertexSetRegionEdges_iff RS insideᶜ left).2
        ⟨vertex, hleftEndpoint, houtside⟩,
      (mem_vertexSetRegionEdges_iff RS insideᶜ right).2
        ⟨vertex, hrightEndpoint, houtside⟩⟩

/-- Concrete tracked-connectivity coverage for every coloring and tracked
color pair on the two sides of a vertex cut. -/
theorem regionalTrackedAdjacencyCovered_vertexSetRegionEdges_compl
    (RS : RotationSystem V E) (inside : Finset V)
    (C : E → Color) (a b : Color) :
    RegionalTrackedAdjacencyCovered RS
      (vertexSetRegionEdges RS inside)
      (vertexSetRegionEdges RS insideᶜ) C a b :=
  regionalTrackedAdjacencyCovered_of_edgeAdjacencyCovered RS
    (vertexSetRegionEdges RS inside)
    (vertexSetRegionEdges RS insideᶜ)
    (regionalEdgeAdjacencyCovered_vertexSetRegionEdges_compl RS inside)
    C a b

/-- Concrete occurrence-sensitive facial coverage for every face of the two
sides of a cubic cyclic rotation system. -/
theorem regionalFaceAdjacencyCovered_vertexSetRegionEdges_compl
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (inside : Finset V)
    (root : RS.D) :
    RegionalFaceAdjacencyCovered RS root
      (vertexSetRegionEdges RS inside)
      (vertexSetRegionEdges RS insideᶜ) :=
  regionalFaceAdjacencyCovered_of_edgeAdjacencyCovered RS hcubic hrotation
    (vertexSetRegionEdges RS inside)
    (vertexSetRegionEdges RS insideᶜ)
    (regionalEdgeAdjacencyCovered_vertexSetRegionEdges_compl RS inside)
    root

end

end GoertzelV24TerminalProfileVertexSideCoverage

end Mettapedia.GraphTheory.FourColor
