import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# The coloring half of digon suppression

Suppressing a digon is an exact two-edge-cut cap: the side containing the
two digon vertices has two vertices, and the complementary cap is the graph
obtained by replacing the two exterior edges by one edge.  This file proves
the coloring statement without appealing to a picture.

The only fact needed about the digon side is its cardinality.  Any cubic
rotation system on two vertices has three edges, so assigning its edges
bijectively to the three nonzero Tait colors gives a Tait coloring.  The
already-proved two-edge-cut gluing theorem then shows that an uncolorable
ambient map has an uncolorable complementary cap.

This is deliberately only the coloring half of normalization.  Producing the
exact cut data from a parallel pair, and proving that the complementary cap
stays in the spherical structural class, are separate geometric statements.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DigonSuppressionColor

open GoertzelV24TwoEdgeCutMinimality

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- There are exactly three nonzero colors in `F₂²`. -/
theorem card_nonzeroColor :
    Fintype.card {color : Color // color ≠ 0} = 3 := by
  have hcolor : Fintype.card Color = 4 := by decide
  rw [Fintype.card_subtype_compl (fun color : Color => color = 0),
    Fintype.card_subtype_eq, hcolor]

/-- A cubic rotation system on two vertices has exactly three edges. -/
theorem card_edges_eq_three_of_card_vertices_two
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hvertices : Fintype.card V = 2) :
    Fintype.card E = 3 := by
  have hdartsVertices :=
    RS.card_darts_eq_three_times_card_vertices hcubic
  have hdartsEdges := RS.card_darts_eq_twice_card_edges
  omega

/-- Canonically choose a bijection from the three edges of a two-vertex
cubic rotation system to the three nonzero Tait colors. -/
def edgeEquivNonzeroColor
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hvertices : Fintype.card V = 2) :
    E ≃ {color : Color // color ≠ 0} :=
  Fintype.equivOfCardEq
    ((card_edges_eq_three_of_card_vertices_two RS hcubic hvertices).trans
      card_nonzeroColor.symm)

/-- Color the three edges of a two-vertex cubic rotation system by the three
different nonzero colors. -/
def twoVertexCubicColoring
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hvertices : Fintype.card V = 2) :
    RS.EdgeColoring Color :=
  SimpleGraph.Coloring.mk
    (fun edge => (edgeEquivNonzeroColor RS hcubic hvertices edge).1) <| by
      intro left right _hadjacent heq
      apply _hadjacent.ne
      apply (edgeEquivNonzeroColor RS hcubic hvertices).injective
      exact Subtype.ext heq

/-- The canonical three-edge coloring is a Tait coloring. -/
theorem twoVertexCubicColoring_isTait
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hvertices : Fintype.card V = 2) :
    RS.IsTaitEdgeColoring
      (twoVertexCubicColoring RS hcubic hvertices) := by
  intro edge
  exact (edgeEquivNonzeroColor RS hcubic hvertices edge).2

/-- Every cubic rotation system on exactly two vertices is Tait colorable.
No planarity, connectedness, or rotation hypothesis is needed. -/
theorem rotationSystemTaitColorable_of_card_vertices_two
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hvertices : Fintype.card V = 2) :
    RotationSystemTaitColorable RS :=
  ⟨twoVertexCubicColoring RS hcubic hvertices,
    twoVertexCubicColoring_isTait RS hcubic hvertices⟩

namespace RotationSystem.TwoEdgeCutPairData

variable {RS : RotationSystem V E} (data : RS.TwoEdgeCutPairData)

/-- The vertex carrier of the chosen cap has the cardinality of the chosen
finite side. -/
theorem card_sideCapVertex_eq_card_side :
    Fintype.card data.sideData.CapVertex = data.side.card := by
  rw [Fintype.card_subtype]
  simp [RotationSystem.TwoEdgeCutSideData.keep,
    RotationSystem.TwoEdgeCutPairData.sideData]

/-- If the chosen side of an exact two-edge cut consists of two vertices,
then its cap is the three-edge dipole and is Tait colorable. -/
theorem sideCap_taitColorable_of_card_two
    (hcubic : RS.IsCubic) (hside : data.side.card = 2) :
    RotationSystemTaitColorable data.sideData.capRotationSystem := by
  apply rotationSystemTaitColorable_of_card_vertices_two
  · exact data.sideCap_isCubic hcubic
  · rw [card_sideCapVertex_eq_card_side data, hside]

/-- **Coloring half of digon suppression.**  If the two-vertex side of an
exact two-edge cut is capped off, uncolorability of the ambient cubic map
forces uncolorability of the complementary cap.  Equivalently, every Tait
coloring of the suppressed map lifts through the digon. -/
theorem not_complementCap_taitColorable_of_not_ambient
    (hcubic : RS.IsCubic) (hside : data.side.card = 2)
    (hnot : ¬ RotationSystemTaitColorable RS) :
    ¬ RotationSystemTaitColorable data.complementData.capRotationSystem := by
  intro hcomplement
  apply hnot
  exact data.taitColorable_of_caps
    (sideCap_taitColorable_of_card_two data hcubic hside)
    hcomplement

end RotationSystem.TwoEdgeCutPairData

end

end GoertzelV24DigonSuppressionColor

end Mettapedia.GraphTheory.FourColor
