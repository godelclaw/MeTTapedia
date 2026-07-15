import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSpliceConstructor
import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationSpliceConstructor

variable {V D : Type*} [Fintype V] [DecidableEq V]
  [Fintype D] [DecidableEq D]

noncomputable section

namespace RewiredDartSystem

/-- A representative dart of a computed two-dart edge orbit. -/
def edgeRepresentative (data : RewiredDartSystem V D)
    (edge : data.Edge) : D :=
  Classical.choose edge.property

/-- The selected representative lies on the edge it represents. -/
theorem edge_eq_edgeOf_edgeRepresentative
    (data : RewiredDartSystem V D) (edge : data.Edge) :
    edge = data.edgeOf (data.edgeRepresentative edge) := by
  apply Subtype.ext
  exact Classical.choose_spec edge.property

/-- A dart coloring invariant under the rewired flip descends to the computed
edge orbits. -/
def descendedEdgeColor (data : RewiredDartSystem V D)
    (dartColor : D → Color) (edge : data.Edge) : Color :=
  dartColor (data.edgeRepresentative edge)

/-- The descended edge color can be read from either dart in its orbit. -/
theorem descendedEdgeColor_edgeOf
    (data : RewiredDartSystem V D) (dartColor : D → Color)
    (hAlpha : ∀ dart, dartColor (data.alpha dart) = dartColor dart)
    (dart : D) :
    data.descendedEdgeColor dartColor (data.edgeOf dart) = dartColor dart := by
  change dartColor (data.edgeRepresentative (data.edgeOf dart)) = dartColor dart
  have hedges :
      data.edgeOf (data.edgeRepresentative (data.edgeOf dart)) =
        data.edgeOf dart :=
    (data.edge_eq_edgeOf_edgeRepresentative (data.edgeOf dart)).symm
  rcases (data.edgeOf_eq_edgeOf_iff _ _).1 hedges with hsame | hopposite
  · exact congrArg dartColor hsame
  · rw [hopposite, hAlpha]

/-- Local properness on darts based at one vertex is sufficient to construct
a proper coloring of the computed edge-adjacency graph. -/
def descendedColoring (data : RewiredDartSystem V D)
    (dartColor : D → Color)
    (hAlpha : ∀ dart, dartColor (data.alpha dart) = dartColor dart)
    (hProper : ∀ {left right : D},
      data.vertOf left = data.vertOf right → left ≠ right →
        dartColor left ≠ dartColor right) :
    data.toRotationSystem.EdgeColoring Color :=
  SimpleGraph.Coloring.mk (data.descendedEdgeColor dartColor) <| by
    intro leftEdge rightEdge hadjacent
    rcases (data.toRotationSystem.edgeAdjacencyGraph_adj_iff).1 hadjacent with
      ⟨hedgeNe, vertex, hleftVertex, hrightVertex⟩
    rcases (data.toRotationSystem.mem_endpoints_iff).1 hleftVertex with
      ⟨leftDart, hleftDartEdge, hleftDartVertex⟩
    rcases (data.toRotationSystem.mem_endpoints_iff).1 hrightVertex with
      ⟨rightDart, hrightDartEdge, hrightDartVertex⟩
    have hleftEdge : data.edgeOf leftDart = leftEdge :=
      (data.toRotationSystem.mem_dartsOn).1 hleftDartEdge
    have hrightEdge : data.edgeOf rightDart = rightEdge :=
      (data.toRotationSystem.mem_dartsOn).1 hrightDartEdge
    have hdartNe : leftDart ≠ rightDart := by
      intro hdarts
      apply hedgeNe
      rw [← hleftEdge, ← hrightEdge, hdarts]
    rw [← hleftEdge, ← hrightEdge,
      data.descendedEdgeColor_edgeOf dartColor hAlpha,
      data.descendedEdgeColor_edgeOf dartColor hAlpha]
    apply hProper
    · exact hleftDartVertex.trans hrightDartVertex.symm
    · exact hdartNe

/-- Nonzero dart colors descend to a Tait edge coloring. -/
theorem descendedColoring_isTait
    (data : RewiredDartSystem V D)
    (dartColor : D → Color)
    (hAlpha : ∀ dart, dartColor (data.alpha dart) = dartColor dart)
    (hProper : ∀ {left right : D},
      data.vertOf left = data.vertOf right → left ≠ right →
        dartColor left ≠ dartColor right)
    (hNonzero : ∀ dart, dartColor dart ≠ 0) :
    data.toRotationSystem.IsTaitEdgeColoring
      (data.descendedColoring dartColor hAlpha hProper) := by
  intro edge
  exact hNonzero (data.edgeRepresentative edge)

end RewiredDartSystem

end

end GoertzelV24RotationSpliceConstructor

end Mettapedia.GraphTheory.FourColor
