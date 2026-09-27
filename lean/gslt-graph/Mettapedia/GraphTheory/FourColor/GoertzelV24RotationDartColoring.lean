import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

/-!
# Descending a dart coloring on a rotation system

A cut-open piece is naturally colored on darts before its edge colors are
assembled.  This small generic adapter records the elementary descent: an
alpha-invariant, locally proper dart coloring determines a proper edge
coloring of the original rotation system.  It is independent of any
configuration catalogue or covering-style reduction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationDartColoring

open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Choose one of the two darts of an edge. -/
def dartRepresentative (RS : RotationSystem V E) (edge : E) : RS.D :=
  Classical.choose (RS.dartsOn_nonempty edge)

/-- The chosen dart really lies on its named edge. -/
theorem dartRepresentative_mem_dartsOn
    (RS : RotationSystem V E) (edge : E) :
    dartRepresentative RS edge ∈ RS.dartsOn edge :=
  Classical.choose_spec (RS.dartsOn_nonempty edge)

/-- The chosen dart's edge is its named edge. -/
theorem edgeOf_dartRepresentative
    (RS : RotationSystem V E) (edge : E) :
    RS.edgeOf (dartRepresentative RS edge) = edge :=
  (RS.mem_dartsOn).1 (dartRepresentative_mem_dartsOn RS edge)

/-- Descend an alpha-invariant locally proper dart coloring to the original
edge carrier. -/
def edgeColoringOfDartColor
    (RS : RotationSystem V E) (dartColor : RS.D → Color)
    (hAlpha : ∀ dart, dartColor (RS.alpha dart) = dartColor dart)
    (hProper : ∀ {left right : RS.D},
      RS.vertOf left = RS.vertOf right → left ≠ right →
        dartColor left ≠ dartColor right) :
    RS.EdgeColoring Color :=
  SimpleGraph.Coloring.mk (fun edge => dartColor (dartRepresentative RS edge)) <| by
    intro leftEdge rightEdge hadjacent
    rcases (RS.edgeAdjacencyGraph_adj_iff).1 hadjacent with
      ⟨hedgeNe, vertex, hleftVertex, hrightVertex⟩
    rcases (RS.mem_endpoints_iff).1 hleftVertex with
      ⟨left, hleftDart, hleftAtVertex⟩
    rcases (RS.mem_endpoints_iff).1 hrightVertex with
      ⟨right, hrightDart, hrightAtVertex⟩
    have hleftEdge : RS.edgeOf left = leftEdge :=
      (RS.mem_dartsOn).1 hleftDart
    have hrightEdge : RS.edgeOf right = rightEdge :=
      (RS.mem_dartsOn).1 hrightDart
    have hleftColor :
        dartColor (dartRepresentative RS leftEdge) = dartColor left := by
      rcases RS.edge_fiber_two_cases
          (edgeOf_dartRepresentative RS leftEdge) hleftEdge with hsame | hopposite
      · exact congrArg dartColor hsame.symm
      · rw [hopposite]
        exact (hAlpha (dartRepresentative RS leftEdge)).symm
    have hrightColor :
        dartColor (dartRepresentative RS rightEdge) = dartColor right := by
      rcases RS.edge_fiber_two_cases
          (edgeOf_dartRepresentative RS rightEdge) hrightEdge with hsame | hopposite
      · exact congrArg dartColor hsame.symm
      · rw [hopposite]
        exact (hAlpha (dartRepresentative RS rightEdge)).symm
    rw [hleftColor, hrightColor]
    apply hProper
    · exact hleftAtVertex.trans hrightAtVertex.symm
    · intro hdarts
      apply hedgeNe
      rw [← hleftEdge, ← hrightEdge, hdarts]

/-- The descended edge coloring reads back the supplied dart color at either
dart of the original edge. -/
theorem edgeColoringOfDartColor_edgeOf
    (RS : RotationSystem V E) (dartColor : RS.D → Color)
    (hAlpha : ∀ dart, dartColor (RS.alpha dart) = dartColor dart)
    (hProper : ∀ {left right : RS.D},
      RS.vertOf left = RS.vertOf right → left ≠ right →
        dartColor left ≠ dartColor right)
    (dart : RS.D) :
    edgeColoringOfDartColor RS dartColor hAlpha hProper (RS.edgeOf dart) =
      dartColor dart := by
  change dartColor (dartRepresentative RS (RS.edgeOf dart)) = dartColor dart
  rcases RS.edge_fiber_two_cases (e := RS.edgeOf dart) (d := dart)
      (y := dartRepresentative RS (RS.edgeOf dart)) rfl
      (edgeOf_dartRepresentative RS (RS.edgeOf dart)) with hsame | hopposite
  · rw [hsame]
  · rw [hopposite]
    exact hAlpha dart

/-- Nonzero dart colors descend to a Tait edge coloring. -/
theorem edgeColoringOfDartColor_isTait
    (RS : RotationSystem V E) (dartColor : RS.D → Color)
    (hAlpha : ∀ dart, dartColor (RS.alpha dart) = dartColor dart)
    (hProper : ∀ {left right : RS.D},
      RS.vertOf left = RS.vertOf right → left ≠ right →
        dartColor left ≠ dartColor right)
    (hNonzero : ∀ dart, dartColor dart ≠ 0) :
    RS.IsTaitEdgeColoring (edgeColoringOfDartColor RS dartColor hAlpha hProper) := by
  intro edge
  change dartColor (dartRepresentative RS edge) ≠ 0
  exact hNonzero _

end

end GoertzelV24RotationDartColoring

end Mettapedia.GraphTheory.FourColor
