import Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFace
import Mettapedia.GraphTheory.FourColor.GoertzelV24ThetaPresentationCounterexample

/-!
# A literal parallel-edge consumer of spanning-face calibration

The spherical theta source has two vertices and three distinct edges. Its
actual face touches both vertices. Every target Tait witness therefore
calibrates to a genuine source witness while preserving all three cross
edges. The geometric instance and one input witness establish nonvacuity;
the generic calibration proof does not depend on this fixture.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFaceExample

open GoertzelV24ThetaPresentationCounterexample
open GoertzelV24OrbitFaceTwoSided DualTruncateColoring

noncomputable section

abbrev source := thetaRotationSystem

theorem twoSided : OrbitFacesTwoSided source := by
  have hnot : ∀ dart : source.D, ¬source.phi.SameCycle dart (source.alpha dart) := by
    decide +kernel
  intro dart heq
  exact hnot dart (Quotient.exact heq)

/-- Recognition uses only actual vertex incidence and face traversal. -/
def face : DualTruncateSpanningFace.SpanningFace source where
  seed := .firstLeft
  covers := by
    intro vertex
    cases vertex
    · exact ⟨.firstLeft, rfl, Equiv.Perm.SameCycle.refl _ _⟩
    · refine ⟨.thirdRight, rfl, ?_⟩
      refine ⟨1, ?_⟩
      simpa only [zpow_one] using
        (show source.phi ThetaDart.firstLeft = ThetaDart.thirdRight from rfl)

def inputSource : ThreeVertexColoring source where
  colour vertex := match vertex with | .left => red | .right => blue
  nonzero := by intro vertex; cases vertex <;> decide
  proper := by intro dart; cases dart <;> decide

abbrev input := colouring source inputSource
theorem input_tait : (rotation source).IsTaitEdgeColoring input := colouring_nonzero source inputSource

/-- The same argument applies to every target colouring, not only the
displayed input or one choice of the three cross-edge values. -/
def calibrate (c : (rotation source).EdgeColoring Color)
    (hc : (rotation source).IsTaitEdgeColoring c) : ThreeVertexColoring source :=
  DualTruncateSpanningFace.sourceColouring source thetaSpherical twoSided
    theta_primalConnected theta_vertexRotationCyclic c hc face

theorem all_cross_preserved (c : (rotation source).EdgeColoring Color)
    (hc : (rotation source).IsTaitEdgeColoring c) (edge : ThetaEdge) :
    colouring source (calibrate c hc) (.inl edge) = c (.inl edge) :=
  DualTruncateSpanningFace.preserves_cross source thetaSpherical twoSided
    theta_primalConnected theta_vertexRotationCyclic c hc face edge

theorem nonvacuous_input :
    ∃ c : (rotation source).EdgeColoring Color,
      ∃ hc : (rotation source).IsTaitEdgeColoring c,
        ∀ edge, colouring source (calibrate c hc) (.inl edge) = c (.inl edge) := by
  refine ⟨input, input_tait, ?_⟩
  intro edge
  exact all_cross_preserved input input_tait edge

end
end Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFaceExample
