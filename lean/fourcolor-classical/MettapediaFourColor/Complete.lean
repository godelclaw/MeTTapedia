import MettapediaFourColor.Orbit9Assembly
import FourColor.Present5
import FourColor.Present6
import FourColor.Present7
import FourColor.Present8
import MettapediaFourColor.DiamondFamilyReducibility

/-!
# The classical Four Colour theorem with compositional reconstruction

The reference supplies 632 reducibility certificates and four discharging
presentations. A joint boundary repair law supplies configuration 4.
Three presentations consume the shared charge bounds.
The minimal-counterexample argument rebuilds an actual colouring through
the GSLT witness relation. The resulting theorem colours finite plane
drawings and supplies compatible choices for exact source constructions.

The classical mathematics is due to Robertson, Sanders, Seymour and Thomas,
with the Gonthier/Werner formalization as realized in Chris Emery's Lean port.
All 633 configurations remain in this assembly.
-/

namespace FourColor.CompositionalComplete

/-- Match the complete certificate range to the decoded configuration list. -/
theorem theConfigs_length : theConfigs.length = 633 := by decide +kernel

/-- The catalogue range includes the independently proved joint diamond repair. -/
theorem reducibility : Reducibility := by
  unfold Reducibility
  rw [theConfigs_length]
  exact DiamondFamilyReducibility.reducible_all

theorem no_minimalCounterExample {D : Type} [Finite D] (G : Hypermap D) :
    ¬ G.MinimalCounterExample :=
  Orbit9Assembly.no_minimalCounterExample_of_checks reducibility
    exclude5 exclude6 exclude7 exclude8 G

/-- Every simple map of the real plane admits four colours. -/
theorem fourColorTheorem : FourColorTheorem :=
  Orbit9Assembly.fourColorTheorem_of_checks reducibility
    exclude5 exclude6 exclude7 exclude8

/-- A finite graph with a noncrossing drawing has a Mathlib four-colouring.
Disconnected graphs, isolated vertices and the empty graph are included. -/
theorem colorable_of_planeDrawing {V : Type*} [Finite V] {G : SimpleGraph V}
    (drawing : PlaneDrawing G) : G.Colorable 4 :=
  Orbit9Assembly.colorable_of_planeDrawing reducibility
    exclude5 exclude6 exclude7 exclude8 drawing

open Mettapedia.GraphTheory.FourColor
open GoertzelV24TwoEdgeCutMinimality
open SourceVertexCodeTrace TubeSlab.VertexTransfer

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u, u, u} V E}

/-- Every map in the source spherical cubic class has an exact closed
construction with compatible colouring witnesses along the whole route. -/
theorem supported_source_construction (hclass : BridgelessSphericalCubicMapData RS) :
    ∃ trace : VertexCodeTrace.Trace 0,
      Nonempty (VertexCodeSourceGeometry.Model trace.realize
        (terminalCoordinates (RS := RS) completeOrder visited_complete)) ∧
      Fintype.card trace.Vertex = Fintype.card V ∧
      VertexConstructionGSLT.colouring.Supports (VertexConstructionGSLT.route trace)
        Fin.elim0 Fin.elim0 :=
  Orbit9Assembly.supported_source_construction_of_checks reducibility
    exclude5 exclude6 exclude7 exclude8 hclass

/-- Any complete valid vertex sweep admits compatible choices. This asserts
existence of a successful choice, without requiring all partial choices to extend. -/
theorem supported_source_sweep (hclass : BridgelessSphericalCubicMapData RS)
    (order : List V) (hn : order.Nodup) (hne : order ≠ [])
    (hcover : ∀ v, visited order v) :
    VertexConstructionGSLT.colouring.Supports
      (VertexConstructionGSLT.route (encodeClosed hclass.spherical.cubic
        hclass.vertexRotationCyclic order hn hne hcover).trace) Fin.elim0 Fin.elim0 :=
  SourceConstruction.supported_sweep_of_unavoidability
    no_minimalCounterExample hclass order hn hne hcover

end FourColor.CompositionalComplete
