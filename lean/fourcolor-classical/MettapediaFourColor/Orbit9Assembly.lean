import MettapediaFourColor.Orbit11Assembly
import MettapediaFourColor.Orbit9.Coverage

/-!
# Composition of three presentations with shared charge certificates

Arity nine joins arities ten and eleven in the same reconstruction argument.
Reducibility and arities five through eight remain explicit inputs. Both the
finite graph and exact construction endpoints retain actual colouring witnesses.
-/

namespace FourColor.Orbit9Assembly

theorem no_minimalCounterExample_of_checks (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    {D : Type} [Finite D] (G : Hypermap D) : ¬ G.MinimalCounterExample :=
  Orbit11Assembly.no_minimalCounterExample_of_checks hred
    e5 e6 e7 e8 Orbit9.exclude9 G

theorem fourColorTheorem_of_checks (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8) : FourColorTheorem :=
  Orbit11Assembly.fourColorTheorem_of_checks hred
    e5 e6 e7 e8 Orbit9.exclude9

theorem colorable_of_planeDrawing (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    {V : Type*} [Finite V] {G : SimpleGraph V} (drawing : PlaneDrawing G) :
    G.Colorable 4 :=
  Orbit11Assembly.colorable_of_planeDrawing hred
    e5 e6 e7 e8 Orbit9.exclude9 drawing

open Mettapedia.GraphTheory.FourColor
open GoertzelV24TwoEdgeCutMinimality
open SourceVertexCodeTrace TubeSlab.VertexTransfer

universe u

theorem supported_source_construction_of_checks (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    {RS : RotationSystem.{u, u, u} V E}
    (hclass : BridgelessSphericalCubicMapData RS) :
    ∃ trace : VertexCodeTrace.Trace 0,
      Nonempty (VertexCodeSourceGeometry.Model trace.realize
        (terminalCoordinates (RS := RS) completeOrder visited_complete)) ∧
      Fintype.card trace.Vertex = Fintype.card V ∧
      VertexConstructionGSLT.colouring.Supports (VertexConstructionGSLT.route trace)
        Fin.elim0 Fin.elim0 :=
  Orbit11Assembly.supported_source_construction_of_checks hred
    e5 e6 e7 e8 Orbit9.exclude9 hclass

end FourColor.Orbit9Assembly
