import MettapediaFourColor.OrbitAssembly
import MettapediaFourColor.Orbit11.Coverage

/-!
# Composition of the shared arity-ten and arity-eleven presentations

Both presentations supply semantic charge certificates to the same classical
reconstruction. Reducibility and the five lower arities remain explicit.
The graph and construction endpoints retain actual colouring witnesses.
-/

namespace FourColor.Orbit11Assembly

theorem no_minimalCounterExample_of_checks (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    (e9 : ExcludedArity (RedpartSound theRedpart) 9)
    {D : Type} [Finite D] (G : Hypermap D) : ¬ G.MinimalCounterExample :=
  OrbitAssembly.no_minimalCounterExample_of_checks hred
    e5 e6 e7 e8 e9 Orbit11.exclude11 G

theorem fourColorTheorem_of_checks (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    (e9 : ExcludedArity (RedpartSound theRedpart) 9) : FourColorTheorem :=
  OrbitAssembly.fourColorTheorem_of_checks hred
    e5 e6 e7 e8 e9 Orbit11.exclude11

theorem colorable_of_planeDrawing (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    (e9 : ExcludedArity (RedpartSound theRedpart) 9)
    {V : Type*} [Finite V] {G : SimpleGraph V} (drawing : PlaneDrawing G) :
    G.Colorable 4 :=
  OrbitAssembly.colorable_of_planeDrawing hred
    e5 e6 e7 e8 e9 Orbit11.exclude11 drawing

open Mettapedia.GraphTheory.FourColor
open GoertzelV24TwoEdgeCutMinimality
open SourceVertexCodeTrace TubeSlab.VertexTransfer

universe u

theorem supported_source_construction_of_checks (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    (e9 : ExcludedArity (RedpartSound theRedpart) 9)
    {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    {RS : RotationSystem.{u, u, u} V E}
    (hclass : BridgelessSphericalCubicMapData RS) :
    ∃ trace : VertexCodeTrace.Trace 0,
      Nonempty (VertexCodeSourceGeometry.Model trace.realize
        (terminalCoordinates (RS := RS) completeOrder visited_complete)) ∧
      Fintype.card trace.Vertex = Fintype.card V ∧
      VertexConstructionGSLT.colouring.Supports (VertexConstructionGSLT.route trace)
        Fin.elim0 Fin.elim0 :=
  OrbitAssembly.supported_source_construction_of_checks hred
    e5 e6 e7 e8 e9 Orbit11.exclude11 hclass

end FourColor.Orbit11Assembly
