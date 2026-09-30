import MettapediaFourColor.PentagonalCoronaReduction
import Mettapedia.GraphTheory.FourColor.PentagonalCoronaChordExclusion

/-!
# A corona reduction with outer inducedness derived

The actual central pentagon and its four pentagonal neighbours and one
hexagonal neighbour determine a strict reduction whenever the sixteen traced
vertices are distinct and the ambient normal-form hypotheses hold. Cyclic
connectivity rules out all extra outer chords. The replacement still removes
sixteen vertices, introduces four, and reconstructs a jointly compatible
colouring. No outer frame, rotation equation, or inducedness premise is supplied.
-/

namespace FourColor.PentagonalLobePatch.Tangle.Corona

open Mettapedia.GraphTheory.FourColor
open PentagonalCoronaGeometry PhysicalForkCodeFaces SimpleGraphDartRotation
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality GoertzelV24WeightedOrbitFaceCorridor
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance coronaMinimalEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance coronaMinimalEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart)
  (hfaces : FaceLengths rotation root)
  (hvertices : Function.Injective (tracedVertex rotation root))

include hfaces hvertices

/-- The normal-form hypotheses derive inducedness and supply the full
strict reduction, including all introduced vertices and colouring repair. -/
theorem strict_reduction_of_cyclicallyFive
    (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    ∃ houter : OuterInduced rotation root,
    let hC := cubic3_of rotation.toRotationSystem h.spherical.cubic h.vertexRotationCyclic
    let L := incidence rotation root hC (hfaces.central_period rotation root)
      (hfaces.neighbour_periods rotation root) hvertices houter
    ∃ recognition : OpenTangleIsomorphism.Iso piece
        (ofVertexSide rotation.toRotationSystem L.patchKeep (Recognition.root L rotation)),
      let candidate := Embedded.smaller rotation L.patchVertices
        (Embedded.ports rotation L.patchVertices (Recognition.root L rotation) recognition 0).1
        (Recognition.root L rotation) recognition
      Fintype.card ({v : V // deletedRegionKeep L.patchVertices v} ⊕ Fin 4) + 12 =
        Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep L.patchVertices v} ⊕ Fin 4) <
        Fintype.card V ∧
      BridgelessSphericalCubicMapData candidate ∧
      (RotationSystemTaitColorable candidate → RotationSystemTaitColorable rotation.toRotationSystem) := by
  have htwenty := SphericalVertexLowerBound.twenty_le_card_vertices
    rotation.toRotationSystem h.spherical hminimum
  have hcubic : G.IsRegularOfDegree 3 := fun v =>
    (GoertzelV24CubicSmallBoundaryCycle.degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v)
  have houter := outerInduced_of_cyclicallyFive rotation root
    (cubic3_of rotation.toRotationSystem h.spherical.cubic h.vertexRotationCyclic)
    (hfaces.central_period rotation root) (hfaces.neighbour_periods rotation root)
    hvertices hcubic hcyclic (by omega)
  exact ⟨houter, strict_reduction rotation root hfaces hvertices houter h htwo hminimum
    (fun cut => (by have := hcyclic cut; omega))⟩

/-- A vertex-minimal counterexample cannot contain the selected face pattern
with sixteen distinct traced vertices. Minimality supplies every other
geometric premise of the existing joint colouring repair. -/
theorem not_in_minimal_counterexample_of_distinct_vertices
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False :=
  not_in_minimal_counterexample rotation root hfaces hvertices
    (outerInduced_of_minimality rotation root hfaces hvertices minimal) minimal

end
end FourColor.PentagonalLobePatch.Tangle.Corona
