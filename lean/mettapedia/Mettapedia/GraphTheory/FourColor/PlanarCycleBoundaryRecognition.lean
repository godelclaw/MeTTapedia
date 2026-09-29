import Mettapedia.GraphTheory.FourColor.CycleBoundaryOrientation
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexSideReturn

/-!
# Recognizing rotations of nonseparating cycle shores

For an actual vertex shore in a spherical cubic map, cycle incidence and
connectedness of both shores determine all the local rotations, up to one
global reversal. Cofaciality is derived from the embedding, not supplied as
part of the incidence coordinates.
-/

namespace Mettapedia.GraphTheory.FourColor.PlanarCycleBoundaryRecognition

open CycleBoundaryOrientation
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24VertexSideOpenTangle
open GoertzelV24DeletedRegionRotationSplice GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance cycleRecognitionEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance cycleRecognitionEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A uniform geometric recognition law for cycles of every length. Its input
specifies only edge/port incidence; the ambient sphere supplies the rotation law. -/
theorem uniform_rotation_of_planarBond
    {k : ℕ} [NeZero k]
    (rotation : SimpleGraphDartRotation.Data G) (deleted : Finset V)
    (root : RetainedDart rotation.toRotationSystem (deletedRegionKeep deleted))
    (C : Incidence k (ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) root))
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretained : (G.induce {v | deletedRegionKeep deleted v}).Connected)
    (hdeleted : (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected) :
    ∃ b : Bool, ∀ d,
      (ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) root).rho (C.darts d) =
        C.darts (turn k (fun _ => b) d) := by
  apply C.uniform_rotation
  · exact openRotationCyclic_ofVertexSide _ _ _ hrotation
  · exact OpenTangleVertexSideReturn.ports_cofacial_of_planarBond
      rotation deleted root hsphere htwo hconnected hrotation hretained hdeleted

/-- Rotation and interface order share the same global choice. The exact
first return is the predecessor or successor in the incidence cycle. -/
theorem uniform_geometry_of_planarBond
    {k : ℕ} [NeZero k]
    (rotation : SimpleGraphDartRotation.Data G) (deleted : Finset V)
    (root : RetainedDart rotation.toRotationSystem (deletedRegionKeep deleted))
    (C : Incidence k (ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) root))
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretained : (G.induce {v | deletedRegionKeep deleted v}).Connected)
    (hdeleted : (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected) :
    ∃ b : Bool,
      (∀ d, (ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) root).rho
        (C.darts d) = C.darts (turn k (fun _ => b) d)) ∧
      ∀ i, OpenTanglePortReplacement.returnCode
          (ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) root) (C.port i) =
        C.port (if b then i + 1 else i - 1) := by
  obtain ⟨b, hb⟩ := uniform_rotation_of_planarBond rotation deleted root C
    hsphere htwo hconnected hrotation hretained hdeleted
  exact ⟨b, hb, C.returnCode_of_uniform_rotation hb⟩

end

end Mettapedia.GraphTheory.FourColor.PlanarCycleBoundaryRecognition
