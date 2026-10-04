import MettapediaFourColor.GraphDiskEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24StellarDualStructure
import Mettapedia.GraphTheory.FourColor.GoertzelV24NonisolatedFaceDualConnectedness

/-!
# Face-potential hypotheses from an actual spherical graph rotation

The reference hypermap's Euler equality supplies the vertex-edge-face
balance used by geometric path separation. Cyclic vertex rotations and
connectedness also supply connectedness of the full face dual.
-/

namespace FourColor.GraphSphericalEuler

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24StellarDualStructure
open Mettapedia.GraphTheory.Hypermap.Reference SimpleGraphBridge

noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

theorem balance (data : Data G) (cyclic : data.IsVertexwiseCyclic)
    (conn : G.Connected) (covered : Function.Surjective (fun d : G.Dart => d.fst))
    (planar : (rotationHypermap data).Planar) :
    (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2 := by
  have nodes := GraphDiskEuler.node_count data cyclic covered
  have comps := GraphDiskEuler.connected data cyclic conn
  have edges : cycleCount (rotationHypermap data).edge = Fintype.card G.edgeSet := by
    rw [← orbitCount_eq_cycleCount]
    exact orbitCount_alpha_eq_card_edge data.toRotationSystem
  have faces : cycleCount (rotationHypermap data).face =
      Fintype.card (OrbitFace data.toRotationSystem) := by
    rw [← orbitCount_eq_cycleCount]
    exact orbitCount_phi_eq_card_orbitFace data.toRotationSystem
  have darts := data.toRotationSystem.card_darts_eq_twice_card_edges
  change Fintype.card G.Dart = 2 * Fintype.card G.edgeSet at darts
  have equation := (rotationHypermap data).evenGenus
  change (rotationHypermap data).genus = 0 at planar
  change (rotationHypermap data).compCount = 1 at comps
  change 2 * (rotationHypermap data).compCount + Nat.card G.Dart =
    2 * (rotationHypermap data).genus +
      (cycleCount (rotationHypermap data).edge +
        (cycleCount (rotationHypermap data).node +
          cycleCount (rotationHypermap data).face)) at equation
  rw [comps,planar,edges,nodes,faces,Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card] at equation
  omega

end
end FourColor.GraphSphericalEuler
