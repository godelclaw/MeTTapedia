import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SimpleGraphFaceDualConnectedness

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A graph-backed rotation is genuinely cyclic when its restriction to every
outgoing-dart fiber is one permutation cycle. -/
def HasCyclicVertexRotations (data : Data G) : Prop :=
  ∀ vertex : V,
    data.vertexRotation.IsCycleOn
      {dart : G.Dart | dart.fst = vertex}

theorem hasCyclicVertexRotations_implies_vertexRotationCyclic
    (data : Data G) (hcyclic : HasCyclicVertexRotations G data) :
    VertexRotationCyclic data.toRotationSystem := by
  intro left right hvertex
  exact (hcyclic left.fst).2 (x := left) rfl (y := right)
    (by simpa using hvertex.symm)

/-- The primal graph recomputed from a graph-backed rotation system is the
original simple graph. -/
theorem rotationPrimalGraph_toRotationSystem_eq (data : Data G) :
    rotationPrimalGraph data.toRotationSystem = G := by
  ext left right
  constructor
  · rintro ⟨dart, hleft, hright⟩
    change dart.fst = left at hleft
    change dart.snd = right at hright
    simpa [hleft, hright] using dart.adj
  · intro hadj
    let dart : G.Dart := ⟨(left, right), hadj⟩
    exact ⟨dart, rfl, rfl⟩

/-- For a connected cubic graph with an actual cyclic rotation at every
vertex, the quotient facial dual of its graph-backed rotation system is
connected. -/
theorem orbitFaceInteriorDual_connected_of_simpleGraph
    (data : Data G) (hcubic : G.IsRegularOfDegree 3)
    (hconnected : G.Connected)
    (hcyclic : HasCyclicVertexRotations G data) :
    (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected := by
  apply GoertzelV24FaceDualConnectedness.orbitFaceInteriorDual_connected
    data.toRotationSystem
  · exact data.toRotationSystem_isCubic_iff.mpr hcubic
  · rw [rotationPrimalGraph_toRotationSystem_eq]
    exact hconnected
  · exact hasCyclicVertexRotations_implies_vertexRotationCyclic G data hcyclic

end GoertzelV24SimpleGraphFaceDualConnectedness

end Mettapedia.GraphTheory.FourColor
