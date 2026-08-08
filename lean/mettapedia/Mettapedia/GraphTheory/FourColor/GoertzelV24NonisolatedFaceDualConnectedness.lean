import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphFaceDualConnectedness

/-!
# Facial-dual connectedness without cubicity

The existing facial-dual theorem uses cubicity only to choose a dart at each
intermediate primal vertex.  Framed annular tangles instead have degrees one,
two, and three.  This module isolates the actual hypothesis—every vertex has
an outgoing dart—and derives it automatically for a connected graph-backed
rotation, whose stored outer dart makes the vertex type nontrivial.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24NonisolatedFaceDualConnectedness

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- A primal walk lifts to facial-dual reachability when every primal vertex
has a dart and the stored rotation is cyclic on each vertex fiber. -/
theorem orbitFaceVertex_reachable_of_primalReachable_of_vertexCovered
    (RS : RotationSystem V E)
    (hcovered : ∀ vertex : V, ∃ dart : RS.D, RS.vertOf dart = vertex)
    (hrotation : VertexRotationCyclic RS) {left right : RS.D}
    (hprimal : (rotationPrimalGraph RS).Reachable
      (RS.vertOf left) (RS.vertOf right)) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Reachable
        (orbitFaceVertex RS left) (orbitFaceVertex RS right) := by
  let FaceReachableAt : V → V → Prop := fun leftVertex rightVertex =>
    ∀ leftDart rightDart : RS.D,
      RS.vertOf leftDart = leftVertex →
      RS.vertOf rightDart = rightVertex →
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Reachable
          (orbitFaceVertex RS leftDart) (orbitFaceVertex RS rightDart)
  have hrefl : ∀ vertex, FaceReachableAt vertex vertex := by
    intro vertex leftDart rightDart hleft hright
    apply orbitFaceVertex_reachable_of_rho_sameCycle RS
    exact hrotation leftDart rightDart (hleft.trans hright.symm)
  have hadj : ∀ {leftVertex rightVertex},
      (rotationPrimalGraph RS).Adj leftVertex rightVertex →
        FaceReachableAt leftVertex rightVertex := by
    rintro leftVertex rightVertex ⟨crossing, hleftCrossing, hrightCrossing⟩
    intro leftDart rightDart hleft hright
    have htoCrossing := orbitFaceVertex_reachable_of_rho_sameCycle RS
      (hrotation leftDart crossing (hleft.trans hleftCrossing.symm))
    have hacross := orbitFaceVertex_reachable_alpha RS crossing
    have hfromCrossing := orbitFaceVertex_reachable_of_rho_sameCycle RS
      (hrotation (RS.alpha crossing) rightDart
        (hrightCrossing.trans hright.symm))
    exact (htoCrossing.trans hacross).trans hfromCrossing
  have hclosure : Relation.ReflTransGen (rotationPrimalGraph RS).Adj
      (RS.vertOf left) (RS.vertOf right) :=
    (SimpleGraph.reachable_iff_reflTransGen _ _).mp hprimal
  have hfaceRelation : FaceReachableAt (RS.vertOf left) (RS.vertOf right) := by
    refine Relation.ReflTransGen.trans_induction_on
      (motive := fun {leftVertex rightVertex} _ =>
        FaceReachableAt leftVertex rightVertex)
      hclosure hrefl (fun h => hadj h) ?_
    intro leftVertex middleVertex rightVertex _ _ hleft hright
      leftDart rightDart hleftDart hrightDart
    obtain ⟨middleDart, hmiddleDart⟩ := hcovered middleVertex
    exact (hleft leftDart middleDart hleftDart hmiddleDart).trans
      (hright middleDart rightDart hmiddleDart hrightDart)
  exact hfaceRelation left right rfl rfl

/-- Connectedness of the computed primal graph, coverage by darts, and cyclic
vertex rotations imply connectedness of the full quotient facial dual. -/
theorem orbitFaceInteriorDual_connected_of_vertexCovered
    (RS : RotationSystem V E)
    (hcovered : ∀ vertex : V, ∃ dart : RS.D, RS.vertOf dart = vertex)
    (hprimal : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected := by
  letI : Nonempty (AmbientFace (Finset.univ : Finset (OrbitFace RS))) :=
    ⟨orbitFaceVertex RS RS.outer⟩
  constructor
  intro leftFace rightFace
  obtain ⟨leftDart, hleftDart⟩ :=
    exists_dartOrbitFace_eq RS leftFace.1
  obtain ⟨rightDart, hrightDart⟩ :=
    exists_dartOrbitFace_eq RS rightFace.1
  have hreach :=
    orbitFaceVertex_reachable_of_primalReachable_of_vertexCovered
      RS hcovered hrotation
        (hprimal (RS.vertOf leftDart) (RS.vertOf rightDart))
  have hleftVertex : orbitFaceVertex RS leftDart = leftFace :=
    Subtype.ext hleftDart
  have hrightVertex : orbitFaceVertex RS rightDart = rightFace :=
    Subtype.ext hrightDart
  rwa [hleftVertex, hrightVertex] at hreach

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A connected graph-backed rotation has a dart based at every vertex.  The
stored outer dart supplies nontriviality, so connectedness rules out isolated
vertices. -/
theorem vertexCovered_of_connected_simpleGraphData
    (data : Data G) (hconnected : G.Connected) :
    ∀ vertex : V,
      ∃ dart : data.toRotationSystem.D,
        data.toRotationSystem.vertOf dart = vertex := by
  letI : Nontrivial V :=
    ⟨⟨data.outer.fst, data.outer.snd, data.outer.fst_ne_snd⟩⟩
  intro vertex
  have hdegree : 0 < G.degree vertex :=
    hconnected.preconnected.degree_pos_of_nontrivial vertex
  rcases (G.degree_pos_iff_exists_adj vertex).1 hdegree with
    ⟨other, hadj⟩
  exact ⟨⟨(vertex, other), hadj⟩, rfl⟩

/-- A connected graph-backed rotation with genuine cyclic vertex rotations
has connected full facial dual, with no regularity or cubicity premise. -/
theorem orbitFaceInteriorDual_connected_of_simpleGraph
    (data : Data G) (hconnected : G.Connected)
    (hcyclic : HasCyclicVertexRotations G data) :
    (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected := by
  apply orbitFaceInteriorDual_connected_of_vertexCovered
    data.toRotationSystem
      (vertexCovered_of_connected_simpleGraphData data hconnected)
  · rw [rotationPrimalGraph_toRotationSystem_eq]
    exact hconnected
  · exact hasCyclicVertexRotations_implies_vertexRotationCyclic
      G data hcyclic

end GoertzelV24NonisolatedFaceDualConnectedness

end Mettapedia.GraphTheory.FourColor
