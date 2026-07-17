import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOppositePortFaceCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCyclicOrder

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance rotationPortFaceCutGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- In the canonical rotation ordering, a restored boundary dart points in
the direction opposite to the corresponding dart based at the deleted
vertex. -/
theorem rotationOrdered_boundaryPortDart_eq_alpha_rotationPortDart
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (port : Fin 4) :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
        (data.rotationOrderedData graphData hcubic hrotation) port =
      graphData.toRotationSystem.alpha
        (data.rotationPortDart graphData port) := by
  let ordered := data.rotationOrderedData graphData hcubic hrotation
  let radial := data.rotationPortDart graphData port
  let boundary :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
      ordered port
  have hdeleted :
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex
          ordered port = radial.fst := by
    simpa [ordered, radial, rotationOrderedData,
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex]
      using (data.rotationPortDart_fst graphData port).symm
  have hport : ordered.portVertex port = radial.snd := by
    rfl
  have hedge : boundary.edge = radial.edge := by
    calc
      boundary.edge =
          GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue
            ordered port := by
        exact GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart_edge
          ordered port
      _ = s(GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex
            ordered port, ordered.portVertex port) :=
        GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_eq
          ordered port
      _ = s(radial.fst, radial.snd) := by rw [hdeleted, hport]
      _ = radial.edge := rfl
  have hboundaryFst : boundary.fst = radial.snd := by
    change ordered.portVertex port = radial.snd
    exact hport
  rcases (SimpleGraph.dart_edge_eq_iff boundary radial).1 hedge with
      hsame | hreversed
  · exfalso
    apply radial.fst_ne_snd
    calc
      radial.fst = boundary.fst :=
        congrArg (fun dart : G.Dart => dart.fst) hsame.symm
      _ = radial.snd := hboundaryFst
  · simpa [boundary, radial] using hreversed

/-- At port `1`, one face step along the canonically oriented restored edge
lands on the central dart based at the first deleted vertex. -/
theorem rotationOrdered_boundaryPortDart_one_phi_eq_rotationCentralDart
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    graphData.toRotationSystem.phi
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
          (data.rotationOrderedData graphData hcubic hrotation) 1) =
      data.rotationCentralDart := by
  rw [data.rotationOrdered_boundaryPortDart_eq_alpha_rotationPortDart
    graphData hcubic hrotation]
  simp only [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  simpa [rotationPortDart] using
    (rho_cube_apply_of_isCubic graphData.toRotationSystem hcubic hrotation
      data.rotationCentralDart)

/-- At port `3`, one face step along the canonically oriented restored edge
lands on the reverse central dart based at the second deleted vertex. -/
theorem rotationOrdered_boundaryPortDart_three_phi_eq_alpha_rotationCentralDart
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    graphData.toRotationSystem.phi
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
          (data.rotationOrderedData graphData hcubic hrotation) 3) =
      graphData.toRotationSystem.alpha data.rotationCentralDart := by
  rw [data.rotationOrdered_boundaryPortDart_eq_alpha_rotationPortDart
    graphData hcubic hrotation]
  simp only [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  simpa [rotationPortDart] using
    (rho_cube_apply_of_isCubic graphData.toRotationSystem hcubic hrotation
      (graphData.toRotationSystem.alpha data.rotationCentralDart))

/-- The retained-side dart at port `1` lies on the face represented by the
forward central dart. -/
theorem rotationOrdered_boundaryPortDart_one_face_eq_rotationCentralDart
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    dartOrbitFace graphData.toRotationSystem
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
          (data.rotationOrderedData graphData hcubic hrotation) 1) =
      dartOrbitFace graphData.toRotationSystem data.rotationCentralDart := by
  let boundary :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
      (data.rotationOrderedData graphData hcubic hrotation) 1
  calc
    dartOrbitFace graphData.toRotationSystem boundary =
        dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.phi boundary) :=
      (dartOrbitFace_phi_eq graphData.toRotationSystem boundary).symm
    _ = dartOrbitFace graphData.toRotationSystem data.rotationCentralDart :=
      congrArg (dartOrbitFace graphData.toRotationSystem)
        (data.rotationOrdered_boundaryPortDart_one_phi_eq_rotationCentralDart
          graphData hcubic hrotation)

/-- The retained-side dart at port `3` lies on the face represented by the
reverse central dart. -/
theorem rotationOrdered_boundaryPortDart_three_face_eq_alpha_rotationCentralDart
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    dartOrbitFace graphData.toRotationSystem
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
          (data.rotationOrderedData graphData hcubic hrotation) 3) =
      dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha data.rotationCentralDart) := by
  let boundary :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
      (data.rotationOrderedData graphData hcubic hrotation) 3
  calc
    dartOrbitFace graphData.toRotationSystem boundary =
        dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.phi boundary) :=
      (dartOrbitFace_phi_eq graphData.toRotationSystem boundary).symm
    _ = dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha data.rotationCentralDart) :=
      congrArg (dartOrbitFace graphData.toRotationSystem)
        (data.rotationOrdered_boundaryPortDart_three_phi_eq_alpha_rotationCentralDart
          graphData hcubic hrotation)

/-- Any face labeling that changes across the central edge gives different
labels to the retained-side faces at the two unused ports `1` and `3`. -/
theorem rotationOrdered_unusedBoundaryFaces_ne_of_centralFaces_ne
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hcentral :
      labels (dartOrbitFace graphData.toRotationSystem
          data.rotationCentralDart) ≠
        labels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha data.rotationCentralDart))) :
    labels (dartOrbitFace graphData.toRotationSystem
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
          (data.rotationOrderedData graphData hcubic hrotation) 1)) ≠
      labels (dartOrbitFace graphData.toRotationSystem
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
          (data.rotationOrderedData graphData hcubic hrotation) 3)) := by
  rw [data.rotationOrdered_boundaryPortDart_one_face_eq_rotationCentralDart
      graphData hcubic hrotation,
    data.rotationOrdered_boundaryPortDart_three_face_eq_alpha_rotationCentralDart
      graphData hcubic hrotation]
  exact hcentral

/-- A retained trail between the canonically opposite ports produces
an exact facial cut whose unused retained-side port faces have different
labels. This packages the global sphere cut with the local cubic rotation. -/
theorem exists_rotationOrdered_oppositePortClosure_exactFaceCut_of_minimal_of_isTrail
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        ((data.rotationOrderedData graphData hcubic hrotation).retainedPort 0)
        ((data.rotationOrderedData graphData hcubic hrotation).retainedPort 2))
    (hpath : path.IsTrail) :
    ∃ labels : OrbitFace graphData.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap graphData.toRotationSystem labels =
          walkEdgeParity
            ((data.rotationOrderedData graphData hcubic hrotation).oppositePortClosure
              path) ∧
        (∀ dart : graphData.toRotationSystem.D,
          labels (dartOrbitFace graphData.toRotationSystem dart) ≠
              labels (dartOrbitFace graphData.toRotationSystem
                (graphData.toRotationSystem.alpha dart)) ↔
            (graphData.toRotationSystem.edgeOf dart).1 ∈
              ((data.rotationOrderedData graphData hcubic hrotation).oppositePortClosure
                path).edges) ∧
        (∀ port : Fin 4,
          labels (dartOrbitFace graphData.toRotationSystem
              (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
                (data.rotationOrderedData graphData hcubic hrotation) port)) ≠
                labels (dartOrbitFace graphData.toRotationSystem
                  (graphData.toRotationSystem.alpha
                    (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
                      (data.rotationOrderedData graphData hcubic hrotation)
                        port))) ↔
            port = 0 ∨ port = 2) ∧
        labels (dartOrbitFace graphData.toRotationSystem
            data.rotationCentralDart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha data.rotationCentralDart)) ∧
        labels (dartOrbitFace graphData.toRotationSystem
            (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
              (data.rotationOrderedData graphData hcubic hrotation) 1)) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
              (data.rotationOrderedData graphData hcubic hrotation) 3)) := by
  let ordered := data.rotationOrderedData graphData hcubic hrotation
  rcases ordered.exists_oppositePortClosure_exactFaceCut_of_minimal_of_isTrail
      graphData minimal path hpath with
    ⟨labels, hlabels, hexact, hports, hcentral⟩
  have hcentral' :
      labels (dartOrbitFace graphData.toRotationSystem
          data.rotationCentralDart) ≠
        labels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha data.rotationCentralDart)) := by
    simpa [ordered, rotationOrderedData, rotationCentralDart,
      oppositePortCentralDart] using hcentral
  exact ⟨labels, hlabels, hexact, hports, hcentral',
    data.rotationOrdered_unusedBoundaryFaces_ne_of_centralFaces_ne
      graphData hcubic hrotation labels hcentral'⟩

/-- The simple-path specialization of the rotation-ordered trail cut. -/
theorem exists_rotationOrdered_oppositePortClosure_exactFaceCut_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        ((data.rotationOrderedData graphData hcubic hrotation).retainedPort 0)
        ((data.rotationOrderedData graphData hcubic hrotation).retainedPort 2))
    (hpath : path.IsPath) :
    ∃ labels : OrbitFace graphData.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap graphData.toRotationSystem labels =
          walkEdgeParity
            ((data.rotationOrderedData graphData hcubic hrotation).oppositePortClosure
              path) ∧
        (∀ dart : graphData.toRotationSystem.D,
          labels (dartOrbitFace graphData.toRotationSystem dart) ≠
              labels (dartOrbitFace graphData.toRotationSystem
                (graphData.toRotationSystem.alpha dart)) ↔
            (graphData.toRotationSystem.edgeOf dart).1 ∈
              ((data.rotationOrderedData graphData hcubic hrotation).oppositePortClosure
                path).edges) ∧
        (∀ port : Fin 4,
          labels (dartOrbitFace graphData.toRotationSystem
              (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
                (data.rotationOrderedData graphData hcubic hrotation) port)) ≠
                labels (dartOrbitFace graphData.toRotationSystem
                  (graphData.toRotationSystem.alpha
                    (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
                      (data.rotationOrderedData graphData hcubic hrotation)
                        port))) ↔
            port = 0 ∨ port = 2) ∧
        labels (dartOrbitFace graphData.toRotationSystem
            data.rotationCentralDart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha data.rotationCentralDart)) ∧
        labels (dartOrbitFace graphData.toRotationSystem
            (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
              (data.rotationOrderedData graphData hcubic hrotation) 1)) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
              (data.rotationOrderedData graphData hcubic hrotation) 3)) := by
  exact data.exists_rotationOrdered_oppositePortClosure_exactFaceCut_of_minimal_of_isTrail
    graphData minimal hcubic hrotation path hpath.isTrail

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
