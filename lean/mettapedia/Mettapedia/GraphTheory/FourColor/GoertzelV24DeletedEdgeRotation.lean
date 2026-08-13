import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedEdgeTrail
import Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationPointDeletion

/-!
# Rotation data after deleting one graph edge

The framed source trail lives on a graph with one edge removed from the closed
cubic ambient graph.  Graph deletion alone does not carry the planar rotation.
Here the two darts of the removed edge are deleted from their respective
vertex-rotation cycles, giving the literal cyclic order on the remaining graph
darts.  This is the first carrier-changing part of the closed-map-to-framed-
trail formation; face-orbit transport is kept separate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DeletedEdgeRotation

open SimpleGraphDartRotation
open GoertzelV24DeletedEdgeTrail
open GoertzelV24PermutationPointDeletion

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The oriented ambient dart from the first endpoint to the second. -/
def forwardDart {u v : V} (huv : G.Adj u v) : G.Dart :=
  ⟨(u, v), huv⟩

/-- The opposite oriented dart of the edge being deleted. -/
def reverseDart {u v : V} (huv : G.Adj u v) : G.Dart :=
  (forwardDart huv).symm

@[simp]
theorem forwardDart_symm {u v : V} (huv : G.Adj u v) :
    (forwardDart huv).symm = reverseDart huv :=
  rfl

theorem forwardDart_ne_reverseDart {u v : V} (huv : G.Adj u v) :
    forwardDart huv ≠ reverseDart huv := by
  exact (SimpleGraph.Dart.symm_ne (forwardDart huv)).symm

/-- Ambient darts other than the two orientations of the removed edge. -/
abbrev RemainingDart {u v : V} (huv : G.Adj u v) :=
  { dart : G.Dart //
    dart ≠ forwardDart huv ∧ dart ≠ reverseDart huv }

/-- A dart of the edge-deleted graph is exactly an ambient dart other than the
two orientations of the deleted edge. -/
def deletedGraphDartEquiv {u v : V} (huv : G.Adj u v) :
    (DeletedEdgeGraph G u v).Dart ≃ RemainingDart huv where
  toFun dart := by
    have hadj : G.Adj dart.fst dart.snd :=
      (SimpleGraph.deleteEdges_adj.mp dart.adj).1
    let ambient : G.Dart := ⟨dart.1, hadj⟩
    refine ⟨ambient, ?_, ?_⟩
    · intro heq
      have hpair : dart.1 = (u, v) := by
        simpa [ambient, forwardDart] using
          congrArg (fun oldDart : G.Dart => oldDart.1) heq
      exact (SimpleGraph.deleteEdges_adj.mp dart.adj).2 (by simp [hpair])
    · intro heq
      have hpair : dart.1 = (v, u) := by
        simpa [ambient, reverseDart, forwardDart] using
          congrArg (fun oldDart : G.Dart => oldDart.1) heq
      exact (SimpleGraph.deleteEdges_adj.mp dart.adj).2 (by simp [hpair])
  invFun dart := by
    refine ⟨dart.1.1, ?_⟩
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨dart.1.adj, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hedge
    rcases Sym2.eq_iff.mp hedge with hforward | hreverse
    · have hpair : dart.1.1 = (forwardDart huv).1 :=
        Prod.ext hforward.1 hforward.2
      exact dart.2.1 (SimpleGraph.Dart.ext dart.1 (forwardDart huv) hpair)
    · have hpair : dart.1.1 = (reverseDart huv).1 :=
        Prod.ext hreverse.1 hreverse.2
      exact dart.2.2 (SimpleGraph.Dart.ext dart.1 (reverseDart huv) hpair)
  left_inv dart := by
    apply SimpleGraph.Dart.ext
    rfl
  right_inv dart := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    rfl

/-- Delete both orientations of one edge from the ambient vertex rotation. -/
def remainingVertexRotation (data : Data G) {u v : V} (huv : G.Adj u v) :
    Equiv.Perm (RemainingDart huv) :=
  eraseTwoPointsSubtype data.vertexRotation
    (forwardDart_ne_reverseDart huv)

/-- Transport the remaining-dart rotation to the actual dart type of the
edge-deleted simple graph. -/
def deletedVertexRotation (data : Data G) {u v : V} (huv : G.Adj u v) :
    Equiv.Perm (DeletedEdgeGraph G u v).Dart :=
  (deletedGraphDartEquiv huv).symm.permCongr
    (remainingVertexRotation data huv)

@[simp]
theorem deletedGraphDartEquiv_fst {u v : V} (huv : G.Adj u v)
    (dart : (DeletedEdgeGraph G u v).Dart) :
    (deletedGraphDartEquiv huv dart).1.fst = dart.fst :=
  rfl

@[simp]
theorem deletedGraphDartEquiv_symm_fst {u v : V} (huv : G.Adj u v)
    (dart : RemainingDart huv) :
    ((deletedGraphDartEquiv huv).symm dart).fst = dart.1.fst :=
  rfl

/-- Passing from a deleted-graph dart to its ambient representative commutes
with reversing the dart. -/
@[simp]
theorem deletedGraphDartEquiv_symm {u v : V} (huv : G.Adj u v)
    (dart : (DeletedEdgeGraph G u v).Dart) :
    (deletedGraphDartEquiv huv dart.symm).1 =
      ((deletedGraphDartEquiv huv dart).1).symm := by
  apply SimpleGraph.Dart.ext
  rfl

/-- Deleting the two edge darts preserves the vertex supporting every
remaining dart. -/
theorem remainingVertexRotation_fst (data : Data G) {u v : V}
    (huv : G.Adj u v) (dart : RemainingDart huv) :
    (remainingVertexRotation data huv dart).1.fst = dart.1.fst := by
  exact eraseTwoPoints_preserves data.vertexRotation
    (forwardDart huv) (reverseDart huv) (fun dart : G.Dart => dart.fst)
    data.vertexRotation_fst dart.1

/-- At a surviving dart whose old successor also survives, the induced vertex
rotation is literally the old vertex rotation. -/
theorem remainingVertexRotation_apply_of_image_ne
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (dart : RemainingDart huv)
    (hforward : data.vertexRotation dart.1 ≠ forwardDart huv)
    (hreverse : data.vertexRotation dart.1 ≠ reverseDart huv) :
    (remainingVertexRotation data huv dart).1 =
      data.vertexRotation dart.1 := by
  exact eraseTwoPointsSubtype_apply_of_image_ne data.vertexRotation
    (forwardDart_ne_reverseDart huv) dart hforward hreverse

/-- The ambient representative of the induced rotation agrees with the old
rotation whenever the old successor is not one of the two removed darts. -/
theorem deletedVertexRotation_ambient_eq_of_image_ne
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (dart : (DeletedEdgeGraph G u v).Dart)
    (hforward :
      data.vertexRotation (deletedGraphDartEquiv huv dart).1 ≠ forwardDart huv)
    (hreverse :
      data.vertexRotation (deletedGraphDartEquiv huv dart).1 ≠ reverseDart huv) :
    (deletedGraphDartEquiv huv (deletedVertexRotation data huv dart)).1 =
      data.vertexRotation (deletedGraphDartEquiv huv dart).1 := by
  change (remainingVertexRotation data huv
      (deletedGraphDartEquiv huv dart)).1 =
    data.vertexRotation (deletedGraphDartEquiv huv dart).1
  exact remainingVertexRotation_apply_of_image_ne data huv
    (deletedGraphDartEquiv huv dart) hforward hreverse

/-- The induced permutation is a valid vertex rotation on the edge-deleted
graph. -/
theorem deletedVertexRotation_fst (data : Data G) {u v : V}
    (huv : G.Adj u v) (dart : (DeletedEdgeGraph G u v).Dart) :
    (deletedVertexRotation data huv dart).fst = dart.fst := by
  have h := remainingVertexRotation_fst data huv
    (deletedGraphDartEquiv huv dart)
  change ((deletedGraphDartEquiv huv).symm
      (remainingVertexRotation data huv (deletedGraphDartEquiv huv dart))).fst =
    dart.fst
  simpa only [deletedGraphDartEquiv_symm_fst,
    deletedGraphDartEquiv_fst] using h

/-- Bare graph-backed rotation data on the graph obtained by deleting one
ambient edge.  The caller chooses only the irrelevant distinguished root dart;
the cyclic orders are computed from the closed ambient rotation. -/
def deletedEdgeData (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart) :
    Data (DeletedEdgeGraph G u v) where
  vertexRotation := deletedVertexRotation data huv
  vertexRotation_fst := deletedVertexRotation_fst data huv
  outer := outer

/-- A face step whose old successor does not use the deleted edge is unchanged
after transporting the deleted-graph dart back to the ambient carrier.  This
is the local face-orbit preservation fact needed before packaging the framed
source trail's retained faces. -/
theorem deletedEdgeData_phi_ambient_eq_of_ne
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (dart : (DeletedEdgeGraph G u v).Dart)
    (hforward :
      data.toRotationSystem.phi (deletedGraphDartEquiv huv dart).1 ≠
        forwardDart huv)
    (hreverse :
      data.toRotationSystem.phi (deletedGraphDartEquiv huv dart).1 ≠
        reverseDart huv) :
    (deletedGraphDartEquiv huv
      ((deletedEdgeData data huv outer).toRotationSystem.phi dart)).1 =
        data.toRotationSystem.phi (deletedGraphDartEquiv huv dart).1 := by
  change data.vertexRotation ((deletedGraphDartEquiv huv dart).1).symm ≠
    forwardDart huv at hforward
  change data.vertexRotation ((deletedGraphDartEquiv huv dart).1).symm ≠
    reverseDart huv at hreverse
  rw [RotationSystem.phi_apply, RotationSystem.phi_apply]
  change (deletedGraphDartEquiv huv
      (deletedVertexRotation data huv dart.symm)).1 =
    data.vertexRotation ((deletedGraphDartEquiv huv dart).1).symm
  simpa only [deletedGraphDartEquiv_symm] using
    deletedVertexRotation_ambient_eq_of_image_ne data huv dart.symm
      (by simpa only [deletedGraphDartEquiv_symm] using hforward)
      (by simpa only [deletedGraphDartEquiv_symm] using hreverse)

end

end GoertzelV24DeletedEdgeRotation

end Mettapedia.GraphTheory.FourColor
