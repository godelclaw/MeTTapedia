import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedEdgeRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence

/-!
# Face surgery at one deleted edge

Deleting an edge from a rotation system removes its two darts from the
vertex rotations.  On the facial permutation this splices the predecessor of
one dart directly to the successor on the other dart side.  This is the
atomic calculation needed to turn a facial pentagon cap into one opened collar
face: the five cap-cycle deletions must later compose five such splices.

The result below is deliberately one-edge and carrier-generic.  It neither
chooses a pentagon cap nor asserts that five splices already form one hole.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DeletedEdgeFaceMerge

open SimpleGraphDartRotation
open GoertzelV24DeletedEdgeTrail
open GoertzelV24DeletedEdgeRotation
open GoertzelV24FaceOrbitIncidence
open GoertzelV24PermutationPointDeletion

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Erasing `first` and then `second` from a permutation sends the predecessor
of `first` directly to its old successor, provided neither the predecessor nor
that successor is the second erased point. -/
theorem eraseTwoPoints_apply_predecessor_first
    {A : Type*} [DecidableEq A] (perm : Equiv.Perm A)
    {first second : A}
    (hpre : perm.symm first ≠ second)
    (hsucc : perm first ≠ second) :
    eraseTwoPoints perm first second (perm.symm first) = perm first := by
  rw [eraseTwoPoints]
  have hfirst : erasePoint perm first (perm.symm first) = perm first := by
    rw [erasePoint, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  calc
    erasePoint (erasePoint perm first) second (perm.symm first) =
        erasePoint perm first (perm.symm first) :=
      erasePoint_apply_of_ne_of_apply_ne (erasePoint perm first) second
        (perm.symm first) hpre (by simpa [hfirst] using hsucc)
    _ = perm first := hfirst

/-- The exact facial splice produced by deleting one edge.  If an old facial
step lands on the forward dart of the removed edge, then the induced face step
lands at the old successor of the reverse dart.  In a two-sided closed map the
two endpoints lie on the two formerly distinct incident face cycles, so this
is the local face-merger calculation used by cap opening. -/
theorem deletedEdgeData_phi_ambient_eq_of_phi_eq_forward
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (dart : (DeletedEdgeGraph G u v).Dart)
    (hphi : data.toRotationSystem.phi (deletedGraphDartEquiv huv dart).1 =
      forwardDart huv)
    (hsucc : data.toRotationSystem.phi (reverseDart huv) ≠ reverseDart huv) :
    (deletedGraphDartEquiv huv
      ((deletedEdgeData data huv outer).toRotationSystem.phi dart)).1 =
      data.toRotationSystem.phi (reverseDart huv) := by
  rw [RotationSystem.phi_apply, RotationSystem.phi_apply]
  change (deletedGraphDartEquiv huv
      (deletedVertexRotation data huv dart.symm)).1 =
    data.vertexRotation (reverseDart huv).symm
  change (remainingVertexRotation data huv
      (deletedGraphDartEquiv huv dart.symm)).1 =
    data.vertexRotation (forwardDart huv)
  change eraseTwoPoints data.vertexRotation (forwardDart huv) (reverseDart huv)
      (deletedGraphDartEquiv huv dart.symm).1 =
    data.vertexRotation (forwardDart huv)
  rw [show (deletedGraphDartEquiv huv dart.symm).1 =
      ((deletedGraphDartEquiv huv dart).1).symm by
        exact deletedGraphDartEquiv_symm huv dart]
  have hpre : ((deletedGraphDartEquiv huv dart).1).symm ≠ reverseDart huv := by
    intro h
    have : (deletedGraphDartEquiv huv dart).1 = forwardDart huv := by
      simpa only [reverseDart, SimpleGraph.Dart.symm_symm] using
        congrArg SimpleGraph.Dart.symm h
    exact (deletedGraphDartEquiv huv dart).2.1 this
  have hvalue : ((deletedGraphDartEquiv huv dart).1).symm =
      data.vertexRotation.symm (forwardDart huv) := by
    apply data.vertexRotation.injective
    change data.vertexRotation ((deletedGraphDartEquiv huv dart).1).symm =
      forwardDart huv at hphi
    calc
      data.vertexRotation ((deletedGraphDartEquiv huv dart).1).symm =
          forwardDart huv := hphi
      _ = data.vertexRotation (data.vertexRotation.symm (forwardDart huv)) := by simp
  have hpreimage : data.vertexRotation.symm (forwardDart huv) ≠ reverseDart huv := by
    rw [← hvalue]
    exact hpre
  rw [hvalue]
  exact eraseTwoPoints_apply_predecessor_first data.vertexRotation
    hpreimage (by
      change data.toRotationSystem.phi (reverseDart huv) ≠ reverseDart huv
      exact hsucc)

/-- The surviving dart reached from the reverse side of a deleted edge. -/
def reverseSuccessorDart
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (hsuccForward : data.toRotationSystem.phi (reverseDart huv) ≠ forwardDart huv)
    (hsuccReverse : data.toRotationSystem.phi (reverseDart huv) ≠ reverseDart huv) :
    (DeletedEdgeGraph G u v).Dart :=
  (deletedGraphDartEquiv huv).symm
    ⟨data.toRotationSystem.phi (reverseDart huv),
      ⟨hsuccForward, hsuccReverse⟩⟩

@[simp]
theorem deletedGraphDartEquiv_reverseSuccessorDart
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (hsuccForward : data.toRotationSystem.phi (reverseDart huv) ≠ forwardDart huv)
    (hsuccReverse : data.toRotationSystem.phi (reverseDart huv) ≠ reverseDart huv) :
    (deletedGraphDartEquiv huv
      (reverseSuccessorDart data huv hsuccForward hsuccReverse)).1 =
      data.toRotationSystem.phi (reverseDart huv) :=
  rfl

/-- Orbit-level form of the one-edge face surgery.  The predecessor that used
to enter the forward dart and the successor leaving the reverse dart occupy
one face orbit after deletion. -/
theorem dartOrbitFace_eq_reverseSuccessor_of_phi_eq_forward
    (data : Data G) {u v : V} (huv : G.Adj u v)
    (outer : (DeletedEdgeGraph G u v).Dart)
    (dart : (DeletedEdgeGraph G u v).Dart)
    (hphi : data.toRotationSystem.phi (deletedGraphDartEquiv huv dart).1 =
      forwardDart huv)
    (hsuccForward : data.toRotationSystem.phi (reverseDart huv) ≠ forwardDart huv)
    (hsuccReverse : data.toRotationSystem.phi (reverseDart huv) ≠ reverseDart huv) :
    dartOrbitFace (deletedEdgeData data huv outer).toRotationSystem dart =
      dartOrbitFace (deletedEdgeData data huv outer).toRotationSystem
        (reverseSuccessorDart data huv hsuccForward hsuccReverse) := by
  calc
    dartOrbitFace (deletedEdgeData data huv outer).toRotationSystem dart =
        dartOrbitFace (deletedEdgeData data huv outer).toRotationSystem
          ((deletedEdgeData data huv outer).toRotationSystem.phi dart) :=
      (dartOrbitFace_phi_eq _ _).symm
    _ = dartOrbitFace (deletedEdgeData data huv outer).toRotationSystem
          (reverseSuccessorDart data huv hsuccForward hsuccReverse) := by
      apply congrArg (dartOrbitFace (deletedEdgeData data huv outer).toRotationSystem)
      apply (deletedGraphDartEquiv huv).injective
      apply Subtype.ext
      change (deletedGraphDartEquiv huv
        ((deletedEdgeData data huv outer).toRotationSystem.phi dart)).1 =
        data.toRotationSystem.phi (reverseDart huv)
      rw [deletedEdgeData_phi_ambient_eq_of_phi_eq_forward data huv outer dart
        hphi hsuccReverse]

end

end GoertzelV24DeletedEdgeFaceMerge

end Mettapedia.GraphTheory.FourColor
