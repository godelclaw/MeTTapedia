import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching
import Mathlib.Data.Fin.Rev

/-!
# Physical noncrossing in either orientation at arbitrary width

Reversing all boundary coordinates preserves crossings and conjugates the
cyclic successor to its inverse. Thus the same physical separator theorem
applies to the boundary as seen from either complementary shore.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

open BoundaryKempeSwitch
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24PortTangleCutParity GoertzelV24RotationCutDartDecomposition
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24VertexSidePrimalKempeTrail

variable {n : ℕ}

theorem chordsCross_rev_iff (a b c d : Fin n) :
    ChordsCross a.rev b.rev c.rev d.rev ↔ ChordsCross a b c d := by
  simp only [ChordsCross, Fin.val_rev]
  omega

theorem noncrossing_rev {mate : Fin n → Fin n} (h : IsNoncrossingMatching mate) :
    IsNoncrossingMatching (fun i => (mate i.rev).rev) := by
  intro i j hc
  apply h i.rev j.rev
  have hh := (chordsCross_rev_iff i (mate i.rev).rev j (mate j.rev).rev).mpr hc
  simpa only [Fin.rev_rev] using hh

theorem rev_cycle : Fin.revPerm.permCongr (finRotate n) = (finRotate n)⁻¹ := by
  apply Equiv.ext
  intro i
  have := i.neZero
  simp [Fin.rev_add]

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance inverseGraphEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Inverse cyclic coordinates retain the same physical component pairing. -/
theorem physicalMateInCoordinates_isNoncrossing_inverse
    (graphData : SimpleGraphDartRotation.Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (keep : V → Prop)
    (hcomplementConnected : (G.induce {v | ¬keep v}).Connected)
    (hwidth : 2 ≤ n)
    (order : Fin n ≃ BoundaryDart graphData.toRotationSystem keep)
    (horder : order.permCongr (finRotate n) =
      (retainedRegionBoundarySuccessor graphData.toRotationSystem keep)⁻¹)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (hproper : IsProper coloring) (pair : TaitColorPair) :
    IsNoncrossingMatching (physicalMateInCoordinates order
      (vertexSidePortTangle graphData keep outer)
      (isCubic_vertexSidePortTangle graphData keep outer hcubic) coloring hproper pair) := by
  have hs : (Fin.revPerm.trans order).permCongr (finRotate n) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem keep := by
    change order.permCongr (Fin.revPerm.permCongr (finRotate n)) = _
    rw [rev_cycle]
    exact congrArg Equiv.symm horder
  have h := physicalMateInCoordinates_isNoncrossing graphData htwoSided hdual hconnected
    hsphere hcubic hrotation keep hcomplementConnected hwidth (Fin.revPerm.trans order) hs
    outer coloring hproper pair
  have hr := noncrossing_rev h
  convert hr using 1
  funext i
  simp only [physicalMateInCoordinates, Equiv.trans_apply,
    Equiv.symm_trans_apply, Fin.revPerm_apply, Fin.revPerm_symm, Fin.rev_rev]

end
end Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching
