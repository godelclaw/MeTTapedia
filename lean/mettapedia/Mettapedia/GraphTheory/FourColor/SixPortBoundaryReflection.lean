import Mettapedia.GraphTheory.FourColor.GoertzelV24PhysicalKempeNoncrossingClosure
import Mathlib.Data.Fin.Rev

/-!
# Physical noncrossing in either boundary orientation

Complementary shores traverse a common cut in opposite directions. Reflecting
all six coordinates preserves crossing, including inactive fixed ports. Thus
the physical separator theorem applies to either orientation of the same cut.
-/

namespace Mettapedia.GraphTheory.FourColor.SixPortBoundaryReflection

open GoertzelV24PhysicalKempeNoncrossingClosure GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity GoertzelV24RotationCutDartDecomposition
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24VertexSidePrimalKempeTrail

theorem chordsCross_rev_iff (a b c d : Fin 6) :
    ChordsCross a.rev b.rev c.rev d.rev ↔ ChordsCross a b c d := by
  simp only [ChordsCross, Fin.val_rev]
  omega

theorem noncrossing_rev {mate : Fin 6 → Fin 6} (h : IsNoncrossingMatching mate) :
    IsNoncrossingMatching (fun i => (mate i.rev).rev) := by
  intro i j hc
  apply h i.rev j.rev
  have hh := (chordsCross_rev_iff i (mate i.rev).rev j (mate j.rev).rev).mpr hc
  simpa only [Fin.rev_rev] using hh

theorem rev_cycle : Fin.revPerm.permCongr (finRotate 6) = (finRotate 6)⁻¹ := by
  apply Equiv.ext
  intro i
  fin_cases i <;> decide

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Inverse cyclic coordinates need no new topological hypothesis. -/
theorem orderedPhysicalMate_isNoncrossing_inverse
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
    (order : Fin 6 ≃ BoundaryDart graphData.toRotationSystem keep)
    (horder : order.permCongr (finRotate 6) =
      (retainedRegionBoundarySuccessor graphData.toRotationSystem keep)⁻¹)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (hproper : IsProper coloring) (pair : TaitColorPair) :
    IsNoncrossingMatching (orderedPhysicalMate order
      (vertexSidePortTangle graphData keep outer)
      (isCubic_vertexSidePortTangle graphData keep outer hcubic) coloring hproper pair) := by
  let data : SixPortCyclicBondBoundaryData graphData.toRotationSystem keep :=
    { order := Fin.revPerm.trans order
      successor_eq := by
        change order.permCongr (Fin.revPerm.permCongr (finRotate 6)) = _
        rw [rev_cycle]
        exact congrArg Equiv.symm horder }
  have h := orderedPhysicalMate_isNoncrossing graphData htwoSided hdual hconnected
    hsphere hcubic hrotation keep hcomplementConnected data outer coloring hproper pair
  have hr := noncrossing_rev h
  convert hr using 1
  funext i
  simp only [orderedPhysicalMate, data, Equiv.trans_apply,
    Equiv.symm_trans_apply, Fin.revPerm_apply, Fin.revPerm_symm, Fin.rev_rev]

end
end Mettapedia.GraphTheory.FourColor.SixPortBoundaryReflection
