import Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeSupport
import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutShoreLanguage

/-!
# The exceptional pentagon profile for physical shores

The finite support classification applies to literal proper colourings of a
cubic port tangle. For a spherical vertex shore, the existing separator
theorem supplies the noncrossing premise in the actual cyclic boundary order.

A starting proper shore colouring is explicit. The theorem neither supplies
that colouring nor rules out the exceptional profile. Its positive conclusion
contains both a shore colouring and an internal pentagon colouring with the
same five spoke colours.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeSupport

open BoundaryKempeSwitch CyclicBoundaryMatching FiveCutShoreLanguage
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24PortTangleCutParity
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle

universe u

variable {V I P : Type u}
  [Fintype V] [Fintype I] [Fintype P]
  [DecidableEq V] [DecidableEq I] [DecidableEq P]

/-- Remove only the nonzero subtypes from the existing exact support. -/
theorem shoreLanguage_iff_coloring (order : Fin 5 ≃ P) (T : PortTangle V I P)
    (w : CAP5BoundaryWord) :
    shoreLanguage order T w ↔
      ∃ coloring : Coloring T, IsProper coloring ∧
        (fun i => word coloring (order i)) = w := by
  constructor
  · rintro ⟨boundary, ⟨coloring, hproper, hword⟩, hval⟩
    refine ⟨coloring, hproper, ?_⟩
    funext i
    have h := congrFun hword (order i)
    simpa only [Equiv.symm_apply_apply, hval] using h
  · rintro ⟨coloring, hproper, rfl⟩
    exact shoreLanguage_of_coloring order coloring hproper

/-- A literal compatible pair of shore and pentagon colourings. -/
def CompatiblePentagon (order : Fin 5 ≃ P) (T : PortTangle V I P) : Prop :=
  ∃ coloring : Coloring T, IsProper coloring ∧
    ∃ cycle : CAP5InternalCycleColoring,
      CAP5ExtendsAcrossCycleWith (fun i => word coloring (order i)) cycle

/-- With one starting colouring and noncrossing physical mates, compatibility
fails precisely at the exceptional five-orbit profile. -/
theorem compatiblePentagon_iff_ne_bad
    (order : Fin 5 ≃ P) (T : PortTangle V I P) (hcubic : IsCubic T)
    (hnc : ∀ (coloring : Coloring T) (hproper : IsProper coloring)
      (pair : TaitColorPair), IsNoncrossingMatching
        (physicalMateInCoordinates order T hcubic coloring hproper pair))
    (hcolorable : ∃ coloring : Coloring T, IsProper coloring) :
    CompatiblePentagon order T ↔
      orbitSupport (shoreLanguage order T) ≠ (bad : Set (Fin 10)) := by
  have hL := boundaryLanguage_shoreLanguage order T hcubic hnc
  have hne : ∃ w, shoreLanguage order T w := by
    obtain ⟨coloring, hproper⟩ := hcolorable
    exact ⟨_, shoreLanguage_of_coloring order coloring hproper⟩
  rw [← meets_pentagon_iff_ne_bad hL hne]
  constructor
  · rintro ⟨coloring, hproper, cycle, hcycle⟩
    exact ⟨_, (shoreLanguage_iff_coloring order T _).mpr
      ⟨coloring, hproper, rfl⟩, cycle, hcycle⟩
  · rintro ⟨w, hw, cycle, hcycle⟩
    obtain ⟨coloring, hproper, hword⟩ := (shoreLanguage_iff_coloring order T w).mp hw
    exact ⟨coloring, hproper, cycle, hword.symm ▸ hcycle⟩

/-- Failure of pentagon gluing determines the entire shore language. -/
theorem shoreLanguage_eq_rejected_of_incompatible
    (order : Fin 5 ≃ P) (T : PortTangle V I P) (hcubic : IsCubic T)
    (hnc : ∀ (coloring : Coloring T) (hproper : IsProper coloring)
      (pair : TaitColorPair), IsNoncrossingMatching
        (physicalMateInCoordinates order T hcubic coloring hproper pair))
    (hcolorable : ∃ coloring : Coloring T, IsProper coloring)
    (hnot : ¬ CompatiblePentagon order T) : shoreLanguage order T = Rejected := by
  apply language_eq_rejected_of_avoids
    (boundaryLanguage_shoreLanguage order T hcubic hnc)
  · obtain ⟨coloring, hproper⟩ := hcolorable
    exact ⟨_, shoreLanguage_of_coloring order coloring hproper⟩
  · intro w hw hext
    obtain ⟨coloring, hproper, hword⟩ := (shoreLanguage_iff_coloring order T w).mp hw
    exact hnot ⟨coloring, hproper, hword.symm ▸ hext⟩

section Spherical

open SimpleGraphDartRotation
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenTangleComposition GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition GoertzelV24VertexSidePrimalKempeTrail

variable {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph W} [DecidableRel G.Adj]

/-- The exact geometric adapter: the noncrossing premise is proved from
spherical shore geometry, with every side condition retained. -/
theorem spherical_compatiblePentagon_iff_ne_bad
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (keep : W → Prop)
    (hcomplementConnected : (G.induce {vertex | ¬keep vertex}).Connected)
    (order : Fin 5 ≃ BoundaryDart graphData.toRotationSystem keep)
    (hsuccessor : order.permCongr (finRotate 5) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem keep)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (hcolorable : ∃ coloring : Coloring (vertexSidePortTangle graphData keep outer),
      IsProper coloring) :
    CompatiblePentagon order (vertexSidePortTangle graphData keep outer) ↔
      orbitSupport (shoreLanguage order (vertexSidePortTangle graphData keep outer)) ≠
        (bad : Set (Fin 10)) :=
  compatiblePentagon_iff_ne_bad order _
    (isCubic_vertexSidePortTangle graphData keep outer hcubic)
    (fun coloring hproper pair => physicalMateInCoordinates_isNoncrossing_five
      graphData htwoSided hdual hconnected hsphere hcubic hrotation keep
      hcomplementConnected order hsuccessor outer coloring hproper pair) hcolorable

end Spherical

end Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeSupport
