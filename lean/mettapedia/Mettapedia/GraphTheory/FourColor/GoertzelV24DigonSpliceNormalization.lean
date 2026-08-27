import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonSuppressionSphere
import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonThetaColoring

/-!
# Parallel-seam normalization

Suppressing a digon takes a bridgeless spherical cubic map to a bridgeless
spherical cubic map with two fewer vertices, and preserves failure of Tait
colourability.  The one configuration it cannot treat — the theta, where both
exterior edges are the same edge — is Tait colourable outright.

So a counterexample of least vertex count carries no parallel pair at all:
either it would suppress to a smaller counterexample, or it is a theta and is
already coloured.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationEdgeBridge
open GoertzelV24TwoEdgeCutMinimality

noncomputable section

namespace DigonPatchData

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem V E} (D : @DigonPatchData V E)

/-- **The digon splice.**  Away from the theta configuration, suppressing a
parallel pair stays inside the bridgeless spherical cubic class. -/
theorem suppressed_bridgelessSphericalCubicMapData
    (hD : D.WellFormed RS) (hclass : BridgelessSphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS) (houter : D.vFar hD ≠ D.u) :
    BridgelessSphericalCubicMapData
      (D.suppressed hD hclass.spherical.cubic hclass.edgeBridgeFree houter) :=
  { spherical :=
      D.suppressed_orbitSphericalCubicMapData hD hclass.spherical.cubic
        hclass.edgeBridgeFree houter hclass.vertexRotationCyclic
        (D.hasExactDigonFace_of_twoSided hD hclass.spherical.cubic
          hclass.vertexRotationCyclic htwoSided houter)
        hclass.spherical
    primalConnected :=
      D.suppressed_primalConnected hD hclass.spherical.cubic
        hclass.edgeBridgeFree houter hclass.primalConnected
    vertexRotationCyclic :=
      D.suppressed_vertexRotationCyclic hD hclass.spherical.cubic
        hclass.edgeBridgeFree houter hclass.vertexRotationCyclic
    edgeBridgeFree :=
      D.suppressed_edgeBridgeFree hD hclass.spherical.cubic
        hclass.edgeBridgeFree houter hclass.primalConnected }

/-- Consumer-facing form of the digon splice: away from the theta branch,
suppression stays in the structural class and removes exactly two vertices. -/
theorem suppressed_class_and_card
    (hD : D.WellFormed RS) (hclass : BridgelessSphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS) (houter : D.vFar hD ≠ D.u) :
    BridgelessSphericalCubicMapData
        (D.suppressed hD hclass.spherical.cubic hclass.edgeBridgeFree houter) ∧
      Fintype.card
          (D.twoEdgeCut hD hclass.spherical.cubic
            hclass.edgeBridgeFree houter).complementData.CapVertex + 2 =
        Fintype.card V :=
  ⟨D.suppressed_bridgelessSphericalCubicMapData hD hclass htwoSided houter,
    D.card_suppressed_vertex hD hclass.spherical.cubic
      hclass.edgeBridgeFree houter⟩

end DigonPatchData

/-- **Parallel-seam normalization.**  A vertex-minimal Tait counterexample in
the bridgeless spherical cubic class has no parallel pair. -/
theorem no_wellFormed_digonPatchData_of_minimal
    {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (RS : RotationSystem.{u, u, u} V E)
    (hclass : BridgelessSphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hnot : ¬ RotationSystemTaitColorable RS)
    (hsmaller :
      ∀ {V' E' : Type u}
        [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
        (candidate : RotationSystem.{u, u, u} V' E'),
        Fintype.card V' < Fintype.card V →
        BridgelessSphericalCubicMapData candidate →
        RotationSystemTaitColorable candidate)
    (D : @DigonPatchData V E) (hD : D.WellFormed RS) : False := by
  classical
  by_cases htheta : D.vFar hD = D.u
  · exact hnot
      (D.taitColorable_of_theta hD hclass.spherical.cubic htheta
        hclass.primalConnected)
  · refine D.not_suppressed_taitColorable hD hclass.spherical.cubic
      hclass.edgeBridgeFree htheta hnot ?_
    exact hsmaller
      (D.suppressed hD hclass.spherical.cubic hclass.edgeBridgeFree htheta)
      (D.card_suppressed_vertex_lt hD hclass.spherical.cubic
        hclass.edgeBridgeFree htheta)
      (D.suppressed_bridgelessSphericalCubicMapData hD hclass htwoSided htheta)

end

end RotationSystem

/-! ## Publication-facing declaration aliases

The implementation theorems above live in the generic `RotationSystem`
namespace.  These aliases put the two consumer-facing results under the module
namespace as well, so a manuscript citation determines its defining module
without a global source search.
-/

alias GoertzelV24DigonSpliceNormalization.suppressed_class_and_card :=
  RotationSystem.DigonPatchData.suppressed_class_and_card

alias GoertzelV24DigonSpliceNormalization.no_wellFormed_digonPatchData_of_minimal :=
  RotationSystem.no_wellFormed_digonPatchData_of_minimal

end Mettapedia.GraphTheory.FourColor
