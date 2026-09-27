import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSphericity
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamCubic
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# Structural data for an oriented open-tangle composite

This is the final packaging layer for the fields already proved separately
about OpenTangleData.composeRotationSystem.

Two face-simple spherical hub closures and an orientation-reversing port
matching supply the spherical Euler field.  Connected, boundary-essential
open sides supply primal connectedness and bridge-freeness.  Open cubicity and
rotation-cyclicity transport literally through the composite carrier.

The hypotheses deliberately remain visible: constructing the two hub closures
from a tight noose is a separate geometric adapter.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CompositeStructuralData

open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24CompositeSeamMultigraph
open GoertzelV24CompositeSeamCubic
open GoertzelV24CompositeSphericity
open GoertzelV24SeamExchange
open GoertzelV24FaceDualConnectedness
open GoertzelV24BoundaryEssentialGluing
open GoertzelV24RotationSpliceConstructor
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24FaceOrbitIncidence
open GoertzelV24TwoEdgeCutMinimality

section Composite

variable {V W I L J R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  [Nonempty V]
  (left : OpenTangleData V I L) (right : OpenTangleData W J R)
  (matching : L ≃ R) (ρL : Equiv.Perm L) (ρR : Equiv.Perm R)

/-- The Euler calculation and open-side cubicity package directly as the
orbit-face spherical cubic interface consumed by the map theory. -/
def orbitSphericalCubicMapData_composeRotationSystem
    (hCubicL : OpenIsCubic left) (hCubicR : OpenIsCubic right)
    (hFacesL : HubFacesDistinct left ρL)
    (hFacesR : HubFacesDistinct right ρR)
    (hrev : OrientationReversing matching ρL ρR)
    (hSphereL : ClosedSideSpherical left ρL)
    (hSphereR : ClosedSideSpherical right ρR) :
    OrbitSphericalCubicMapData
      (left.composeRotationSystem right matching) where
  cubic :=
    isCubic_composeRotationSystem left right matching hCubicL hCubicR
  euler := by
    change
      (Fintype.card (V ⊕ W) : Int) -
          Fintype.card (compositeDarts left right matching).Edge +
          Fintype.card (OrbitFace (compositeRS left right matching)) = 2
    have hEuler :=
      composite_euler left right matching ρL ρR
        hFacesL hFacesR hrev hSphereL hSphereR
    have hEulerInt :
        (Fintype.card (V ⊕ W) : Int) +
            Fintype.card
              (OrbitFace (compositeRS left right matching)) =
          Fintype.card (compositeDarts left right matching).Edge + 2 := by
      exact_mod_cast hEuler
    omega

/-- All four structural fields of the cap-stable minimality class are
delivered on the literal composite rotation system. -/
def bridgelessSphericalCubicMapData_composeRotationSystem
    (hConnectedL : (sideMultigraph left).Connected)
    (hConnectedR : (sideMultigraph right).Connected)
    (hEssentialL :
      BoundaryEssential (sideMultigraph left) left.boundaryVert)
    (hEssentialR :
      BoundaryEssential (sideMultigraph right)
        (fun port : L => right.boundaryVert (matching port)))
    (p₀ q₀ : L) (hpq : p₀ ≠ q₀)
    (hCubicL : OpenIsCubic left) (hCubicR : OpenIsCubic right)
    (hRotationL : OpenRotationCyclic left)
    (hRotationR : OpenRotationCyclic right)
    (hFacesL : HubFacesDistinct left ρL)
    (hFacesR : HubFacesDistinct right ρR)
    (hrev : OrientationReversing matching ρL ρR)
    (hSphereL : ClosedSideSpherical left ρL)
    (hSphereR : ClosedSideSpherical right ρR) :
    BridgelessSphericalCubicMapData
      (left.composeRotationSystem right matching) where
  spherical :=
    orbitSphericalCubicMapData_composeRotationSystem
      left right matching ρL ρR
      hCubicL hCubicR hFacesL hFacesR hrev hSphereL hSphereR
  primalConnected :=
    primalConnected_composeRotationSystem
      left right matching hConnectedL hConnectedR p₀
  vertexRotationCyclic :=
    vertexRotationCyclic_composeRotationSystem
      left right matching hRotationL hRotationR
  edgeBridgeFree :=
    edgeBridgeFree_composeRotationSystem
      left right matching hConnectedL hConnectedR
      hEssentialL hEssentialR hpq

end Composite

end GoertzelV24CompositeStructuralData

end Mettapedia.GraphTheory.FourColor
