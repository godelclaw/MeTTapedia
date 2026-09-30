import Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement
import Mettapedia.GraphTheory.FourColor.OpenTangleConnectedReplacement
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexReflection
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# Map-class preservation from an exact boundary replacement

Equal ordered face returns and Euler mass preserve sphericity in every
fixed exterior. Connectedness and boundary-essentiality of the replacement
preserve bridge-freedom when that exterior is connected. Cubic vertex
rotations complete the ambient class needed by smaller-map induction.

The old and new interiors may have different vertex and dart carriers.
Colouring reconstruction and strict size decrease are separate obligations.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleReplacementClass

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24CompositeSeamMultigraph GoertzelV24BoundaryEssentialGluing
open GoertzelV24CompositeSeamCubic OpenTangleVertexReflection
open GoertzelV24TwoEdgeCutMinimality OpenTanglePortReplacement OpenTangleReplacementEuler

noncomputable section
variable {V W W' I J J' L R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype W'] [DecidableEq W'] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (outside : OpenTangleData V I L) (old : OpenTangleData W J R)
  (new : OpenTangleData W' J' R) (seam : L ≃ R)

/-- One class-preservation argument for arbitrary finite interfaces and
connected, boundary-essential interiors. All seam edges are retained. -/
theorem mapClass
    (hreturn : returnCode old = returnCode new) (hmass : eulerMass old = eulerMass new)
    (hcubic : OpenIsCubic new) (hcyclic : OpenRotationCyclic new)
    (hout : (sideMultigraph outside).Connected) (hnew : (sideMultigraph new).Connected)
    (he : BoundaryEssential (sideMultigraph new) (new.boundaryVert ∘ seam))
    {p q : L} (hpq : p ≠ q)
    (h : BridgelessSphericalCubicMapData (outside.composeRotationSystem old seam)) :
    BridgelessSphericalCubicMapData (outside.composeRotationSystem new seam) := by
  have hs := OpenTangleConnectedReplacement.replacement_structural outside old new seam seam
    hout hnew he ⟨h.primalConnected, h.edgeBridgeFree⟩ hpq
  have hEuler := (OpenTanglePortReplacement.euler_eq_iff_mass old new hreturn outside seam).mpr hmass
  exact {
    spherical := {
      cubic := isCubic_composeRotationSystem outside new seam
        (exterior_isCubic outside old seam h.spherical.cubic) hcubic
      euler := by
        change OpenTangleRewireFaces.compositeEuler outside new seam = 2
        rw [← hEuler]
        exact h.spherical.euler }
    primalConnected := hs.1
    vertexRotationCyclic := vertexRotationCyclic_composeRotationSystem outside new seam
      (exterior_rotationCyclic outside old seam h.vertexRotationCyclic) hcyclic
    edgeBridgeFree := hs.2 }

end
end Mettapedia.GraphTheory.FourColor.OpenTangleReplacementClass
