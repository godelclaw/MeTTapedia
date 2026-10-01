import Mettapedia.GraphTheory.FourColor.DualTruncateBrooksSource
import Mettapedia.GraphTheory.FourColor.DualTruncateSourceDomainExample
import Mettapedia.GraphTheory.FourColor.DualTruncateInverseExample

/-!
# Target-only Brooks consumers on the prism and cube expansions

The eighteen- and twenty-four-vertex targets supply their own inverse
face-cover data, connectivity and size. The general source theorem now
constructs both recovered colourings, independently of their earlier
source-specific coupled or cyclic-cut suppliers.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateBrooksExample

open DualTruncateColoring DualTruncateInverse
open GoertzelV24FaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

noncomputable section
attribute [local instance] Classical.propDecidable

theorem prism_recovered_colouring :
    Nonempty (ThreeVertexColoring DualTruncateSourceDomainExample.recovered) :=
  DualTruncateBrooksSource.inverse_source DualTruncateSourceDomainExample.target
    DualTruncateSourceDomainExample.data
    (DualTruncateFaceGeometry.facesTwoSided DualTruncateSourceDomainExample.original)
    DualTruncateSourceDomainExample.unmarked_hexagons
    DualTruncateSourceDomainExample.target_mapClass.primalConnected (by decide +kernel)

theorem prism_target_tait : RotationSystemTaitColorable DualTruncateSourceDomainExample.target :=
  DualTruncateBrooksSource.inverse_tait DualTruncateSourceDomainExample.target
    DualTruncateSourceDomainExample.data
    (DualTruncateFaceGeometry.facesTwoSided DualTruncateSourceDomainExample.original)
    DualTruncateSourceDomainExample.unmarked_hexagons
    DualTruncateSourceDomainExample.target_mapClass.primalConnected (by decide +kernel)

theorem cube_recovered_colouring :
    Nonempty (ThreeVertexColoring DualTruncateInverseExample.recovered) :=
  DualTruncateBrooksSource.inverse_source DualTruncateInverseExample.target
    DualTruncateInverseExample.data
    (DualTruncateFaceGeometry.facesTwoSided DualTruncateInverseExample.original)
    DualTruncateInverseExample.unmarked_hexagons
    DualTruncateGeometryExample.target_mapClass.primalConnected (by decide +kernel)

theorem cube_target_tait : RotationSystemTaitColorable DualTruncateInverseExample.target :=
  DualTruncateBrooksSource.inverse_tait DualTruncateInverseExample.target
    DualTruncateInverseExample.data
    (DualTruncateFaceGeometry.facesTwoSided DualTruncateInverseExample.original)
    DualTruncateInverseExample.unmarked_hexagons
    DualTruncateGeometryExample.target_mapClass.primalConnected (by decide +kernel)

theorem prism_every_complete_sweep (order : List DualTruncateSourceDomainExample.original.D)
    (hn : order.Nodup) (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic DualTruncateSourceDomainExample.original)
        (DualTruncateConstructionGSLT.rotationCyclic DualTruncateSourceDomainExample.original)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 := by
  obtain ⟨c⟩ := prism_recovered_colouring
  exact DualTruncateInverseGeometry.every_complete_sweep DualTruncateSourceDomainExample.target
    DualTruncateSourceDomainExample.data
    (DualTruncateFaceGeometry.facesTwoSided DualTruncateSourceDomainExample.original)
    c order hn he hcover

theorem cube_every_complete_sweep (order : List DualTruncateInverseExample.original.D)
    (hn : order.Nodup) (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic DualTruncateInverseExample.original)
        (DualTruncateConstructionGSLT.rotationCyclic DualTruncateInverseExample.original)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 := by
  obtain ⟨c⟩ := cube_recovered_colouring
  exact DualTruncateInverseGeometry.every_complete_sweep DualTruncateInverseExample.target
    DualTruncateInverseExample.data
    (DualTruncateFaceGeometry.facesTwoSided DualTruncateInverseExample.original)
    c order hn he hcover

/-- The exception is necessary even at the allowed degree bound. -/
theorem four_clique_exception : ¬(⊤ : SimpleGraph (Fin 4)).Colorable 3 := by
  intro hc
  apply hc.cliqueFree (by decide : 3 < 4) Finset.univ
  refine ⟨?_, by decide⟩
  intro x _ y _ hxy
  exact hxy

end
end Mettapedia.GraphTheory.FourColor.DualTruncateBrooksExample
