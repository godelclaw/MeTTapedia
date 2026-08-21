import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationBridge

/-!
# Endpoint injectivity for graph-backed rotations

A finite simple graph has at most one edge with a given unordered endpoint
pair.  This small bridge records the corresponding rotation-system fact.
It supplies the representation premise used when a source graph's rotation is
converted back into its computed primal graph.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SimpleGraphRotationEndpointInjective

open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A finite simple graph's edge endpoint sets identify its edges. -/
theorem endpoints_injective (data : Data G) :
    Function.Injective data.toRotationSystem.endpoints := by
  intro first second hends
  apply Subtype.ext
  apply Sym2.ext
  intro vertex
  rw [← GoertzelV24RotationVertexCutProfile.mem_simpleGraphRotationSystem_endpoints_iff
      data first vertex,
    ← GoertzelV24RotationVertexCutProfile.mem_simpleGraphRotationSystem_endpoints_iff
      data second vertex,
    hends]

end GoertzelV24SimpleGraphRotationEndpointInjective

end Mettapedia.GraphTheory.FourColor
