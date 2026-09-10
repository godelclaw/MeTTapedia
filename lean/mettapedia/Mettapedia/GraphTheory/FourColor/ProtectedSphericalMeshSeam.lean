import Mettapedia.GraphTheory.FourColor.ProtectedCubicMesh
import Mettapedia.GraphTheory.FourColor.SphericalMeshFreeSeam

/-!
# The spherical reduction alternative with a protected mesh carrier

Inflating the mesh dimensions by the proved avoidance loss upgrades the
existing alternative to a mesh whose complete paths avoid an ambient
buffer, or the same strictly smaller ordinary zero-Count map preserving
the designated edges. No clean mesh is assumed as input. The protected
carrier does not yet provide a clean disk or a reduction of the mesh branch.
-/

namespace Mettapedia.GraphTheory.FourColor.ProtectedSphericalMeshSeam

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationMultigraphAdapter GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24MajorityShorePhysicalReplacement
open MarkedSeamState MarkedCotreeSeam SphericalMeshFreeSeam ProtectedOrderedMesh

noncomputable section
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
  {M : Type v} [Fintype M]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A conservative dimension loss for a prescribed ambient buffer. -/
def loss (vertices radius : Nat) : Nat := 3 * (vertices * 4 ^ radius)

/-- Either construct a protected ordered mesh, or construct the existing
strict physical replacement. The latter preserves ordinary noncolourability,
not merely emptiness of an equality-constrained colouring fibre. -/
theorem exists_protectedMesh_or_marked_replacement (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable rotation.toRotationSystem)
    (p q radius : Nat) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (marks : Finset V) (mark : M → G.Dart)
    (hmarks : ∀ m, (mark m).fst ∈ marks)
    (hclosed : ∀ m, ∃ m', rotation.toRotationSystem.alpha (mark m) = mark m')
    (hlarge : sizeBound (p + loss marks.card radius) (q + loss marks.card radius)
      marks.card (Fintype.card M) < Fintype.card V) :
    (∃ mesh : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) p q,
      AvoidsVertices mesh (buffer G marks radius)) ∨
    ∃ w, w ≤ widthBound (p + loss marks.card radius) (q + loss marks.card radius)
      marks.card (Fintype.card M) ∧
      ∃ pair : SeamPair rotation marks mark w,
        Nonempty (StrictPhysicalReplacementData rotation pair.outer.shore pair.inner.shore
          pair.outer.outsideOuter pair.inner.innerOuter pair.width pair.outerWidth pair.innerWidth) ∧
        ∀ m, ∃ d : pair.candidate.D, pair.ambientDart d = mark m ∧
          pair.ambientDart (pair.candidate.alpha d) = rotation.toRotationSystem.alpha (mark m) := by
  rcases exists_orderedMesh_or_marked_replacement rotation ambient htwo hzero
      (p + loss marks.card radius) (q + loss marks.card radius) (by omega)
      marks mark hmarks hclosed hlarge with hm | replacement
  · obtain ⟨mesh⟩ := hm
    obtain ⟨r, c, hav⟩ := exists_buffer_avoiding_submesh rotation ambient.spherical.cubic
      mesh marks radius hp hq (by rfl) (by rfl)
    exact Or.inl ⟨restrict mesh r c, hav⟩
  · exact Or.inr replacement

end
end Mettapedia.GraphTheory.FourColor.ProtectedSphericalMeshSeam
