import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedMinimumCurvatureRouteFamily

/-!
# Simultaneous finite selection of minimum curvature routings

Metric uncrossing changes both the two routes and their endpoint assignment.
Consequently it is not enough to choose geodesics only after fixing one
minimum assignment.  This module defines a finite routing candidate as:

* any weighted-L9 assignment having the same minimum total distance as the
  canonical minimum assignment; and
* a geodesic table for every possible internal pentagon/negative-curvature
  endpoint pair.

For any natural-valued secondary complexity, Lean then chooses a simultaneous
candidate minimizing that complexity.  A later rotation-sensitive module must
define the actual crossing complexity and prove that uncrossing a forbidden
intersection strictly lowers it.  This file constructs the optimizer; it does
not assume or prove that strict-decrease theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

/-- Weighted-L9 assignments attaining the already constructed minimum total
internal-dual distance. -/
abbrev MinimumCurvatureAssignment
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :=
  {assignment : embedded.PositiveCurvatureCredit ≃
      embedded.NegativeCurvatureDebt //
    embedded.curvaturePairingCost assignment =
      embedded.curvaturePairingCost
        (embedded.minimumCurvatureCreditDebtEquiv hsource geometry)}

/-- The canonical minimum assignment, regarded as a member of the full finite
set of minimum assignments. -/
def canonicalMinimumCurvatureAssignment
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    MinimumCurvatureAssignment hsource embedded geometry :=
  ⟨embedded.minimumCurvatureCreditDebtEquiv hsource geometry, rfl⟩

/-- A geodesic for every possible internal pentagon/negative-curvature pair.
Only entries selected by an assignment are active, but the full table makes
endpoint swaps type-correct. -/
abbrev CurvatureGeodesicTable
    {source : SourceTrail G} (embedded : source.AnnularEmbedding) :=
  {routes : ∀ (pentagon : embedded.InteriorPentagonToken)
      (debt : embedded.InteriorNegativeCurvatureToken),
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).Path debt.face pentagon.face //
    ∀ (pentagon : embedded.InteriorPentagonToken)
      (debt : embedded.InteriorNegativeCurvatureToken),
      (routes pentagon debt).1.length =
        (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).dist debt.face pentagon.face}

/-- Connectedness of the internal facial dual supplies at least one complete
geodesic table. -/
noncomputable def canonicalCurvatureGeodesicTable
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    CurvatureGeodesicTable embedded := by
  let route := fun (pentagon : embedded.InteriorPentagonToken)
      (debt : embedded.InteriorNegativeCurvatureToken) =>
    Classical.choose
      (geometry.internalDualConnected.exists_path_of_dist
        debt.face pentagon.face)
  refine ⟨fun pentagon debt =>
      ⟨route pentagon debt,
        (Classical.choose_spec
          (geometry.internalDualConnected.exists_path_of_dist
            debt.face pentagon.face)).1⟩, ?_⟩
  intro pentagon debt
  exact (Classical.choose_spec
    (geometry.internalDualConnected.exists_path_of_dist
      debt.face pentagon.face)).2

/-- A simultaneous minimum-distance assignment and complete geodesic table. -/
abbrev MinimumCurvatureRouting
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :=
  MinimumCurvatureAssignment hsource embedded geometry ×
    CurvatureGeodesicTable embedded

/-- The finite candidate space is inhabited by the canonical minimum
assignment and canonical geodesic table. -/
noncomputable def canonicalMinimumCurvatureRouting
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    MinimumCurvatureRouting hsource embedded geometry :=
  (embedded.canonicalMinimumCurvatureAssignment hsource geometry,
    embedded.canonicalCurvatureGeodesicTable geometry)

noncomputable local instance minimumCurvatureAssignmentFintype
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry} :
    Fintype (MinimumCurvatureAssignment hsource embedded geometry) :=
  Fintype.ofFinite _

noncomputable local instance minimumCurvatureRoutingInternalDualDecidableRel
    {source : SourceTrail G} {embedded : source.AnnularEmbedding} :
    DecidableRel
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).Adj :=
  Classical.decRel _

noncomputable local instance curvatureGeodesicTableFintype
    {source : SourceTrail G} {embedded : source.AnnularEmbedding} :
    Fintype (CurvatureGeodesicTable embedded) :=
  Fintype.ofFinite _

/-- Choose, among all minimum-distance assignments and all complete geodesic
tables, a routing minimizing an arbitrary finite secondary complexity. -/
noncomputable def minimumSecondaryCurvatureRouting
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (complexity : MinimumCurvatureRouting hsource embedded geometry → Nat) :
    MinimumCurvatureRouting hsource embedded geometry := by
  let seed := embedded.canonicalMinimumCurvatureRouting hsource geometry
  let candidates : Finset
      (MinimumCurvatureRouting hsource embedded geometry) := Finset.univ
  exact Classical.choose
    (candidates.exists_min_image complexity ⟨seed, Finset.mem_univ seed⟩)

/-- The simultaneous selector has no larger secondary complexity than any
other minimum-distance assignment/geodesic-table candidate. -/
theorem minimumSecondaryCurvatureRouting_complexity_le
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (complexity : MinimumCurvatureRouting hsource embedded geometry → Nat)
    (other : MinimumCurvatureRouting hsource embedded geometry) :
    complexity
        (embedded.minimumSecondaryCurvatureRouting
          hsource geometry complexity) ≤
      complexity other := by
  let seed := embedded.canonicalMinimumCurvatureRouting hsource geometry
  let candidates : Finset
      (MinimumCurvatureRouting hsource embedded geometry) := Finset.univ
  exact Classical.choose_spec
    (candidates.exists_min_image complexity ⟨seed, Finset.mem_univ seed⟩) |>.2
      other (Finset.mem_univ other)

end AnnularEmbedding

end SourceTrail

end


end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
