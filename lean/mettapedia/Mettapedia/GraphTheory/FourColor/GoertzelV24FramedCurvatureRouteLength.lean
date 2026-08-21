import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedDegreePath
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCurvatureRouteFamily

/-!
# Length versus congestion in the framed curvature-route family

The weighted L9 repair assigns all but the fixed source-foot allowance of
the negative-curvature tokens to distinct internal pentagons, then joins
each paired source face to its pentagon by a shortest path in the internal
facial dual.  This file proves the first quantitative alternative for that
actual route family.

For routes emitted by one negative-curvature face, either one route is
longer than a chosen radius or their distinct pentagon endpoints fit in the
closed dual ball of that radius.  Bounding the dual degree by the already
proved `W + 6` face-size bound gives an explicit capacity `(W + 7)^r`.
Pigeonhole over all internal source faces gives a formally correct global
alternative.  The final theorem below also records the decisive limitation:
that global capacity branch is automatic, because distinct paired routes
already have distinct pentagon endpoints.  Thus bounded-radius counting alone
cannot discharge high curvature; the next step must retain cyclic-order or
laminar information that this arbitrary exact-cardinality pairing forgets.

This is an L6 high-curvature entrance, not the missing planar depth theorem.
Its capacity still depends on the negative-curvature weight `W`; removing
that self-dependence requires the source's annular noncrossing/laminar
organization of the route family.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedDegreePath
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

local instance framedCurvatureRouteLengthInternalDualDecidableRel
    {source : SourceTrail G} {embedded : source.AnnularEmbedding} :
    DecidableRel
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).Adj :=
  Classical.decRel _

/-- At one negative-curvature face, either a paired route exceeds `radius`
or the distinct pentagon endpoints inject into the closed dual ball of that
radius. -/
theorem negativeFaceFiber_longRoute_or_card_le_boundedReach
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (face : AmbientFace embedded.cellulation.interiorFaces)
    (radius : Nat) :
    (∃ pair :
        {pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry //
          pair.negativeFace = face},
        radius < pair.1.curvatureRoute.length) ∨
      Fintype.card
          {pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry //
            pair.negativeFace = face} ≤
        (boundedReach
          (interiorDualGraph
            (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
            embedded.cellulation.interiorFaces)
          face radius).card := by
  classical
  by_cases hlong : ∃ pair :
      {pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry //
        pair.negativeFace = face},
      radius < pair.1.curvatureRoute.length
  · exact Or.inl hlong
  · right
    let endpoint :
        {pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry //
          pair.negativeFace = face} →
        {target // target ∈ boundedReach
          (interiorDualGraph
            (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
            embedded.cellulation.interiorFaces)
          face radius} := fun pair =>
      ⟨pair.1.pentagonFace, by
        have hendpoint :=
          endpoint_mem_boundedReach_of_walk_length_le _
            pair.1.curvatureRoute
            (Nat.le_of_not_gt (fun hroute => hlong ⟨pair, hroute⟩))
        simpa [pair.2] using hendpoint⟩
    simpa using Fintype.card_le_of_injective endpoint (by
        intro left right heq
        apply Subtype.ext
        exact pentagonFaceProjection_injective
          (congrArg Subtype.val heq))

/-- The internal facial dual has degree at most `W + 6`, where `W` is the
actual internal negative-curvature weight. -/
theorem internalDual_degree_le_negativeWeight_add_six
    {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    ∀ face : AmbientFace embedded.cellulation.interiorFaces,
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).degree face ≤
      embedded.interiorNegativeCurvatureWeight + 6 := by
  intro face
  exact (interiorDualGraph_degree_le_faceBoundary_card
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    embedded.cellulation.interiorFaces
    embedded.internalFace_incidence_le_two face).trans
      (embedded.internalFaceBoundary_card_le_weight_add_six face.2)

/-- A one-face fiber is either represented by a route longer than `radius`
or has the explicit bounded-degree capacity `(W + 7)^radius`. -/
theorem negativeFaceFiber_longRoute_or_card_le_pow
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (face : AmbientFace embedded.cellulation.interiorFaces)
    (radius : Nat) :
    (∃ pair :
        {pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry //
          pair.negativeFace = face},
        radius < pair.1.curvatureRoute.length) ∨
      Fintype.card
          {pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry //
            pair.negativeFace = face} ≤
        (embedded.interiorNegativeCurvatureWeight + 7) ^ radius := by
  rcases embedded.negativeFaceFiber_longRoute_or_card_le_boundedReach
      face radius with hlong | hshort
  · exact Or.inl hlong
  · exact Or.inr <| hshort.trans <|
      card_boundedReach_le_pow _
        (embedded.interiorNegativeCurvatureWeight + 6)
        embedded.internalDual_degree_le_negativeWeight_add_six face radius

/-- A sufficiently long paired curvature route is itself the geodesic axis
needed by the existing boundary-clean L1 path adapter. -/
theorem hasBoundaryCleanHexagonalGeodesicBlock_of_curvatureRoute
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry)
    (blockLength : Nat) (hpositive : 0 < blockLength)
    (hlong :
      (embedded.boundaryCleanContaminationBudget + 1) * blockLength ≤
        pair.curvatureRoute.length + 1) :
    embedded.HasBoundaryCleanHexagonalGeodesicBlock blockLength := by
  apply embedded.hasBoundaryCleanHexagonalGeodesicBlock_of_geodesic
    hsource geometry pair.curvatureRoute
  · exact pair.curvatureRoute.isPath_of_length_eq_dist
      pair.curvatureRoute_length_eq_dist
  · exact pair.curvatureRoute_length_eq_dist
  · exact hpositive
  · exact hlong

/-- Global length/congestion alternative for the actual curvature-route
family.  If no paired route is longer than `radius`, all pairs fit into the
number of internal source faces times the one-face capacity.  The theorem is
correct, but `pair_count_le_global_pow_capacity` below proves that its second
branch carries no new information globally. -/
theorem exists_long_curvatureRoute_or_pair_count_le
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (radius : Nat) :
    (∃ pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry,
        radius < pair.curvatureRoute.length) ∨
      Fintype.card
          (PentagonPairedNegativeCurvatureToken hsource embedded geometry) ≤
        Fintype.card (AmbientFace embedded.cellulation.interiorFaces) *
          (embedded.interiorNegativeCurvatureWeight + 7) ^ radius := by
  let capacity := (embedded.interiorNegativeCurvatureWeight + 7) ^ radius
  by_cases hlarge :
      Fintype.card (AmbientFace embedded.cellulation.interiorFaces) * capacity <
        Fintype.card
          (PentagonPairedNegativeCurvatureToken hsource embedded geometry)
  · left
    obtain ⟨face, hmany⟩ :=
      embedded.exists_negativeFace_with_many_pentagonRoutes
        hsource geometry capacity hlarge
    rcases embedded.negativeFaceFiber_longRoute_or_card_le_pow
        face radius with hlong | hcapacity
    · obtain ⟨pair, hpair⟩ := hlong
      exact ⟨pair.1, hpair⟩
    · exact False.elim (Nat.not_lt_of_ge hcapacity hmany)
  · right
    exact Nat.le_of_not_gt hlarge

/-- The complete paired route family has at most one route per internal face,
because its pentagon endpoints are distinct.  This is the global bound against
which any proposed curvature-route pigeonhole must be measured. -/
theorem card_pentagonPairedNegativeCurvatureToken_le_internalFaces
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    Fintype.card
        (PentagonPairedNegativeCurvatureToken hsource embedded geometry) ≤
      Fintype.card (AmbientFace embedded.cellulation.interiorFaces) := by
  calc
    Fintype.card
          (PentagonPairedNegativeCurvatureToken hsource embedded geometry) ≤
        embedded.interiorFaceLengths.count 5 :=
      embedded.card_pentagonPairedNegativeCurvatureToken_le_pentagons
        hsource geometry
    _ ≤ embedded.interiorFaceLengths.card := Multiset.count_le_card _ _
    _ = Fintype.card
          (AmbientFace embedded.cellulation.interiorFaces) := by
      simp [interiorFaceLengths]

/-- Kernel-checked refutation of the naive global bounded-ball strategy: its
displayed capacity bound holds for every radius, without assuming that the
curvature routes are short.  The factor `(W + 7)^radius` is at least one, while
the route family already injects into the internal faces through its distinct
pentagon endpoints.  Therefore this inequality cannot yield the missing
uniform `V₀`; a repair must use order, separation, or laminar depth. -/
theorem pair_count_le_global_pow_capacity
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (radius : Nat) :
    Fintype.card
        (PentagonPairedNegativeCurvatureToken hsource embedded geometry) ≤
      Fintype.card (AmbientFace embedded.cellulation.interiorFaces) *
        (embedded.interiorNegativeCurvatureWeight + 7) ^ radius := by
  have hpow : 1 ≤
      (embedded.interiorNegativeCurvatureWeight + 7) ^ radius := by
    have hpositive : 0 <
        (embedded.interiorNegativeCurvatureWeight + 7) ^ radius :=
      Nat.pow_pos (by omega)
    omega
  calc
    Fintype.card
          (PentagonPairedNegativeCurvatureToken hsource embedded geometry) ≤
        Fintype.card (AmbientFace embedded.cellulation.interiorFaces) :=
      embedded.card_pentagonPairedNegativeCurvatureToken_le_internalFaces
        hsource geometry
    _ = Fintype.card (AmbientFace embedded.cellulation.interiorFaces) * 1 := by
      omega
    _ ≤ Fintype.card (AmbientFace embedded.cellulation.interiorFaces) *
          (embedded.interiorNegativeCurvatureWeight + 7) ^ radius :=
      Nat.mul_le_mul_left _ hpow

/-- Quantitative high-curvature L1 alternative.  Either one of the actual
weighted-L9 routes contains a boundary-clean corridor of the requested
length, or the entire pentagon-backed route family obeys the displayed
self-dependent congestion bound.  The latter inequality is exposed for
diagnosis, but `pair_count_le_global_pow_capacity` shows that it is automatic;
it is not itself the missing laminar-depth input. -/
theorem hasBoundaryCleanHexagonalGeodesicBlock_or_pair_count_le
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (blockLength : Nat) (hpositive : 0 < blockLength) :
    embedded.HasBoundaryCleanHexagonalGeodesicBlock blockLength ∨
      Fintype.card
          (PentagonPairedNegativeCurvatureToken hsource embedded geometry) ≤
        Fintype.card (AmbientFace embedded.cellulation.interiorFaces) *
          (embedded.interiorNegativeCurvatureWeight + 7) ^
            (((embedded.boundaryCleanContaminationBudget + 1) *
              blockLength) - 1) := by
  let radius :=
    ((embedded.boundaryCleanContaminationBudget + 1) * blockLength) - 1
  rcases embedded.exists_long_curvatureRoute_or_pair_count_le
      hsource geometry radius with hlong | hcapacity
  · left
    obtain ⟨pair, hpair⟩ := hlong
    apply embedded.hasBoundaryCleanHexagonalGeodesicBlock_of_curvatureRoute
      hsource geometry pair blockLength hpositive
    dsimp [radius] at hpair
    omega
  · right
    simpa [radius] using hcapacity

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
