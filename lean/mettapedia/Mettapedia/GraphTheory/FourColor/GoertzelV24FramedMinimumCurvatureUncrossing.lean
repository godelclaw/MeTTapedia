import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedMinimumCurvaturePairing
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkTailExchange

/-!
# Metric uncrossing for the minimum framed curvature pairing

If two geodesic routes selected by the minimum weighted-L9 pairing meet at a
face, exchanging their tails preserves the minimum total distance.  Both
exchanged walks are consequently geodesics for the swapped endpoints.

This is the metric L6 uncrossing step.  It does not yet choose a simultaneous
route family with minimum crossing complexity or prove that such a family is
laminar in the annular rotation system.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open GoertzelV24WalkTailExchange
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

/-- Two intersecting geodesics belonging to the minimum curvature pairing
saturate the two-pair exchange inequality. -/
theorem minimumCurvaturePairing_crossed_dist_eq_of_shared_face
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (firstPentagon secondPentagon : embedded.InteriorPentagonToken)
    (firstDebt secondDebt : embedded.InteriorNegativeCurvatureToken)
    (hne : firstPentagon ≠ secondPentagon)
    (hfirst : embedded.minimumCurvatureCreditDebtEquiv hsource geometry
        (Sum.inl firstPentagon) = Sum.inl firstDebt)
    (hsecond : embedded.minimumCurvatureCreditDebtEquiv hsource geometry
        (Sum.inl secondPentagon) = Sum.inl secondDebt)
    (firstRoute : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).Walk
        firstDebt.face firstPentagon.face)
    (secondRoute : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).Walk
        secondDebt.face secondPentagon.face)
    (hfirstGeodesic : firstRoute.length =
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).dist
          firstDebt.face firstPentagon.face)
    (hsecondGeodesic : secondRoute.length =
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).dist
          secondDebt.face secondPentagon.face)
    (common : AmbientFace embedded.cellulation.interiorFaces)
    (hcommonFirst : common ∈ firstRoute.support)
    (hcommonSecond : common ∈ secondRoute.support) :
    (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).dist
        firstDebt.face firstPentagon.face +
      (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).dist
        secondDebt.face secondPentagon.face =
    (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).dist
        firstDebt.face secondPentagon.face +
      (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).dist
        secondDebt.face firstPentagon.face := by
  have hminimum :=
    embedded.minimumCurvatureCreditDebtEquiv_pentagon_exchange hsource
      geometry firstPentagon secondPentagon firstDebt secondDebt hne hfirst
      hsecond
  have hcrossed :=
    dist_add_dist_le_dist_add_dist_of_geodesics_shared_vertex firstRoute
      secondRoute hcommonFirst hcommonSecond hfirstGeodesic hsecondGeodesic
  omega

/-- At a shared face, swapping the tails of two minimum-pairing geodesics
again gives two geodesics, now for the crossed endpoint assignment. -/
theorem minimumCurvaturePairing_tailExchange_geodesic
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (firstPentagon secondPentagon : embedded.InteriorPentagonToken)
    (firstDebt secondDebt : embedded.InteriorNegativeCurvatureToken)
    (hne : firstPentagon ≠ secondPentagon)
    (hfirst : embedded.minimumCurvatureCreditDebtEquiv hsource geometry
        (Sum.inl firstPentagon) = Sum.inl firstDebt)
    (hsecond : embedded.minimumCurvatureCreditDebtEquiv hsource geometry
        (Sum.inl secondPentagon) = Sum.inl secondDebt)
    (firstRoute : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).Walk
        firstDebt.face firstPentagon.face)
    (secondRoute : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).Walk
        secondDebt.face secondPentagon.face)
    (hfirstGeodesic : firstRoute.length =
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).dist
          firstDebt.face firstPentagon.face)
    (hsecondGeodesic : secondRoute.length =
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).dist
          secondDebt.face secondPentagon.face)
    (common : AmbientFace embedded.cellulation.interiorFaces)
    (hcommonFirst : common ∈ firstRoute.support)
    (hcommonSecond : common ∈ secondRoute.support) :
    (firstExchange firstRoute secondRoute hcommonFirst hcommonSecond).length =
        (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).dist
            firstDebt.face secondPentagon.face ∧
      (secondExchange firstRoute secondRoute hcommonFirst hcommonSecond).length =
        (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).dist
            secondDebt.face firstPentagon.face := by
  have hdist :=
    embedded.minimumCurvaturePairing_crossed_dist_eq_of_shared_face hsource
      geometry firstPentagon secondPentagon firstDebt secondDebt hne hfirst
      hsecond firstRoute secondRoute hfirstGeodesic hsecondGeodesic common
      hcommonFirst hcommonSecond
  have hlength := firstExchange_length_add_secondExchange_length firstRoute
    secondRoute hcommonFirst hcommonSecond
  have hfirstLower := dist_le
    (firstExchange firstRoute secondRoute hcommonFirst hcommonSecond)
  have hsecondLower := dist_le
    (secondExchange firstRoute secondRoute hcommonFirst hcommonSecond)
  constructor <;> omega

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
