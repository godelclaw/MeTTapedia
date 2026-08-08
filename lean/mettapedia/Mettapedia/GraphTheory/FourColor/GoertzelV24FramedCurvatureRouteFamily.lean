import Mathlib.Combinatorics.Pigeonhole
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCurvaturePairing

/-!
# Finite structure of the framed curvature-route family

The exact weighted-curvature pairing supplies canonical shortest dual routes
from long-face curvature tokens to pentagons.  This module records two finite
facts needed before the planar length/depth argument: different paired tokens
have different pentagon endpoints, and a sufficiently large route family must
concentrate many routes at one negative-curvature face.

No planar pumping or splice theorem is assumed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CurvatureScope
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

/-- The pentagon token at the target of a pentagon-backed curvature route. -/
def PentagonPairedNegativeCurvatureToken.pentagonToken
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry) :
    embedded.InteriorPentagonToken :=
  pair.1.2

/-- Exact weighted-L9 pairing never assigns two curvature tokens to the same
pentagon token. -/
theorem pentagonTokenProjection_injective
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry} :
    Function.Injective
      (fun pair : PentagonPairedNegativeCurvatureToken
          hsource embedded geometry => pair.pentagonToken) := by
  intro left right hpentagon
  have himages :
      (embedded.curvatureCreditDebtEquiv hsource geometry).symm
          (Sum.inl left.1.1) =
        (embedded.curvatureCreditDebtEquiv hsource geometry).symm
          (Sum.inl right.1.1) := by
    calc
      (embedded.curvatureCreditDebtEquiv hsource geometry).symm
          (Sum.inl left.1.1) = Sum.inl left.1.2 := left.2
      _ = Sum.inl right.1.2 := congrArg Sum.inl hpentagon
      _ = (embedded.curvatureCreditDebtEquiv hsource geometry).symm
          (Sum.inl right.1.1) := right.2.symm
  have hnegative : left.1.1 = right.1.1 := by
    exact Sum.inl.inj
      ((embedded.curvatureCreditDebtEquiv hsource geometry).symm.injective
        himages)
  apply Subtype.ext
  exact Prod.ext hnegative hpentagon

/-- Pentagon-backed curvature routes have pairwise distinct pentagon faces. -/
theorem pentagonFaceProjection_injective
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry} :
    Function.Injective
      (fun pair : PentagonPairedNegativeCurvatureToken
          hsource embedded geometry => pair.pentagonFace) := by
  intro left right hface
  apply pentagonTokenProjection_injective
  apply Subtype.ext
  exact congrArg
    (fun face : AmbientFace embedded.cellulation.interiorFaces => face.1)
    hface

/-- The number of pentagon-backed curvature routes is at most the number of
internal pentagons. -/
theorem card_pentagonPairedNegativeCurvatureToken_le_pentagons
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    Fintype.card
        (PentagonPairedNegativeCurvatureToken hsource embedded geometry) ≤
      embedded.interiorFaceLengths.count 5 := by
  calc
    Fintype.card
        (PentagonPairedNegativeCurvatureToken hsource embedded geometry) ≤
        Fintype.card embedded.InteriorPentagonToken :=
      Fintype.card_le_of_injective
        (fun pair : PentagonPairedNegativeCurvatureToken
          hsource embedded geometry => pair.pentagonToken)
        pentagonTokenProjection_injective
    _ = embedded.interiorFaceLengths.count 5 :=
      embedded.card_interiorPentagonToken

/-- If the route family is larger than `bound` times the number of internal
faces, one negative-curvature face emits more than `bound` routes. -/
theorem exists_negativeFace_with_many_pentagonRoutes
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) (bound : Nat)
    (hlarge :
      Fintype.card (AmbientFace embedded.cellulation.interiorFaces) * bound <
        Fintype.card
          (PentagonPairedNegativeCurvatureToken hsource embedded geometry)) :
    ∃ face : AmbientFace embedded.cellulation.interiorFaces,
      bound < Fintype.card
        {pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry //
          pair.negativeFace = face} := by
  obtain ⟨face, hface⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card
      (f := fun pair : PentagonPairedNegativeCurvatureToken
        hsource embedded geometry => pair.negativeFace)
      hlarge
  refine ⟨face, ?_⟩
  rw [Fintype.card_subtype]
  exact hface

/-- Either one negative-curvature face emits many routes, or the whole route
family has the corresponding finite congestion bound. -/
theorem negativeFace_congestion_or_pair_count_le
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) (bound : Nat) :
    (∃ face : AmbientFace embedded.cellulation.interiorFaces,
      bound < Fintype.card
        {pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry //
          pair.negativeFace = face}) ∨
      Fintype.card
          (PentagonPairedNegativeCurvatureToken hsource embedded geometry) ≤
        Fintype.card (AmbientFace embedded.cellulation.interiorFaces) * bound := by
  by_cases hlarge :
      Fintype.card (AmbientFace embedded.cellulation.interiorFaces) * bound <
        Fintype.card
          (PentagonPairedNegativeCurvatureToken hsource embedded geometry)
  · exact Or.inl
      (embedded.exists_negativeFace_with_many_pentagonRoutes
        hsource geometry bound hlarge)
  · exact Or.inr (Nat.le_of_not_gt hlarge)

/-- Even among routes emitted by one negative-curvature face, pentagon
endpoints remain pairwise distinct. -/
theorem negativeFaceFiber_pentagonFace_injective
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (face : AmbientFace embedded.cellulation.interiorFaces) :
    Function.Injective
      (fun pair :
          {pair : PentagonPairedNegativeCurvatureToken
              hsource embedded geometry // pair.negativeFace = face} =>
        pair.1.pentagonFace) := by
  intro left right hface
  apply Subtype.ext
  exact pentagonFaceProjection_injective hface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
