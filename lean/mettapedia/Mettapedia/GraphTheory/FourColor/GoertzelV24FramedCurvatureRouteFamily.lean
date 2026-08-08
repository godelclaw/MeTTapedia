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

/-- The long-face curvature token at the source of a pentagon-backed route. -/
def PentagonPairedNegativeCurvatureToken.negativeToken
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry) :
    embedded.InteriorNegativeCurvatureToken :=
  pair.1.1

/-- Exact weighted-L9 pairing never uses one long-face curvature token twice. -/
theorem negativeTokenProjection_injective
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry} :
    Function.Injective
      (fun pair : PentagonPairedNegativeCurvatureToken
          hsource embedded geometry => pair.negativeToken) := by
  intro left right hnegative
  have hpentagon : left.1.2 = right.1.2 := by
    apply Sum.inl.inj
    calc
      Sum.inl left.1.2 =
          (embedded.curvatureCreditDebtEquiv hsource geometry).symm
            (Sum.inl left.1.1) := left.2.symm
      _ = (embedded.curvatureCreditDebtEquiv hsource geometry).symm
            (Sum.inl right.1.1) := congrArg
              (fun token =>
                (embedded.curvatureCreditDebtEquiv hsource geometry).symm
                  (Sum.inl token)) hnegative
      _ = Sum.inl right.1.2 := right.2
  apply Subtype.ext
  exact Prod.ext hnegative hpentagon

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

/-- Curvature tokens supported on one face are exactly its units of excess
over length six. -/
noncomputable def negativeCurvatureTokenAtFaceEquiv
    {source : SourceTrail G}
    (embedded : source.AnnularEmbedding)
    (face : AmbientFace embedded.cellulation.interiorFaces) :
    {token : embedded.InteriorNegativeCurvatureToken // token.1 = face} ≃
      Fin ((orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face.1).card - 6) where
  toFun token := Fin.cast
    (congrArg
      (fun current : AmbientFace embedded.cellulation.interiorFaces =>
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
          current.1).card - 6)
      token.2)
    token.1.2
  invFun index := ⟨⟨face, index⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨tokenFace, index⟩, hface⟩
    change tokenFace = face at hface
    subst tokenFace
    rfl
  right_inv := by
    intro index
    rfl

theorem card_negativeCurvatureTokenAtFace
    {source : SourceTrail G}
    (embedded : source.AnnularEmbedding)
    (face : AmbientFace embedded.cellulation.interiorFaces) :
    Fintype.card
        {token : embedded.InteriorNegativeCurvatureToken // token.1 = face} =
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face.1).card - 6 := by
  rw [Fintype.card_congr
    (embedded.negativeCurvatureTokenAtFaceEquiv face)]
  exact Fintype.card_fin _

/-- Restrict the source-token projection to the routes emitted by one face. -/
def negativeTokenAtNegativeFace
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (face : AmbientFace embedded.cellulation.interiorFaces)
    (pair :
      {pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry //
        pair.negativeFace = face}) :
    {token : embedded.InteriorNegativeCurvatureToken // token.1 = face} :=
  ⟨pair.1.negativeToken, pair.2⟩

theorem negativeTokenAtNegativeFace_injective
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (face : AmbientFace embedded.cellulation.interiorFaces) :
    Function.Injective
      (negativeTokenAtNegativeFace
        (hsource := hsource) (geometry := geometry) face) := by
  intro left right htoken
  apply Subtype.ext
  apply negativeTokenProjection_injective
  exact congrArg Subtype.val htoken

/-- A face of length `m` can emit at most `m - 6` pentagon-backed curvature
routes: the exact pairing has only that many source tokens on the face. -/
theorem card_negativeFaceFiber_le_faceExcess
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (face : AmbientFace embedded.cellulation.interiorFaces) :
    Fintype.card
        {pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry //
          pair.negativeFace = face} ≤
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face.1).card - 6 := by
  calc
    Fintype.card
        {pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry //
          pair.negativeFace = face} ≤
        Fintype.card
          {token : embedded.InteriorNegativeCurvatureToken // token.1 = face} :=
      Fintype.card_le_of_injective
        (negativeTokenAtNegativeFace
          (hsource := hsource) (geometry := geometry) face)
        (negativeTokenAtNegativeFace_injective face)
    _ = _ := embedded.card_negativeCurvatureTokenAtFace face

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

/-- If the complete route family is too large for `bound` routes per internal
face, some source face has length strictly larger than `bound + 6`. -/
theorem exists_long_negativeFace_of_many_pentagonRoutes
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) (bound : Nat)
    (hlarge :
      Fintype.card (AmbientFace embedded.cellulation.interiorFaces) * bound <
        Fintype.card
          (PentagonPairedNegativeCurvatureToken hsource embedded geometry)) :
    ∃ face : AmbientFace embedded.cellulation.interiorFaces,
      bound + 6 <
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
          face.1).card := by
  obtain ⟨face, hmany⟩ :=
    embedded.exists_negativeFace_with_many_pentagonRoutes
      hsource geometry bound hlarge
  refine ⟨face, ?_⟩
  have hcapacity := card_negativeFaceFiber_le_faceExcess
    (hsource := hsource) (geometry := geometry) face
  omega

/-- Weighted negative curvature above the per-face congestion budget and the
fixed source-foot allowance forces a quantitatively long internal face. -/
theorem exists_long_negativeFace_of_weight_gt
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) (bound : Nat)
    (hweight :
      Fintype.card (AmbientFace embedded.cellulation.interiorFaces) * bound +
          4 + 2 * source.frozenInterfaceStubVertices.card <
        embedded.interiorNegativeCurvatureWeight) :
    ∃ face : AmbientFace embedded.cellulation.interiorFaces,
      bound + 6 <
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
          face.1).card := by
  apply embedded.exists_long_negativeFace_of_many_pentagonRoutes
    hsource geometry bound
  exact embedded.pentagonPairBound_lt_card_of_weight_gt
    hsource geometry
    (pairBound :=
      Fintype.card (AmbientFace embedded.cellulation.interiorFaces) * bound)
    hweight

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
