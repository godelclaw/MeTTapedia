import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedMinimumCurvatureUncrossing

/-!
# The route family of the minimum framed curvature pairing

The minimum weighted-L9 assignment is converted here into its literal finite
family of pentagon-backed negative-curvature tokens.  Every member carries a
shortest path in the internal facial dual.  Distinct members have distinct
negative-curvature and pentagon tokens, and the fixed source-foot credits can
absorb only their fixed number of negative-curvature debts.

This is the source-facing route family for the L6 repair.  It replaces the
older family built from an arbitrary exact-cardinality pairing.  The final
theorem packages metric tail exchange for two intersecting members.  It still
does not choose a globally noncrossing family or prove annular laminar depth.
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

/-- A negative-curvature token paid by an internal pentagon under the minimum
weighted-L9 assignment. -/
abbrev MinimumPentagonPairedNegativeCurvatureToken
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :=
  {pair : embedded.InteriorPentagonToken ×
      embedded.InteriorNegativeCurvatureToken //
    embedded.minimumCurvatureCreditDebtEquiv hsource geometry
        (Sum.inl pair.1) = Sum.inl pair.2}

/-- A negative-curvature token paid by one of the fixed source-foot credits
under the minimum weighted-L9 assignment. -/
abbrev MinimumSourceFootPairedNegativeCurvatureToken
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :=
  {pair : Fin (4 + 2 * source.frozenInterfaceStubVertices.card) ×
      embedded.InteriorNegativeCurvatureToken //
    embedded.minimumCurvatureCreditDebtEquiv hsource geometry
        (Sum.inr pair.1) = Sum.inl pair.2}

/-- The pentagon token at the target of a minimum-pairing route. -/
def MinimumPentagonPairedNegativeCurvatureToken.pentagonToken
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : MinimumPentagonPairedNegativeCurvatureToken
      hsource embedded geometry) : embedded.InteriorPentagonToken :=
  pair.1.1

/-- The long-face curvature token at the source of a minimum-pairing route. -/
def MinimumPentagonPairedNegativeCurvatureToken.negativeToken
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : MinimumPentagonPairedNegativeCurvatureToken
      hsource embedded geometry) : embedded.InteriorNegativeCurvatureToken :=
  pair.1.2

/-- The long face supporting a minimum-paired negative-curvature token. -/
def MinimumPentagonPairedNegativeCurvatureToken.negativeFace
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : MinimumPentagonPairedNegativeCurvatureToken
      hsource embedded geometry) :
    AmbientFace embedded.cellulation.interiorFaces :=
  pair.negativeToken.face

/-- The pentagonal face paying for a minimum-paired negative-curvature token. -/
def MinimumPentagonPairedNegativeCurvatureToken.pentagonFace
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : MinimumPentagonPairedNegativeCurvatureToken
      hsource embedded geometry) :
    AmbientFace embedded.cellulation.interiorFaces :=
  pair.pentagonToken.face

/-- The minimum assignment never uses one negative-curvature debt twice. -/
theorem minimumNegativeTokenProjection_injective
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry} :
    Function.Injective
      (fun pair : MinimumPentagonPairedNegativeCurvatureToken
          hsource embedded geometry => pair.negativeToken) := by
  intro left right hnegative
  have hcredits :
      (Sum.inl left.pentagonToken : embedded.PositiveCurvatureCredit) =
        Sum.inl right.pentagonToken := by
    apply (embedded.minimumCurvatureCreditDebtEquiv hsource geometry).injective
    calc
      embedded.minimumCurvatureCreditDebtEquiv hsource geometry
          (Sum.inl left.pentagonToken) = Sum.inl left.negativeToken := left.2
      _ = Sum.inl right.negativeToken := congrArg Sum.inl hnegative
      _ = embedded.minimumCurvatureCreditDebtEquiv hsource geometry
          (Sum.inl right.pentagonToken) := right.2.symm
  apply Subtype.ext
  exact Prod.ext (Sum.inl.inj hcredits) hnegative

/-- The minimum assignment never uses one pentagon credit twice. -/
theorem minimumPentagonTokenProjection_injective
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry} :
    Function.Injective
      (fun pair : MinimumPentagonPairedNegativeCurvatureToken
          hsource embedded geometry => pair.pentagonToken) := by
  intro left right hpentagon
  have hdebts :
      (Sum.inl left.negativeToken : embedded.NegativeCurvatureDebt) =
        Sum.inl right.negativeToken := by
    calc
      Sum.inl left.negativeToken =
          embedded.minimumCurvatureCreditDebtEquiv hsource geometry
            (Sum.inl left.pentagonToken) := left.2.symm
      _ = embedded.minimumCurvatureCreditDebtEquiv hsource geometry
            (Sum.inl right.pentagonToken) := congrArg
              (fun token => embedded.minimumCurvatureCreditDebtEquiv
                hsource geometry (Sum.inl token)) hpentagon
      _ = Sum.inl right.negativeToken := right.2
  apply Subtype.ext
  exact Prod.ext hpentagon (Sum.inl.inj hdebts)

/-- Minimum-pairing routes have pairwise distinct pentagonal endpoint faces. -/
theorem minimumPentagonFaceProjection_injective
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry} :
    Function.Injective
      (fun pair : MinimumPentagonPairedNegativeCurvatureToken
          hsource embedded geometry => pair.pentagonFace) := by
  intro left right hface
  apply minimumPentagonTokenProjection_injective
  apply Subtype.ext
  exact congrArg
    (fun face : AmbientFace embedded.cellulation.interiorFaces => face.1)
    hface

/-- The minimum-pairing route family has at most one member per internal
pentagon. -/
theorem card_minimumPentagonPairedNegativeCurvatureToken_le_pentagons
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    Fintype.card
        (MinimumPentagonPairedNegativeCurvatureToken
          hsource embedded geometry) ≤
      embedded.interiorFaceLengths.count 5 := by
  calc
    Fintype.card
          (MinimumPentagonPairedNegativeCurvatureToken
            hsource embedded geometry) ≤
        Fintype.card embedded.InteriorPentagonToken :=
      Fintype.card_le_of_injective
        (fun pair : MinimumPentagonPairedNegativeCurvatureToken
          hsource embedded geometry => pair.pentagonToken)
        minimumPentagonTokenProjection_injective
    _ = embedded.interiorFaceLengths.count 5 :=
      embedded.card_interiorPentagonToken

/-- Split every negative-curvature debt according to whether the minimum
assignment pays it with a pentagon or a fixed source foot. -/
noncomputable def minimumNegativeCurvatureTokenPairingDecomposition
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.InteriorNegativeCurvatureToken →
      MinimumPentagonPairedNegativeCurvatureToken hsource embedded geometry ⊕
        MinimumSourceFootPairedNegativeCurvatureToken hsource embedded geometry :=
  fun token =>
    match hcredit :
        (embedded.minimumCurvatureCreditDebtEquiv hsource geometry).symm
          (Sum.inl token) with
    | Sum.inl pentagon => Sum.inl ⟨(pentagon, token), by
        have himage := congrArg
          (embedded.minimumCurvatureCreditDebtEquiv hsource geometry) hcredit
        simpa using himage.symm⟩
    | Sum.inr foot => Sum.inr ⟨(foot, token), by
        have himage := congrArg
          (embedded.minimumCurvatureCreditDebtEquiv hsource geometry) hcredit
        simpa using himage.symm⟩

/-- Forget the credit endpoint of a minimum-paired negative-curvature token. -/
def minimumPairedNegativeCurvatureToken
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry} :
    MinimumPentagonPairedNegativeCurvatureToken hsource embedded geometry ⊕
        MinimumSourceFootPairedNegativeCurvatureToken hsource embedded geometry →
      embedded.InteriorNegativeCurvatureToken
  | Sum.inl pair => pair.negativeToken
  | Sum.inr pair => pair.1.2

@[simp]
theorem minimumPairedNegativeCurvatureToken_decomposition
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (token : embedded.InteriorNegativeCurvatureToken) :
    minimumPairedNegativeCurvatureToken
        (minimumNegativeCurvatureTokenPairingDecomposition
          hsource embedded geometry token) = token := by
  unfold minimumNegativeCurvatureTokenPairingDecomposition
  split <;> rfl

theorem minimumNegativeCurvatureTokenPairingDecomposition_injective
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    Function.Injective
      (minimumNegativeCurvatureTokenPairingDecomposition
        hsource embedded geometry) :=
  Function.LeftInverse.injective fun token =>
    embedded.minimumPairedNegativeCurvatureToken_decomposition
      hsource geometry token

/-- Distinct negative-curvature debts cannot be paid by one source-foot
credit under the minimum assignment. -/
theorem minimumSourceFootProjection_injective
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry} :
    Function.Injective
      (fun pair : MinimumSourceFootPairedNegativeCurvatureToken
          hsource embedded geometry => pair.1.1) := by
  intro left right hfoot
  have hdebts :
      (Sum.inl left.1.2 : embedded.NegativeCurvatureDebt) =
        Sum.inl right.1.2 := by
    calc
      Sum.inl left.1.2 =
          embedded.minimumCurvatureCreditDebtEquiv hsource geometry
            (Sum.inr left.1.1) := left.2.symm
      _ = embedded.minimumCurvatureCreditDebtEquiv hsource geometry
            (Sum.inr right.1.1) := congrArg
              (fun foot => embedded.minimumCurvatureCreditDebtEquiv
                hsource geometry (Sum.inr foot)) hfoot
      _ = Sum.inl right.1.2 := right.2
  apply Subtype.ext
  exact Prod.ext hfoot (Sum.inl.inj hdebts)

/-- At most the fixed number of source-foot credits can absorb negative
curvature under the minimum assignment. -/
theorem card_minimumSourceFootPairedNegativeCurvatureToken_le_sourceFeet
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    Fintype.card
        (MinimumSourceFootPairedNegativeCurvatureToken
          hsource embedded geometry) ≤
      4 + 2 * source.frozenInterfaceStubVertices.card := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
    (fun pair : MinimumSourceFootPairedNegativeCurvatureToken
      hsource embedded geometry => pair.1.1)
    minimumSourceFootProjection_injective

/-- Apart from the fixed source-foot exceptions, every unit of negative
curvature belongs to the minimum pentagon-backed route family. -/
theorem interiorNegativeCurvatureWeight_le_minimumPairs_add_sourceFeet
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.interiorNegativeCurvatureWeight ≤
      Fintype.card
        (MinimumPentagonPairedNegativeCurvatureToken
          hsource embedded geometry) +
        (4 + 2 * source.frozenInterfaceStubVertices.card) := by
  have hdecomposition := Fintype.card_le_of_injective
    (minimumNegativeCurvatureTokenPairingDecomposition
      hsource embedded geometry)
    (embedded.minimumNegativeCurvatureTokenPairingDecomposition_injective
      hsource geometry)
  rw [Fintype.card_sum] at hdecomposition
  rw [← embedded.card_interiorNegativeCurvatureToken]
  exact hdecomposition.trans
    (Nat.add_le_add_left
      (embedded.card_minimumSourceFootPairedNegativeCurvatureToken_le_sourceFeet
        hsource geometry) _)

/-- Negative curvature above a proposed route-family bound and the fixed
source-foot allowance forces more minimum-pairing routes than that bound. -/
theorem minimumPairBound_lt_card_of_weight_gt
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) (pairBound : Nat)
    (hweight : pairBound + 4 +
        2 * source.frozenInterfaceStubVertices.card <
      embedded.interiorNegativeCurvatureWeight) :
    pairBound < Fintype.card
      (MinimumPentagonPairedNegativeCurvatureToken
        hsource embedded geometry) := by
  have hpairs :=
    embedded.interiorNegativeCurvatureWeight_le_minimumPairs_add_sourceFeet
      hsource geometry
  omega

/-- A canonical geodesic for each member of the minimum-pairing family. -/
noncomputable def MinimumPentagonPairedNegativeCurvatureToken.curvatureRoute
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : MinimumPentagonPairedNegativeCurvatureToken
      hsource embedded geometry) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).Walk
        pair.negativeFace pair.pentagonFace :=
  Classical.choose
    (geometry.internalDualConnected.exists_walk_length_eq_dist
      pair.negativeFace pair.pentagonFace)

theorem MinimumPentagonPairedNegativeCurvatureToken.curvatureRoute_length_eq_dist
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : MinimumPentagonPairedNegativeCurvatureToken
      hsource embedded geometry) :
    pair.curvatureRoute.length =
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).dist
          pair.negativeFace pair.pentagonFace :=
  Classical.choose_spec
    (geometry.internalDualConnected.exists_walk_length_eq_dist
      pair.negativeFace pair.pentagonFace)

theorem MinimumPentagonPairedNegativeCurvatureToken.curvatureRoute_isPath
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : MinimumPentagonPairedNegativeCurvatureToken
      hsource embedded geometry) : pair.curvatureRoute.IsPath :=
  pair.curvatureRoute.isPath_of_length_eq_dist
    pair.curvatureRoute_length_eq_dist

/-- Two intersecting routes from the actual minimum-pairing family can
exchange tails; both exchanged walks remain geodesics for the crossed
endpoint assignment. -/
theorem minimumCurvatureRoute_tailExchange_geodesic
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (first second : MinimumPentagonPairedNegativeCurvatureToken
      hsource embedded geometry)
    (hne : first ≠ second)
    (common : AmbientFace embedded.cellulation.interiorFaces)
    (hcommonFirst : common ∈ first.curvatureRoute.support)
    (hcommonSecond : common ∈ second.curvatureRoute.support) :
    (firstExchange first.curvatureRoute second.curvatureRoute
        hcommonFirst hcommonSecond).length =
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).dist
          first.negativeFace second.pentagonFace ∧
    (secondExchange first.curvatureRoute second.curvatureRoute
        hcommonFirst hcommonSecond).length =
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).dist
          second.negativeFace first.pentagonFace := by
  have hpentagon : first.pentagonToken ≠ second.pentagonToken := by
    intro heq
    exact hne (minimumPentagonTokenProjection_injective heq)
  exact embedded.minimumCurvaturePairing_tailExchange_geodesic hsource
    geometry first.pentagonToken second.pentagonToken first.negativeToken
    second.negativeToken hpentagon first.2 second.2 first.curvatureRoute
    second.curvatureRoute first.curvatureRoute_length_eq_dist
    second.curvatureRoute_length_eq_dist common hcommonFirst hcommonSecond

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
