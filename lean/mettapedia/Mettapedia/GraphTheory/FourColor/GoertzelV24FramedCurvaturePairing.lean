import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedBoundaryCleanCorridor

/-!
# Curvature tokens for the framed high-pentagon branch

Exact weighted L9 is an equality of finite resources.  This module exposes
those resources as finite types: pentagon/source-foot credits on one side,
and long-face curvature/boundary-surplus debts on the other.  The resulting
pairing supplies concrete endpoints for the remaining planar length/depth
pumping argument; it does not assume that argument.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CurvatureScope
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

/-- Internal pentagonal facial orbits. -/
def interiorPentagonFaces {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Finset (OrbitFace embedded.cellulation.rotation.toRotationSystem) :=
  embedded.cellulation.interiorFaces.filter fun face =>
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card = 5

@[simp]
theorem mem_interiorPentagonFaces_iff {source : SourceTrail G}
    (embedded : source.AnnularEmbedding)
    (face : OrbitFace embedded.cellulation.rotation.toRotationSystem) :
    face ∈ embedded.interiorPentagonFaces ↔
      face ∈ embedded.cellulation.interiorFaces ∧
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
          face).card = 5 := by
  simp [interiorPentagonFaces]

/-- One positive curvature token for each internal pentagon. -/
abbrev InteriorPentagonToken {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :=
  {face // face ∈ embedded.interiorPentagonFaces}

/-- One negative-curvature token for each unit by which an internal face
exceeds length six. -/
abbrev InteriorNegativeCurvatureToken {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :=
  Σ face : AmbientFace embedded.cellulation.interiorFaces,
    Fin ((orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face.1).card - 6)

theorem card_interiorPentagonFaces_eq_count {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    embedded.interiorPentagonFaces.card =
      embedded.interiorFaceLengths.count 5 := by
  unfold interiorPentagonFaces interiorFaceLengths
  rw [Finset.card_def, Finset.filter_val, Multiset.count_map]
  congr 1
  ext face
  simp [eq_comm]

theorem card_interiorPentagonToken {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Fintype.card embedded.InteriorPentagonToken =
      embedded.interiorFaceLengths.count 5 := by
  rw [Fintype.card_coe, embedded.card_interiorPentagonFaces_eq_count]

theorem card_interiorNegativeCurvatureToken {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Fintype.card embedded.InteriorNegativeCurvatureToken =
      embedded.interiorNegativeCurvatureWeight := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  unfold interiorNegativeCurvatureWeight faceCycleNegativeCurvatureWeight
  unfold interiorFaceLengths
  rw [Multiset.map_map]
  simp only [Function.comp_apply]
  rw [Finset.univ_eq_attach]
  simpa using (Finset.sum_attach embedded.cellulation.interiorFaces
    (fun face =>
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face).card - 6))

/-- Positive credits in weighted L9: internal pentagons and the fixed framed
source feet. -/
abbrev PositiveCurvatureCredit {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :=
  embedded.InteriorPentagonToken ⊕
    Fin (4 + 2 * source.frozenInterfaceStubVertices.card)

/-- Negative debts in weighted L9: units of long-face curvature and units of
boundary surplus. -/
abbrev NegativeCurvatureDebt {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :=
  embedded.InteriorNegativeCurvatureToken ⊕
    Fin (embedded.cellulation.boundarySurplus source.toFramedTrailData)

theorem card_positiveCurvatureCredit {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Fintype.card embedded.PositiveCurvatureCredit =
      embedded.interiorFaceLengths.count 5 + 4 +
        2 * source.frozenInterfaceStubVertices.card := by
  rw [Fintype.card_sum, embedded.card_interiorPentagonToken,
    Fintype.card_fin]
  omega

theorem card_negativeCurvatureDebt {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Fintype.card embedded.NegativeCurvatureDebt =
      embedded.interiorNegativeCurvatureWeight +
        embedded.cellulation.boundarySurplus source.toFramedTrailData := by
  rw [Fintype.card_sum, embedded.card_interiorNegativeCurvatureToken,
    Fintype.card_fin]

/-- Exact weighted L9 as a finite pairing.  This pairing is deliberately
non-geometric; the next structural layer must route its face-supported pairs
through the connected annular dual and prove a spliceable repetition. -/
noncomputable def curvatureCreditDebtEquiv
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.PositiveCurvatureCredit ≃ embedded.NegativeCurvatureDebt :=
  Fintype.equivOfCardEq (by
    rw [embedded.card_positiveCurvatureCredit,
      embedded.card_negativeCurvatureDebt]
    exact embedded.interiorPentagonCount_add_sourceFeet_eq_weight_add_boundarySurplus
      hsource geometry)

/-- A long-face curvature token whose exact L9 credit is an internal
pentagon rather than one of the finitely many source feet. -/
abbrev PentagonPairedNegativeCurvatureToken
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :=
  {pair : embedded.InteriorNegativeCurvatureToken ×
      embedded.InteriorPentagonToken //
    (embedded.curvatureCreditDebtEquiv hsource geometry).symm
        (Sum.inl pair.1) = Sum.inl pair.2}

/-- A long-face curvature token paid by one of the fixed source feet rather
than by an internal pentagon. -/
abbrev SourceFootPairedNegativeCurvatureToken
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :=
  {pair : embedded.InteriorNegativeCurvatureToken ×
      Fin (4 + 2 * source.frozenInterfaceStubVertices.card) //
    (embedded.curvatureCreditDebtEquiv hsource geometry).symm
        (Sum.inl pair.1) = Sum.inr pair.2}

/-- Split every long-face curvature token according to whether exact L9
pairs it with a pentagon or with a fixed source foot. -/
noncomputable def negativeCurvatureTokenPairingDecomposition
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.InteriorNegativeCurvatureToken →
      PentagonPairedNegativeCurvatureToken hsource embedded geometry ⊕
        SourceFootPairedNegativeCurvatureToken hsource embedded geometry :=
  fun token =>
    match hcredit :
        (embedded.curvatureCreditDebtEquiv hsource geometry).symm
          (Sum.inl token) with
    | Sum.inl pentagon => Sum.inl ⟨(token, pentagon), hcredit⟩
    | Sum.inr foot => Sum.inr ⟨(token, foot), hcredit⟩

/-- Forget the credit endpoint of a paired long-face curvature token. -/
def pairedNegativeCurvatureToken
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry} :
    PentagonPairedNegativeCurvatureToken hsource embedded geometry ⊕
        SourceFootPairedNegativeCurvatureToken hsource embedded geometry →
      embedded.InteriorNegativeCurvatureToken
  | Sum.inl pair => pair.1.1
  | Sum.inr pair => pair.1.1

@[simp]
theorem pairedNegativeCurvatureToken_decomposition
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (token : embedded.InteriorNegativeCurvatureToken) :
  pairedNegativeCurvatureToken
      (negativeCurvatureTokenPairingDecomposition
        hsource embedded geometry token) = token := by
  unfold negativeCurvatureTokenPairingDecomposition
  split <;> rfl

theorem negativeCurvatureTokenPairingDecomposition_injective
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    Function.Injective
      (negativeCurvatureTokenPairingDecomposition hsource embedded geometry) :=
  Function.LeftInverse.injective fun token =>
    embedded.pairedNegativeCurvatureToken_decomposition
      hsource geometry token

/-- Distinct curvature tokens cannot be paid by the same source-foot token. -/
theorem sourceFootProjection_injective
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry} :
    Function.Injective
      (fun pair : SourceFootPairedNegativeCurvatureToken
          hsource embedded geometry => pair.1.2) := by
  intro left right hfoot
  have himages :
      (embedded.curvatureCreditDebtEquiv hsource geometry).symm
          (Sum.inl left.1.1) =
        (embedded.curvatureCreditDebtEquiv hsource geometry).symm
          (Sum.inl right.1.1) := by
    calc
      (embedded.curvatureCreditDebtEquiv hsource geometry).symm
          (Sum.inl left.1.1) = Sum.inr left.1.2 := left.2
      _ = Sum.inr right.1.2 := congrArg Sum.inr hfoot
      _ = (embedded.curvatureCreditDebtEquiv hsource geometry).symm
          (Sum.inl right.1.1) := right.2.symm
  have htoken : left.1.1 = right.1.1 := by
    exact Sum.inl.inj
      ((embedded.curvatureCreditDebtEquiv hsource geometry).symm.injective
        himages)
  apply Subtype.ext
  exact Prod.ext htoken hfoot

/-- Only the fixed number of framed source feet can absorb long-face
curvature tokens without assigning them to internal pentagons. -/
theorem card_sourceFootPairedNegativeCurvatureToken_le_sourceFeet
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    Fintype.card
        (SourceFootPairedNegativeCurvatureToken hsource embedded geometry) ≤
      4 + 2 * source.frozenInterfaceStubVertices.card := by
  have hcard := Fintype.card_le_of_injective
    (fun pair : SourceFootPairedNegativeCurvatureToken
      hsource embedded geometry => pair.1.2)
    sourceFootProjection_injective
  simpa only [Fintype.card_fin] using hcard

/-- Apart from the fixed source-foot exceptions, every unit of negative
curvature produces a routed long-face/pentagon pair. -/
theorem interiorNegativeCurvatureWeight_le_pentagonPairedTokens_add_sourceFeet
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.interiorNegativeCurvatureWeight ≤
      Fintype.card
        (PentagonPairedNegativeCurvatureToken hsource embedded geometry) +
          (4 + 2 * source.frozenInterfaceStubVertices.card) := by
  have hdecomposition := Fintype.card_le_of_injective
    (negativeCurvatureTokenPairingDecomposition hsource embedded geometry)
    (embedded.negativeCurvatureTokenPairingDecomposition_injective
      hsource geometry)
  rw [Fintype.card_sum] at hdecomposition
  rw [← embedded.card_interiorNegativeCurvatureToken]
  exact hdecomposition.trans
    (Nat.add_le_add_left
      (embedded.card_sourceFootPairedNegativeCurvatureToken_le_sourceFeet
        hsource geometry) _)

theorem pentagonPairBound_lt_card_of_weight_gt
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) (pairBound : Nat)
    (hweight : pairBound + 4 +
        2 * source.frozenInterfaceStubVertices.card <
      embedded.interiorNegativeCurvatureWeight) :
    pairBound < Fintype.card
      (PentagonPairedNegativeCurvatureToken hsource embedded geometry) := by
  have hpairs :=
    embedded.interiorNegativeCurvatureWeight_le_pentagonPairedTokens_add_sourceFeet
      hsource geometry
  omega

/-- Long face supporting a pentagon-paired negative-curvature token. -/
def PentagonPairedNegativeCurvatureToken.negativeFace
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry) :
    AmbientFace embedded.cellulation.interiorFaces :=
  pair.1.1.1

/-- Pentagon face paying for the paired negative-curvature token. -/
def PentagonPairedNegativeCurvatureToken.pentagonFace
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry) :
    AmbientFace embedded.cellulation.interiorFaces :=
  ⟨pair.1.2.1,
    (embedded.mem_interiorPentagonFaces_iff pair.1.2.1).1 pair.1.2.2 |>.1⟩

/-- A canonical shortest dual route from each long-face curvature token to
its paired pentagon.  The remaining high-curvature theorem must organize
this route family into a bounded-interface length/depth repetition. -/
noncomputable def PentagonPairedNegativeCurvatureToken.curvatureRoute
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).Walk
        pair.negativeFace pair.pentagonFace :=
  Classical.choose
    (geometry.internalDualConnected.exists_walk_length_eq_dist
      pair.negativeFace pair.pentagonFace)

theorem PentagonPairedNegativeCurvatureToken.curvatureRoute_length_eq_dist
    {source : SourceTrail G} {hsource : source.WellFormed}
    {embedded : source.AnnularEmbedding}
    {geometry : embedded.CorridorGeometry}
    (pair : PentagonPairedNegativeCurvatureToken hsource embedded geometry) :
    pair.curvatureRoute.length =
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).dist
          pair.negativeFace pair.pentagonFace :=
  Classical.choose_spec
    (geometry.internalDualConnected.exists_walk_length_eq_dist
      pair.negativeFace pair.pentagonFace)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
