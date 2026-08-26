import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedSourceClosure

/-!
# Executable generators for the two-pair replay, and the exact interface gap

The two-pair realized alphabet and realizable initial image are specified as
images over the ambient witness type.  A replay checker cannot decide
membership in such a set: `realizedCodeImage` is `Finset.univ.image`, and the
witness `Fintype` in scope is obtained by `Fintype.ofFinite`, so `Finset.univ`
is a choice term with no kernel normal form.

This file replaces that specification by a finite generator wherever doing so
is derivable, and names precisely what is not.

* A generator is a `List` of realizations.  `generated…Set` maps the encoder
  over it and takes `toFinset`; membership is then list lookup, decidable and
  kernel-reducible for any supplied list.
* One direction is unconditional and needs no completeness hypothesis:
  `generated…_subset_realized`.  Every code produced by any list of
  realizations really is realized.  This is the executable direction and it is
  proved here for both the letter set and the initial set.
* The converse is exactly one equivalence, isolated as
  `PositionedRealizationEnumeration.complete` and
  `FirstRealizationEnumeration.complete`: the supplied list exhausts the
  realization type.  Granting it, `realized…_eq_generated` gives the
  extensional equality, and `allowedLetter_eq_generated` /
  `realizable_eq_generated` restate a replay's two specification fields as
  decidable list membership.

## Why the enumeration is not derivable here

Two independent obstructions, both upstream of this file.

The first is an interface gap.  The opened cap-deleted graph carries adjacency
only through `Classical.decRel`, so its edge set has no computable `Fintype`,
so neither does the positive colour function on it, so neither does the
realization subtype.  Supplying a genuine `DecidableRel` for the opened
graph's adjacency would make the whole chain computable, and that single
instance is the smallest technical repair that would unblock enumeration.

The second is structural and is not an interface gap.  The encoder consumes
the minimality datum: `sourceLocalLayerSerialPositionedRootedInteractionStep`
threads it into the value it returns, and
`GraphBackedVertexMinimalTaitCounterexample` carries a non-colourability field
together with a quantification over every smaller carrier in the universe.  A
closed term of that type is not something any concrete planar instance can
supply.  Kernel evaluation of the realized image therefore has no closed term
to evaluate even after the first obstruction is repaired.

Consequently no exact reachable-closure numeral is stated here, and none
should be quoted from this layer.  What *is* stated unconditionally is the
uniform carrier bound: the realized initial image and the realized letter
alphabet are bounded by the two-pair carrier and its square, with explicit
numerals, for every ambient instance at once.  Those bounds need no
enumeration, no ambient witness, and no choice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedSourceReplay

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedClosure
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedSourceClosure
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FiniteClosureInterfaces
open GoertzelV24SourceCorridorProfile
open GoertzelV24SourceTerminalAwareProfileCompression
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance positionedSourceReplayOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-! ## The isolated missing equivalence -/

/-- **The missing equivalence, for the letter alphabet.**  A list of
positioned realizations that exhausts the realization type.  Everything the
replay needs beyond the unconditional direction follows from this one field,
and nothing in the current interfaces supplies it. -/
structure PositionedRealizationEnumeration
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) where
  witnesses : List (SourceLocalLayerSerialPositionedRootedInteractionRealization
    graphData caps coloring web corridor hunique)
  complete : ∀ witness :
    SourceLocalLayerSerialPositionedRootedInteractionRealization graphData caps
      coloring web corridor hunique, witness ∈ witnesses

/-- **The missing equivalence, for the initial image.** -/
structure FirstRealizationEnumeration
    (graphData : Data G)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hlength : 2 < blockLength - 3) where
  witnesses : List (SourceLocalLayerSerialFirstRootedInteractionRealization
    graphData caps coloring web corridor hunique hlength)
  complete : ∀ witness :
    SourceLocalLayerSerialFirstRootedInteractionRealization graphData caps
      coloring web corridor hunique hlength, witness ∈ witnesses

/-! ## Finite generators -/

/-- The compressed two-pair letter alphabet generated by a supplied list of
realizations.  Membership is list lookup: decidable, and reducible by the
kernel for any closed list. -/
def generatedSourceCompressedProfileEdgeSet
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (witnesses : List
      (SourceLocalLayerSerialPositionedRootedInteractionRealization graphData
        caps coloring web corridor hunique)) :
    Finset SourceLocalLayerSerialPositionedSourceCompressedProfileEdge :=
  (witnesses.map
    (sourceLocalLayerSerialPositionedSourceCompressedProfileEdge graphData minimal caps coloring web corridor hunique)).toFinset

/-- The compressed two-pair initial image generated by a supplied list of
first-position realizations. -/
def generatedInitialSourceCompressedProfileSet
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hlength : 2 < blockLength - 3)
    (witnesses : List
      (SourceLocalLayerSerialFirstRootedInteractionRealization graphData caps
        coloring web corridor hunique hlength)) :
    Finset SourceLocalLayerSerialPositionedSourceCompressedProfile :=
  (witnesses.map
    (sourceLocalLayerSerialFirstSourceCompressedProfile graphData minimal caps coloring web corridor hunique hlength)).toFinset

/-! ## The unconditional direction

No completeness hypothesis is used below.  Any list of realizations whatsoever
generates codes that are genuinely realized. -/

/-- Every generated letter is realized, for any supplied list. -/
theorem generatedSourceCompressedProfileEdgeSet_subset_realized
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (witnesses : List
      (SourceLocalLayerSerialPositionedRootedInteractionRealization graphData
        caps coloring web corridor hunique)) :
    generatedSourceCompressedProfileEdgeSet graphData minimal caps coloring web corridor hunique witnesses ⊆
      sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet
        graphData minimal caps coloring web corridor hunique := by
  classical
  intro edge hedge
  rw [generatedSourceCompressedProfileEdgeSet, List.mem_toFinset,
    List.mem_map] at hedge
  obtain ⟨witness, -, hcode⟩ := hedge
  exact
    (mem_sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet_iff
      graphData minimal caps coloring web corridor hunique edge).mpr ⟨witness, hcode⟩

/-- Every generated initial profile is realizable, for any supplied list. -/
theorem generatedInitialSourceCompressedProfileSet_subset_realized
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hlength : 2 < blockLength - 3)
    (witnesses : List
      (SourceLocalLayerSerialFirstRootedInteractionRealization graphData caps
        coloring web corridor hunique hlength)) :
    generatedInitialSourceCompressedProfileSet graphData minimal caps coloring web corridor hunique hlength witnesses ⊆
      sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet graphData minimal caps coloring web corridor hunique hlength := by
  classical
  intro profile hprofile
  rw [generatedInitialSourceCompressedProfileSet, List.mem_toFinset,
    List.mem_map] at hprofile
  obtain ⟨witness, -, hcode⟩ := hprofile
  exact
    (mem_sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet_iff
      graphData minimal caps coloring web corridor hunique hlength profile).mpr ⟨witness, hcode⟩

/-! ## The conditional direction, granted the isolated equivalence -/

/-- Granted completeness, the ambient-image specification of the letter
alphabet is extensionally the generated finite set. -/
theorem realizedSourceCompressedProfileEdgeSet_eq_generated
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (enumeration : PositionedRealizationEnumeration graphData caps coloring web corridor hunique) :
    sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet
        graphData minimal caps coloring web corridor hunique =
      generatedSourceCompressedProfileEdgeSet graphData minimal caps coloring web corridor hunique enumeration.witnesses := by
  classical
  apply Finset.Subset.antisymm
  · intro edge hedge
    obtain ⟨witness, hcode⟩ :=
      (mem_sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet_iff
        graphData minimal caps coloring web corridor hunique edge).mp hedge
    rw [generatedSourceCompressedProfileEdgeSet, List.mem_toFinset,
      List.mem_map]
    exact ⟨witness, enumeration.complete witness, hcode⟩
  · exact generatedSourceCompressedProfileEdgeSet_subset_realized graphData minimal caps coloring web corridor hunique
      enumeration.witnesses

/-- Granted completeness, the ambient-image specification of the initial image
is extensionally the generated finite set. -/
theorem realizedInitialSourceCompressedProfileSet_eq_generated
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hlength : 2 < blockLength - 3)
    (enumeration : FirstRealizationEnumeration graphData caps coloring web corridor hunique hlength) :
    sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet graphData minimal caps coloring web corridor hunique hlength =
      generatedInitialSourceCompressedProfileSet graphData minimal caps coloring web corridor hunique hlength enumeration.witnesses := by
  classical
  apply Finset.Subset.antisymm
  · intro profile hprofile
    obtain ⟨witness, hcode⟩ :=
      (mem_sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet_iff
        graphData minimal caps coloring web corridor hunique hlength profile).mp hprofile
    rw [generatedInitialSourceCompressedProfileSet, List.mem_toFinset,
      List.mem_map]
    exact ⟨witness, enumeration.complete witness, hcode⟩
  · exact generatedInitialSourceCompressedProfileSet_subset_realized graphData minimal caps coloring web corridor hunique hlength
      enumeration.witnesses

/-! ## Restating a replay's specification fields executably -/

/-- Granted completeness, a replay's allowed-letter field is decidable list
membership in the generated alphabet. -/
theorem allowedLetter_eq_generated
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hlength : 2 < blockLength - 3)
    (replay :
      SourceLocalLayerSerialPositionedSourceCompressedProfileClosureReplay graphData minimal caps coloring web corridor hunique hlength)
    (enumeration : PositionedRealizationEnumeration graphData caps coloring web corridor hunique) :
    replay.certificate.allowedLetter =
      fun edge => edge ∈
        generatedSourceCompressedProfileEdgeSet graphData minimal caps coloring web corridor hunique enumeration.witnesses := by
  rw [replay.allowedLetter_eq,
    realizedSourceCompressedProfileEdgeSet_eq_generated graphData minimal caps coloring web corridor hunique enumeration]

/-- Granted completeness, a replay's realizable field is decidable list
membership in the generated initial image. -/
theorem realizable_eq_generated
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hlength : 2 < blockLength - 3)
    (replay :
      SourceLocalLayerSerialPositionedSourceCompressedProfileClosureReplay graphData minimal caps coloring web corridor hunique hlength)
    (enumeration : FirstRealizationEnumeration graphData caps coloring web corridor hunique hlength) :
    replay.certificate.realizable =
      fun profile => profile ∈
        generatedInitialSourceCompressedProfileSet graphData minimal caps coloring web corridor hunique hlength enumeration.witnesses := by
  rw [replay.realizable_eq,
    realizedInitialSourceCompressedProfileSet_eq_generated graphData minimal caps coloring web corridor hunique hlength enumeration]

/-! ## Unconditional uniform bounds

These need no enumeration, no ambient witness, and no choice.  They hold for
every ambient instance simultaneously, and they are the authoritative
statements this layer supports about the size of the realized data. -/

/-- The realizable two-pair initial image never exceeds the manuscript's own
compressed carrier. -/
theorem card_realizedInitialSourceCompressedProfileSet_le
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hlength : 2 < blockLength - 3) :
    (sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet
        graphData minimal caps coloring web corridor hunique hlength).card ≤ 784806951168 := by
  classical
  refine le_trans (Finset.card_le_univ _) ?_
  rw [card_boundedSourceTerminalAwareCompressedProfile,
    boundedSourceTerminalAwareCompressedProfileCount_two_one_four]

/-- The realized two-pair letter alphabet never exceeds the square of the
manuscript's own compressed carrier. -/
theorem card_realizedSourceCompressedProfileEdgeSet_le
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    (sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet
        graphData minimal caps coloring web corridor hunique).card ≤ 784806951168 * 784806951168 := by
  classical
  refine le_trans (Finset.card_le_univ _) ?_
  rw [Fintype.card_prod, card_boundedSourceTerminalAwareCompressedProfile,
    boundedSourceTerminalAwareCompressedProfileCount_two_one_four]

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedSourceReplay

end Mettapedia.GraphTheory.FourColor
