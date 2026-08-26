import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedClosure
import Mettapedia.GraphTheory.FourColor.GoertzelV24SourceTerminalAwareProfileCompression

/-!
# The positioned corridor alphabet in the manuscript's own profile

The positioned closure builds its realized alphabet from the conservative
three-pair cut profile.  The manuscript's length profile records two
connectivity families, `alpha ∪ beta` and `alpha ∪ gamma`.  This file projects
the positioned source and target profiles onto those two families and then
applies the two-pair lossless terminal-aware compression, so that the realized
alphabet, the initial image, and the sparse replay interface are all stated in
the profile the source actually specifies.

Two facts keep the projection honest.  Compression is lossless *relative to
the two-pair profile*: `..._eq_iff` says two compressed edges agree exactly
when the projected two-pair source and target profiles already agreed.  It
does not say the three-pair profiles agreed, and no theorem here claims that;
the discarded family is genuinely discarded.  Consequently the cardinality
theorems below relate the compressed image to the two-pair image, never to the
three-pair one.

The three-pair engine is untouched and remains available: every definition
here factors through the existing positioned rooted step and its semantic
certificate, so local transition reasoning continues in the conservative
carrier while the reported alphabet is the source's.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedSourceClosure

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedClosure
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FiniteClosureInterfaces
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SourceCorridorProfile
open GoertzelV24SourceTerminalAwareProfileCompression
open GoertzelV24TerminalAwareProfileCompression
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The opened-graph decidability instance is `local` at its defining site, so
it is re-declared here on the same terms. -/
local instance positionedSourceClosureOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The manuscript's two-pair cut profile at one serial cut. -/
abbrev SourceLocalLayerSerialPositionedSourceProfile :=
  BoundedSourceCorridorCutProfile 2 1 4

/-- One directed edge of the two-pair profile transition graph. -/
abbrev SourceLocalLayerSerialPositionedSourceProfileEdge :=
  SourceLocalLayerSerialPositionedSourceProfile ×
    SourceLocalLayerSerialPositionedSourceProfile

/-- The finite lossless carrier for the two-pair profile. -/
abbrev SourceLocalLayerSerialPositionedSourceCompressedProfile :=
  BoundedSourceTerminalAwareCompressedProfile 2 1 4

/-- One directed edge after two-pair lossless compression. -/
abbrev SourceLocalLayerSerialPositionedSourceCompressedProfileEdge :=
  SourceLocalLayerSerialPositionedSourceCompressedProfile ×
    SourceLocalLayerSerialPositionedSourceCompressedProfile

/-- The singleton transition relation denoted by one two-pair profile edge. -/
def sourceLocalLayerSerialPositionedSourceProfileEdgeTransition
    (edge : SourceLocalLayerSerialPositionedSourceProfileEdge)
    (source target : SourceLocalLayerSerialPositionedSourceProfile) : Prop :=
  source = edge.1 ∧ target = edge.2

/-- The singleton transition relation carried by one compressed two-pair
profile edge. -/
def sourceLocalLayerSerialPositionedSourceCompressedProfileEdgeTransition
    (edge : SourceLocalLayerSerialPositionedSourceCompressedProfileEdge)
    (source target : SourceLocalLayerSerialPositionedSourceCompressedProfile) :
    Prop :=
  source = edge.1 ∧ target = edge.2

/-- Project a literal positioned rooted step to the manuscript's two-pair
source and target cut profiles. -/
def sourceLocalLayerSerialPositionedSourceProfileEdge
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
    (witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
      graphData caps coloring web corridor hunique) :
    SourceLocalLayerSerialPositionedSourceProfileEdge :=
  let step := sourceLocalLayerSerialPositionedRootedInteractionStep graphData minimal caps coloring web corridor hunique witness
  (toBoundedSourceProfile step.source.input,
    toBoundedSourceProfile step.target.input)

/-- Compress both two-pair endpoints of one literal positioned witness. -/
def sourceLocalLayerSerialPositionedSourceCompressedProfileEdge
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
    (witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
      graphData caps coloring web corridor hunique) :
    SourceLocalLayerSerialPositionedSourceCompressedProfileEdge :=
  let step := sourceLocalLayerSerialPositionedRootedInteractionStep graphData minimal caps coloring web corridor hunique witness
  let semantic :=
    sourceLocalLayerSerialPositionedStep_endpoints_areTerminalGraphSemantic
      graphData minimal caps coloring web corridor hunique witness
  (compressBounded (toBoundedSourceProfile step.source.input)
      (isSourceTerminalGraphSemantic_toSourceProfile semantic.1),
    compressBounded (toBoundedSourceProfile step.target.input)
      (isSourceTerminalGraphSemantic_toSourceProfile semantic.2))

/-- **Losslessness, exactly scoped.**  Two compressed edges are equal exactly
when the projected two-pair source and target profiles were already equal.
The discarded third connectivity family is not recovered by this statement and
is not claimed to be. -/
theorem sourceLocalLayerSerialPositionedSourceCompressedProfileEdge_eq_iff
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
    (left right : SourceLocalLayerSerialPositionedRootedInteractionRealization
      graphData caps coloring web corridor hunique) :
    sourceLocalLayerSerialPositionedSourceCompressedProfileEdge graphData minimal caps coloring web corridor hunique left =
      sourceLocalLayerSerialPositionedSourceCompressedProfileEdge graphData minimal caps coloring web corridor hunique right ↔
      sourceLocalLayerSerialPositionedSourceProfileEdge graphData minimal caps coloring web corridor hunique left =
      sourceLocalLayerSerialPositionedSourceProfileEdge graphData minimal caps coloring web corridor hunique right := by
  have leftSemantic :=
    sourceLocalLayerSerialPositionedStep_endpoints_areTerminalGraphSemantic
      graphData minimal caps coloring web corridor hunique left
  have rightSemantic :=
    sourceLocalLayerSerialPositionedStep_endpoints_areTerminalGraphSemantic
      graphData minimal caps coloring web corridor hunique right
  constructor
  · intro heq
    apply Prod.ext
    · exact compressBounded_injective
        (isSourceTerminalGraphSemantic_toSourceProfile leftSemantic.1)
        (isSourceTerminalGraphSemantic_toSourceProfile rightSemantic.1)
        (congrArg Prod.fst heq)
    · exact compressBounded_injective
        (isSourceTerminalGraphSemantic_toSourceProfile leftSemantic.2)
        (isSourceTerminalGraphSemantic_toSourceProfile rightSemantic.2)
        (congrArg Prod.snd heq)
  · intro heq
    apply Prod.ext
    · exact compressBounded_eq_of_eq
        (isSourceTerminalGraphSemantic_toSourceProfile leftSemantic.1)
        (isSourceTerminalGraphSemantic_toSourceProfile rightSemantic.1)
        (congrArg Prod.fst heq)
    · exact compressBounded_eq_of_eq
        (isSourceTerminalGraphSemantic_toSourceProfile leftSemantic.2)
        (isSourceTerminalGraphSemantic_toSourceProfile rightSemantic.2)
        (congrArg Prod.snd heq)

/-- The finite image of two-pair profile edges realized along the fixed
corridor. -/
def sourceLocalLayerSerialPositionedRealizedSourceProfileEdgeSet
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
    Finset SourceLocalLayerSerialPositionedSourceProfileEdge :=
  realizedCodeImage
    (sourceLocalLayerSerialPositionedSourceProfileEdge graphData minimal caps coloring web corridor hunique)

/-- Exact literal-witness meaning of a realized two-pair profile edge. -/
theorem mem_sourceLocalLayerSerialPositionedRealizedSourceProfileEdgeSet_iff
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
    (edge : SourceLocalLayerSerialPositionedSourceProfileEdge) :
    edge ∈ sourceLocalLayerSerialPositionedRealizedSourceProfileEdgeSet
        graphData minimal caps coloring web corridor hunique ↔
      ∃ witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
          graphData caps coloring web corridor hunique,
        sourceLocalLayerSerialPositionedSourceProfileEdge graphData minimal caps coloring web corridor hunique witness = edge := by
  classical
  simp [sourceLocalLayerSerialPositionedRealizedSourceProfileEdgeSet,
    realizedCodeImage]

/-- The finite image of compressed two-pair profile edges realized along the
fixed corridor. -/
def sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet
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
    Finset SourceLocalLayerSerialPositionedSourceCompressedProfileEdge :=
  realizedCodeImage
    (sourceLocalLayerSerialPositionedSourceCompressedProfileEdge graphData minimal caps coloring web corridor hunique)

/-- Exact literal-witness meaning of a compressed two-pair profile edge. -/
theorem mem_sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet_iff
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
    (edge : SourceLocalLayerSerialPositionedSourceCompressedProfileEdge) :
    edge ∈ sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet
        graphData minimal caps coloring web corridor hunique ↔
      ∃ witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
          graphData caps coloring web corridor hunique,
        sourceLocalLayerSerialPositionedSourceCompressedProfileEdge graphData minimal caps coloring web corridor hunique
          witness = edge := by
  classical
  simp [sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet,
    realizedCodeImage]

/-- Two-pair compression changes the representation of the realized alphabet
but not its exact cardinality. -/
theorem card_sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet_eq
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
        graphData minimal caps coloring web corridor hunique).card =
      (sourceLocalLayerSerialPositionedRealizedSourceProfileEdgeSet
        graphData minimal caps coloring web corridor hunique).card := by
  classical
  symm
  exact card_realizedCodeImage_eq_of_fiber_iff
    (sourceLocalLayerSerialPositionedSourceProfileEdge graphData minimal caps coloring web corridor hunique)
    (sourceLocalLayerSerialPositionedSourceCompressedProfileEdge graphData minimal caps coloring web corridor hunique)
    (fun first second =>
      (sourceLocalLayerSerialPositionedSourceCompressedProfileEdge_eq_iff
        graphData minimal caps coloring web corridor hunique first second).symm)

/-! ## The initial image, in the manuscript's profile -/

/-- The two-pair source profile of a literal first-position witness.  The
following-position bound packages that witness as an ordinary positioned
witness, so the initial and edge projections use one definition. -/
def sourceLocalLayerSerialFirstSourceProfile
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
    (witness : SourceLocalLayerSerialFirstRootedInteractionRealization graphData
      caps coloring web corridor hunique hlength) :
    SourceLocalLayerSerialPositionedSourceProfile :=
  (sourceLocalLayerSerialPositionedSourceProfileEdge graphData minimal caps coloring web corridor hunique
    ⟨sourceLocalLayerSerialFirstRollingPosition hlength, witness⟩).1

/-- Its provenance: the projection of the literal first rooted state's own cut
profile onto the manuscript's two connectivity families. -/
theorem sourceLocalLayerSerialFirstSourceProfile_eq
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
    (witness : SourceLocalLayerSerialFirstRootedInteractionRealization graphData
      caps coloring web corridor hunique hlength) :
    sourceLocalLayerSerialFirstSourceProfile graphData minimal caps coloring web corridor hunique hlength witness =
      toBoundedSourceProfile
        (sourceLocalLayerSerialFirstRootedInteractionState graphData minimal caps coloring web corridor hunique hlength witness).input :=
  rfl

/-- Compress the two-pair source profile of a literal first-position witness. -/
def sourceLocalLayerSerialFirstSourceCompressedProfile
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
    (witness : SourceLocalLayerSerialFirstRootedInteractionRealization graphData
      caps coloring web corridor hunique hlength) :
    SourceLocalLayerSerialPositionedSourceCompressedProfile :=
  (sourceLocalLayerSerialPositionedSourceCompressedProfileEdge graphData minimal caps coloring web corridor hunique
    ⟨sourceLocalLayerSerialFirstRollingPosition hlength, witness⟩).1

/-- First-position compression has exactly the equality fibers of the
uncompressed two-pair initial profile. -/
theorem sourceLocalLayerSerialFirstSourceCompressedProfile_eq_iff
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
    (left right : SourceLocalLayerSerialFirstRootedInteractionRealization
      graphData caps coloring web corridor hunique hlength) :
    sourceLocalLayerSerialFirstSourceCompressedProfile graphData minimal caps coloring web corridor hunique hlength left =
      sourceLocalLayerSerialFirstSourceCompressedProfile graphData minimal caps coloring web corridor hunique hlength right ↔
      sourceLocalLayerSerialFirstSourceProfile graphData minimal caps coloring web corridor hunique hlength left =
      sourceLocalLayerSerialFirstSourceProfile graphData minimal caps coloring web corridor hunique hlength right := by
  have leftSemantic :=
    sourceLocalLayerSerialPositionedStep_endpoints_areTerminalGraphSemantic
      graphData minimal caps coloring web corridor hunique ⟨sourceLocalLayerSerialFirstRollingPosition hlength, left⟩
  have rightSemantic :=
    sourceLocalLayerSerialPositionedStep_endpoints_areTerminalGraphSemantic
      graphData minimal caps coloring web corridor hunique ⟨sourceLocalLayerSerialFirstRollingPosition hlength, right⟩
  exact ⟨compressBounded_injective
      (isSourceTerminalGraphSemantic_toSourceProfile leftSemantic.1)
      (isSourceTerminalGraphSemantic_toSourceProfile rightSemantic.1),
    compressBounded_eq_of_eq
      (isSourceTerminalGraphSemantic_toSourceProfile leftSemantic.1)
      (isSourceTerminalGraphSemantic_toSourceProfile rightSemantic.1)⟩

/-- The exact image of realizable first-cut two-pair profiles. -/
def sourceLocalLayerSerialRealizedInitialSourceProfileSet
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
    Finset SourceLocalLayerSerialPositionedSourceProfile :=
  realizedCodeImage (sourceLocalLayerSerialFirstSourceProfile graphData minimal caps coloring web corridor hunique hlength)

/-- A two-pair initial profile is present exactly when a literal compatible
first-position witness produces it. -/
theorem mem_sourceLocalLayerSerialRealizedInitialSourceProfileSet_iff
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
    (profile : SourceLocalLayerSerialPositionedSourceProfile) :
    profile ∈ sourceLocalLayerSerialRealizedInitialSourceProfileSet graphData minimal caps coloring web corridor hunique hlength ↔
      ∃ witness : SourceLocalLayerSerialFirstRootedInteractionRealization
          graphData caps coloring web corridor hunique hlength,
        sourceLocalLayerSerialFirstSourceProfile graphData minimal caps coloring web corridor hunique hlength witness = profile := by
  classical
  simp [sourceLocalLayerSerialRealizedInitialSourceProfileSet, realizedCodeImage]

/-- The exact compressed image of realizable first-cut two-pair profiles. -/
def sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet
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
    Finset SourceLocalLayerSerialPositionedSourceCompressedProfile :=
  realizedCodeImage (sourceLocalLayerSerialFirstSourceCompressedProfile graphData minimal caps coloring web corridor hunique hlength)

/-- A compressed two-pair initial profile is present exactly when a literal
compatible first-position witness produces it. -/
theorem mem_sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet_iff
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
    (profile : SourceLocalLayerSerialPositionedSourceCompressedProfile) :
    profile ∈ sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet
        graphData minimal caps coloring web corridor hunique hlength ↔
      ∃ witness : SourceLocalLayerSerialFirstRootedInteractionRealization
          graphData caps coloring web corridor hunique hlength,
        sourceLocalLayerSerialFirstSourceCompressedProfile graphData minimal caps coloring web corridor hunique hlength witness =
          profile := by
  classical
  simp [sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet,
    realizedCodeImage]

/-- Two-pair compression preserves the exact cardinality of the realizable
initial image. -/
theorem card_sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet_eq
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
        graphData minimal caps coloring web corridor hunique hlength).card =
      (sourceLocalLayerSerialRealizedInitialSourceProfileSet graphData minimal caps coloring web corridor hunique hlength).card := by
  classical
  symm
  exact card_realizedCodeImage_eq_of_fiber_iff
    (sourceLocalLayerSerialFirstSourceProfile graphData minimal caps coloring web corridor hunique hlength)
    (sourceLocalLayerSerialFirstSourceCompressedProfile graphData minimal caps coloring web corridor hunique hlength)
    (fun first second =>
      (sourceLocalLayerSerialFirstSourceCompressedProfile_eq_iff
        graphData minimal caps coloring web corridor hunique hlength first second).symm)

/-! ## Sparse replay over the manuscript's own profile graph -/

/-- Sparse exact-closure replay over the losslessly compressed two-pair
profile graph.  Its state count is definitionally a count of compressed
two-pair semantic profiles; the injectivity above makes it equally a count of
the represented two-pair profiles.  It is not a count of three-pair profiles,
and physical composition of successive witnesses remains the separate
profile-splice obligation. -/
structure SourceLocalLayerSerialPositionedSourceCompressedProfileClosureReplay
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
    (hlength : 2 < blockLength - 3) where
  certificate : ExactReachableClosureCertificate
    SourceLocalLayerSerialPositionedSourceCompressedProfile
    SourceLocalLayerSerialPositionedSourceCompressedProfileEdge Unit
  transition_eq : certificate.transition =
    fun source edge target =>
      sourceLocalLayerSerialPositionedSourceCompressedProfileEdgeTransition edge
        source target
  allowedLetter_eq : certificate.allowedLetter =
    fun edge => edge ∈
      sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet
        graphData minimal caps coloring web corridor hunique
  realizable_eq : certificate.realizable =
    fun profile => profile ∈
      sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet graphData minimal caps coloring web corridor hunique hlength

/-- The replay's letter array contains exactly the compressed two-pair edges
of literal positioned witnesses. -/
theorem SourceLocalLayerSerialPositionedSourceCompressedProfileClosureReplay.letter_entry_iff_witness
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {caps : OrientedFacialPentagonCapPair graphData}
    {coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring}
    {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hlength : 2 < blockLength - 3}
    (replay :
      SourceLocalLayerSerialPositionedSourceCompressedProfileClosureReplay
        graphData minimal caps coloring web corridor hunique hlength)
    (edge : SourceLocalLayerSerialPositionedSourceCompressedProfileEdge) :
    (∃ letterIndex : Nat,
      replay.certificate.letters[letterIndex]? = some edge) ↔
      ∃ witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
          graphData caps coloring web corridor hunique,
        sourceLocalLayerSerialPositionedSourceCompressedProfileEdge graphData minimal caps coloring web corridor hunique
          witness = edge := by
  rw [← replay.certificate.letters_exact, replay.allowedLetter_eq]
  change edge ∈
      sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet
        graphData minimal caps coloring web corridor hunique ↔ _
  exact
    mem_sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet_iff
      graphData minimal caps coloring web corridor hunique edge

/-- The replay's initial array contains exactly the compressed two-pair
profiles of literal first-position witnesses. -/
theorem SourceLocalLayerSerialPositionedSourceCompressedProfileClosureReplay.initial_entry_iff_witness
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {caps : OrientedFacialPentagonCapPair graphData}
    {coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring}
    {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hlength : 2 < blockLength - 3}
    (replay :
      SourceLocalLayerSerialPositionedSourceCompressedProfileClosureReplay
        graphData minimal caps coloring web corridor hunique hlength)
    (profile : SourceLocalLayerSerialPositionedSourceCompressedProfile) :
    (∃ position profileIndex : Nat,
      replay.certificate.initialIndex[position]? = some profileIndex ∧
      replay.certificate.states[profileIndex]? = some profile) ↔
      ∃ witness : SourceLocalLayerSerialFirstRootedInteractionRealization
          graphData caps coloring web corridor hunique hlength,
        sourceLocalLayerSerialFirstSourceCompressedProfile graphData minimal caps coloring web corridor hunique hlength witness =
          profile := by
  rw [ExactReachableClosureCertificate.initial_entry_iff_realizable,
    replay.realizable_eq]
  change profile ∈
      sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet
        graphData minimal caps coloring web corridor hunique hlength ↔ _
  exact mem_sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet_iff
    graphData minimal caps coloring web corridor hunique hlength profile

/-- Exact semantic meaning of the replay's reported state count. -/
theorem SourceLocalLayerSerialPositionedSourceCompressedProfileClosureReplay.state_entry_iff
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {caps : OrientedFacialPentagonCapPair graphData}
    {coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring}
    {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {hlength : 2 < blockLength - 3}
    (replay :
      SourceLocalLayerSerialPositionedSourceCompressedProfileClosureReplay
        graphData minimal caps coloring web corridor hunique hlength)
    (profile : SourceLocalLayerSerialPositionedSourceCompressedProfile) :
    (∃ profileIndex : Nat,
      replay.certificate.states[profileIndex]? = some profile) ↔
      ClosureReachable
        (fun source edge target =>
          sourceLocalLayerSerialPositionedSourceCompressedProfileEdgeTransition
            edge source target)
        (fun candidate => candidate ∈
          sourceLocalLayerSerialRealizedInitialSourceCompressedProfileSet
            graphData minimal caps coloring web corridor hunique hlength)
        (fun edge => edge ∈
          sourceLocalLayerSerialPositionedRealizedSourceCompressedProfileEdgeSet
            graphData minimal caps coloring web corridor hunique)
        profile := by
  rw [ExactReachableClosureCertificate.state_entry_iff_reachable,
    replay.transition_eq, replay.realizable_eq, replay.allowedLetter_eq]

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedSourceClosure

end Mettapedia.GraphTheory.FourColor
