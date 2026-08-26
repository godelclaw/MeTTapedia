import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRealizableTransition
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialTerminalProfileCompression

/-!
# Positioned realized alphabet and initial carrier

The exact executable factorization at one fixed Cell position is not yet the
alphabet of a corridor word: a word ranges over every position at which the
Cell and the following rebase are defined.  This file takes that finite union
without enumerating the ambient factor type.

A positioned witness packages its offset together with the two successor
bounds required by the rolling transition.  Three finite images are exposed.
The factor image supports graph-free application of a realized Cell--rebase
factor to candidate states.  The smaller endpoint image contains exactly the
literal source/target edges and therefore carries direct witness provenance
without a separate one-step realizability assumption.  The source-profile
image then forgets the rooted implementation receipts and retains the cut
colors, strand connectivity, and capped face progress used by `Count`.
Separately, the first-position witness images give the exact realizable rooted
states and source profiles for the corridor run.

No numerical reachable closure is asserted here.  Sparse replay interfaces are
provided for the source-profile graph, exact rooted endpoint graph, and more
permissive pooled factor system; their different semantic scopes are explicit
in their types.  Turning composable profile paths into physical splices remains
a separate theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedClosure

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebLocalLayerSerialCellCountNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRealizableTransition
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransition
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransitionColorParametric
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FiniteClosureInterfaces
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24TerminalAwareProfileCompression
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance positionedClosureOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A corridor offset carrying exactly the two following positions needed by
one Cell--rebase--roll step. -/
structure SourceLocalLayerSerialRollingPosition (blockLength : Nat) where
  offset : Fin (blockLength - 3)
  twoSteps : offset.val + 2 < blockLength - 3

private def sourceLocalLayerSerialRollingPositionEquiv (blockLength : Nat) :
    SourceLocalLayerSerialRollingPosition blockLength ≃
      {offset : Fin (blockLength - 3) //
        offset.val + 2 < blockLength - 3} where
  toFun position := ⟨position.offset, position.twoSteps⟩
  invFun position := ⟨position.1, position.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (blockLength : Nat) :
    Fintype (SourceLocalLayerSerialRollingPosition blockLength) :=
  Fintype.ofEquiv _
    (sourceLocalLayerSerialRollingPositionEquiv blockLength).symm

noncomputable instance (blockLength : Nat) :
    DecidableEq (SourceLocalLayerSerialRollingPosition blockLength) :=
  Classical.decEq _

/-- The first successor bound extracted from a rolling position. -/
theorem SourceLocalLayerSerialRollingPosition.hasNext
    {blockLength : Nat}
    (position : SourceLocalLayerSerialRollingPosition blockLength) :
    position.offset.val + 1 < blockLength - 3 := by
  exact (Nat.lt_succ_self (position.offset.val + 1)).trans position.twoSteps

/-- The second successor bound extracted from a rolling position. -/
theorem SourceLocalLayerSerialRollingPosition.hasNextNext
    {blockLength : Nat}
    (position : SourceLocalLayerSerialRollingPosition blockLength) :
    (sourceLocalLayerNextOffset position.offset position.hasNext).val + 1 <
      blockLength - 3 := by
  simpa using position.twoSteps

/-- A compatible positive prefix/Cell witness at any executable position of
the fixed source corridor. -/
abbrev SourceLocalLayerSerialPositionedRootedInteractionRealization
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
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :=
  Σ position : SourceLocalLayerSerialRollingPosition blockLength,
    SourceLocalLayerSerialRootedInteractionRealizationAt graphData caps coloring
      web corridor hunique position.offset position.hasNext

noncomputable instance sourceLocalLayerSerialPositionedRealizationFintype
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
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    Fintype (SourceLocalLayerSerialPositionedRootedInteractionRealization
      graphData caps coloring web corridor hunique) :=
  Fintype.ofFinite _

/-- Extract the exact source/factor/target step from one positioned witness. -/
noncomputable def sourceLocalLayerSerialPositionedRootedInteractionStep
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
    SourceLocalLayerSerialRootedInteractionRealizedStep :=
  sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
    coloring web corridor hunique witness.1.offset witness.1.hasNext
      witness.1.hasNextNext witness.2

/-- The representation-free observable edge of one positioned literal
witness.  Different positions and ambient witnesses which realize the same
rooted source and target collapse to one value. -/
abbrev SourceLocalLayerSerialPositionedRootedInteractionEdge :=
  SourceLocalLayerSerialRootedInteractionState ×
    SourceLocalLayerSerialRootedInteractionState

/-- Forget a positioned witness while retaining exactly its rooted transition
endpoints. -/
noncomputable def sourceLocalLayerSerialPositionedRootedInteractionEdge
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
    SourceLocalLayerSerialPositionedRootedInteractionEdge :=
  let step := sourceLocalLayerSerialPositionedRootedInteractionStep graphData
    minimal caps coloring web corridor hunique witness
  (step.source, step.target)

/-- The executable relation denoted by one observable rooted edge. -/
def sourceLocalLayerSerialPositionedEdgeTransition
    (edge : SourceLocalLayerSerialPositionedRootedInteractionEdge)
    (source target : SourceLocalLayerSerialRootedInteractionState) : Prop :=
  source = edge.1 ∧ target = edge.2

/-- A realized step relation is exactly the singleton relation carried by its
observable endpoint pair. -/
theorem sourceLocalLayerSerialPositionedStep_transition_eq_edgeTransition
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
    (sourceLocalLayerSerialPositionedRootedInteractionStep graphData minimal caps
      coloring web corridor hunique witness).transition =
      sourceLocalLayerSerialPositionedEdgeTransition
        (sourceLocalLayerSerialPositionedRootedInteractionEdge graphData minimal
          caps coloring web corridor hunique witness) := by
  funext source target
  apply propext
  exact
    sourceLocalLayerSerialRootedInteractionRealizedStepAt_transition_iff graphData
      minimal caps coloring web corridor hunique witness.1.offset
        witness.1.hasNext witness.1.hasNextNext witness.2 source target

/-- Exact finite rooted-letter presentation obtained by quotienting all
positioned literal witnesses by their observable transition endpoints. -/
noncomputable def sourceLocalLayerSerialPositionedEdgePresentation
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
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :=
  RootedLetterPresentation.ofFiniteImage
    (fun witness :
        SourceLocalLayerSerialPositionedRootedInteractionRealization graphData
          caps coloring web corridor hunique =>
      (sourceLocalLayerSerialPositionedRootedInteractionStep graphData minimal
        caps coloring web corridor hunique witness).transition)
    (sourceLocalLayerSerialPositionedRootedInteractionEdge graphData minimal caps
      coloring web corridor hunique)
    (by
      intro left right hedge
      rw [sourceLocalLayerSerialPositionedStep_transition_eq_edgeTransition,
        sourceLocalLayerSerialPositionedStep_transition_eq_edgeTransition,
        hedge])

/-- The finite set of distinct rooted transition edges realized at some
executable position of the fixed corridor. -/
noncomputable def sourceLocalLayerSerialPositionedRealizedEdgeSet
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
    Finset SourceLocalLayerSerialPositionedRootedInteractionEdge :=
  realizedCodeImage
    (sourceLocalLayerSerialPositionedRootedInteractionEdge graphData minimal caps
      coloring web corridor hunique)

/-- Membership in the observable edge image is equivalent to realization by
an actual compatible literal witness at an executable corridor position. -/
theorem mem_sourceLocalLayerSerialPositionedRealizedEdgeSet_iff
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
    (edge : SourceLocalLayerSerialPositionedRootedInteractionEdge) :
    edge ∈ sourceLocalLayerSerialPositionedRealizedEdgeSet graphData minimal caps
        coloring web corridor hunique ↔
      ∃ witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
          graphData caps coloring web corridor hunique,
        sourceLocalLayerSerialPositionedRootedInteractionEdge graphData minimal
          caps coloring web corridor hunique witness = edge := by
  classical
  simp [sourceLocalLayerSerialPositionedRealizedEdgeSet, realizedCodeImage]

/-- The source-facing object carried by a serial cut.  The much larger rooted
interaction state is an executable receipt; its `input` field is the actual
finite profile (cut colours, strand connectivity, and capped face progress)
specified by the compositional counting functor. -/
abbrev SourceLocalLayerSerialPositionedProfile :=
  BoundedCorridorCutProfile 2 1 4

/-- One directed edge of the source-facing profile transition graph. -/
abbrev SourceLocalLayerSerialPositionedProfileEdge :=
  SourceLocalLayerSerialPositionedProfile ×
    SourceLocalLayerSerialPositionedProfile

/-- The singleton transition relation denoted by one source-facing profile
edge. -/
def sourceLocalLayerSerialPositionedProfileEdgeTransition
    (edge : SourceLocalLayerSerialPositionedProfileEdge)
    (source target : SourceLocalLayerSerialPositionedProfile) : Prop :=
  source = edge.1 ∧ target = edge.2

/-- Project a literal positioned rooted step to its source and target cut
profiles. -/
noncomputable def sourceLocalLayerSerialPositionedProfileEdge
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
    SourceLocalLayerSerialPositionedProfileEdge :=
  let step := sourceLocalLayerSerialPositionedRootedInteractionStep graphData
    minimal caps coloring web corridor hunique witness
  (step.source.input, step.target.input)

/-- The finite image of source-facing profile edges realized by literal
compatible witnesses somewhere along the fixed corridor. -/
noncomputable def sourceLocalLayerSerialPositionedRealizedProfileEdgeSet
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
    Finset SourceLocalLayerSerialPositionedProfileEdge :=
  realizedCodeImage
    (sourceLocalLayerSerialPositionedProfileEdge graphData minimal caps coloring
      web corridor hunique)

/-- Exact literal-witness meaning of a realized source-profile edge. -/
theorem mem_sourceLocalLayerSerialPositionedRealizedProfileEdgeSet_iff
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
    (edge : SourceLocalLayerSerialPositionedProfileEdge) :
    edge ∈ sourceLocalLayerSerialPositionedRealizedProfileEdgeSet graphData
        minimal caps coloring web corridor hunique ↔
      ∃ witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
          graphData caps coloring web corridor hunique,
        sourceLocalLayerSerialPositionedProfileEdge graphData minimal caps
          coloring web corridor hunique witness = edge := by
  classical
  simp [sourceLocalLayerSerialPositionedRealizedProfileEdgeSet,
    realizedCodeImage]

/-- A source-profile edge is exactly the projection of some realized rooted
edge.  This connects the executable receipt graph to the finite object graph
of the manuscript's counting functor without claiming the converse lifting of
arbitrary profile paths; that is the separate splice theorem. -/
theorem mem_realizedProfileEdgeSet_iff_exists_realizedRootedEdge
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
    (profileEdge : SourceLocalLayerSerialPositionedProfileEdge) :
    profileEdge ∈ sourceLocalLayerSerialPositionedRealizedProfileEdgeSet
        graphData minimal caps coloring web corridor hunique ↔
      ∃ rootedEdge : SourceLocalLayerSerialPositionedRootedInteractionEdge,
        rootedEdge ∈ sourceLocalLayerSerialPositionedRealizedEdgeSet graphData
          minimal caps coloring web corridor hunique ∧
        (rootedEdge.1.input, rootedEdge.2.input) = profileEdge := by
  constructor
  · intro hedge
    rcases
        (mem_sourceLocalLayerSerialPositionedRealizedProfileEdgeSet_iff graphData
          minimal caps coloring web corridor hunique profileEdge).1 hedge with
      ⟨witness, hwitness⟩
    let rootedEdge :=
      sourceLocalLayerSerialPositionedRootedInteractionEdge graphData minimal caps
        coloring web corridor hunique witness
    refine ⟨rootedEdge, ?_, ?_⟩
    · exact
        (mem_sourceLocalLayerSerialPositionedRealizedEdgeSet_iff graphData minimal
          caps coloring web corridor hunique rootedEdge).2 ⟨witness, rfl⟩
    · exact hwitness
  · rintro ⟨rootedEdge, hrooted, hprojection⟩
    rcases
        (mem_sourceLocalLayerSerialPositionedRealizedEdgeSet_iff graphData minimal
          caps coloring web corridor hunique rootedEdge).1 hrooted with
      ⟨witness, hwitness⟩
    apply
      (mem_sourceLocalLayerSerialPositionedRealizedProfileEdgeSet_iff graphData
        minimal caps coloring web corridor hunique profileEdge).2
    refine ⟨witness, ?_⟩
    rw [← hprojection, ← hwitness]
    rfl

/-- The source-realized factor alphabet across every executable position of
the fixed corridor. -/
abbrev SourceLocalLayerSerialPositionedRealizedFactor
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
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :=
  RealizedCode (fun witness :
      SourceLocalLayerSerialPositionedRootedInteractionRealization graphData caps
        coloring web corridor hunique =>
    (sourceLocalLayerSerialPositionedRootedInteractionStep graphData minimal caps
      coloring web corridor hunique witness).factor)

/-- Representation-invariant rooted-letter presentation for the entire fixed
corridor, obtained by quotienting positioned ambient witnesses by their
compiled finite factor. -/
noncomputable def sourceLocalLayerSerialPositionedFactorPresentation
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
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :=
  RootedLetterPresentation.ofFiniteImage
    (fun witness :
        SourceLocalLayerSerialPositionedRootedInteractionRealization graphData
          caps coloring web corridor hunique =>
      sourceLocalLayerSerialRootedInteractionFactorTransition
        (sourceLocalLayerSerialPositionedRootedInteractionStep graphData minimal
          caps coloring web corridor hunique witness).factor)
    (fun witness :
        SourceLocalLayerSerialPositionedRootedInteractionRealization graphData
          caps coloring web corridor hunique =>
      (sourceLocalLayerSerialPositionedRootedInteractionStep graphData minimal
        caps coloring web corridor hunique witness).factor)
    (by
      intro left right heq
      exact congrArg sourceLocalLayerSerialRootedInteractionFactorTransition heq)

/-- The executable factor values realized somewhere along the fixed corridor.
This is the underlying `Finset` of the positioned factor-code subtype. -/
noncomputable def sourceLocalLayerSerialPositionedRealizedFactorSet
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
    Finset SourceLocalLayerSerialRootedInteractionRollingCellFactor :=
  realizedCodeImage (fun witness :
      SourceLocalLayerSerialPositionedRootedInteractionRealization graphData caps
        coloring web corridor hunique =>
    (sourceLocalLayerSerialPositionedRootedInteractionStep graphData minimal caps
      coloring web corridor hunique witness).factor)

/-- The graph-free one-step relation generated by every executable factor
realized at some position of the fixed corridor.  Pooling positions is
deliberate: it is the abstract closure relation.  A later theorem must prove
concatenation realizability before its closure may be called the exact set of
literal source runs. -/
noncomputable def sourceLocalLayerSerialPositionedOneStep
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
    (source target : SourceLocalLayerSerialRootedInteractionState) : Prop :=
  ∃ factor ∈ sourceLocalLayerSerialPositionedRealizedFactorSet graphData
      minimal caps coloring web corridor hunique,
    sourceLocalLayerSerialRootedInteractionFactorTransition factor source target

noncomputable instance sourceLocalLayerSerialPositionedOneStepDecidable
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
    DecidableRel (sourceLocalLayerSerialPositionedOneStep graphData minimal caps
      coloring web corridor hunique) :=
  Classical.decRel _

/-- Exact one-step correspondence: a pooled abstract step is precisely the
transition of some compatible positive literal witness at some executable
position of the corridor. -/
theorem sourceLocalLayerSerialPositionedOneStep_iff_exists_witness
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
    (source target : SourceLocalLayerSerialRootedInteractionState) :
    sourceLocalLayerSerialPositionedOneStep graphData minimal caps coloring web
        corridor hunique source target ↔
      ∃ witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
          graphData caps coloring web corridor hunique,
        sourceLocalLayerSerialRootedInteractionFactorTransition
          (sourceLocalLayerSerialPositionedRootedInteractionStep graphData minimal
            caps coloring web corridor hunique witness).factor source target := by
  classical
  constructor
  · rintro ⟨factor, hfactor, htransition⟩
    rcases Finset.mem_image.mp hfactor with ⟨witness, _hwitness, rfl⟩
    exact ⟨witness, htransition⟩
  · rintro ⟨witness, htransition⟩
    exact ⟨_, Finset.mem_image.mpr ⟨witness, Finset.mem_univ witness, rfl⟩,
      htransition⟩

set_option maxHeartbeats 800000 in
/-- Every positioned source witness executes through its canonical factor code
to its literal positioned target. -/
theorem sourceLocalLayerSerialPositioned_factorCodedTransition
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
    let step := sourceLocalLayerSerialPositionedRootedInteractionStep graphData
      minimal caps coloring web corridor hunique witness
    (sourceLocalLayerSerialPositionedFactorPresentation graphData minimal caps
      coloring web corridor hunique).codedTransition
        ((sourceLocalLayerSerialPositionedFactorPresentation graphData minimal
          caps coloring web corridor hunique).code witness)
        step.source step.target := by
  classical
  dsimp only
  rw [
    ← RootedLetterPresentation.rawTransition_eq_codedTransition
      (sourceLocalLayerSerialPositionedFactorPresentation graphData minimal caps
        coloring web corridor hunique) witness]
  exact
    (sourceLocalLayerSerialRootedInteractionRealizedStepAt_transition graphData
      minimal caps coloring web corridor hunique witness.1.offset
        witness.1.hasNext witness.1.hasNextNext witness.2).2.1

/-- Every literal positioned step belongs to the pooled executable one-step
relation, with its source and target fields unchanged. -/
theorem sourceLocalLayerSerialPositionedStep_oneStep
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
    let step := sourceLocalLayerSerialPositionedRootedInteractionStep graphData
      minimal caps coloring web corridor hunique witness
    sourceLocalLayerSerialPositionedOneStep graphData minimal caps coloring web
      corridor hunique step.source step.target := by
  exact
    (sourceLocalLayerSerialPositionedOneStep_iff_exists_witness graphData minimal
      caps coloring web corridor hunique _ _).2 ⟨witness,
        (sourceLocalLayerSerialRootedInteractionRealizedStepAt_transition graphData
          minimal caps coloring web corridor hunique witness.1.offset
            witness.1.hasNext witness.1.hasNextNext witness.2).2.1⟩

/-- The exact literal one-step relation: an edge is admitted only when some
compatible positive source witness realizes precisely those two endpoints.
Unlike the pooled factor relation above, this definition does not apply a
realized factor to a source state for which no literal representative has yet
been constructed. -/
noncomputable def sourceLocalLayerSerialPositionedExactOneStep
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
    (source target : SourceLocalLayerSerialRootedInteractionState) : Prop :=
  (source, target) ∈
    sourceLocalLayerSerialPositionedRealizedEdgeSet graphData minimal caps coloring
      web corridor hunique

noncomputable instance sourceLocalLayerSerialPositionedExactOneStepDecidable
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
    DecidableRel (sourceLocalLayerSerialPositionedExactOneStep graphData minimal
      caps coloring web corridor hunique) :=
  Classical.decRel _

/-- Exact source meaning of one observable edge. -/
theorem sourceLocalLayerSerialPositionedExactOneStep_iff_exists_witness
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
    (source target : SourceLocalLayerSerialRootedInteractionState) :
    sourceLocalLayerSerialPositionedExactOneStep graphData minimal caps coloring
        web corridor hunique source target ↔
      ∃ witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
          graphData caps coloring web corridor hunique,
        (sourceLocalLayerSerialPositionedRootedInteractionStep graphData minimal
          caps coloring web corridor hunique witness).source = source ∧
        (sourceLocalLayerSerialPositionedRootedInteractionStep graphData minimal
          caps coloring web corridor hunique witness).target = target := by
  classical
  rw [sourceLocalLayerSerialPositionedExactOneStep,
    mem_sourceLocalLayerSerialPositionedRealizedEdgeSet_iff]
  constructor
  · rintro ⟨witness, hedge⟩
    exact ⟨witness, congrArg Prod.fst hedge, congrArg Prod.snd hedge⟩
  · rintro ⟨witness, hsource, htarget⟩
    refine ⟨witness, ?_⟩
    exact Prod.ext hsource htarget

/-- Every exact literal edge is accepted by the pooled executable-factor
relation.  The converse is intentionally not claimed: it is precisely the
missing concatenation-realizability obligation for applying a factor to a new
rooted source. -/
theorem sourceLocalLayerSerialPositionedExactOneStep_imp_oneStep
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
    {source target : SourceLocalLayerSerialRootedInteractionState}
    (hstep : sourceLocalLayerSerialPositionedExactOneStep graphData minimal caps
      coloring web corridor hunique source target) :
    sourceLocalLayerSerialPositionedOneStep graphData minimal caps coloring web
      corridor hunique source target := by
  rcases
      (sourceLocalLayerSerialPositionedExactOneStep_iff_exists_witness graphData
        minimal caps coloring web corridor hunique source target).1 hstep with
    ⟨witness, hsource, htarget⟩
  subst source
  subst target
  exact sourceLocalLayerSerialPositionedStep_oneStep graphData minimal caps
    coloring web corridor hunique witness

/-- The first executable rolling position, under the exact length premise
needed for two following cuts. -/
def sourceLocalLayerSerialFirstRollingPosition
    {blockLength : Nat} (hlength : 2 < blockLength - 3) :
    SourceLocalLayerSerialRollingPosition blockLength where
  offset := ⟨0, by omega⟩
  twoSteps := by simpa using hlength

/-- Compatible positive witnesses at the actual first rolling position. -/
abbrev SourceLocalLayerSerialFirstRootedInteractionRealization
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
    (hlength : 2 < blockLength - 3) :=
  SourceLocalLayerSerialRootedInteractionRealizationAt graphData caps coloring
    web corridor hunique (sourceLocalLayerSerialFirstRollingPosition hlength).offset
      (sourceLocalLayerSerialFirstRollingPosition hlength).hasNext

noncomputable instance sourceLocalLayerSerialFirstRealizationFintype
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
    (hlength : 2 < blockLength - 3) :
    Fintype (SourceLocalLayerSerialFirstRootedInteractionRealization graphData
      caps coloring web corridor hunique hlength) :=
  Fintype.ofFinite _

/-- Encode the rooted source state of a first-position witness. -/
noncomputable def sourceLocalLayerSerialFirstRootedInteractionState
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
    SourceLocalLayerSerialRootedInteractionState :=
  (sourceLocalLayerSerialRootedInteractionRealizedStepAt graphData minimal caps
    coloring web corridor hunique
      (sourceLocalLayerSerialFirstRollingPosition hlength).offset
      (sourceLocalLayerSerialFirstRollingPosition hlength).hasNext
      (sourceLocalLayerSerialFirstRollingPosition hlength).hasNextNext witness
  ).source

/-- The executable rooted states produced by compatible witnesses at the actual
first rolling position. -/
noncomputable def sourceLocalLayerSerialRealizedInitialStateSet
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
    Finset SourceLocalLayerSerialRootedInteractionState :=
  realizedCodeImage (sourceLocalLayerSerialFirstRootedInteractionState graphData
    minimal caps coloring web corridor hunique hlength)

/-- Exact finite image of realizable first-cut rooted states. -/
abbrev SourceLocalLayerSerialRealizedInitialState
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
    (hlength : 2 < blockLength - 3) :=
  {state // state ∈ sourceLocalLayerSerialRealizedInitialStateSet graphData
    minimal caps coloring web corridor hunique hlength}

/-- Membership in the executable initial set is equivalent to having a literal
compatible witness at the first rolling position. -/
theorem mem_sourceLocalLayerSerialRealizedInitialStateSet_iff
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
    (state : SourceLocalLayerSerialRootedInteractionState) :
    state ∈ sourceLocalLayerSerialRealizedInitialStateSet graphData minimal caps
        coloring web corridor hunique hlength ↔
      ∃ witness : SourceLocalLayerSerialFirstRootedInteractionRealization
          graphData caps coloring web corridor hunique hlength,
        sourceLocalLayerSerialFirstRootedInteractionState graphData minimal caps
          coloring web corridor hunique hlength witness = state := by
  classical
  simp [sourceLocalLayerSerialRealizedInitialStateSet, realizedCodeImage]

/-- Every canonical initial-state code has an actual compatible first-position
witness. -/
theorem sourceLocalLayerSerialRealizedInitialState_hasRepresentative
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
    (state : SourceLocalLayerSerialRealizedInitialState graphData minimal caps
      coloring web corridor hunique hlength) :
    ∃ witness : SourceLocalLayerSerialFirstRootedInteractionRealization
        graphData caps coloring web corridor hunique hlength,
      sourceLocalLayerSerialFirstRootedInteractionState graphData minimal caps
        coloring web corridor hunique hlength witness = state.1 := by
  classical
  let encode := sourceLocalLayerSerialFirstRootedInteractionState graphData
    minimal caps coloring web corridor hunique hlength
  exact ⟨realizedCodeRepresentative encode state,
    congrArg Subtype.val (realizedCodeOf_representative encode state)⟩

/-- The exact first-cut image after forgetting executable rooted receipts and
retaining only the source-facing cut profile. -/
noncomputable def sourceLocalLayerSerialRealizedInitialProfileSet
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
    Finset SourceLocalLayerSerialPositionedProfile :=
  realizedCodeImage (fun witness :
      SourceLocalLayerSerialFirstRootedInteractionRealization graphData caps
        coloring web corridor hunique hlength =>
    (sourceLocalLayerSerialFirstRootedInteractionState graphData minimal caps
      coloring web corridor hunique hlength witness).input)

/-- A first-cut profile is realizable exactly when some compatible literal
first-position witness projects to it. -/
theorem mem_sourceLocalLayerSerialRealizedInitialProfileSet_iff
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
    (profile : SourceLocalLayerSerialPositionedProfile) :
    profile ∈ sourceLocalLayerSerialRealizedInitialProfileSet graphData minimal
        caps coloring web corridor hunique hlength ↔
      ∃ witness : SourceLocalLayerSerialFirstRootedInteractionRealization
          graphData caps coloring web corridor hunique hlength,
        (sourceLocalLayerSerialFirstRootedInteractionState graphData minimal caps
          coloring web corridor hunique hlength witness).input = profile := by
  classical
  simp [sourceLocalLayerSerialRealizedInitialProfileSet, realizedCodeImage]

/-- Sparse exact-closure replay for the source-facing profile graph.  A
certificate inhabiting this structure reports a count of reachable profile
objects, not of rooted implementation receipts.  Physical realization of an
arbitrary composite profile path remains the separate splice theorem. -/
structure SourceLocalLayerSerialPositionedProfileClosureReplay
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
    SourceLocalLayerSerialPositionedProfile
    SourceLocalLayerSerialPositionedProfileEdge Unit
  transition_eq : certificate.transition =
    fun source edge target =>
      sourceLocalLayerSerialPositionedProfileEdgeTransition edge source target
  allowedLetter_eq : certificate.allowedLetter =
    fun edge => edge ∈
      sourceLocalLayerSerialPositionedRealizedProfileEdgeSet graphData minimal caps
        coloring web corridor hunique
  realizable_eq : certificate.realizable =
    fun profile => profile ∈
      sourceLocalLayerSerialRealizedInitialProfileSet graphData minimal caps
        coloring web corridor hunique hlength

/-- The profile replay contains exactly the profile edges projected from
literal compatible positioned witnesses. -/
theorem SourceLocalLayerSerialPositionedProfileClosureReplay.letter_entry_iff_witness
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
    (replay : SourceLocalLayerSerialPositionedProfileClosureReplay graphData
      minimal caps coloring web corridor hunique hlength)
    (edge : SourceLocalLayerSerialPositionedProfileEdge) :
    (∃ letterIndex : Nat,
      replay.certificate.letters[letterIndex]? = some edge) ↔
      ∃ witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
          graphData caps coloring web corridor hunique,
        sourceLocalLayerSerialPositionedProfileEdge graphData minimal caps
          coloring web corridor hunique witness = edge := by
  rw [← replay.certificate.letters_exact, replay.allowedLetter_eq]
  change edge ∈ sourceLocalLayerSerialPositionedRealizedProfileEdgeSet
      graphData minimal caps coloring web corridor hunique ↔ _
  exact mem_sourceLocalLayerSerialPositionedRealizedProfileEdgeSet_iff
    graphData minimal caps coloring web corridor hunique edge

/-- The profile replay's initial array contains exactly the projected profiles
of compatible first-position witnesses. -/
theorem SourceLocalLayerSerialPositionedProfileClosureReplay.initial_entry_iff_witness
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
    (replay : SourceLocalLayerSerialPositionedProfileClosureReplay graphData
      minimal caps coloring web corridor hunique hlength)
    (profile : SourceLocalLayerSerialPositionedProfile) :
    (∃ position profileIndex : Nat,
      replay.certificate.initialIndex[position]? = some profileIndex ∧
      replay.certificate.states[profileIndex]? = some profile) ↔
      ∃ witness : SourceLocalLayerSerialFirstRootedInteractionRealization
          graphData caps coloring web corridor hunique hlength,
        (sourceLocalLayerSerialFirstRootedInteractionState graphData minimal caps
          coloring web corridor hunique hlength witness).input = profile := by
  rw [ExactReachableClosureCertificate.initial_entry_iff_realizable,
    replay.realizable_eq]
  change profile ∈ sourceLocalLayerSerialRealizedInitialProfileSet graphData
      minimal caps coloring web corridor hunique hlength ↔ _
  exact mem_sourceLocalLayerSerialRealizedInitialProfileSet_iff graphData minimal
    caps coloring web corridor hunique hlength profile

/-- Exact semantic meaning of the profile replay's reported integer.  The
array size counts precisely the relational closure generated by literal
source-profile edges from literal first-cut profiles. -/
theorem SourceLocalLayerSerialPositionedProfileClosureReplay.state_entry_iff
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
    (replay : SourceLocalLayerSerialPositionedProfileClosureReplay graphData
      minimal caps coloring web corridor hunique hlength)
    (profile : SourceLocalLayerSerialPositionedProfile) :
    (∃ profileIndex : Nat,
      replay.certificate.states[profileIndex]? = some profile) ↔
      ClosureReachable
        (fun source edge target =>
          sourceLocalLayerSerialPositionedProfileEdgeTransition edge source target)
        (fun candidate => candidate ∈
          sourceLocalLayerSerialRealizedInitialProfileSet graphData minimal caps
            coloring web corridor hunique hlength)
        (fun edge => edge ∈
          sourceLocalLayerSerialPositionedRealizedProfileEdgeSet graphData minimal
            caps coloring web corridor hunique)
        profile := by
  rw [ExactReachableClosureCertificate.state_entry_iff_reachable,
    replay.transition_eq, replay.realizable_eq, replay.allowedLetter_eq]

/-- A sparse closure replay over exact literal endpoint pairs.  In contrast to
the factor replay below, its transition alphabet contains no application of a
realized factor to an unrelated source state: every allowed edge has a literal
compatible witness by `mem_sourceLocalLayerSerialPositionedRealizedEdgeSet_iff`.
-/
structure SourceLocalLayerSerialPositionedExactEdgeClosureReplay
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
    SourceLocalLayerSerialRootedInteractionState
    SourceLocalLayerSerialPositionedRootedInteractionEdge Unit
  transition_eq : certificate.transition =
    fun source edge target =>
      sourceLocalLayerSerialPositionedEdgeTransition edge source target
  allowedLetter_eq : certificate.allowedLetter =
    fun edge => edge ∈
      sourceLocalLayerSerialPositionedRealizedEdgeSet graphData minimal caps
        coloring web corridor hunique
  realizable_eq : certificate.realizable =
    fun state => state ∈
      sourceLocalLayerSerialRealizedInitialStateSet graphData minimal caps coloring
        web corridor hunique hlength

/-- The edge replay's letter array is exactly the image of literal compatible
positioned witnesses. -/
theorem SourceLocalLayerSerialPositionedExactEdgeClosureReplay.letter_entry_iff
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
    (replay : SourceLocalLayerSerialPositionedExactEdgeClosureReplay graphData
      minimal caps coloring web corridor hunique hlength)
    (edge : SourceLocalLayerSerialPositionedRootedInteractionEdge) :
    (∃ letterIndex : Nat,
      replay.certificate.letters[letterIndex]? = some edge) ↔
      edge ∈ sourceLocalLayerSerialPositionedRealizedEdgeSet graphData minimal
        caps coloring web corridor hunique := by
  rw [← replay.certificate.letters_exact, replay.allowedLetter_eq]

/-- Every replayed edge has direct literal source provenance. -/
theorem SourceLocalLayerSerialPositionedExactEdgeClosureReplay.letter_entry_iff_witness
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
    (replay : SourceLocalLayerSerialPositionedExactEdgeClosureReplay graphData
      minimal caps coloring web corridor hunique hlength)
    (edge : SourceLocalLayerSerialPositionedRootedInteractionEdge) :
    (∃ letterIndex : Nat,
      replay.certificate.letters[letterIndex]? = some edge) ↔
      ∃ witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
          graphData caps coloring web corridor hunique,
        sourceLocalLayerSerialPositionedRootedInteractionEdge graphData minimal
          caps coloring web corridor hunique witness = edge := by
  rw [replay.letter_entry_iff,
    mem_sourceLocalLayerSerialPositionedRealizedEdgeSet_iff]

/-- Exact semantic meaning of the edge replay's reported state count.  The
array entries are precisely the states reachable from exact first-cut states
through endpoint pairs which themselves have literal compatible witnesses. -/
theorem SourceLocalLayerSerialPositionedExactEdgeClosureReplay.state_entry_iff
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
    (replay : SourceLocalLayerSerialPositionedExactEdgeClosureReplay graphData
      minimal caps coloring web corridor hunique hlength)
    (state : SourceLocalLayerSerialRootedInteractionState) :
    (∃ stateIndex : Nat,
      replay.certificate.states[stateIndex]? = some state) ↔
      ClosureReachable
        (fun source edge target =>
          sourceLocalLayerSerialPositionedEdgeTransition edge source target)
        (fun candidate => candidate ∈
          sourceLocalLayerSerialRealizedInitialStateSet graphData minimal caps
            coloring web corridor hunique hlength)
        (fun edge => edge ∈
          sourceLocalLayerSerialPositionedRealizedEdgeSet graphData minimal caps
            coloring web corridor hunique)
        state := by
  rw [ExactReachableClosureCertificate.state_entry_iff_reachable,
    replay.transition_eq, replay.realizable_eq, replay.allowedLetter_eq]

/-- A sparse exact-closure replay bound to this source instance rather than to
three arbitrary arrays.  The equalities make the certificate's transition,
alphabet and initial predicate definitionally auditable against the executable
Cell--rebase factorization above.  `Unit` is sufficient as the row witness:
the transition itself is executable, while source realizability is already
carried by the finite letter image. -/
structure SourceLocalLayerSerialPositionedExactClosureReplay
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
    SourceLocalLayerSerialRootedInteractionState
    SourceLocalLayerSerialRootedInteractionRollingCellFactor Unit
  transition_eq : certificate.transition =
    fun source factor target =>
      sourceLocalLayerSerialRootedInteractionFactorTransition factor source target
  allowedLetter_eq : certificate.allowedLetter =
    fun factor => factor ∈
      sourceLocalLayerSerialPositionedRealizedFactorSet graphData minimal caps
        coloring web corridor hunique
  realizable_eq : certificate.realizable =
    fun state => state ∈
      sourceLocalLayerSerialRealizedInitialStateSet graphData minimal caps coloring
        web corridor hunique hlength

/-- The replay's letter array contains exactly the source-realized executable
factor set for this corridor. -/
theorem SourceLocalLayerSerialPositionedExactClosureReplay.letter_entry_iff
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
    (replay : SourceLocalLayerSerialPositionedExactClosureReplay graphData minimal
      caps coloring web corridor hunique hlength)
    (factor : SourceLocalLayerSerialRootedInteractionRollingCellFactor) :
    (∃ letterIndex : Nat,
      replay.certificate.letters[letterIndex]? = some factor) ↔
      factor ∈ sourceLocalLayerSerialPositionedRealizedFactorSet graphData
        minimal caps coloring web corridor hunique := by
  rw [← replay.certificate.letters_exact, replay.allowedLetter_eq]

/-- The replay's initial index array contains exactly the compatible rooted
states at the first executable cut. -/
theorem SourceLocalLayerSerialPositionedExactClosureReplay.initial_entry_iff
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
    (replay : SourceLocalLayerSerialPositionedExactClosureReplay graphData minimal
      caps coloring web corridor hunique hlength)
    (state : SourceLocalLayerSerialRootedInteractionState) :
    (∃ position stateIndex : Nat,
      replay.certificate.initialIndex[position]? = some stateIndex ∧
      replay.certificate.states[stateIndex]? = some state) ↔
      state ∈ sourceLocalLayerSerialRealizedInitialStateSet graphData minimal caps
        coloring web corridor hunique hlength := by
  rw [ExactReachableClosureCertificate.initial_entry_iff_realizable,
    replay.realizable_eq]

/-- Exact semantic meaning of the replayed integer.  An ambient rooted state is
listed in `certificate.states` iff it is reachable from the exact first-cut
image by a finite sequence of executable factors from the exact positioned
factor image.  Since the certificate also proves `states_injective`, the array
size is the cardinality of this abstract reachable closure. -/
theorem SourceLocalLayerSerialPositionedExactClosureReplay.state_entry_iff
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
    (replay : SourceLocalLayerSerialPositionedExactClosureReplay graphData minimal
      caps coloring web corridor hunique hlength)
    (state : SourceLocalLayerSerialRootedInteractionState) :
    (∃ stateIndex : Nat,
      replay.certificate.states[stateIndex]? = some state) ↔
      ClosureReachable
        (fun source factor target =>
          sourceLocalLayerSerialRootedInteractionFactorTransition factor source
            target)
        (fun candidate => candidate ∈
          sourceLocalLayerSerialRealizedInitialStateSet graphData minimal caps
            coloring web corridor hunique hlength)
        (fun factor => factor ∈
          sourceLocalLayerSerialPositionedRealizedFactorSet graphData minimal caps
            coloring web corridor hunique)
        state := by
  rw [ExactReachableClosureCertificate.state_entry_iff_reachable,
    replay.transition_eq, replay.realizable_eq, replay.allowedLetter_eq]

/-! ## Lossless terminal-aware compression of the exact profile graph -/

/-- The profile field of every literal rooted state constructor satisfies the
terminal graph laws used by the lossless compressor. -/
theorem sourceLocalLayerSerialRootedInteractionStateForColorAt_input_isTerminalGraphSemantic
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
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        offset).crossingEdge step) ≠ 0) :
    BoundedIsTerminalGraphSemantic
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique offset hnext color hcrossing).input := by
  change BoundedIsTerminalGraphSemantic
    (terminalInputBoundedProfileForColorAt corridor hunique offset color
      hcrossing)
  exact terminalInputBoundedProfileForColorAt_isTerminalGraphSemantic corridor
    hunique offset color hcrossing

/-- Both endpoints of every literal positioned step satisfy the terminal graph
laws.  The target law is applied to the actual prefix/Cell splice, not merely
to the ambient web colouring. -/
theorem sourceLocalLayerSerialPositionedStep_endpoints_areTerminalGraphSemantic
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
    let step := sourceLocalLayerSerialPositionedRootedInteractionStep graphData
      minimal caps coloring web corridor hunique witness
    BoundedIsTerminalGraphSemantic step.source.input ∧
      BoundedIsTerminalGraphSemantic step.target.input := by
  rcases witness with ⟨position, ⟨⟨prefixData, cellColoring⟩, hcompatible⟩⟩
  let cellColor := sourceLocalLayerCellLiteralColorAt caps coloring web corridor
    hunique position.offset cellColoring
  let hcell : ∀ {edge}, edge ∈
      sourceLocalLayerCellRegionAt corridor hunique position.offset →
        cellColor edge ≠ 0 :=
    sourceLocalLayerCellLiteralColorAt_ne_zero_of_mem caps coloring web corridor
      hunique position.offset cellColoring
  let splice := sourceLocalLayerSerialCellSplicedColorAt corridor hunique
    position.offset prefixData.1 cellColor
  let hrole : ∀ role, splice
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique position.offset
        position.hasNext role) ≠ 0 :=
    sourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero_of_prefix
      corridor hunique position.offset position.hasNext prefixData.1 cellColor
        prefixData.2 hcell
  let hnextCrossing := successorCrossingNonzeroForColorAt corridor hunique
    position.offset position.hasNext splice hrole
  constructor
  · simpa [sourceLocalLayerSerialPositionedRootedInteractionStep,
      sourceLocalLayerSerialRootedInteractionRealizedStepAt] using
      (sourceLocalLayerSerialRootedInteractionStateForColorAt_input_isTerminalGraphSemantic
        graphData minimal caps coloring web corridor hunique position.offset
          position.hasNext prefixData.1 (fun step => prefixData.2 _))
  · simpa [sourceLocalLayerSerialPositionedRootedInteractionStep,
      sourceLocalLayerSerialRootedInteractionRealizedStepAt, cellColor, hcell,
      splice, hrole, hnextCrossing] using
      (sourceLocalLayerSerialRootedInteractionStateForColorAt_input_isTerminalGraphSemantic
        graphData minimal caps coloring web corridor hunique
          (sourceLocalLayerNextOffset position.offset position.hasNext)
          position.hasNextNext splice hnextCrossing)

/-- The finite lossless carrier for the source-facing terminal profile. -/
abbrev SourceLocalLayerSerialPositionedCompressedProfile :=
  BoundedTerminalAwareCompressedProfile 2 1 4

/-- One directed edge after lossless terminal-aware compression. -/
abbrev SourceLocalLayerSerialPositionedCompressedProfileEdge :=
  SourceLocalLayerSerialPositionedCompressedProfile ×
    SourceLocalLayerSerialPositionedCompressedProfile

/-- Compress both source-facing endpoints of one literal positioned witness. -/
noncomputable def sourceLocalLayerSerialPositionedCompressedProfileEdge
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
    SourceLocalLayerSerialPositionedCompressedProfileEdge :=
  let step := sourceLocalLayerSerialPositionedRootedInteractionStep graphData
    minimal caps coloring web corridor hunique witness
  let semantic :=
    sourceLocalLayerSerialPositionedStep_endpoints_areTerminalGraphSemantic
      graphData minimal caps coloring web corridor hunique witness
  (compressBounded step.source.input semantic.1,
    compressBounded step.target.input semantic.2)

/-- Compression identifies two literal profile edges exactly when their full
five-field source and target profiles were already equal. -/
theorem sourceLocalLayerSerialPositionedCompressedProfileEdge_eq_iff
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
    sourceLocalLayerSerialPositionedCompressedProfileEdge graphData minimal caps
        coloring web corridor hunique left =
      sourceLocalLayerSerialPositionedCompressedProfileEdge graphData minimal caps
        coloring web corridor hunique right ↔
      sourceLocalLayerSerialPositionedProfileEdge graphData minimal caps coloring
        web corridor hunique left =
      sourceLocalLayerSerialPositionedProfileEdge graphData minimal caps coloring
        web corridor hunique right := by
  let leftStep := sourceLocalLayerSerialPositionedRootedInteractionStep graphData
    minimal caps coloring web corridor hunique left
  let rightStep := sourceLocalLayerSerialPositionedRootedInteractionStep graphData
    minimal caps coloring web corridor hunique right
  have leftSemantic :=
    sourceLocalLayerSerialPositionedStep_endpoints_areTerminalGraphSemantic
      graphData minimal caps coloring web corridor hunique left
  have rightSemantic :=
    sourceLocalLayerSerialPositionedStep_endpoints_areTerminalGraphSemantic
      graphData minimal caps coloring web corridor hunique right
  constructor
  · intro heq
    apply Prod.ext
    · exact compressBounded_injective leftSemantic.1 rightSemantic.1
        (congrArg Prod.fst heq)
    · exact compressBounded_injective leftSemantic.2 rightSemantic.2
        (congrArg Prod.snd heq)
  · intro heq
    have hsource : leftStep.source.input = rightStep.source.input :=
      congrArg Prod.fst heq
    have htarget : leftStep.target.input = rightStep.target.input :=
      congrArg Prod.snd heq
    apply Prod.ext
    · exact compressBounded_eq_of_eq leftSemantic.1 rightSemantic.1 hsource
    · exact compressBounded_eq_of_eq leftSemantic.2 rightSemantic.2 htarget

/-- The finite image of losslessly compressed profile edges realized along the
fixed corridor. -/
noncomputable def sourceLocalLayerSerialPositionedRealizedCompressedProfileEdgeSet
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
    Finset SourceLocalLayerSerialPositionedCompressedProfileEdge :=
  realizedCodeImage
    (sourceLocalLayerSerialPositionedCompressedProfileEdge graphData minimal caps
      coloring web corridor hunique)

/-- Exact literal-witness meaning of a compressed source-profile edge. -/
theorem mem_sourceLocalLayerSerialPositionedRealizedCompressedProfileEdgeSet_iff
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
    (edge : SourceLocalLayerSerialPositionedCompressedProfileEdge) :
    edge ∈ sourceLocalLayerSerialPositionedRealizedCompressedProfileEdgeSet
        graphData minimal caps coloring web corridor hunique ↔
      ∃ witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
          graphData caps coloring web corridor hunique,
        sourceLocalLayerSerialPositionedCompressedProfileEdge graphData minimal
          caps coloring web corridor hunique witness = edge := by
  classical
  simp [sourceLocalLayerSerialPositionedRealizedCompressedProfileEdgeSet,
    realizedCodeImage]

/-- The singleton transition relation carried by one compressed profile edge. -/
def sourceLocalLayerSerialPositionedCompressedProfileEdgeTransition
    (edge : SourceLocalLayerSerialPositionedCompressedProfileEdge)
    (source target : SourceLocalLayerSerialPositionedCompressedProfile) : Prop :=
  source = edge.1 ∧ target = edge.2

/-- Compress the source profile of a literal first-position witness.  The
following-position bound packages that witness as an ordinary positioned
transition witness, so the initial and edge encodings use one definition. -/
noncomputable def sourceLocalLayerSerialFirstCompressedProfile
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
    SourceLocalLayerSerialPositionedCompressedProfile :=
  (sourceLocalLayerSerialPositionedCompressedProfileEdge graphData minimal caps
    coloring web corridor hunique
      ⟨sourceLocalLayerSerialFirstRollingPosition hlength, witness⟩).1

/-- The exact compressed image of realizable first-cut profiles. -/
noncomputable def sourceLocalLayerSerialRealizedInitialCompressedProfileSet
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
    Finset SourceLocalLayerSerialPositionedCompressedProfile :=
  realizedCodeImage (sourceLocalLayerSerialFirstCompressedProfile graphData
    minimal caps coloring web corridor hunique hlength)

/-- A compressed initial profile is present exactly when a literal compatible
first-position witness produces it. -/
theorem mem_sourceLocalLayerSerialRealizedInitialCompressedProfileSet_iff
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
    (profile : SourceLocalLayerSerialPositionedCompressedProfile) :
    profile ∈ sourceLocalLayerSerialRealizedInitialCompressedProfileSet
        graphData minimal caps coloring web corridor hunique hlength ↔
      ∃ witness : SourceLocalLayerSerialFirstRootedInteractionRealization
          graphData caps coloring web corridor hunique hlength,
        sourceLocalLayerSerialFirstCompressedProfile graphData minimal caps
          coloring web corridor hunique hlength witness = profile := by
  classical
  simp [sourceLocalLayerSerialRealizedInitialCompressedProfileSet,
    realizedCodeImage]

/-- Sparse exact-closure replay over the losslessly compressed source-profile
graph.  Its state count is definitionally a count of compressed semantic
profiles; injectivity above makes it equally a count of the represented raw
five-field profiles.  Physical composition of successive witnesses remains the
separate profile-splice obligation. -/
structure SourceLocalLayerSerialPositionedCompressedProfileClosureReplay
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
    SourceLocalLayerSerialPositionedCompressedProfile
    SourceLocalLayerSerialPositionedCompressedProfileEdge Unit
  transition_eq : certificate.transition =
    fun source edge target =>
      sourceLocalLayerSerialPositionedCompressedProfileEdgeTransition edge source
        target
  allowedLetter_eq : certificate.allowedLetter =
    fun edge => edge ∈
      sourceLocalLayerSerialPositionedRealizedCompressedProfileEdgeSet graphData
        minimal caps coloring web corridor hunique
  realizable_eq : certificate.realizable =
    fun profile => profile ∈
      sourceLocalLayerSerialRealizedInitialCompressedProfileSet graphData minimal
        caps coloring web corridor hunique hlength

/-- The compressed replay's letter array contains exactly the losslessly
compressed edges of literal positioned witnesses. -/
theorem SourceLocalLayerSerialPositionedCompressedProfileClosureReplay.letter_entry_iff_witness
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
    (replay : SourceLocalLayerSerialPositionedCompressedProfileClosureReplay
      graphData minimal caps coloring web corridor hunique hlength)
    (edge : SourceLocalLayerSerialPositionedCompressedProfileEdge) :
    (∃ letterIndex : Nat,
      replay.certificate.letters[letterIndex]? = some edge) ↔
      ∃ witness : SourceLocalLayerSerialPositionedRootedInteractionRealization
          graphData caps coloring web corridor hunique,
        sourceLocalLayerSerialPositionedCompressedProfileEdge graphData minimal
          caps coloring web corridor hunique witness = edge := by
  rw [← replay.certificate.letters_exact, replay.allowedLetter_eq]
  change edge ∈
      sourceLocalLayerSerialPositionedRealizedCompressedProfileEdgeSet graphData
        minimal caps coloring web corridor hunique ↔ _
  exact
    mem_sourceLocalLayerSerialPositionedRealizedCompressedProfileEdgeSet_iff
      graphData minimal caps coloring web corridor hunique edge

/-- The compressed replay's initial array contains exactly the compressed
profiles of literal first-position witnesses. -/
theorem SourceLocalLayerSerialPositionedCompressedProfileClosureReplay.initial_entry_iff_witness
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
    (replay : SourceLocalLayerSerialPositionedCompressedProfileClosureReplay
      graphData minimal caps coloring web corridor hunique hlength)
    (profile : SourceLocalLayerSerialPositionedCompressedProfile) :
    (∃ position profileIndex : Nat,
      replay.certificate.initialIndex[position]? = some profileIndex ∧
      replay.certificate.states[profileIndex]? = some profile) ↔
      ∃ witness : SourceLocalLayerSerialFirstRootedInteractionRealization
          graphData caps coloring web corridor hunique hlength,
        sourceLocalLayerSerialFirstCompressedProfile graphData minimal caps
          coloring web corridor hunique hlength witness = profile := by
  rw [ExactReachableClosureCertificate.initial_entry_iff_realizable,
    replay.realizable_eq]
  change profile ∈ sourceLocalLayerSerialRealizedInitialCompressedProfileSet
      graphData minimal caps coloring web corridor hunique hlength ↔ _
  exact mem_sourceLocalLayerSerialRealizedInitialCompressedProfileSet_iff
    graphData minimal caps coloring web corridor hunique hlength profile

/-- Exact semantic meaning of the compressed replay's reported state count. -/
theorem SourceLocalLayerSerialPositionedCompressedProfileClosureReplay.state_entry_iff
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
    (replay : SourceLocalLayerSerialPositionedCompressedProfileClosureReplay
      graphData minimal caps coloring web corridor hunique hlength)
    (profile : SourceLocalLayerSerialPositionedCompressedProfile) :
    (∃ profileIndex : Nat,
      replay.certificate.states[profileIndex]? = some profile) ↔
      ClosureReachable
        (fun source edge target =>
          sourceLocalLayerSerialPositionedCompressedProfileEdgeTransition edge
            source target)
        (fun candidate => candidate ∈
          sourceLocalLayerSerialRealizedInitialCompressedProfileSet graphData
            minimal caps coloring web corridor hunique hlength)
        (fun edge => edge ∈
          sourceLocalLayerSerialPositionedRealizedCompressedProfileEdgeSet
            graphData minimal caps coloring web corridor hunique)
        profile := by
  rw [ExactReachableClosureCertificate.state_entry_iff_reachable,
    replay.transition_eq, replay.realizable_eq, replay.allowedLetter_eq]

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedClosure

end Mettapedia.GraphTheory.FourColor
