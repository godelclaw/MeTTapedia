import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRealizableTransition

/-!
# Positioned realized alphabet and initial carrier

The exact executable factorization at one fixed Cell position is not yet the
alphabet of a corridor word: a word ranges over every position at which the
Cell and the following rebase are defined.  This file takes that finite union
without enumerating the ambient factor type.

A positioned witness packages its offset together with the two successor
bounds required by the rolling transition.  Its encoded letter is the finite
Cell--rebase factor, so equal codes remain representation-invariant even when
they arose at different positions.  Separately, the first-position witness
image gives the exact realizable initial states for the corridor run.

No reachable closure is asserted here.  The next layer starts from the finite
initial image and repeatedly applies the finite positioned factor image, or
replays an external sparse certificate for that same transition system.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedClosure

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellCountNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRealizableTransition
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransition
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingTransitionColorParametric
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FiniteClosureInterfaces
open GoertzelV24HexSlabConnectivityProfile
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

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPositionedClosure

end Mettapedia.GraphTheory.FourColor
