import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedSource
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedCoreState

/-!
# A finite expanded predecessor receipt for one Cell rebase

The rolling twenty-one-edge predecessor carrier need not contain every one of
the four semantic roles of the following boundary rebase.  A role absent from
that carrier can still be an old ambient edge of the accumulated prefix, so it
is not sound to declare every such occurrence inactive.

This file takes the other exact branch.  One transition carries the
mask-independent interface-exterior code on the predecessor coordinates plus
the four role occurrences.  The carrier has at most twenty-five occurrences,
is finite, and records aliases explicitly.  On literal source data the receipt
is exact for every tracked colour pair.  Applying the already verified finite
role mask then gives the exact deletion-safe core consumed by the successor
recurrence, without a fresh-role hypothesis.

This is the tracked lookahead field of a relational Cell--rebase letter.  It
does not assert that every arbitrary finite receipt is source-realizable, and
it does not measure a reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedReceipt

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedInterface
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedCoreState
open GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedSource
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedDeletionStablePreRebaseTotal
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24InterfaceDeletionComponentFactorTotal
open GoertzelV24InterfaceDeletionComponentFactorTotalGraph
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedReceiptOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The bounded tracked lookahead carried by one relational Cell--rebase
letter.  The old coordinates and the four semantic roles are occurrences, not
assumed-distinct ambient edges. -/
abbrev SourceLocalLayerSerialCellRebaseExpandedReceipt
    (current : Finset G.edgeSet) :=
  TrackedColorPair →
    BoundedInterfaceExteriorCode
      (SourceLocalLayerSerialCellRebaseExpandedInterface current)

/-- Closed finite carrier for the tracked part of one Cell--rebase receipt.
The predecessor cardinality, rather than its ambient edge type, indexes the
code.  The two old output crossings are retained as coordinates because they
are the persistent ports used by the core decoder. -/
structure SourceLocalLayerSerialCellRebaseBoundedExpandedReceipt where
  predecessorCount : Fin 22
  code : TrackedColorPair →
    BoundedInterfaceExteriorCode
      (Fin predecessorCount.val ⊕ SourceLocalLayerBoundaryRebaseRole)
  rightCrossingCoordinate : Fin 2 → Fin predecessorCount.val

noncomputable instance :
    DecidableEq SourceLocalLayerSerialCellRebaseBoundedExpandedReceipt :=
  Classical.decEq _

private def sourceLocalLayerSerialCellRebaseBoundedExpandedReceiptEquiv :
    SourceLocalLayerSerialCellRebaseBoundedExpandedReceipt ≃
      Σ predecessorCount : Fin 22,
        (TrackedColorPair → BoundedInterfaceExteriorCode
          (Fin predecessorCount.val ⊕
            SourceLocalLayerBoundaryRebaseRole)) ×
        (Fin 2 → Fin predecessorCount.val) where
  toFun receipt :=
    ⟨receipt.predecessorCount,
      receipt.code, receipt.rightCrossingCoordinate⟩
  invFun receipt := {
    predecessorCount := receipt.1
    code := receipt.2.1
    rightCrossingCoordinate := receipt.2.2 }
  left_inv receipt := by cases receipt; rfl
  right_inv receipt := by cases receipt; rfl

noncomputable instance :
    Fintype SourceLocalLayerSerialCellRebaseBoundedExpandedReceipt := by
  letI (predecessorCount : Fin 22) :
      Fintype ((TrackedColorPair → BoundedInterfaceExteriorCode
          (Fin predecessorCount.val ⊕
            SourceLocalLayerBoundaryRebaseRole)) ×
        (Fin 2 → Fin predecessorCount.val)) :=
    Fintype.ofFinite _
  exact Fintype.ofEquiv _
    sourceLocalLayerSerialCellRebaseBoundedExpandedReceiptEquiv.symm

/-- Executable alias-sensitive survival predicate for deleting every semantic
role occurrence.  The equality row, not coordinate-name equality, decides
whether an old coordinate aliases a removed role. -/
def expandedReceiptRoleSurvives
    {Old : Type*} [Fintype Old]
    (code : BoundedInterfaceExteriorCode
      (Old ⊕ SourceLocalLayerBoundaryRebaseRole))
    (slot : Old ⊕ SourceLocalLayerBoundaryRebaseRole) : Bool :=
  codeSurvivesPartialRetained code (fun role => some (Sum.inr role)) slot

/-- Graph-free total reachability after the four role occurrences are
deleted.  Equality remains the code's equality row, so distinct coordinate
names for one deleted ambient edge still denote one reflexive component. -/
def ExpandedReceiptRoleMaskedReachability
    {Old : Type*} [Fintype Old]
    (code : BoundedInterfaceExteriorCode
      (Old ⊕ SourceLocalLayerBoundaryRebaseRole))
    (left right : Old ⊕ SourceLocalLayerBoundaryRebaseRole) : Prop :=
  code.vertexEq left right = true ∨
    ∃ (hleft : expandedReceiptRoleSurvives code left = true)
      (hright : expandedReceiptRoleSurvives code right = true),
      Relation.ReflTransGen
        (fun first second : CodeSurvivingSlot code
            (fun role => some (Sum.inr role)) =>
          InterfaceExteriorFactoredStep code first.1 second.1)
        ⟨left, hleft⟩ ⟨right, hright⟩

/-- On a canonical graph code, the graph-free role mask is exactly the
literal alias-sensitive deletion mask.  This is the representation-invariant
bridge needed before a source-independent reachable closure can be counted. -/
theorem expandedReceiptRoleMaskedReachability_exact_iff
    {N Old : Type*} [Fintype Old]
    [DecidableEq (Old ⊕ SourceLocalLayerBoundaryRebaseRole)]
    (graph : SimpleGraph N)
    (interfaceVertex :
      Old ⊕ SourceLocalLayerBoundaryRebaseRole → N)
    (left right : Old ⊕ SourceLocalLayerBoundaryRebaseRole) :
    ExpandedReceiptRoleMaskedReachability
        (exactInterfaceExteriorCode graph interfaceVertex) left right ↔
      InterfaceExteriorTotalFactoredReachability
        (exactInterfaceExteriorCode graph interfaceVertex)
        interfaceVertex
        (partialRetainedCoordinateMask
          (fun role : SourceLocalLayerBoundaryRebaseRole =>
            some (Sum.inr role)))
        left right := by
  let retain := fun role : SourceLocalLayerBoundaryRebaseRole =>
    some (Sum.inr role : Old ⊕ SourceLocalLayerBoundaryRebaseRole)
  let coordinateEquiv := codeSurvivingExactEquiv graph interfaceVertex retain
  constructor
  · rintro (heq | ⟨hleft, hright, hclosure⟩)
    · left
      simpa [exactInterfaceExteriorCode] using heq
    · right
      let codeLeft : CodeSurvivingSlot
          (exactInterfaceExteriorCode graph interfaceVertex) retain :=
        ⟨left, hleft⟩
      let codeRight : CodeSurvivingSlot
          (exactInterfaceExteriorCode graph interfaceVertex) retain :=
        ⟨right, hright⟩
      refine ⟨
        (codeSurvivesPartialRetained_exact_iff graph interfaceVertex retain
          left).1 hleft,
        (codeSurvivesPartialRetained_exact_iff graph interfaceVertex retain
          right).1 hright, ?_⟩
      have hmapped : Relation.ReflTransGen
          (fun first second : SurvivingInterfaceSlot interfaceVertex
              (partialRetainedCoordinateMask retain) =>
            InterfaceExteriorFactoredStep
              (exactInterfaceExteriorCode graph interfaceVertex)
              first.1 second.1)
          (coordinateEquiv codeLeft) (coordinateEquiv codeRight) := by
        apply Mettapedia.GraphTheory.ReflTransGen.map_rel coordinateEquiv
        · intro first second hstep
          exact hstep
        · exact hclosure
      exact hmapped
  · rintro (heq | ⟨hleft, hright, hclosure⟩)
    · left
      simpa [exactInterfaceExteriorCode] using heq
    · right
      let codeLeft : CodeSurvivingSlot
          (exactInterfaceExteriorCode graph interfaceVertex) retain :=
        ⟨left, (codeSurvivesPartialRetained_exact_iff graph interfaceVertex
          retain left).2 hleft⟩
      let codeRight : CodeSurvivingSlot
          (exactInterfaceExteriorCode graph interfaceVertex) retain :=
        ⟨right, (codeSurvivesPartialRetained_exact_iff graph interfaceVertex
          retain right).2 hright⟩
      refine ⟨codeLeft.2, codeRight.2, ?_⟩
      have hmapped : Relation.ReflTransGen
          (fun first second : CodeSurvivingSlot
              (exactInterfaceExteriorCode graph interfaceVertex) retain =>
            InterfaceExteriorFactoredStep
              (exactInterfaceExteriorCode graph interfaceVertex)
              first.1 second.1)
          (coordinateEquiv.symm (coordinateEquiv codeLeft))
          (coordinateEquiv.symm (coordinateEquiv codeRight)) := by
        apply Mettapedia.GraphTheory.ReflTransGen.map_rel coordinateEquiv.symm
        · intro first second hstep
          change InterfaceExteriorFactoredStep
            (exactInterfaceExteriorCode graph interfaceVertex)
            first.1 second.1 at hstep
          simpa only [coordinateEquiv,
            codeSurvivingExactEquiv_symm_apply_val] using hstep
        · exact hclosure
      simpa [coordinateEquiv, codeLeft, codeRight] using hmapped

/-- Turn the graph-free role-masked relation into a simple component graph.
Loops are discarded and the relation is symmetrized; exact component
relations retain the same reflexive-transitive closure. -/
def expandedReceiptRoleMaskedComponentGraph
    {Old : Type*} [Fintype Old]
    (code : BoundedInterfaceExteriorCode
      (Old ⊕ SourceLocalLayerBoundaryRebaseRole)) :
    SimpleGraph (Old ⊕ SourceLocalLayerBoundaryRebaseRole) :=
  SimpleGraph.fromRel fun left right =>
    ExpandedReceiptRoleMaskedReachability code left right

/-- A graph-free receipt relation which exactly presents reachability in a
literal graph has the same connected components after graphification. -/
theorem expandedReceiptRoleMaskedComponentGraph_reachable_iff_of_exact
    {N Old : Type*} [Fintype Old]
    (code : BoundedInterfaceExteriorCode
      (Old ⊕ SourceLocalLayerBoundaryRebaseRole))
    (graph : SimpleGraph N)
    (interfaceVertex : Old ⊕ SourceLocalLayerBoundaryRebaseRole → N)
    (hexact : ∀ left right,
      ExpandedReceiptRoleMaskedReachability code left right ↔
        graph.Reachable (interfaceVertex left) (interfaceVertex right))
    (left right : Old ⊕ SourceLocalLayerBoundaryRebaseRole) :
    (expandedReceiptRoleMaskedComponentGraph code).Reachable left right ↔
      graph.Reachable (interfaceVertex left) (interfaceVertex right) := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro hclosure
    induction hclosure with
    | refl => exact SimpleGraph.Reachable.rfl
    | @tail middle finish _ hadj ih =>
        have hstep : graph.Reachable
            (interfaceVertex middle) (interfaceVertex finish) := by
          rcases (SimpleGraph.fromRel_adj _ middle finish).1 hadj with
            ⟨_, hforward | hbackward⟩
          · exact (hexact middle finish).1 hforward
          · exact ((hexact finish middle).1 hbackward).symm
        exact ih.trans hstep
  · intro hreachable
    by_cases heq : left = right
    · subst right
      exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.single
      apply (SimpleGraph.fromRel_adj _ left right).2
      exact ⟨heq, Or.inl ((hexact left right).2 hreachable)⟩

/-- Decode the closed expanded receipt into the finite tracked core state
consumed by the already-proved local collar recurrence. -/
noncomputable def expandedReceiptTrackedCoreState
    {Old : Type*} [Fintype Old] [DecidableEq Old]
    (code : TrackedColorPair → BoundedInterfaceExteriorCode
      (Old ⊕ SourceLocalLayerBoundaryRebaseRole))
    (rightCrossingCoordinate : Fin 2 → Old) :
    SourceLocalLayerBoundaryRebaseTrackedCoreState where
  corePortConnected := fun pair left right => by
    classical
    exact decide
      ((expandedReceiptRoleMaskedComponentGraph (code pair)).Reachable
        (Sum.inl (rightCrossingCoordinate left))
        (Sum.inl (rightCrossingCoordinate right)))
  coreResidual := fun pair =>
    exactSupportedPortResidualCode
      (expandedReceiptRoleMaskedComponentGraph (code pair))
      (fun role => Sum.inr role)
      (fun port => Sum.inl (rightCrossingCoordinate port))

/-- The decoded tracked core state presents exactly the graph-free receipt's
role components. -/
theorem expandedReceiptTrackedCoreState_connected_iff
    {Old : Type*} [Fintype Old] [DecidableEq Old]
    (code : TrackedColorPair → BoundedInterfaceExteriorCode
      (Old ⊕ SourceLocalLayerBoundaryRebaseRole))
    (rightCrossingCoordinate : Fin 2 → Old)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) :
    (expandedReceiptTrackedCoreState code rightCrossingCoordinate
      ).connected pair left right ↔
      (expandedReceiptRoleMaskedComponentGraph (code pair)).Reachable
        (Sum.inr left) (Sum.inr right) := by
  let graph := expandedReceiptRoleMaskedComponentGraph (code pair)
  let roleVertex := fun role : SourceLocalLayerBoundaryRebaseRole =>
    (Sum.inr role : Old ⊕ SourceLocalLayerBoundaryRebaseRole)
  let portVertex := fun port : Fin 2 =>
    (Sum.inl (rightCrossingCoordinate port) :
      Old ⊕ SourceLocalLayerBoundaryRebaseRole)
  let portConnected := fun first second : Fin 2 =>
    (expandedReceiptTrackedCoreState code rightCrossingCoordinate
      ).corePortConnected pair first second = true
  have hportSound : ∀ first second,
      portConnected first second →
        graph.Reachable (portVertex first) (portVertex second) := by
    intro first second hconnected
    simpa [portConnected, expandedReceiptTrackedCoreState, graph,
      portVertex] using hconnected
  have hportComplete : ∀ first second,
      portVertex first ∈ graph.support →
      portVertex second ∈ graph.support →
      graph.Reachable (portVertex first) (portVertex second) →
        portConnected first second := by
    intro first second _ _ hconnected
    simpa [portConnected, expandedReceiptTrackedCoreState, graph,
      portVertex] using hconnected
  have hexact := reachable_iff_exactSupportedPortResidualFactoredReachability
    graph roleVertex portVertex portConnected hportSound hportComplete
      left right
  exact hexact.symm

/-- Decoder of the closed bounded package. -/
noncomputable def
    SourceLocalLayerSerialCellRebaseBoundedExpandedReceipt.coreState
    (receipt : SourceLocalLayerSerialCellRebaseBoundedExpandedReceipt) :
    SourceLocalLayerBoundaryRebaseTrackedCoreState :=
  expandedReceiptTrackedCoreState receipt.code receipt.rightCrossingCoordinate

noncomputable instance (current : Finset G.edgeSet) :
    DecidableEq (SourceLocalLayerSerialCellRebaseExpandedReceipt current) :=
  Classical.decEq _

noncomputable instance (current : Finset G.edgeSet) :
    Fintype (SourceLocalLayerSerialCellRebaseExpandedReceipt current) :=
  Fintype.ofFinite _

/-- The expanded predecessor interface has at most the twenty-one old
coordinates plus four role occurrences.  Aliases do not increase this bound. -/
theorem sourceLocalLayerSerialCellRebaseExpandedInterface_card_le_twentyFive
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
    (offset : Fin (blockLength - 3)) :
    Fintype.card (SourceLocalLayerSerialCellRebaseExpandedInterface
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset)) ≤ 25 := by
  have hcurrent :=
    sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      graphData minimal caps coloring web corridor hunique offset
  simp only [SourceLocalLayerSerialCellRebaseExpandedInterface,
    Fintype.card_sum, Fintype.card_fin]
  change
    (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
      web corridor hunique offset).card + 4 ≤ 25
  omega

/-- Extract the canonical expanded receipt from the literal cumulative graph
immediately before the rebase, for an arbitrary compatible colour function. -/
noncomputable def sourceLocalLayerSerialCellRebaseExpandedReceiptForColorAt
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
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    SourceLocalLayerSerialCellRebaseExpandedReceipt
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset) :=
  let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
    caps coloring web corridor hunique offset
  let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
    hnext
  let expandedVertex := expandedInterfaceEdgeAt current roleAt
  fun pair =>
    exactInterfaceExteriorCode
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2)
      expandedVertex

/-- Package the literal expanded receipt in the closed, source-independent
bounded carrier.  No ambient edge name occurs in the resulting type. -/
noncomputable def
    sourceLocalLayerSerialCellRebaseBoundedExpandedReceiptForColorAt
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    SourceLocalLayerSerialCellRebaseBoundedExpandedReceipt := by
  let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
    caps coloring web corridor hunique offset
  have hcurrent : current.card < 22 :=
    Nat.lt_succ_of_le
      (sourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
        graphData minimal caps coloring web corridor hunique offset)
  exact {
    predecessorCount := ⟨current.card, hcurrent⟩
    code := sourceLocalLayerSerialCellRebaseExpandedReceiptForColorAt graphData
      caps coloring web corridor hunique offset hnext color
    rightCrossingCoordinate :=
      sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
        coloring web corridor hunique offset }

@[simp]
theorem sourceLocalLayerSerialCellRebaseBoundedExpandedReceiptForColorAt_count
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
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    (sourceLocalLayerSerialCellRebaseBoundedExpandedReceiptForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext color
      ).predecessorCount.val =
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset).card := by
  rfl

/-- Every row of the canonical receipt is the exact primitive interface step
of the literal pre-rebase tracked graph.  No role-coverage or role-inactivity
premise is needed. -/
theorem sourceLocalLayerSerialCellRebaseExpandedReceiptForColorAt_step_iff
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
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerSerialCellRebaseExpandedInterface
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset)) :
    InterfaceExteriorFactoredStep
        (sourceLocalLayerSerialCellRebaseExpandedReceiptForColorAt graphData
          caps coloring web corridor hunique offset hnext color pair)
        left right ↔
      let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
        caps coloring web corridor hunique offset
      let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
        hnext
      let graph := regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
      InterfaceExteriorStep graph (expandedInterfaceEdgeAt current roleAt)
        left right := by
  dsimp [sourceLocalLayerSerialCellRebaseExpandedReceiptForColorAt]
  exact exactInterfaceExteriorCode_step_iff _ _ left right

/-- Selecting the four right-summand role occurrences by the generic partial
mask is definitionally the source's expanded role mask. -/
theorem partialRetainedCoordinateMask_inr_eq_roleSummandMask
    {Old : Type*} [Fintype Old] [DecidableEq (Old ⊕
      SourceLocalLayerBoundaryRebaseRole)] :
    partialRetainedCoordinateMask
        (fun role : SourceLocalLayerBoundaryRebaseRole =>
          some (Sum.inr role : Old ⊕ SourceLocalLayerBoundaryRebaseRole)) =
      (fun slot => match slot with
        | Sum.inl _ => false
        | Sum.inr _ => true) := by
  funext slot
  cases slot with
  | inl old =>
      simp [partialRetainedCoordinateMask]
  | inr role =>
      simp [partialRetainedCoordinateMask]

/-- The closed graph-free receipt computes the literal unchanged core for
every pair of predecessor-or-role occurrences.  This is the source adequacy
and representation-invariance theorem for the tracked lookahead itself; no
fresh-role premise remains. -/
theorem
    sourceLocalLayerSerialCellRebaseExpandedReceiptForColorAt_roleMasked_iff_core
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
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerSerialCellRebaseExpandedInterface
      (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps coloring
        web corridor hunique offset)) :
    ExpandedReceiptRoleMaskedReachability
        (sourceLocalLayerSerialCellRebaseExpandedReceiptForColorAt graphData
          caps coloring web corridor hunique offset hnext color pair)
        left right ↔
      (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).Reachable
        (expandedInterfaceEdgeAt
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset)
          (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
          left)
        (expandedInterfaceEdgeAt
          (sourceLocalLayerSerialTrackedTransitionCarrierAt graphData caps
            coloring web corridor hunique offset)
          (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
          right) := by
  let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
    caps coloring web corridor hunique offset
  let graph := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    color (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2
  let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
    hnext
  let edgeAt := expandedInterfaceEdgeAt current roleAt
  change ExpandedReceiptRoleMaskedReachability
      (exactInterfaceExteriorCode graph edgeAt) left right ↔
    (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
      ).Reachable (edgeAt left) (edgeAt right)
  rw [expandedReceiptRoleMaskedReachability_exact_iff graph edgeAt left right]
  rw [show partialRetainedCoordinateMask
        (fun role : SourceLocalLayerBoundaryRebaseRole =>
          some (Sum.inr role :
            SourceLocalLayerSerialCellRebaseExpandedInterface current)) =
      expandedInterfaceRoleMask current by
        funext slot
        cases slot with
        | inl old =>
            simp [partialRetainedCoordinateMask,
              expandedInterfaceRoleMask]
        | inr role =>
            simp [partialRetainedCoordinateMask,
              expandedInterfaceRoleMask]]
  rw [exactInterfaceExteriorCode_totalFactoredReachability_iff]
  rw [restrictedPreRebaseTrackedGraph_expandedRoleMask_eq_core graphData caps
    coloring web corridor hunique offset hnext color pair]

/-- Decoding the canonical closed receipt gives the exact literal tracked
core relation on the four successor roles. -/
theorem
    sourceLocalLayerSerialCellRebaseExpandedReceiptTrackedCoreStateForColorAt_connected_iff
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
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) :
    (expandedReceiptTrackedCoreState
      (sourceLocalLayerSerialCellRebaseExpandedReceiptForColorAt graphData caps
        coloring web corridor hunique offset hnext color)
      (sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
        coloring web corridor hunique offset)).connected pair left right ↔
      (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).Reachable
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
          right) := by
  let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
    caps coloring web corridor hunique offset
  let code := sourceLocalLayerSerialCellRebaseExpandedReceiptForColorAt
    graphData caps coloring web corridor hunique offset hnext color
  let coordinate :=
    sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
      coloring web corridor hunique offset
  let graph := coreTrackedGraphForColorAt corridor hunique offset hnext color pair
  let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
    hnext
  let edgeAt := expandedInterfaceEdgeAt current roleAt
  rw [show expandedReceiptTrackedCoreState code coordinate =
      expandedReceiptTrackedCoreState code coordinate by rfl]
  rw [expandedReceiptTrackedCoreState_connected_iff code coordinate pair left
    right]
  rw [expandedReceiptRoleMaskedComponentGraph_reachable_iff_of_exact
    (code pair) graph edgeAt]
  · rfl
  · intro first second
    exact
      sourceLocalLayerSerialCellRebaseExpandedReceiptForColorAt_roleMasked_iff_core
        graphData caps coloring web corridor hunique offset hnext color pair
          first second

/-- The source-independent bounded package has the same exact core decoder.
This is the finite value which can be enumerated by the later reachable-state
closure. -/
theorem
    sourceLocalLayerSerialCellRebaseBoundedExpandedReceiptForColorAt_coreState_connected_iff
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
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) :
    (sourceLocalLayerSerialCellRebaseBoundedExpandedReceiptForColorAt
      graphData minimal caps coloring web corridor hunique offset hnext color
      ).coreState.connected pair left right ↔
      (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).Reachable
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
          right) := by
  exact
    sourceLocalLayerSerialCellRebaseExpandedReceiptTrackedCoreStateForColorAt_connected_iff
      graphData caps coloring web corridor hunique offset hnext color pair left
        right

/-- Decode the finite expanded predecessor receipt through the four-role mask
into the tracked core state already consumed by the local successor
recurrence. -/
noncomputable def
    sourceLocalLayerSerialCellRebaseExpandedReceiptCoreStateForColorAt
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
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    SourceLocalLayerBoundaryRebaseTrackedCoreState :=
  let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
    caps coloring web corridor hunique offset
  let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
    hnext
  trackedCoreStateOfExpandedInterfaceCode current roleAt
    (sourceLocalLayerSerialCellRebaseExpandedReceiptForColorAt graphData caps
      coloring web corridor hunique offset hnext color)
    (sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
      coloring web corridor hunique offset)

/-- The decoded receipt is exactly the unchanged tracked core on all four
semantic roles, for an arbitrary compatible colour function.  This is the
unconditional replacement for the earlier partial expansion theorem with its
`fresh role is inactive` premise. -/
theorem
    sourceLocalLayerSerialCellRebaseExpandedReceiptCoreStateForColorAt_connected_iff
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
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) :
    (sourceLocalLayerSerialCellRebaseExpandedReceiptCoreStateForColorAt
      graphData caps coloring web corridor hunique offset hnext color
      ).connected pair left right ↔
      (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).Reachable
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
          right) := by
  let current := sourceLocalLayerSerialTrackedTransitionCarrierAt graphData
    caps coloring web corridor hunique offset
  let graph := regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    color (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2
  let roleAt := sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset
    hnext
  let edgeAt := expandedInterfaceEdgeAt current roleAt
  let code := sourceLocalLayerSerialCellRebaseExpandedReceiptForColorAt
    graphData caps coloring web corridor hunique offset hnext color
  let portCoordinate :=
    sourceLocalLayerSerialTrackedRightCrossingCoordinateAt graphData caps
      coloring web corridor hunique offset
  rw [show
      sourceLocalLayerSerialCellRebaseExpandedReceiptCoreStateForColorAt
          graphData caps coloring web corridor hunique offset hnext color =
        trackedCoreStateOfExpandedInterfaceCode current roleAt code
          portCoordinate by rfl]
  rw [trackedCoreStateOfExpandedInterfaceCode_connected_iff current roleAt code
    portCoordinate pair left right]
  rw [show code pair = exactInterfaceExteriorCode graph edgeAt by rfl]
  rw [exactInterfaceExteriorCode_totalFactoredComponentGraph_reachable_iff]
  rw [restrictedPreRebaseTrackedGraph_expandedRoleMask_eq_core graphData caps
    coloring web corridor hunique offset hnext color pair]
  rfl

end

end GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedReceipt

end Mettapedia.GraphTheory.FourColor
