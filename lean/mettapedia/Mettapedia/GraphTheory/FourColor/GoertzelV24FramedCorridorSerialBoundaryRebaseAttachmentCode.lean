import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseTrackedAttachment

/-!
# Finite attachment coordinates for a literal serial rebase

The old endpoint of every tracked or occurrence-sensitive facial rebase seam
has already been localized to one of three source roles: an input crossing of
the current Cell, an output crossing of the current Cell, or an output
crossing of the immediately preceding Cell.  This file turns that geometric
classification into a finite dependent coordinate type.

The predecessor coordinate exists only when the current offset has a genuine
predecessor.  Consequently the code contains at most six positions and has no
padding position that is silently interpreted as source geometry.

This is an addressability theorem for the finite rebase decoder.  It does not
claim that a tracked or facial excursion through the accumulated prefix is
determined by these attachment coordinates; that semantic factorization
remains a separate obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileRegionalCoverage
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseAttachmentCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The exact finite source roles at which the old side of a successor rebase
may attach.  The left summand contains the current Cell's input and output
crossings.  The right summand contains the unique immediately preceding Cell
when such a Cell exists. -/
abbrev SourceCorridorSerialBoundaryRebaseOldAttachmentRole
    {blockLength : Nat} (offset : Fin (blockLength - 3)) :=
  (Fin 2 ⊕ Fin 2) ⊕
    ({historical : Fin (blockLength - 3) //
        historical.val + 1 = offset.val} × Fin 2)

/-- The ambient primal edge named by one finite old-attachment role. -/
noncomputable def sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    G.edgeSet :=
  match role with
  | .inl (.inl step) =>
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).localLayerPrefixCrossing step
  | .inl (.inr step) =>
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing step
  | .inr previous =>
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        previous.1.1).nextLocalLayerPrefixCrossing previous.2

/-- There are at most six exact old-attachment coordinates: two current
inputs, two current outputs, and at most two immediate-predecessor outputs. -/
theorem sourceCorridorSerialBoundaryRebaseOldAttachmentRole_card_le_six
    {blockLength : Nat} (offset : Fin (blockLength - 3)) :
    Fintype.card
        (SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) ≤ 6 := by
  have hsub : Subsingleton
      {historical : Fin (blockLength - 3) //
        historical.val + 1 = offset.val} := by
    constructor
    intro first second
    apply Subtype.ext
    omega
  have hcard : Fintype.card
      {historical : Fin (blockLength - 3) //
        historical.val + 1 = offset.val} ≤ 1 :=
    Fintype.card_le_one_iff.mpr (fun first second => hsub.elim first second)
  simp only [SourceCorridorSerialBoundaryRebaseOldAttachmentRole,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

/-- Every tracked rebase seam adjacency has an old endpoint named by one of
the at-most-six finite source coordinates. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSeamAt_adj_has_oldAttachmentRole
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (first second : Color) {x y : G.edgeSet}
    (hadj : (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization
      hcubic hrotation htwoSided hunique offset hnext color first second).Adj
        x y) :
    ∃ old new : G.edgeSet,
      ∃ role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset,
      (embedded.cellulation.rotation.toRotationSystem.trackedEdgeGraph
        color first second).Adj old new ∧
      old ∈ (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges ∧
      new ∈ sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
        hrotation htwoSided hunique offset hnext ∧
      new ∉ (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges ∧
      old = sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
        hcubic hrotation htwoSided hunique offset role := by
  rcases
      sourceCorridorSerialBoundaryRebaseTrackedSeamAt_adj_has_local_old_attachment
        realization hcubic hrotation htwoSided hunique offset hnext color first
          second hadj with
    ⟨old, new, hadjAmbient, hold, hnew, hnewOld,
      hinput | hcurrentOutput | hprevious⟩
  · rcases hinput with ⟨step, holdEq⟩
    refine ⟨old, new, .inl (.inl step), hadjAmbient, hold, hnew, hnewOld, ?_⟩
    simpa [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt] using holdEq
  · rcases hcurrentOutput with ⟨step, holdEq⟩
    refine ⟨old, new, .inl (.inr step), hadjAmbient, hold, hnew, hnewOld, ?_⟩
    simpa [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt] using holdEq
  · rcases hprevious with ⟨historical, step, hhistorical, holdEq⟩
    let previous : {historical : Fin (blockLength - 3) //
        historical.val + 1 = offset.val} := ⟨historical, hhistorical⟩
    refine ⟨old, new, .inr (previous, step), hadjAmbient, hold, hnew,
      hnewOld, ?_⟩
    simpa [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt, previous]
      using holdEq

/-- Endpoint-oriented finite localization of a tracked rebase seam.  One
literal endpoint is an old attachment role and the other is one of the two
newly displayed rebase edges. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSeamAt_adj_oriented_roles
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (first second : Color) {x y : G.edgeSet}
    (hadj : (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization
      hcubic hrotation htwoSided hunique offset hnext color first second).Adj
        x y) :
    (∃ role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset,
        x = sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
          hcubic hrotation htwoSided hunique offset role ∧
        y ∈ sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
          hrotation htwoSided hunique offset hnext) ∨
      ∃ role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset,
        y = sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
          hcubic hrotation htwoSided hunique offset role ∧
        x ∈ sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
          hrotation htwoSided hunique offset hnext := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let newRegion := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization
    hcubic hrotation htwoSided hunique offset hnext
  have hraw := (regionalTrackedSeamGraph_adj_iff RS oldRegion newRegion
    color first second x y).1 hadj
  have holdBoundary :=
    sourceCorridorSerialBoundaryRebaseTrackedSeamAt_adj_oldEndpoint_mem_truePrefixCrossing
      realization hcubic hrotation htwoSided hunique offset hnext color first
        second hadj
  have encode {old : G.edgeSet}
      (hlocal :
        ((∃ step : Fin 2,
            old = (sourceSlabInterfaceAt realization hcubic hrotation
              htwoSided hunique offset).localLayerPrefixCrossing step) ∨
          (∃ step : Fin 2,
            old = (sourceSlabInterfaceAt realization hcubic hrotation
              htwoSided hunique offset).nextLocalLayerPrefixCrossing step) ∨
          ∃ historical : Fin (blockLength - 3), ∃ step : Fin 2,
            historical.val + 1 = offset.val ∧
            old = (sourceSlabInterfaceAt realization hcubic hrotation
              htwoSided hunique historical).nextLocalLayerPrefixCrossing step)) :
      ∃ role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset,
        old = sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
          hcubic hrotation htwoSided hunique offset role := by
    rcases hlocal with hinput | houtput | hprevious
    · rcases hinput with ⟨step, holdEq⟩
      refine ⟨.inl (.inl step), ?_⟩
      simpa [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt] using holdEq
    · rcases houtput with ⟨step, holdEq⟩
      refine ⟨.inl (.inr step), ?_⟩
      simpa [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt] using holdEq
    · rcases hprevious with ⟨historical, step, hhistorical, holdEq⟩
      let previous : {historical : Fin (blockLength - 3) //
          historical.val + 1 = offset.val} := ⟨historical, hhistorical⟩
      refine ⟨.inr (previous, step), ?_⟩
      simpa [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt, previous]
        using holdEq
  rcases hraw.2 with hforward | hbackward
  · have hxBoundary : x ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1) := by
      rcases holdBoundary with hx | hy
      · exact hx.2
      · exact False.elim (hforward.2.2.2 hy.1)
    have hlocal :=
      sourceCorridorSerialBoundaryRebaseTrackedOldEndpoint_has_local_attachment
        realization hcubic hrotation htwoSided hunique offset hnext color first
          second hraw.1 hforward.2.2.1 hxBoundary
    rcases encode hlocal with ⟨role, hx⟩
    exact Or.inl ⟨role, hx, hforward.2.2.1⟩
  · have hyBoundary : y ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1) := by
      rcases holdBoundary with hx | hy
      · exact False.elim (hbackward.2.1 hx.1)
      · exact hy.2
    have hlocal :=
      sourceCorridorSerialBoundaryRebaseTrackedOldEndpoint_has_local_attachment
        realization hcubic hrotation htwoSided hunique offset hnext color first
          second hraw.1.symm hbackward.1 hyBoundary
    rcases encode hlocal with ⟨role, hy⟩
    exact Or.inr ⟨role, hy, hbackward.1⟩

/-- Every occurrence-sensitive facial rebase seam adjacency projects to an
old primal edge named by the same at-most-six source coordinates. -/
theorem sourceCorridorSerialBoundaryRebaseFaceSeamAt_adj_has_oldAttachmentRole
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    {x y : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card}
    (hadj : (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
      hrotation htwoSided hunique offset hnext root).Adj x y) :
    ∃ old new : Fin
        (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card,
      ∃ role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset,
      (faceCyclePositionGraph embedded.cellulation.rotation.toRotationSystem
        root).Adj old new ∧
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root old ∈
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges ∧
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root new ∈
        sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
          hrotation htwoSided hunique offset hnext ∧
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root new ∉
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges ∧
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root old =
        sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
          hcubic hrotation htwoSided hunique offset role := by
  rcases
      sourceCorridorSerialBoundaryRebaseFaceSeamAt_adj_has_local_old_attachment
        realization hcubic hrotation htwoSided hunique offset hnext root hadj
      with
    ⟨old, new, hadjAmbient, hold, hnew, hnewOld,
      hinput | hcurrentOutput | hprevious⟩
  · rcases hinput with ⟨step, holdEq⟩
    refine ⟨old, new, .inl (.inl step), hadjAmbient, hold, hnew, hnewOld, ?_⟩
    simpa [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt] using holdEq
  · rcases hcurrentOutput with ⟨step, holdEq⟩
    refine ⟨old, new, .inl (.inr step), hadjAmbient, hold, hnew, hnewOld, ?_⟩
    simpa [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt] using holdEq
  · rcases hprevious with ⟨historical, step, hhistorical, holdEq⟩
    let previous : {historical : Fin (blockLength - 3) //
        historical.val + 1 = offset.val} := ⟨historical, hhistorical⟩
    refine ⟨old, new, .inr (previous, step), hadjAmbient, hold, hnew,
      hnewOld, ?_⟩
    simpa [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt, previous]
      using holdEq

/-- Endpoint-oriented finite localization of an occurrence-sensitive facial
rebase seam.  After projection to primal edges, one literal endpoint is an old
attachment role and the other is one of the two newly displayed rebase edges.
Unlike the older existential statement above, this theorem retains which
endpoint has which role. -/
theorem sourceCorridorSerialBoundaryRebaseFaceSeamAt_adj_oriented_roles
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    {x y : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card}
    (hadj : (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
      hrotation htwoSided hunique offset hnext root).Adj x y) :
    (∃ role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset,
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x =
          sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
            hcubic hrotation htwoSided hunique offset role ∧
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y ∈
          sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
            hrotation htwoSided hunique offset hnext) ∨
      ∃ role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset,
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y =
          sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
            hcubic hrotation htwoSided hunique offset role ∧
        faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x ∈
          sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
            hrotation htwoSided hunique offset hnext := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let newRegion := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization
    hcubic hrotation htwoSided hunique offset hnext
  have hraw := (faceRegionalSeamGraph_adj_iff RS root oldRegion newRegion
    x y).1 hadj
  have hedgeAdj := edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
    RS hcubic hrotation root hraw.1
  have holdBoundary :=
    sourceCorridorSerialBoundaryRebaseFaceSeamAt_adj_oldEndpoint_mem_truePrefixCrossing
      realization hcubic hrotation htwoSided hunique offset hnext root hadj
  have classify {old new : G.edgeSet}
      (hadjAmbient : RS.edgeAdjacencyGraph.Adj old new)
      (hnewRegion : new ∈ newRegion)
      (holdBoundary : old ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1)) :
      ((∃ step : Fin 2,
          old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).localLayerPrefixCrossing step) ∨
        (∃ step : Fin 2,
          old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).nextLocalLayerPrefixCrossing step) ∨
        ∃ historical : Fin (blockLength - 3), ∃ step : Fin 2,
          historical.val + 1 = offset.val ∧
          old = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique historical).nextLocalLayerPrefixCrossing step) := by
    rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hnewRegion with
      ⟨newStep, hnew⟩
    rcases sourceCorridorSerialPrefixTrueCrossingEdge_eq_cell_input_or_output
        realization hcubic hrotation htwoSided hunique (offset.val + 1)
          holdBoundary with ⟨historical, hhistorical, hinput | houtput⟩
    · rcases hinput with ⟨oldStep, holdEq⟩
      have hindex :=
        sourceSlabInputCrossing_index_eq_of_lt_cut_of_adj_rebaseCrossing
          realization hcubic hrotation htwoSided hunique offset historical
            hnext hhistorical oldStep newStep (by
              simpa [RS, newRegion, holdEq, hnew] using hadjAmbient)
      have heq : historical = offset := Fin.ext hindex
      subst historical
      exact Or.inl ⟨oldStep, holdEq⟩
    · rcases houtput with ⟨oldStep, holdEq⟩
      have hindex :=
        sourceSlabOutputCrossing_index_eq_or_succ_eq_of_lt_cut_of_adj_rebaseCrossing
          realization hcubic hrotation htwoSided hunique offset historical
            hnext hhistorical oldStep newStep (by
              simpa [RS, newRegion, holdEq, hnew] using hadjAmbient)
      rcases hindex with hcurrent | hprevious
      · have heq : historical = offset := Fin.ext hcurrent
        subst historical
        exact Or.inr (Or.inl ⟨oldStep, holdEq⟩)
      · exact Or.inr (Or.inr ⟨historical, oldStep, hprevious, holdEq⟩)
  have encode {old : G.edgeSet}
      (hlocal :
        ((∃ step : Fin 2,
            old = (sourceSlabInterfaceAt realization hcubic hrotation
              htwoSided hunique offset).localLayerPrefixCrossing step) ∨
          (∃ step : Fin 2,
            old = (sourceSlabInterfaceAt realization hcubic hrotation
              htwoSided hunique offset).nextLocalLayerPrefixCrossing step) ∨
          ∃ historical : Fin (blockLength - 3), ∃ step : Fin 2,
            historical.val + 1 = offset.val ∧
            old = (sourceSlabInterfaceAt realization hcubic hrotation
              htwoSided hunique historical).nextLocalLayerPrefixCrossing step)) :
      ∃ role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset,
        old = sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
          hcubic hrotation htwoSided hunique offset role := by
    rcases hlocal with hinput | houtput | hprevious
    · rcases hinput with ⟨step, holdEq⟩
      refine ⟨.inl (.inl step), ?_⟩
      simpa [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt] using holdEq
    · rcases houtput with ⟨step, holdEq⟩
      refine ⟨.inl (.inr step), ?_⟩
      simpa [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt] using holdEq
    · rcases hprevious with ⟨historical, step, hhistorical, holdEq⟩
      let previous : {historical : Fin (blockLength - 3) //
          historical.val + 1 = offset.val} := ⟨historical, hhistorical⟩
      refine ⟨.inr (previous, step), ?_⟩
      simpa [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt, previous]
        using holdEq
  rcases hraw.2 with hforward | hbackward
  · have hxBoundary : faceCycleEdge RS root x ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1) := by
      rcases holdBoundary with hx | hy
      · exact hx.2
      · exact False.elim (hforward.2.2.2 hy.1)
    rcases encode (classify hedgeAdj hforward.2.2.1 hxBoundary) with
      ⟨role, hx⟩
    exact Or.inl ⟨role, hx, hforward.2.2.1⟩
  · have hyBoundary : faceCycleEdge RS root y ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1) := by
      rcases holdBoundary with hx | hy
      · exact False.elim (hbackward.2.1 hx.1)
      · exact hy.2
    rcases encode (classify hedgeAdj.symm hbackward.1 hyBoundary) with
      ⟨role, hy⟩
    exact Or.inr ⟨role, hy, hbackward.1⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
