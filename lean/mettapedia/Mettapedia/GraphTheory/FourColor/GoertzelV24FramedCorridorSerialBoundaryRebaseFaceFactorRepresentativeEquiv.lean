import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceOldFactorFragment

/-!
# Finite representatives are the literal predecessor face factors

For one successor face fragment, the finite rebase decoder selects one
canonical coordinate from every present predecessor component which reaches
that successor.  This file proves that those coordinates are in exact
bijection with the literal old-prefix factor fragments of the successor.

The proof includes singleton factors through the explicit `oldPresent` bit;
adjacency support alone would lose precisely those components.  This is the
adequacy bridge needed to transport the finite predecessor cap sum to the
manuscript's literal regional face slice.  It does not yet combine that old
contribution with the newly displayed Cell contribution.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceSliceFragments
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceFactorRepresentativeEquivEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Two present finite coordinates decode to the same literal old-prefix face
fragment exactly when the finite predecessor-component bit relates them. -/
theorem sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt_eq_iff
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
    (left right : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root
          ).localCode.vertexCount.val)
    (hleft :
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext root).oldPresent left =
          true)
    (hright :
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext root).oldPresent right =
          true) :
    sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt realization hcubic
        hrotation htwoSided hunique offset hnext root left hleft =
      sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt realization hcubic
        hrotation htwoSided hunique offset hnext root right hright ↔
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldComponent left right =
          true := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let region := (sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset).regionEdges
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  change Fin carrier.card at left right
  let leftPosition :=
    sourceCorridorSerialBoundaryRebaseOldFactorPositionAt realization hcubic
      hrotation htwoSided hunique offset hnext root left hleft
  let rightPosition :=
    sourceCorridorSerialBoundaryRebaseOldFactorPositionAt realization hcubic
      hrotation htwoSided hunique offset hnext root right hright
  have hcomponent :
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldComponent left right =
          true ↔
        (faceRegionalAmbientPositionGraph RS root region).Reachable
          leftPosition.1 rightPosition.1 := by
    simpa [RS, region, carrier, leftPosition, rightPosition] using
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt_oldComponent_eq_true_iff
        realization hcubic hrotation htwoSided hunique offset hnext root left
          right)
  change
    (faceRegionalPositionGraph RS root region).connectedComponentMk
        leftPosition =
      (faceRegionalPositionGraph RS root region).connectedComponentMk
        rightPosition ↔ _
  constructor
  · intro heq
    apply hcomponent.2
    apply (faceRegionalPositionGraph_reachable_iff_ambient RS root region
      leftPosition rightPosition).1
    exact SimpleGraph.ConnectedComponent.exact heq
  · intro hsame
    apply SimpleGraph.ConnectedComponent.sound
    apply (faceRegionalPositionGraph_reachable_iff_ambient RS root region
      leftPosition rightPosition).2
    exact hcomponent.1 hsame

/-- Every literal predecessor factor of a chosen successor fragment is named
by one of the finite decoder's contributing canonical representatives. -/
theorem exists_contributingOldComponentRepresentative_for_factorFragment
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
    (successorFragment :
      SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt realization hcubic
        hrotation htwoSided hunique offset hnext)
    (factorFragment : FaceRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
            ).fragmentFace successorFragment))
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges)
    (hfactor : factorFragment ∈ faceRegionalFactorFragments
      embedded.cellulation.rotation.toRotationSystem
      (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
            ).fragmentFace successorFragment))
      (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext))
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges
      (sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
        hcubic hrotation htwoSided hunique offset hnext
          successorFragment).2.1) :
    let RS := embedded.cellulation.rotation.toRotationSystem
    let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
      htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
    let root := orbitFaceRoot RS (data.fragmentFace successorFragment)
    let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
      realization hcubic hrotation htwoSided hunique offset hnext root
    let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
    let semantic :=
      sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
        realization hcubic hrotation htwoSided hunique offset hnext root
    let output : Fin code.localCode.vertexCount.val := carrierCoordinate carrier
      (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
        hcubic hrotation htwoSided hunique offset hnext successorFragment)
    ∃ representative,
      representative ∈
          code.contributingOldComponentRepresentatives semantic output ∧
        ∃ hpresent : code.oldPresent representative = true,
          sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt realization
            hcubic hrotation htwoSided hunique offset hnext root representative
              hpresent = factorFragment := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace successorFragment)
  let oldRegion := (sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset).regionEdges
  let nextRegion := sourceCorridorSerialCutRegionAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let boundaryFragment :=
    sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
      hcubic hrotation htwoSided hunique offset hnext successorFragment
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  let semantic :=
    sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
      realization hcubic hrotation htwoSided hunique offset hnext root
  let outputPosition :=
    sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization hcubic
      hrotation htwoSided hunique offset hnext successorFragment
  let output : Fin code.localCode.vertexCount.val :=
    carrierCoordinate carrier outputPosition
  rcases (mem_faceRegionalFactorFragments_iff RS root nextRegion oldRegion
    boundaryFragment.2.1 factorFragment).1 hfactor with
    ⟨position, hpositionFactor, hpositionNext⟩
  rcases (mem_faceRegionalFragmentPositions_iff RS root oldRegion
    factorFragment position).1 hpositionFactor with
    ⟨positionOld, hpositionOldSupp, hpositionOldValue⟩
  have hpositionOld : faceCycleEdge RS root position ∈ oldRegion := by
    have hmem := positionOld.2
    rw [mem_faceRegionalPositions_iff] at hmem
    simpa [hpositionOldValue] using hmem
  have houtputNext : outputPosition.1 ∈
      faceRegionalFragmentPositions RS root nextRegion boundaryFragment.2.1 :=
    boundaryRegionalFragmentCutPosition_mem RS
      (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
        htwoSided hunique offset hnext)
      nextRegion boundaryFragment
  rcases (mem_faceRegionalFragmentPositions_iff RS root nextRegion
    boundaryFragment.2.1 outputPosition.1).1 houtputNext with
    ⟨outputRegional, houtputSupp, houtputValue⟩
  rcases (mem_faceRegionalFragmentPositions_iff RS root nextRegion
    boundaryFragment.2.1 position).1 hpositionNext with
    ⟨positionNext, hpositionNextSupp, hpositionNextValue⟩
  have houtputPosition :
      (faceRegionalAmbientPositionGraph RS root nextRegion).Reachable
        outputPosition.1 position := by
    have hregional := faceRegionalFragment_reachable RS root nextRegion
      boundaryFragment.2.1 houtputSupp hpositionNextSupp
    have hambient :=
      (faceRegionalPositionGraph_reachable_iff_ambient RS root nextRegion
        outputRegional positionNext).1 hregional
    simpa [houtputValue, hpositionNextValue] using hambient
  rcases exists_sourceCorridorSerialBoundaryRebaseOldFactorAnchor realization
      hcubic hrotation htwoSided hunique offset hnext root outputPosition
      position hpositionOld houtputPosition with
    ⟨anchor, hanchorPosition, hclosure⟩
  let coordinate := carrierCoordinate carrier anchor
  have hanchorOld : faceCycleEdge RS root anchor.1 ∈ oldRegion := by
    by_cases heq : anchor.1 = position
    · simpa [heq] using hpositionOld
    · have hsupport := SimpleGraph.mem_support_of_reachable heq hanchorPosition
      rw [SimpleGraph.mem_support] at hsupport
      rcases hsupport with ⟨neighbor, hadjacent⟩
      exact hadjacent.2.1
  have hpresent : code.oldPresent coordinate = true := by
    apply (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_oldPresent_iff
      realization hcubic hrotation htwoSided hunique offset hnext root
        coordinate).2
    simpa [code, coordinate, carrier] using hanchorOld
  let representative := code.oldComponentRepresentative semantic coordinate
  have hrepresentative : representative ∈
      code.contributingOldComponentRepresentatives semantic output := by
    apply code.oldComponentRepresentative_mem_contributing_of_present_of_reachable
      semantic output coordinate hpresent
    change Relation.ReflTransGen
      (boundedSerialBoundaryRebaseFaceComponentStep
        (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
          hrotation htwoSided hunique offset hnext root)) output coordinate
    simpa [output, coordinate, carrier] using hclosure
  have hrepresentativePresent : code.oldPresent representative = true :=
    (code.mem_oldComponentRepresentatives_iff semantic representative).1
      ((code.mem_contributingOldComponentRepresentatives_iff semantic output
        representative).1 hrepresentative).1 |>.1
  have hcoordinateFragment :
      sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt realization hcubic
          hrotation htwoSided hunique offset hnext root coordinate hpresent =
        factorFragment := by
    let anchorOld : FaceRegionalPosition RS root oldRegion :=
      sourceCorridorSerialBoundaryRebaseOldFactorPositionAt realization hcubic
        hrotation htwoSided hunique offset hnext root coordinate hpresent
    have hregional : (faceRegionalPositionGraph RS root oldRegion).Reachable
        anchorOld positionOld := by
      apply (faceRegionalPositionGraph_reachable_iff_ambient RS root oldRegion
        anchorOld positionOld).2
      simpa [anchorOld, coordinate, carrier, hpositionOldValue] using
        hanchorPosition
    change (faceRegionalPositionGraph RS root oldRegion).connectedComponentMk
        anchorOld = factorFragment
    exact (SimpleGraph.ConnectedComponent.sound hregional).trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff factorFragment
        positionOld).1 hpositionOldSupp)
  have hrepresentativeCoordinate : code.oldComponent representative coordinate =
      true := by
    exact semantic.oldComponent_symm
      ((code.mem_oldComponentPartition_part_iff semantic coordinate
        representative).1
          (code.oldComponentRepresentative_mem_part semantic coordinate))
  refine ⟨representative, hrepresentative, hrepresentativePresent, ?_⟩
  exact
    (sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt_eq_iff realization
      hcubic hrotation htwoSided hunique offset hnext root representative
      coordinate hrepresentativePresent hpresent).2 hrepresentativeCoordinate
      |>.trans hcoordinateFragment

/-- Distinct contributing canonical representatives decode to distinct
literal predecessor factors. -/
theorem sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt_injective_on_contributing
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
    (successorFragment :
      SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt realization hcubic
        hrotation htwoSided hunique offset hnext)
    (left right : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext
          (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
            ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
              htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
                ).fragmentFace successorFragment))).localCode.vertexCount.val)
    (hleft : left ∈
      let root := orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
            ).fragmentFace successorFragment)
      let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext root
      let semantic :=
        sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
          realization hcubic hrotation htwoSided hunique offset hnext root
      let output : Fin code.localCode.vertexCount.val := carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
          hcubic hrotation htwoSided hunique offset hnext root)
        (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
          hcubic hrotation htwoSided hunique offset hnext successorFragment)
      code.contributingOldComponentRepresentatives semantic output)
    (hright : right ∈
      let root := orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
            ).fragmentFace successorFragment)
      let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext root
      let semantic :=
        sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
          realization hcubic hrotation htwoSided hunique offset hnext root
      let output : Fin code.localCode.vertexCount.val := carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
          hcubic hrotation htwoSided hunique offset hnext root)
        (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
          hcubic hrotation htwoSided hunique offset hnext successorFragment)
      code.contributingOldComponentRepresentatives semantic output)
    (hfragments :
      let root := orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
            ).fragmentFace successorFragment)
      let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext root
      let leftPresent : code.oldPresent left = true :=
        (code.mem_oldComponentRepresentatives_iff
          (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
            realization hcubic hrotation htwoSided hunique offset hnext root)
          left).1
          ((code.mem_contributingOldComponentRepresentatives_iff
            (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
              realization hcubic hrotation htwoSided hunique offset hnext root)
            _ left).1 hleft).1 |>.1
      let rightPresent : code.oldPresent right = true :=
        (code.mem_oldComponentRepresentatives_iff
          (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
            realization hcubic hrotation htwoSided hunique offset hnext root)
          right).1
          ((code.mem_contributingOldComponentRepresentatives_iff
            (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
              realization hcubic hrotation htwoSided hunique offset hnext root)
            _ right).1 hright).1 |>.1
      sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt realization hcubic
          hrotation htwoSided hunique offset hnext root left leftPresent =
        sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt realization hcubic
          hrotation htwoSided hunique offset hnext root right rightPresent) :
    left = right := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace successorFragment)
  let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  let semantic :=
    sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
      realization hcubic hrotation htwoSided hunique offset hnext root
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let output : Fin code.localCode.vertexCount.val := carrierCoordinate carrier
    (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization hcubic
      hrotation htwoSided hunique offset hnext successorFragment)
  have hleftRepresentative : left ∈ code.oldComponentRepresentatives semantic :=
    ((code.mem_contributingOldComponentRepresentatives_iff semantic output
      left).1 hleft).1
  have hrightRepresentative : right ∈ code.oldComponentRepresentatives semantic :=
    ((code.mem_contributingOldComponentRepresentatives_iff semantic output
      right).1 hright).1
  have hleftPresent : code.oldPresent left = true :=
    (code.mem_oldComponentRepresentatives_iff semantic left).1
      hleftRepresentative |>.1
  have hrightPresent : code.oldPresent right = true :=
    (code.mem_oldComponentRepresentatives_iff semantic right).1
      hrightRepresentative |>.1
  have hsame : code.oldComponent left right = true := by
    apply (sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt_eq_iff
      realization hcubic hrotation htwoSided hunique offset hnext root left
        right hleftPresent hrightPresent).1
    simpa [RS, data, root, code, semantic, carrier, output, hleftPresent,
      hrightPresent] using hfragments
  have hcanonical := code.eq_oldComponentRepresentative_of_mem_of_same semantic
    hleftRepresentative hsame
  exact hcanonical.trans
    ((code.mem_oldComponentRepresentatives_iff semantic right).1
      hrightRepresentative |>.2)

/-- The finite type of canonical predecessor-component representatives which
contribute to one chosen successor face fragment. -/
abbrev SourceCorridorSerialBoundaryRebaseContributingOldRepresentativeAt
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
    (successorFragment :
      SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt realization hcubic
        hrotation htwoSided hunique offset hnext) :=
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace successorFragment)
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  let semantic :=
    sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
      realization hcubic hrotation htwoSided hunique offset hnext root
  let output : Fin code.localCode.vertexCount.val := carrierCoordinate carrier
    (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization hcubic
      hrotation htwoSided hunique offset hnext successorFragment)
  { representative // representative ∈
      code.contributingOldComponentRepresentatives semantic output }

/-- The finite type of literal old-prefix factors contained in one chosen
successor face fragment. -/
abbrev SourceCorridorSerialBoundaryRebaseOldFactorAt
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
    (successorFragment :
      SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt realization hcubic
        hrotation htwoSided hunique offset hnext) :=
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace successorFragment)
  let oldRegion := (sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset).regionEdges
  let nextRegion := sourceCorridorSerialCutRegionAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let boundaryFragment :=
    sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization hcubic
      hrotation htwoSided hunique offset hnext successorFragment
  { factorFragment // factorFragment ∈
      faceRegionalFactorFragments RS root nextRegion oldRegion
        boundaryFragment.2.1 }

/-- Decode a contributing canonical finite coordinate to its literal
old-prefix factor fragment. -/
noncomputable def sourceCorridorSerialBoundaryRebaseRepresentativeToOldFactor
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
    (successorFragment :
      SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt realization hcubic
        hrotation htwoSided hunique offset hnext) :
    SourceCorridorSerialBoundaryRebaseContributingOldRepresentativeAt
        realization hcubic hrotation htwoSided hunique offset hnext
          successorFragment →
      SourceCorridorSerialBoundaryRebaseOldFactorAt realization hcubic hrotation
        htwoSided hunique offset hnext successorFragment := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace successorFragment)
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  let semantic :=
    sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
      realization hcubic hrotation htwoSided hunique offset hnext root
  let outputPosition :=
    sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization hcubic
      hrotation htwoSided hunique offset hnext successorFragment
  let output : Fin code.localCode.vertexCount.val :=
    carrierCoordinate carrier outputPosition
  intro representative
  have hrepresentative : representative.1 ∈
      code.contributingOldComponentRepresentatives semantic output :=
    representative.2
  have hpresent : code.oldPresent representative.1 = true :=
    (code.mem_oldComponentRepresentatives_iff semantic representative.1).1
      ((code.mem_contributingOldComponentRepresentatives_iff semantic output
        representative.1).1 hrepresentative).1 |>.1
  have hclosure :=
    ((code.mem_contributingOldComponentRepresentatives_iff semantic output
      representative.1).1 hrepresentative).2
  refine ⟨sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt realization
    hcubic hrotation htwoSided hunique offset hnext root representative.1
      hpresent, ?_⟩
  exact sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt_mem_factors
    realization hcubic hrotation htwoSided hunique offset hnext
      successorFragment representative.1 hpresent hclosure

/-- The representative decoder is bijective: it neither loses literal old
factors nor counts one old component twice. -/
theorem sourceCorridorSerialBoundaryRebaseRepresentativeToOldFactor_bijective
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
    (successorFragment :
      SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt realization hcubic
        hrotation htwoSided hunique offset hnext) :
    Function.Bijective
      (sourceCorridorSerialBoundaryRebaseRepresentativeToOldFactor realization
        hcubic hrotation htwoSided hunique offset hnext successorFragment) := by
  classical
  constructor
  · intro left right heq
    apply Subtype.ext
    apply sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt_injective_on_contributing
      realization hcubic hrotation htwoSided hunique offset hnext
        successorFragment left.1 right.1 left.2 right.2
    exact congrArg Subtype.val heq
  · intro factorFragment
    rcases exists_contributingOldComponentRepresentative_for_factorFragment
        realization hcubic hrotation htwoSided hunique offset hnext
          successorFragment factorFragment.1 factorFragment.2 with
      ⟨representative, hrepresentative, hpresent, hfragment⟩
    refine ⟨⟨representative, hrepresentative⟩, ?_⟩
    apply Subtype.ext
    change sourceCorridorSerialBoundaryRebaseOldFactorFragmentAt realization
        hcubic hrotation htwoSided hunique offset hnext _ representative _ =
      factorFragment.1
    simpa using hfragment

/-- Exact equivalence between the graph-free finite representatives and the
literal predecessor factor fragments seen by one successor face. -/
noncomputable def sourceCorridorSerialBoundaryRebaseOldFactorEquiv
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
    (successorFragment :
      SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt realization hcubic
        hrotation htwoSided hunique offset hnext) :
    SourceCorridorSerialBoundaryRebaseContributingOldRepresentativeAt
        realization hcubic hrotation htwoSided hunique offset hnext
          successorFragment ≃
      SourceCorridorSerialBoundaryRebaseOldFactorAt realization hcubic hrotation
        htwoSided hunique offset hnext successorFragment :=
  Equiv.ofBijective
    (sourceCorridorSerialBoundaryRebaseRepresentativeToOldFactor realization
      hcubic hrotation htwoSided hunique offset hnext successorFragment)
    (sourceCorridorSerialBoundaryRebaseRepresentativeToOldFactor_bijective
      realization hcubic hrotation htwoSided hunique offset hnext
        successorFragment)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
