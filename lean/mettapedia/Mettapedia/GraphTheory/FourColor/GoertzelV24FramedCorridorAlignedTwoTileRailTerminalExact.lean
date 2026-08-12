import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileRailTerminalSupport

/-!
# Exact rail-terminal partition of a source-aligned slab

The source-aligned two-tile slab has a literal six-edge boundary.  Its two
rail terminals do not merely lie among the rail crossings: together they are
exactly the two rail crossings.  This closes the local physical port
partition without asserting anything about a cumulative prefix frontier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileRailTerminalExactEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The two terminal coordinates select distinct positions of the literal
six-step aligned boundary. -/
theorem sourceTwoTileAlignedRailCrossingIndexAt_injective
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
    (offset : Fin (blockLength - 4)) :
    Function.Injective
      (sourceTwoTileAlignedRailCrossingIndexAt realization hcubic hrotation
        htwoSided hunique offset) := by
  let pair := sourceTwoTileRailPairAt realization hcubic hrotation htwoSided
    hunique offset
  have hrails : pair.secondRail.length + pair.firstRail.length = 2 := by
    have hsum := pair.firstRail_length_add_secondRail_length_eq_two
    omega
  let railIndex : Fin pair.secondRail.length ⊕ Fin pair.firstRail.length → Fin 6 :=
    Sum.rec
      (fun secondStep =>
        ⟨2 + secondStep.val, by
          have hstep := secondStep.isLt
          have hbound := pair.secondRail_length_le_two
          omega⟩)
      (fun firstStep =>
        ⟨2 + pair.secondRail.length + 2 + firstStep.val, by
          have hstep := firstStep.isLt
          have hsum := pair.firstRail_length_add_secondRail_length_eq_two
          omega⟩)
  have hformula (terminal : Fin 2) :
      sourceTwoTileAlignedRailCrossingIndexAt realization hcubic hrotation
          htwoSided hunique offset terminal =
        railIndex (finSumFinEquiv.symm (Fin.cast hrails.symm terminal)) := by
    rfl
  have hrailIndex : Function.Injective railIndex := by
    rintro (first | first) (second | second) heq
    · apply congrArg Sum.inl
      apply Fin.ext
      have hval := congrArg Fin.val heq
      simp only [railIndex] at hval
      omega
    · exfalso
      have hval := congrArg Fin.val heq
      simp only [railIndex] at hval
      have hfirst := first.isLt
      have hsecond := second.isLt
      omega
    · exfalso
      have hval := congrArg Fin.val heq
      simp only [railIndex] at hval
      have hfirst := first.isLt
      have hsecond := second.isLt
      omega
    · apply congrArg Sum.inr
      apply Fin.ext
      have hval := congrArg Fin.val heq
      simp only [railIndex] at hval
      omega
  intro first second heq
  apply Fin.cast_injective hrails.symm
  apply Equiv.injective finSumFinEquiv.symm
  apply hrailIndex
  rw [← hformula first, ← hformula second]
  exact heq

/-- The two terminal edges of the literal `4 + 2` profile are distinct. -/
theorem sourceTwoTileAlignedTerminalProfileDataAt_terminalEdge_injective
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
    (offset : Fin (blockLength - 4)) :
    Function.Injective
      (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).terminalEdge := by
  intro first second heq
  apply sourceTwoTileAlignedRailCrossingIndexAt_injective realization hcubic
    hrotation htwoSided hunique offset
  apply (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
    htwoSided hunique offset).orderedCrossing_injective
  simpa only [sourceTwoTileAlignedTerminalProfileDataAt_terminalEdge] using heq

/-- The terminal part of the literal `4 + 2` profile is exactly the two
primal crossings of its two exterior rails. -/
theorem sourceTwoTileAlignedTerminalProfileDataAt_terminalEdges_eq_railCrossingEdges
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
    (offset : Fin (blockLength - 4)) :
    (Finset.univ.image
      (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).terminalEdge) =
      sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation htwoSided
        hunique offset := by
  apply Finset.eq_of_subset_of_card_le
  · intro edge hedge
    rcases Finset.mem_image.1 hedge with ⟨terminal, -, rfl⟩
    exact sourceTwoTileAlignedTerminalProfileDataAt_terminalEdge_mem_railCrossingEdges
      realization hcubic hrotation htwoSided hunique offset terminal
  · calc
      (sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation htwoSided
          hunique offset).card = 2 :=
        sourceTwoTileRailCrossingEdgesAt_card_eq_two realization hcubic hrotation
          htwoSided hunique offset
      _ = (Finset.univ : Finset (Fin 2)).card := by simp
      _ = (Finset.univ.image
          (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
            htwoSided hunique offset).terminalEdge).card := by
        symm
        exact Finset.card_image_of_injective _
          (sourceTwoTileAlignedTerminalProfileDataAt_terminalEdge_injective
            realization hcubic hrotation htwoSided hunique offset)
      _ ≤ (Finset.univ.image
          (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
            htwoSided hunique offset).terminalEdge).card := le_rfl

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
