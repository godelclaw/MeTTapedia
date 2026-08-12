import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTilePortCoordinates
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileRailTerminalExact

/-!
# Exact physical port partition of an aligned two-tile slab

The aligned source slab has one literal six-edge boundary.  Its displayed
four transverse ports and two rail ports must be a partition of that actual
boundary before the slab can serve as a source-open generator.  This file
proves the coordinate part of that assertion; it does not identify a raw
prefix of Cells with a serial composite or make the rail observations
persistent across slabs.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTilePortExactEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The four transverse and two rail ports occupy distinct coordinates of
the literal six-step aligned boundary. -/
theorem sourceTwoTileAlignedTerminalPortBoundaryIndexAt_injective
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
      (sourceTwoTileAlignedTerminalPortBoundaryIndexAt realization hcubic
        hrotation htwoSided hunique offset) := by
  let pair := sourceTwoTileRailPairAt realization hcubic hrotation htwoSided
    hunique offset
  have hsum : pair.secondRail.length + pair.firstRail.length = 2 := by
    have h := pair.firstRail_length_add_secondRail_length_eq_two
    omega
  have hfirstWalk :
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).toInterface.localLayer.walk.length = 2 :=
    (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
      hunique offset).toInterface.localLayer_walk_length_eq_two
  have hsecondWalk :
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).toInterface.localLayer.walk.length = 2 :=
    (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
      hunique offset).toInterface.localLayer_walk_length_eq_two
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
          omega⟩)
  have hrailFormula (terminal : Fin 2) :
      sourceTwoTileAlignedTerminalPortBoundaryIndexAt realization hcubic
          hrotation htwoSided hunique offset (.inr terminal) =
        railIndex (finSumFinEquiv.symm (Fin.cast hsum.symm terminal)) := by
    rfl
  have hfirstFormula (step : Fin 2) :
      sourceTwoTileAlignedTerminalPortBoundaryIndexAt realization hcubic
          hrotation htwoSided hunique offset
          (.inl (finSumFinEquiv (Sum.inl step : Fin 2 ⊕ Fin 2))) =
        sourceTwoTileAlignedFirstCrossingIndex step := by
    simp [sourceTwoTileAlignedTerminalPortBoundaryIndexAt]
  have hsecondFormula (step : Fin 2) :
      sourceTwoTileAlignedTerminalPortBoundaryIndexAt realization hcubic
          hrotation htwoSided hunique offset
          (.inl (finSumFinEquiv (Sum.inr step : Fin 2 ⊕ Fin 2))) =
        sourceTwoTileAlignedSecondCrossingIndexAt realization hcubic
          hrotation htwoSided hunique offset step := by
    simp [sourceTwoTileAlignedTerminalPortBoundaryIndexAt]
  have hfirstValue (step : Fin 2) :
      (sourceTwoTileAlignedTerminalPortBoundaryIndexAt realization hcubic
          hrotation htwoSided hunique offset
          (.inl (finSumFinEquiv (Sum.inl step : Fin 2 ⊕ Fin 2)))).val =
        step.val := by
    rw [hfirstFormula]
    rfl
  have hsecondValue (step : Fin 2) :
      (sourceTwoTileAlignedTerminalPortBoundaryIndexAt realization hcubic
          hrotation htwoSided hunique offset
          (.inl (finSumFinEquiv (Sum.inr step : Fin 2 ⊕ Fin 2)))).val =
        2 + pair.secondRail.length + (2 - (step.val + 1)) := by
    rw [hsecondFormula]
    simp [sourceTwoTileAlignedSecondCrossingIndexAt, pair, hfirstWalk,
      hsecondWalk]
  have hcrossing_eq {crossing : Fin 4} {split : Fin 2 ⊕ Fin 2}
      (hsplit : finSumFinEquiv.symm crossing = split) :
      crossing = finSumFinEquiv split := by
    rw [← hsplit]
    exact ((@finSumFinEquiv 2 2).apply_symm_apply crossing).symm
  intro first second heq
  rcases first with crossingFirst | terminalFirst
  · rcases second with crossingSecond | terminalSecond
    · rcases hfirst : (finSumFinEquiv.symm crossingFirst : Fin 2 ⊕ Fin 2) with
        firstStep | firstStep
      · have hcrossingFirst : crossingFirst =
            finSumFinEquiv (Sum.inl firstStep : Fin 2 ⊕ Fin 2) := by
          exact hcrossing_eq hfirst
        rcases hsecond : (finSumFinEquiv.symm crossingSecond : Fin 2 ⊕ Fin 2) with
            secondStep | secondStep
        · have hcrossingSecond : crossingSecond =
              finSumFinEquiv (Sum.inl secondStep : Fin 2 ⊕ Fin 2) := by
            exact hcrossing_eq hsecond
          have hvalue := congrArg Fin.val heq
          rw [hcrossingFirst, hcrossingSecond, hfirstValue, hfirstValue] at hvalue
          have hsteps : firstStep = secondStep := by
            apply Fin.ext
            omega
          have hcrossing : crossingFirst = crossingSecond := calc
            crossingFirst = finSumFinEquiv (Sum.inl firstStep : Fin 2 ⊕ Fin 2) :=
              hcrossingFirst
            _ = finSumFinEquiv (Sum.inl secondStep : Fin 2 ⊕ Fin 2) := by
              exact congrArg finSumFinEquiv (congrArg Sum.inl hsteps)
            _ = crossingSecond := hcrossingSecond.symm
          exact congrArg Sum.inl hcrossing
        · have hcrossingSecond : crossingSecond =
              finSumFinEquiv (Sum.inr secondStep : Fin 2 ⊕ Fin 2) := by
            exact hcrossing_eq hsecond
          exfalso
          have hvalue := congrArg Fin.val heq
          rw [hcrossingFirst, hcrossingSecond, hfirstValue, hsecondValue] at hvalue
          have hstep := secondStep.isLt
          omega
      · have hcrossingFirst : crossingFirst =
            finSumFinEquiv (Sum.inr firstStep : Fin 2 ⊕ Fin 2) := by
          exact hcrossing_eq hfirst
        rcases hsecond : (finSumFinEquiv.symm crossingSecond : Fin 2 ⊕ Fin 2) with
            secondStep | secondStep
        · have hcrossingSecond : crossingSecond =
              finSumFinEquiv (Sum.inl secondStep : Fin 2 ⊕ Fin 2) := by
            exact hcrossing_eq hsecond
          exfalso
          have hvalue := congrArg Fin.val heq
          rw [hcrossingFirst, hcrossingSecond, hsecondValue, hfirstValue] at hvalue
          have hstep := firstStep.isLt
          omega
        · have hcrossingSecond : crossingSecond =
              finSumFinEquiv (Sum.inr secondStep : Fin 2 ⊕ Fin 2) := by
            exact hcrossing_eq hsecond
          have hvalue := congrArg Fin.val heq
          rw [hcrossingFirst, hcrossingSecond, hsecondValue, hsecondValue] at hvalue
          have hsteps : firstStep = secondStep := by
            apply Fin.ext
            have hleft := firstStep.isLt
            have hright := secondStep.isLt
            omega
          have hcrossing : crossingFirst = crossingSecond := calc
            crossingFirst = finSumFinEquiv (Sum.inr firstStep : Fin 2 ⊕ Fin 2) :=
              hcrossingFirst
            _ = finSumFinEquiv (Sum.inr secondStep : Fin 2 ⊕ Fin 2) := by
              exact congrArg finSumFinEquiv (congrArg Sum.inr hsteps)
            _ = crossingSecond := hcrossingSecond.symm
          exact congrArg Sum.inl hcrossing
    · rcases hfirst : (finSumFinEquiv.symm crossingFirst : Fin 2 ⊕ Fin 2) with
        firstStep | firstStep
      · have hcrossingFirst : crossingFirst =
            finSumFinEquiv (Sum.inl firstStep : Fin 2 ⊕ Fin 2) := by
          exact hcrossing_eq hfirst
        rcases hterminal : (finSumFinEquiv.symm
            (Fin.cast hsum.symm terminalSecond) :
              Fin pair.secondRail.length ⊕ Fin pair.firstRail.length) with
            railStep | railStep
        · exfalso
          have hvalue := congrArg Fin.val heq
          rw [hcrossingFirst, hfirstValue, hrailFormula, hterminal] at hvalue
          simp [railIndex] at hvalue
          have hstep := railStep.isLt
          omega
        · exfalso
          have hvalue := congrArg Fin.val heq
          rw [hcrossingFirst, hfirstValue, hrailFormula, hterminal] at hvalue
          simp [railIndex] at hvalue
          have hstep := railStep.isLt
          omega
      · have hcrossingFirst : crossingFirst =
            finSumFinEquiv (Sum.inr firstStep : Fin 2 ⊕ Fin 2) := by
          exact hcrossing_eq hfirst
        rcases hterminal : (finSumFinEquiv.symm
            (Fin.cast hsum.symm terminalSecond) :
              Fin pair.secondRail.length ⊕ Fin pair.firstRail.length) with
            railStep | railStep
        · exfalso
          have hvalue := congrArg Fin.val heq
          rw [hcrossingFirst, hsecondValue, hrailFormula, hterminal] at hvalue
          simp [railIndex] at hvalue
          have hfirstStep := firstStep.isLt
          have hrailStep := railStep.isLt
          omega
        · exfalso
          have hvalue := congrArg Fin.val heq
          rw [hcrossingFirst, hsecondValue, hrailFormula, hterminal] at hvalue
          simp [railIndex] at hvalue
          have hfirstStep := firstStep.isLt
          have hrailStep := railStep.isLt
          omega
  · rcases second with crossingSecond | terminalSecond
    · rcases hterminal : (finSumFinEquiv.symm
          (Fin.cast hsum.symm terminalFirst) :
            Fin pair.secondRail.length ⊕ Fin pair.firstRail.length) with
          railStep | railStep
      · rcases hcrossing : (finSumFinEquiv.symm crossingSecond : Fin 2 ⊕ Fin 2) with
          crossingStep | crossingStep
        · exfalso
          have hvalue := congrArg Fin.val heq
          rw [hrailFormula, hterminal] at hvalue
          have hcrossingSecond : crossingSecond =
              finSumFinEquiv (Sum.inl crossingStep : Fin 2 ⊕ Fin 2) := by
            exact hcrossing_eq hcrossing
          rw [hcrossingSecond, hfirstValue] at hvalue
          simp [railIndex] at hvalue
          have hstep := railStep.isLt
          omega
        · exfalso
          have hvalue := congrArg Fin.val heq
          rw [hrailFormula, hterminal] at hvalue
          have hcrossingSecond : crossingSecond =
              finSumFinEquiv (Sum.inr crossingStep : Fin 2 ⊕ Fin 2) := by
            exact hcrossing_eq hcrossing
          rw [hcrossingSecond, hsecondValue] at hvalue
          simp [railIndex] at hvalue
          have hcrossingStep := crossingStep.isLt
          have hrailStep := railStep.isLt
          omega
      · rcases hcrossing : (finSumFinEquiv.symm crossingSecond : Fin 2 ⊕ Fin 2) with
          crossingStep | crossingStep
        · exfalso
          have hvalue := congrArg Fin.val heq
          rw [hrailFormula, hterminal] at hvalue
          have hcrossingSecond : crossingSecond =
              finSumFinEquiv (Sum.inl crossingStep : Fin 2 ⊕ Fin 2) := by
            exact hcrossing_eq hcrossing
          rw [hcrossingSecond, hfirstValue] at hvalue
          simp [railIndex] at hvalue
          have hstep := railStep.isLt
          omega
        · exfalso
          have hvalue := congrArg Fin.val heq
          rw [hrailFormula, hterminal] at hvalue
          have hcrossingSecond : crossingSecond =
              finSumFinEquiv (Sum.inr crossingStep : Fin 2 ⊕ Fin 2) := by
            exact hcrossing_eq hcrossing
          rw [hcrossingSecond, hsecondValue] at hvalue
          simp [railIndex] at hvalue
          have hcrossingStep := crossingStep.isLt
          have hrailStep := railStep.isLt
          omega
    · have hterminal : terminalFirst = terminalSecond := by
        apply sourceTwoTileAlignedRailCrossingIndexAt_injective realization hcubic
          hrotation htwoSided hunique offset
        exact heq
      exact congrArg Sum.inr hterminal

/-- The literal `4 + 2` profile does not repeat a physical boundary edge. -/
theorem sourceTwoTileAlignedTerminalProfileDataAt_portsInjective
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
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
      htwoSided hunique offset).PortsInjective := by
  intro first second heq
  apply sourceTwoTileAlignedTerminalPortBoundaryIndexAt_injective realization hcubic
    hrotation htwoSided hunique offset
  apply (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
    htwoSided hunique offset).orderedCrossing_injective
  rw [← sourceTwoTileAlignedTerminalProfileDataAt_portEdge_eq_orderedCrossing,
    ← sourceTwoTileAlignedTerminalProfileDataAt_portEdge_eq_orderedCrossing]
  exact heq

/-- The four transverse ports and two rail ports exhaust the actual six-edge
boundary of the source-aligned slab. -/
theorem sourceTwoTileAlignedTerminalProfileDataAt_portEdges_eq_boundary
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
        htwoSided hunique offset).portEdge) =
      sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic hrotation
        htwoSided hunique offset := by
  apply Finset.eq_of_subset_of_card_le
  · intro edge hedge
    rcases Finset.mem_image.1 hedge with ⟨port, -, rfl⟩
    exact sourceTwoTileAlignedTerminalProfileDataAt_portEdge_mem_boundary
      realization hcubic hrotation htwoSided hunique offset port
  · calc
      (sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic hrotation
          htwoSided hunique offset).card = 6 :=
        sourceTwoTileAlignedBoundaryCrossingEdgesAt_card_eq_six realization hcubic
          hrotation htwoSided hunique offset
      _ = (Finset.univ : Finset (CorridorPort 4 2)).card := by simp
      _ = (Finset.univ.image
          (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
            hrotation htwoSided hunique offset).portEdge).card := by
        symm
        exact Finset.card_image_of_injective _
          (sourceTwoTileAlignedTerminalProfileDataAt_portsInjective realization
            hcubic hrotation htwoSided hunique offset)
      _ ≤ (Finset.univ.image
          (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
            hrotation htwoSided hunique offset).portEdge).card := le_rfl

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
