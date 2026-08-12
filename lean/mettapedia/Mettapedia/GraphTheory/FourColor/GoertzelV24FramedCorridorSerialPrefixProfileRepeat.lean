import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixFullProfileRelation

/-!
# Repetition of literal serial-prefix profiles

The cumulative source state before each Cell is computed from the literal
union of the preceding complementary Cells together with the displayed input
cut.  Although its exact face-fragment carrier depends on the cut position,
every such state embeds in the common finite carrier
`BoundedCorridorCutProfile 2 0 4`.

This file first connects the graph-derived five-field relation to that bounded
carrier and then applies finite pigeonhole directly to the corrected serial
prefixes.  It does not identify a cumulative prefix state with either matrix
index of one local Cell: those indices retain the Cell's whole fragment
carrier and have separate generator semantics.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixProfileRepeatEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The exact graph-derived input and successor profiles inhabit the common
four-fragment carrier and satisfy the joint five-field serial relation. -/
theorem sourceCorridorSerialPrefixBoundedProfiles_fullRelation
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
    (color : G.edgeSet → Color)
    (hinputColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0)
    (houtputColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0) :
    SourceCorridorSerialPrefixFullProfileRelation realization hcubic
      hrotation htwoSided hunique offset color
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color hinputColor).profile
      (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color houtputColor).profile := by
  exact sourceCorridorSerialPrefixFullProfileRelation realization hcubic
    hrotation htwoSided hunique offset color hinputColor houtputColor

/-- The corrected cumulative profile word on the literal source-Cell prefix.
The nonzero witness is supplied uniformly so the word itself has one finite
codomain. -/
noncomputable def sourceCorridorSerialInputBoundedProfileWord
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
    (color : G.edgeSet → Color)
    (hcolor : ∀ (offset : Fin (blockLength - 3)) (step : Fin 2),
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0) :
    Fin (blockLength - 3) → BoundedCorridorCutProfile 2 0 4 :=
  fun offset =>
    sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
      htwoSided hunique offset color (hcolor offset)

/-- One more literal serial-prefix cross-section than the exact finite-state
count forces two positions to carry the same complete five-field profile. -/
theorem exists_equal_sourceCorridorSerialInputBoundedProfiles
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
    (hlarge : boundedCorridorCutProfileCount 2 0 4 + 1 ≤ blockLength - 3)
    (color : G.edgeSet → Color)
    (hcolor : ∀ (offset : Fin (blockLength - 3)) (step : Fin 2),
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0) :
    ∃ first second : Fin (boundedCorridorCutProfileCount 2 0 4 + 1),
      first ≠ second ∧
      sourceCorridorSerialInputBoundedProfileWord realization hcubic hrotation
          htwoSided hunique color hcolor (Fin.castLE hlarge first) =
        sourceCorridorSerialInputBoundedProfileWord realization hcubic hrotation
          htwoSided hunique color hcolor (Fin.castLE hlarge second) := by
  let profiles : Fin (boundedCorridorCutProfileCount 2 0 4 + 1) →
      BoundedCorridorCutProfile 2 0 4 := fun offset =>
    sourceCorridorSerialInputBoundedProfileWord realization hcubic hrotation
      htwoSided hunique color hcolor (Fin.castLE hlarge offset)
  have hcard :
      Fintype.card (BoundedCorridorCutProfile 2 0 4) <
        Fintype.card (Fin (boundedCorridorCutProfileCount 2 0 4 + 1)) := by
    rw [card_boundedCorridorCutProfile]
    simp
  exact Fintype.exists_ne_map_eq_of_card_lt profiles hcard

/-- Adding a modulo-four tag gives a repeated complete serial-prefix profile
with three whole source positions between the chosen cross-sections. -/
theorem exists_equal_sourceCorridorSerialInputBoundedProfiles_separated
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
    (hlarge : 4 * boundedCorridorCutProfileCount 2 0 4 + 1 ≤
      blockLength - 3)
    (color : G.edgeSet → Color)
    (hcolor : ∀ (offset : Fin (blockLength - 3)) (step : Fin 2),
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0) :
    ∃ first second : Fin (4 * boundedCorridorCutProfileCount 2 0 4 + 1),
      first.val + 3 < second.val ∧
      sourceCorridorSerialInputBoundedProfileWord realization hcubic hrotation
          htwoSided hunique color hcolor (Fin.castLE hlarge first) =
        sourceCorridorSerialInputBoundedProfileWord realization hcubic hrotation
          htwoSided hunique color hcolor (Fin.castLE hlarge second) := by
  let profiles : Fin (4 * boundedCorridorCutProfileCount 2 0 4 + 1) →
      BoundedCorridorCutProfile 2 0 4 := fun offset =>
    sourceCorridorSerialInputBoundedProfileWord realization hcubic hrotation
      htwoSided hunique color hcolor (Fin.castLE hlarge offset)
  by_contra hrepeat
  have hseparated : ∀ first second,
      first.val + 3 < second.val → profiles first ≠ profiles second := by
    intro first second hfar heq
    exact hrepeat ⟨first, second, hfar, heq⟩
  let encode : Fin (4 * boundedCorridorCutProfileCount 2 0 4 + 1) →
      BoundedCorridorCutProfile 2 0 4 × Fin 4 := fun offset =>
    (profiles offset, ⟨offset.val % 4, Nat.mod_lt _ (by omega)⟩)
  have hinjective : Function.Injective encode := by
    intro first second heq
    have hprofile : profiles first = profiles second := congrArg Prod.fst heq
    have hmod : first.val % 4 = second.val % 4 := by
      have hresidue := congrArg (fun pair => pair.2.val) heq
      simpa [encode] using hresidue
    apply Fin.ext
    by_cases hval : first.val = second.val
    · exact hval
    · rcases lt_or_gt_of_ne hval with hfirst | hsecond
      · have hfar : first.val + 3 < second.val := by omega
        exact False.elim (hseparated first second hfar hprofile)
      · have hfar : second.val + 3 < first.val := by omega
        exact False.elim (hseparated second first hfar hprofile.symm)
  have hcard := Fintype.card_le_of_injective encode hinjective
  simp [card_boundedCorridorCutProfile] at hcard
  omega

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
