import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixBoundaryProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceProfileWord

/-!
# Repetition of cumulative source-prefix profiles

The width-four depth profile of a local deletion component and the width-two
profile of a cumulative corridor prefix describe different cuts.  This file
applies the finite-state pigeonhole argument directly to the latter carrier.
Every state in the word is computed from the literal prefix region and its
source-ordered two-edge cross-section.

The separated form is finite-state bookkeeping only.  It does not identify
the repeated cross-sections with the older local layer loops, and it does not
claim that the region between them has already been spliced.

This is the witness-level repeat used by a counterexample species carrying an
actual coloring, such as a closed web.  Fiber-level rejection statements and
the source-crosscut diagonal lift instead require the relational `Count`
support; no such quantifier strengthening is claimed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileRepeatEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The complete cumulative profile at one source-indexed corridor
cross-section.  It is the incoming width-two prefix state of the Cell at that
position, not the width-four profile of the Cell's local deletion component. -/
noncomputable def sourceSlabPrefixBoundedProfile
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
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    BoundedCorridorCutProfile 2 0 4 :=
  let interface := sourceSlabInterfaceAt realization hcubic hrotation htwoSided
    hunique offset
  interface.localLayerLeftPrefixBoundedProfile coloring
    (fun step => hcoloring (interface.localLayerPrefixCrossing step))

/-- One more literal cumulative cross-section than the exact finite carrier
size forces two source positions to carry the same complete profile. -/
theorem exists_equal_sourceSlabPrefixBoundedProfiles
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
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin (boundedCorridorCutProfileCount 2 0 4 + 1),
      first ≠ second ∧
      sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge first) coloring hcoloring =
        sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin (boundedCorridorCutProfileCount 2 0 4 + 1) →
      BoundedCorridorCutProfile 2 0 4 := fun offset =>
    sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
      hunique (Fin.castLE hlarge offset) coloring hcoloring
  have hcard :
      Fintype.card (BoundedCorridorCutProfile 2 0 4) <
        Fintype.card (Fin (boundedCorridorCutProfileCount 2 0 4 + 1)) := by
    rw [card_boundedCorridorCutProfile]
    simp
  exact Fintype.exists_ne_map_eq_of_card_lt profiles hcard

/-- A longer corridor repeats a complete cumulative profile with three whole
source positions between the selected cross-sections.  The modulo-four tag
supplies spacing without changing the profile being repeated. -/
theorem exists_equal_sourceSlabPrefixBoundedProfiles_separated
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
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin (4 * boundedCorridorCutProfileCount 2 0 4 + 1),
      first.val + 3 < second.val ∧
      sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge first) coloring hcoloring =
        sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin (4 * boundedCorridorCutProfileCount 2 0 4 + 1) →
      BoundedCorridorCutProfile 2 0 4 := fun offset =>
    sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
      hunique (Fin.castLE hlarge offset) coloring hcoloring
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
