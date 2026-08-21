import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceOutgoingProfileCodec
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceProfileWord

/-!
# Repetition of literal outgoing source profiles

Every indexed Cell of the heterogeneous source corridor produces a complete
outgoing cumulative-prefix profile.  The joint one-Cell receipt compresses
that profile into the exact `18000`-element source-shaped carrier, and the
codec proves that this compression is lossless on those literal outputs.

This file applies the separated pigeonhole argument directly to that outgoing
word.  It lowers the witness-level L7 length demand from the conservative raw
profile carrier to `4 * 18000 + 1 = 72001`, while concluding equality of the
complete original four-bound profiles.

This is not yet a reachable-closure theorem or a numerical `V0`: iteration of
the one-Cell support still requires the successor identification between one
Cell's outgoing cut and the next Cell's terminal-aware input cut.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedCorridorThreeFacePrefixProfileRepeat
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

/-- Four residue classes buy the required gap of at least four on the exact
source-shaped outgoing carrier. -/
theorem separated_sourceOutgoingProfileCodeCount :
    4 * Fintype.card SourceOutgoingProfileCode + 1 = 72001 := by
  rw [card_sourceOutgoingProfileCode]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance sourceOutgoingProfileRepeatEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The complete four-bound outgoing profile at one literal source Cell. -/
noncomputable def sourceSlabOutgoingProfile
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
  let aligned := sourceSlabCornerInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  aligned.toInterface.localLayerRightPrefixBoundedProfile coloring
    (fun step => hcoloring
      (aligned.toInterface.nextLocalLayerPrefixCrossing step))

/-- The complete narrowed outgoing profile at one literal source Cell. -/
noncomputable def sourceSlabFiniteOutgoingProfile
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
    BoundedCorridorCutProfile 2 0 3 :=
  let aligned := sourceSlabCornerInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  aligned.localLayerFiniteOutputProfile coloring
    (fun step => hcoloring
      (aligned.toInterface.nextLocalLayerPrefixCrossing step))

/-- The exact finite code of one literal outgoing cumulative-prefix profile. -/
noncomputable def sourceSlabOutgoingProfileCode
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
    SourceOutgoingProfileCode :=
  (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
    offset).sourceOutgoingProfileCodeOfTait hcubic hrotation coloring hcoloring

/-- Decoding a source-word letter recovers its complete narrowed outgoing
profile. -/
theorem decode_sourceSlabOutgoingProfileCode
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
    decodeSourceOutgoingProfile
        (sourceSlabOutgoingProfileCode realization hcubic hrotation htwoSided
          hunique offset coloring hcoloring) =
      sourceSlabFiniteOutgoingProfile realization hcubic hrotation htwoSided
        hunique offset coloring hcoloring := by
  let aligned := sourceSlabCornerInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  exact decode_sourceOutgoingProfileCodeOfReceipt
    (aligned.localLayerFiniteInputProfile coloring
      (fun step => hcoloring
        (aligned.toInterface.localLayerPrefixCrossing step)))
    (aligned.localLayerFiniteOutputProfile coloring
      (fun step => hcoloring
        (aligned.toInterface.nextLocalLayerPrefixCrossing step)))
    (aligned.localLayerFiniteOutputProfile_isPortIncidenceSemantic coloring
      (fun step => hcoloring
        (aligned.toInterface.nextLocalLayerPrefixCrossing step)))
    (aligned.exists_localLayerFiniteOneCellReceipt_of_tait
      hcubic hrotation coloring hcoloring)

/-- Literal outgoing source profiles repeat at gap at least four once the
corridor contains `72001` indexed Cells.  The conclusion is equality of the
complete four-bound cumulative-prefix profiles, not merely their codes. -/
theorem exists_equal_sourceSlabOutgoingProfiles_separated
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
    (hlarge : 4 * Fintype.card SourceOutgoingProfileCode + 1 ≤
      blockLength - 3)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin
        (4 * Fintype.card SourceOutgoingProfileCode + 1),
      first.val + 3 < second.val ∧
      sourceSlabOutgoingProfile realization hcubic hrotation htwoSided hunique
          (Fin.castLE hlarge first) coloring hcoloring =
        sourceSlabOutgoingProfile realization hcubic hrotation htwoSided hunique
          (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin
        (4 * Fintype.card SourceOutgoingProfileCode + 1) →
      SourceOutgoingProfileCode := fun offset =>
    sourceSlabOutgoingProfileCode realization hcubic hrotation htwoSided
      hunique (Fin.castLE hlarge offset) coloring hcoloring
  by_contra hrepeat
  have hseparated : ∀ first second,
      first.val + 3 < second.val → profiles first ≠ profiles second := by
    intro first second hfar heq
    apply hrepeat
    refine ⟨first, second, hfar, ?_⟩
    have heq' :
        sourceSlabOutgoingProfileCode realization hcubic hrotation htwoSided
            hunique (Fin.castLE hlarge first) coloring hcoloring =
          sourceSlabOutgoingProfileCode realization hcubic hrotation htwoSided
            hunique (Fin.castLE hlarge second) coloring hcoloring := by
      simpa only [profiles] using heq
    have hnarrow :
        sourceSlabFiniteOutgoingProfile realization hcubic hrotation htwoSided
            hunique (Fin.castLE hlarge first) coloring hcoloring =
          sourceSlabFiniteOutgoingProfile realization hcubic hrotation htwoSided
            hunique (Fin.castLE hlarge second) coloring hcoloring := by
      rw [← decode_sourceSlabOutgoingProfileCode realization hcubic hrotation
          htwoSided hunique (Fin.castLE hlarge first) coloring hcoloring,
        ← decode_sourceSlabOutgoingProfileCode realization hcubic hrotation
          htwoSided hunique (Fin.castLE hlarge second) coloring hcoloring,
        heq']
    unfold sourceSlabOutgoingProfile
    exact narrowFaceFragmentBound_injective
      ((sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided
        hunique (Fin.castLE hlarge first)).toInterface
        |>.localLayerRightPrefixBoundedProfile_faceFragmentCount_le_three
          coloring (fun step => hcoloring _))
      ((sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided
        hunique (Fin.castLE hlarge second)).toInterface
        |>.localLayerRightPrefixBoundedProfile_faceFragmentCount_le_three
          coloring (fun step => hcoloring _))
      hnarrow
  let encode : Fin (4 * Fintype.card SourceOutgoingProfileCode + 1) →
      SourceOutgoingProfileCode × Fin 4 := fun offset =>
    (profiles offset, ⟨offset.val % 4, Nat.mod_lt _ (by omega)⟩)
  have hinjective : Function.Injective encode := by
    intro first second heq
    have hprofile : profiles first = profiles second :=
      congrArg Prod.fst heq
    have hmod : first.val % 4 = second.val % 4 := by
      have hresidue := congrArg (fun pair => pair.2.val) heq
      change first.val % 4 = second.val % 4 at hresidue
      exact hresidue
    apply Fin.ext
    by_cases hval : first.val = second.val
    · exact hval
    · rcases lt_or_gt_of_ne hval with hfirst | hsecond
      · have hfar : first.val + 3 < second.val := by omega
        exact False.elim (hseparated first second hfar hprofile)
      · have hfar : second.val + 3 < first.val := by omega
        exact False.elim (hseparated second first hfar hprofile.symm)
  have hcard := Fintype.card_le_of_injective encode hinjective
  rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin,
    card_sourceOutgoingProfileCode] at hcard
  omega

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
