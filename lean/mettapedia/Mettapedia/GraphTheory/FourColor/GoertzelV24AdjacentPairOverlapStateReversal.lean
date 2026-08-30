import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairStateReversal

/-!
# Reversing a two-site adjacent-pair overlap state

Reading an oriented path segment backward reverses each adjacent-pair site
and exchanges the source and target sites.  This file records the induced
action on the complete finite overlap state.

The overlap matrix is transposed after the four-port reversal, the two
boundary states are exchanged and reversed, and literal agreement on the
common four-vertex deletion is unchanged.  No planarity, cancellation, or
wall statement is involved.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairOverlapStateReversal

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairReversal
open GoertzelV24AdjacentPairStateReversal
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Reverse the direction of a complete two-site overlap observation. -/
def reverseOverlapKempeState (state : OverlapKempeState) :
    OverlapKempeState where
  overlapProfile sourcePort targetPort :=
    state.overlapProfile (reversePort targetPort) (reversePort sourcePort)
  sourceBoundary := reverseBoundaryKempeState state.targetBoundary
  targetBoundary := reverseBoundaryKempeState state.sourceBoundary
  commonRestrictionAgrees := state.commonRestrictionAgrees

/-- Reversing a two-site overlap observation twice is the identity. -/
@[simp] theorem reverseOverlapKempeState_involutive
    (state : OverlapKempeState) :
    reverseOverlapKempeState (reverseOverlapKempeState state) = state := by
  cases state
  simp [reverseOverlapKempeState]

/-- Reversal is a genuine symmetry of the finite overlap-state space. -/
def reverseOverlapKempeStateEquiv :
    OverlapKempeState ≃ OverlapKempeState where
  toFun := reverseOverlapKempeState
  invFun := reverseOverlapKempeState
  left_inv := reverseOverlapKempeState_involutive
  right_inv := reverseOverlapKempeState_involutive

/-- Reversing and exchanging two sites transposes their literal port-overlap
matrix after the four-port reversal. -/
theorem portOverlapProfile_reverse_swap
    (source target : AdjacentPairData G) :
    portOverlapProfile (reverse target) (reverse source) =
      fun sourcePort targetPort =>
        portOverlapProfile source target
          (reversePort targetPort) (reversePort sourcePort) := by
  funext sourcePort targetPort
  simp only [portOverlapProfile, reverse_portVertex]
  by_cases h :
      target.portVertex (reversePort sourcePort) =
        source.portVertex (reversePort targetPort)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg]
    exact fun converse => h converse.symm

/-- The original common four-vertex deletion and the common deletion after
reversing and exchanging the two sites have the same underlying graph. -/
def commonCoreReverseSwapIso (source target : AdjacentPairData G) :
    DeletedTwoPairsGraph G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex ≃g
      DeletedTwoPairsGraph G (reverse target).firstVertex
        (reverse target).secondVertex (reverse source).firstVertex
        (reverse source).secondVertex where
  toFun vertex := ⟨vertex.1,
    vertex.2.2.2.2,
    vertex.2.2.2.1,
    vertex.2.2.1,
    vertex.2.1⟩
  invFun vertex := ⟨vertex.1,
    vertex.2.2.2.2,
    vertex.2.2.2.1,
    vertex.2.2.1,
    vertex.2.1⟩
  left_inv vertex := by ext; rfl
  right_inv vertex := by ext; rfl
  map_rel_iff' := Iff.rfl

/-- On the common core, the reversed target colouring is the original target
colouring after transporting through the common-core isomorphism. -/
theorem firstCommonCore_reverse_target_apply
    (source target : AdjacentPairData G)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (edge : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet) :
    firstDeletionCommonCoreColoring (G := G)
        (first := (reverse target).firstVertex)
        (second := (reverse target).secondVertex)
        (third := (reverse source).firstVertex)
        (fourth := (reverse source).secondVertex)
        (reverseColoring target targetColoring)
        ((commonCoreReverseSwapIso source target).mapEdgeSet edge) =
      secondDeletionCommonCoreColoring (G := G)
        (first := source.firstVertex) (second := source.secondVertex)
        (third := target.firstVertex) (fourth := target.secondVertex)
        targetColoring edge := by
  change targetColoring _ = targetColoring _
  congr 1
  apply Subtype.ext
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right => rfl

/-- On the common core, the reversed source colouring is the original source
colouring after transporting through the common-core isomorphism. -/
theorem secondCommonCore_reverse_source_apply
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (edge : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet) :
    secondDeletionCommonCoreColoring (G := G)
        (first := (reverse target).firstVertex)
        (second := (reverse target).secondVertex)
        (third := (reverse source).firstVertex)
        (fourth := (reverse source).secondVertex)
        (reverseColoring source sourceColoring)
        ((commonCoreReverseSwapIso source target).mapEdgeSet edge) =
      firstDeletionCommonCoreColoring (G := G)
        (first := source.firstVertex) (second := source.secondVertex)
        (third := target.firstVertex) (fourth := target.secondVertex)
        sourceColoring edge := by
  change sourceColoring _ = sourceColoring _
  congr 1
  apply Subtype.ext
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right => rfl

/-- Literal agreement on the common deletion is unchanged when both sites
are reversed and their source--target order is exchanged. -/
theorem commonRestrictionAgreement_reverse_swap_iff
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) :
    firstDeletionCommonCoreColoring (G := G)
        (first := (reverse target).firstVertex)
        (second := (reverse target).secondVertex)
        (third := (reverse source).firstVertex)
        (fourth := (reverse source).secondVertex)
        (reverseColoring target targetColoring) =
      secondDeletionCommonCoreColoring (G := G)
        (first := (reverse target).firstVertex)
        (second := (reverse target).secondVertex)
        (third := (reverse source).firstVertex)
        (fourth := (reverse source).secondVertex)
        (reverseColoring source sourceColoring) ↔
    firstDeletionCommonCoreColoring (G := G)
        (first := source.firstVertex) (second := source.secondVertex)
        (third := target.firstVertex) (fourth := target.secondVertex)
        sourceColoring =
      secondDeletionCommonCoreColoring (G := G)
        (first := source.firstVertex) (second := source.secondVertex)
        (third := target.firstVertex) (fourth := target.secondVertex)
        targetColoring := by
  constructor
  · intro hreversed
    apply DFunLike.ext _ _
    intro edge
    have hat := congrArg
      (fun coloring => coloring
        ((commonCoreReverseSwapIso source target).mapEdgeSet edge))
      hreversed
    have hcolor :
        firstDeletionCommonCoreColoring sourceColoring edge =
          secondDeletionCommonCoreColoring targetColoring edge := by
      calc
        firstDeletionCommonCoreColoring sourceColoring edge =
            secondDeletionCommonCoreColoring
              (reverseColoring source sourceColoring)
              ((commonCoreReverseSwapIso source target).mapEdgeSet edge) :=
          (secondCommonCore_reverse_source_apply
            source target sourceColoring edge).symm
        _ = firstDeletionCommonCoreColoring
              (reverseColoring target targetColoring)
              ((commonCoreReverseSwapIso source target).mapEdgeSet edge) :=
          hat.symm
        _ = secondDeletionCommonCoreColoring targetColoring edge :=
          firstCommonCore_reverse_target_apply
            source target targetColoring edge
    exact hcolor
  · intro horiginal
    apply DFunLike.ext _ _
    intro reversedEdge
    let edge := (commonCoreReverseSwapIso source target).mapEdgeSet.symm
      reversedEdge
    have hmap :
        (commonCoreReverseSwapIso source target).mapEdgeSet edge =
          reversedEdge :=
      (commonCoreReverseSwapIso source target).mapEdgeSet.apply_symm_apply _
    have hat := congrArg (fun coloring => coloring edge) horiginal
    have hcolor :
        firstDeletionCommonCoreColoring
            (reverseColoring target targetColoring) reversedEdge =
          secondDeletionCommonCoreColoring
            (reverseColoring source sourceColoring) reversedEdge := by
      calc
        firstDeletionCommonCoreColoring
            (reverseColoring target targetColoring) reversedEdge =
          firstDeletionCommonCoreColoring
            (reverseColoring target targetColoring)
            ((commonCoreReverseSwapIso source target).mapEdgeSet edge) := by
              rw [hmap]
        _ = secondDeletionCommonCoreColoring targetColoring edge :=
          firstCommonCore_reverse_target_apply
            source target targetColoring edge
        _ = firstDeletionCommonCoreColoring sourceColoring edge := hat.symm
        _ = secondDeletionCommonCoreColoring
            (reverseColoring source sourceColoring)
            ((commonCoreReverseSwapIso source target).mapEdgeSet edge) :=
          (secondCommonCore_reverse_source_apply
            source target sourceColoring edge).symm
        _ = secondDeletionCommonCoreColoring
            (reverseColoring source sourceColoring) reversedEdge := by rw [hmap]
    exact hcolor

/-- The Boolean common-restriction coordinate is invariant under reversal
and exchange of the two sites. -/
theorem commonRestrictionAgreementBit_reverse_swap
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) :
    commonRestrictionAgreementBit (reverse target) (reverse source)
        (reverseColoring target targetColoring)
        (reverseColoring source sourceColoring) =
      commonRestrictionAgreementBit source target
        sourceColoring targetColoring := by
  unfold commonRestrictionAgreementBit
  rw [if_congr (commonRestrictionAgreement_reverse_swap_iff
    source target sourceColoring targetColoring) rfl rfl]

/-- The complete overlap state read from target to source is exactly the
reversal of the state read from source to target. -/
theorem overlapKempeState_reverse_swap
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) :
    overlapKempeState (reverse target) (reverse source)
        (reverseColoring target targetColoring)
        (reverseColoring source sourceColoring) =
      reverseOverlapKempeState
        (overlapKempeState source target sourceColoring targetColoring) := by
  simp only [overlapKempeState, reverseOverlapKempeState]
  rw [portOverlapProfile_reverse_swap source target]
  rw [boundaryKempeState_reverseColoring target targetColoring]
  rw [boundaryKempeState_reverseColoring source sourceColoring]
  rw [commonRestrictionAgreementBit_reverse_swap
    source target sourceColoring targetColoring]

end

end GoertzelV24AdjacentPairOverlapStateReversal

end Mettapedia.GraphTheory.FourColor
