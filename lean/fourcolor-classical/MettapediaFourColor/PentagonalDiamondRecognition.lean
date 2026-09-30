import MettapediaFourColor.PentagonalDiamondScheme
import Mettapedia.GraphTheory.FourColor.PentagonalDiamondGeometry
import Mettapedia.GraphTheory.FourColor.PartialCubicDartBoundary
import Mettapedia.GraphTheory.FourColor.OpenTangleDartRecognition

/-!
# Recognizing the actual pentagonal diamond

The face-derived twelve vertices and all thirty-six incident darts are put
in bijection with the literal piece. The generic boundary theorem excludes
unrecorded internal edges. Every rotation, internal reversal and ordered port
is preserved, so the resulting isomorphism can be sewn into an actual context.
-/

namespace FourColor.PentagonalDiamondPatch.Tangle

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open SimpleGraphDartRotation PhysicalForkCodeFaces
open ConfigurationTable

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The same coordinates connect the literal piece and the actual face traversal. -/
def coordinate : Dart ≃ PentagonalDiamond.Slot where
  toFun d := PentagonalDiamond.unflat (lookup "ACEFGHIKLMNOQRSTVXYZ[\\]^_`abcdBDJPUW" (index d))
  invFun s := index.symm (lookup "A_B`CDEFGaHIJKLbMNOPcQdRSTUVWXYZ[\\]^" (PentagonalDiamond.flat s))
  left_inv := by decide
  right_inv := by decide

theorem coordinate_vertex : ∀ d, piece.vertOf d = (coordinate d).1 := by decide

theorem coordinate_rotate : ∀ d,
    coordinate (piece.rho d) = PentagonalDiamond.rotate (coordinate d) := by decide

theorem coordinate_flip : ∀ i : Fin 30,
    PentagonalDiamond.flip (coordinate (.inl i)) =
      some (coordinate (.inl (piece.interiorAlpha i))) := by decide

theorem coordinate_boundary : ∀ b : Fin 6,
    PentagonalDiamond.flip (coordinate (.inr b)) = none := by decide

theorem unpaired_card : Fintype.card
    (PartialCubicDartSeparation.Realization.Unpaired (P := PentagonalDiamond.diagram)) = 6 := by
  have hs : ∀ d : PentagonalDiamond.Slot, PentagonalDiamond.flip d = none →
      ∃ b : Fin 6, coordinate (.inr b) = d := by decide
  let e : Fin 6 ≃ PartialCubicDartSeparation.Realization.Unpaired
      (P := PentagonalDiamond.diagram) :=
    Equiv.ofBijective (fun b => ⟨coordinate (.inr b), coordinate_boundary b⟩) ⟨by
      intro a b h
      exact Sum.inr.inj (coordinate.injective (congrArg Subtype.val h)), by
      intro d
      obtain ⟨b, hb⟩ := hs d.1 d.2
      exact ⟨b, Subtype.ext hb⟩⟩
  exact (Fintype.card_congr e).symm

namespace Recognition
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance diamondRecognitionEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance diamondRecognitionEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart)
  (hC : Cubic3 rotation.toRotationSystem) (hfaces : PentagonalDiamond.FaceLengths rotation root)

abbrev realized := PentagonalDiamond.realization rotation root hC hfaces

def deleted : Finset V := Finset.univ.image (PentagonalDiamond.vertex rotation root)

abbrev keep := deletedSideKeep (deleted rotation root)

@[simp] theorem keep_iff (v : V) : keep rotation root v ↔
    v ∈ Set.range (PentagonalDiamond.vertex rotation root) := by
  simp [keep, deletedSideKeep, deletedRegionKeep, deleted]

def retained (d : Dart) : RetainedDart rotation.toRotationSystem (keep rotation root) :=
  ⟨(realized rotation root hC hfaces).dart (coordinate d), by
    apply (keep_iff rotation root _).mpr
    exact ⟨(coordinate d).1, ((realized rotation root hC hfaces).fst _).symm⟩⟩

def rootIn : RetainedDart rotation.toRotationSystem (keep rotation root) :=
  retained rotation root hC hfaces (.inr 0)

variable (hv : Function.Injective (PentagonalDiamond.vertex rotation root))

def vertices : Fin 12 ≃ {v // keep rotation root v} :=
  Equiv.ofBijective (fun i => ⟨PentagonalDiamond.vertex rotation root i,
    (keep_iff rotation root _).mpr ⟨i, rfl⟩⟩) ⟨by
      intro a b he
      exact hv (congrArg Subtype.val he), by
      rintro ⟨v, h⟩
      obtain ⟨i, hi⟩ := (keep_iff rotation root v).mp h
      exact ⟨i, Subtype.ext hi⟩⟩

def darts : Dart ≃ RetainedDart rotation.toRotationSystem (keep rotation root) :=
  Equiv.ofBijective (retained rotation root hC hfaces) ⟨by
    intro a b he
    apply coordinate.injective
    exact (realized rotation root hC hfaces).dart_injective hv (congrArg Subtype.val he), by
    intro d
    obtain ⟨v, hv'⟩ := (keep_iff rotation root d.1.fst).mp d.2
    obtain ⟨s, hs⟩ := (realized rotation root hC hfaces).slots_surjective v d.1 hv'.symm
    refine ⟨coordinate.symm (v, s), Subtype.ext ?_⟩
    change (realized rotation root hC hfaces).dart (coordinate (coordinate.symm (v, s))) = d.1
    rw [Equiv.apply_symm_apply]
    exact hs⟩

theorem interior_kept (i : Fin 30) : keep rotation root
    (rotation.toRotationSystem.vertOf
      (rotation.toRotationSystem.alpha (darts rotation root hC hfaces hv (.inl i)).1)) := by
  apply (keep_iff rotation root _).mpr
  change ∃ v, PentagonalDiamond.vertex rotation root v =
    ((realized rotation root hC hfaces).dart (coordinate (.inl i))).snd
  exact ⟨(coordinate (.inl (piece.interiorAlpha i))).1,
    ((realized rotation root hC hfaces).snd_of_flip (coordinate_flip i)).symm⟩

variable (hcubic : G.IsRegularOfDegree 3) (hcyclic : CyclicallyFiveEdgeConnected G)
  (hspace : 15 ≤ Fintype.card V)

include hcubic hcyclic hspace in
theorem boundary_leaves (b : Fin 6) : ¬ keep rotation root
    (rotation.toRotationSystem.vertOf
      (rotation.toRotationSystem.alpha (darts rotation root hC hfaces hv (.inr b)).1)) := by
  have hh := (realized rotation root hC hfaces).unpaired_leaves_of_cyclicallyFive hv
    unpaired_card (by decide) (by decide) (by simpa using hspace) hcubic hcyclic
    ⟨coordinate (.inr b), coordinate_boundary b⟩
  intro hk
  exact hh ((keep_iff rotation root _).mp hk)

/-- Complete occurrence recognition from the face traversal and ambient
cyclic connectivity. No tangle isomorphism is assumed. -/
def recognized : OpenTangleIsomorphism.Iso piece
    (ofVertexSide rotation.toRotationSystem (keep rotation root) (rootIn rotation root hC hfaces)) := by
  apply OpenTangleIsomorphism.ofRetainedDarts piece rotation.toRotationSystem
    (keep rotation root) (rootIn rotation root hC hfaces)
    (vertices rotation root hv) (darts rotation root hC hfaces hv)
    (interior_kept rotation root hC hfaces hv)
    (boundary_leaves rotation root hC hfaces hv hcubic hcyclic hspace)
  · intro i
    exact ((realized rotation root hC hfaces).flip_eq _ _ (coordinate_flip i)).symm
  · intro d
    apply Subtype.ext
    change PentagonalDiamond.vertex rotation root (piece.vertOf d) =
      ((realized rotation root hC hfaces).dart (coordinate d)).fst
    rw [(realized rotation root hC hfaces).fst, coordinate_vertex]
    rfl
  · intro d
    apply Subtype.ext
    change (realized rotation root hC hfaces).dart (coordinate (piece.rho d)) =
      rotation.vertexRotation ((realized rotation root hC hfaces).dart (coordinate d))
    rw [coordinate_rotate]
    exact (realized rotation root hC hfaces).rotate_eq _

end
end Recognition
end FourColor.PentagonalDiamondPatch.Tangle
