import Mettapedia.GraphTheory.FourColor.PaddedCycleCapPortGeometry
import Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation

/-!
# Actual face darts realize the cap's partial cubic diagram

The interpretation preserves all slots, cubic rotations and internal edge
reversals before any vertex injectivity has been proved. Boundary reversals
remain unspecified; this is an immersion, not a recognized cap shore.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap.PartialDiagram

open PartialCubicDartSeparation PhysicalForkCodeFaces FaceTraversal
open Equiv Equiv.Perm

variable (m : ℕ) [NeZero m]
abbrev Slot := PartialCubicDartSeparation.Dart (Vertex m)

def toPosition (d : Slot m) : Position m := (d.1.1,d.1.2,d.2)
def ofPosition (p : Position m) : Slot m := ((p.1,p.2.1),p.2.2)

def flip (d : Slot m) : Option (Slot m) :=
  match star m (toPosition m d) with
  | .inl i => some (ofPosition m (position m (.inl (alpha m i))))
  | .inr _ => none

def rotate (d : Slot m) : Slot m := (d.1,d.2+1)

theorem flip_reverse (d e : Slot m) (he : flip m d = some e) : flip m e = some d := by
  unfold flip at he ⊢
  cases hs : star m (toPosition m d) with
  | inr b => simp [hs] at he
  | inl i =>
    simp only [hs,Option.some.injEq] at he
    rw [← he]
    have ht : toPosition m (ofPosition m (position m (.inl (alpha m i)))) =
        position m (.inl (alpha m i)) := rfl
    rw [ht,star_position]
    have hi : alpha m (alpha m i) = i := by
      rcases i with ⟨k,v,b⟩
      simp [alpha, PaddedCycleCap.flip]
    change some (ofPosition m (position m (.inl (alpha m (alpha m i))))) = some d
    rw [hi]
    have hh := congrArg (ofPosition m ∘ position m) hs
    simp only [Function.comp_apply,position_star] at hh
    exact congrArg some hh.symm

def diagram : Diagram (Vertex m) where
  rotate := rotate m
  flip := flip m
  flip_reverse := flip_reverse m

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (rotation : SimpleGraphDartRotation.Data G) (root : G.Dart)

local instance immersionEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance immersionEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

def interpreted (d : Slot m) : G.Dart := atStar rotation.toRotationSystem m root (toPosition m d)

theorem interpreted_star (d : Slot m) :
    interpreted m rotation root d =
      FaceTraversal.dart rotation.toRotationSystem m root (star m (toPosition m d)) := by
  simp only [FaceTraversal.dart,position_star]
  rfl

variable (hC : Cubic3 rotation.toRotationSystem)
  (hf : FaceLengths rotation.toRotationSystem m root)

omit [NeZero m] in
include hC in
theorem interpreted_slots_injective (v : Vertex m) :
    Function.Injective (fun s => interpreted m rotation root (v,s)) := by
  let RS := rotation.toRotationSystem
  let d := base RS m root v.1 v.2
  have htwo : RS.rho (RS.rho d) ≠ d := by
    intro he
    have hh := congrArg RS.rho he
    rw [hC.cube] at hh
    exact hC.moves d hh.symm
  intro s t he
  fin_cases s <;> fin_cases t <;>
    simp only [interpreted,toPosition,atStar,pow_succ',pow_zero,Perm.mul_apply,
      Perm.one_apply] at he
  · rfl
  · exact (hC.moves d he.symm).elim
  · exact (htwo he.symm).elim
  · exact (hC.moves d he).elim
  · rfl
  · exact (hC.moves (RS.rho d) he.symm).elim
  · exact (htwo he).elim
  · exact (hC.moves (RS.rho d) he).elim
  · rfl

include hC hf in
theorem interpreted_flip (d e : Slot m) (he : flip m d = some e) :
    (interpreted m rotation root d).symm = interpreted m rotation root e := by
  unfold flip at he
  cases hs : star m (toPosition m d) with
  | inr b => simp [hs] at he
  | inl i =>
    simp only [hs,Option.some.injEq] at he
    rw [← he,interpreted_star m rotation root d,hs]
    change rotation.toRotationSystem.alpha (FaceTraversal.dart _ m root (.inl i)) = _
    rw [← dart_alpha rotation.toRotationSystem m root hC hf]
    rfl

include hC hf in
/-- Actual face closure constructs the operation-preserving interpretation;
neither injectivity of all vertices nor exposure of final ports is assumed. -/
def realization : Realization (diagram m) G where
  vertex := vertex rotation.toRotationSystem m root
  dart := interpreted m rotation root
  fst := fun d => atStar_vertex rotation.toRotationSystem m root (toPosition m d)
  slots_injective := interpreted_slots_injective m rotation root hC
  slots_surjective := fun v d hd => atStar_surjective_at rotation.toRotationSystem m root hC v d hd
  rotation := rotation.vertexRotation
  rotate_eq := fun d => atStar_rotate rotation.toRotationSystem m root hC (toPosition m d)
  flip_eq := interpreted_flip m rotation root hC hf

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap.PartialDiagram
