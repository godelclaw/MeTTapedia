import MettapediaFourColor.ThreeBlockDiskDeletion
import MettapediaFourColor.GraphTriangulationEuler
import MettapediaFourColor.GraphRotationRows

/-! # A planar exterior for testing core-list summaries

The pinned D0092 disk is capped by nine triangles on its eleven boundary
vertices. Complete source core rows and a spherical rotation are checked
independently of all colouring-repair certificates.
-/

namespace FourColor.CoreProfileSwitchGeometry

open SimpleGraph FiveTriangleCollapseObstruction ThreeBlockDiskBoundary

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def star (v : Fin 18) : List (Fin 18) :=
  (![[1,7,10,17],
     [0,17,15,2,7],
     [1,15,3,4,7],
     [2,15,12,4],
     [2,3,12,5,7],
     [4,12,13,6,7],
     [5,13,7],
     [0,1,2,4,5,6,13,14,8,10],
     [7,14,11,16,9,10],
     [8,16,10],
     [0,7,8,9,16,17],
     [8,14,12,15,17,16],
     [3,15,11,14,13,5,4],
     [5,12,14,7,6],
     [7,13,12,11,8],
     [1,17,11,12,3,2],
     [8,11,17,10,9],
     [0,10,16,11,15,1]] : Fin 18 → List (Fin 18)) v

private theorem symmetric : ∀ u v : Fin 18, v ∈ star u → u ∈ star v := by decide +kernel
private theorem loopless : ∀ v : Fin 18, v ∉ star v := by decide +kernel

def graph : SimpleGraph (Fin 18) where
  Adj u v := v ∈ star u
  symm := ⟨symmetric⟩
  loopless := ⟨loopless⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

def rows : GraphRotationRows.Rows graph := ⟨star, by decide +kernel, fun _ _ => Iff.rfl⟩
def rotation := rows.rotation (⟨(0,1), by decide +kernel⟩ : graph.Dart)
theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _
theorem triangular : ExceptionalOverlap.Triangular rotation := by
  unfold ExceptionalOverlap.Triangular
  decide +kernel

def hom : upper.graph →g graph where
  toFun := id
  map_rel' := by decide +kernel

theorem core_turn : ∀ i j k, Turn i j k →
    ExceptionalCoreOrientation.Corner rotation (hom i) (hom k) (hom j) := by
  have h : ∀ i j k : Fin 18, Turn i j k →
      graph.Adj (hom i) (hom k) ∧ graph.Adj (hom i) (hom j) ∧
        rows.next (hom i) (hom k) = hom j := by decide +kernel
  intro i j k ht
  obtain ⟨hik, hij, step⟩ := h i j k ht
  exact ⟨hik, hij, Dart.ext _ _ (Prod.ext rfl step)⟩

def reading : Reading rotation := ⟨hom, Function.injective_id, core_turn⟩

theorem connected : graph.Connected := by
  have parents : ∀ v : Fin 18, v ≠ 0 → ∃ w, w.val < v.val ∧ graph.Adj w v := by
    decide +kernel
  have reach : ∀ n (v : Fin 18), v.val = n → graph.Reachable 0 v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases h : v = 0
      · subst v; exact .refl _
      obtain ⟨w, less, edge⟩ := parents v h
      exact (ih w.val (hv ▸ less) w rfl).trans edge.reachable
  apply (connected_iff_exists_forall_reachable (G := graph)).mpr
  exact ⟨0, fun v => reach v.val v rfl⟩

theorem dart_count : Nat.card graph.Dart = 96 := by
  rw [rows.dart_count]
  decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar := by
  apply (GraphTriangulationEuler.planar_iff_balance rotation cyclic connected
    (GraphTriangulationEuler.covered connected) triangular).mpr
  rw [Nat.card_fin, dart_count]

/-- The actual graph retained after deleting the seven source core vertices,
with the original ordered boundary indices as its vertex names. -/
def exterior : SimpleGraph (Fin 11) := graph.comap (Fin.castAdd 7)

instance : DecidableRel exterior.Adj := fun _ _ => inferInstanceAs (Decidable (graph.Adj _ _))

def boundaryIndex (v : keep reading) : Fin 11 :=
  ⟨v.val.val, (keep_point reading v.val).mp v.property⟩

/-- This is the induced exterior, not just a graph with matching boundary edges. -/
def exteriorIso : exterior ≃g graph.induce (keep reading) where
  toFun := port reading
  invFun := boundaryIndex
  left_inv := fun _ => rfl
  right_inv := fun _ => Subtype.ext (Fin.ext rfl)
  map_rel_iff' := Iff.rfl

end FourColor.CoreProfileSwitchGeometry
