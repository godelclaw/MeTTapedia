import MettapediaFourColor.ThreeBlockDiskDeletion

/-! # A complete core reading supplied by a triangulated source cone

One new apex closes the source boundary. This small graph checks that the
uniform deletion contract is inhabited and that its boundary orientation
is compatible with the exact pinned source rows. No colouring is assumed.
-/

namespace FourColor.ThreeBlockDiskBoundary.Example

open SimpleGraph FiveTriangleCollapseObstruction

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def star (v : Fin 19) : List (Fin 19) :=
  if h : v.val < 11 then
    (fan ⟨v.val, h⟩).map Fin.castSucc ++ [18]
  else if h' : v.val < 18 then
    (upper.internalStar ⟨v.val, h'⟩).reverse.map Fin.castSucc
  else (List.finRange 11).map (Fin.castAdd 8)

private theorem symmetric : ∀ u v : Fin 19, v ∈ star u → u ∈ star v := by decide +kernel
private theorem loopless : ∀ v : Fin 19, v ∉ star v := by decide +kernel

def graph : SimpleGraph (Fin 19) where
  Adj u v := v ∈ star u
  symm := ⟨symmetric⟩
  loopless := ⟨loopless⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

def rows : GraphRotationRows.Rows graph :=
  ⟨star, by decide +kernel, fun _ _ => Iff.rfl⟩

def rotation := rows.rotation (⟨(0,1), by decide +kernel⟩ : graph.Dart)

theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _

theorem triangular : ExceptionalOverlap.Triangular rotation := by
  unfold ExceptionalOverlap.Triangular
  decide +kernel

def hom : upper.graph →g graph where
  toFun := Fin.castSucc
  map_rel' := by decide +kernel

theorem core_turn : ∀ i j k, Turn i j k →
    ExceptionalCoreOrientation.Corner rotation (hom i) (hom k) (hom j) := by
  have h : ∀ i j k : Fin 18, Turn i j k →
      graph.Adj (hom i) (hom k) ∧ graph.Adj (hom i) (hom j) ∧
        rows.next (hom i) (hom k) = hom j := by decide +kernel
  intro i j k ht
  obtain ⟨hik, hij, step⟩ := h i j k ht
  exact ⟨hik, hij, Dart.ext _ _ (Prod.ext rfl step)⟩

def reading : Reading rotation := ⟨hom, Fin.castSucc_injective 18, core_turn⟩

theorem deletion_boundary : IsCyclicChain
    (fun a b => b = (outsideRotation reading).toRotationSystem.phi a)
    (outsideRing reading) := outside_boundary reading triangular

theorem deletion_cyclic : (outsideRotation reading).IsVertexwiseCyclic :=
  outside_cyclic reading cyclic

end FourColor.ThreeBlockDiskBoundary.Example
