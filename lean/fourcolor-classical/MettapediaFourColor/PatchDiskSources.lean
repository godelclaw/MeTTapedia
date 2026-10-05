import MettapediaFourColor.PatchDiskSource
import MettapediaFourColor.ThreeBlockRemainingFaces
import MettapediaFourColor.ThreeBlockDeletionCount
import MettapediaFourColor.StripCyclicReading

/-! # Two decoded sources for the common disk-deletion law

D0092 and D0099 satisfy the same local contract. The source rows and their
attribution are inherited from the pinned decoders. These finite checks
concern incidence, cyclic order and dart counts; no colourings are stored.
-/

namespace FourColor.PatchDiskSources

open SimpleGraph PatchDisk FiveTriangleCollapseObstruction TriangleStripAnchors
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation ExceptionalCoreOrientation

set_option maxRecDepth 10000

private theorem core_darts (N b : ℕ) (P : SimpleGraph (Fin N)) [DecidableRel P.Adj] :
    Nat.card {d : P.Dart // b ≤ d.fst.val ∨ b ≤ d.snd.val} =
    Fintype.card {p : Fin N × Fin N // P.Adj p.1 p.2 ∧ (b ≤ p.1.val ∨ b ≤ p.2.val)} := by
  let e : {d : P.Dart // b ≤ d.fst.val ∨ b ≤ d.snd.val} ≃
      {p : Fin N × Fin N // P.Adj p.1 p.2 ∧ (b ≤ p.1.val ∨ b ≤ p.2.val)} :=
    { toFun := fun d => ⟨d.val.toProd, d.val.adj, d.property⟩
      invFun := fun p => ⟨⟨p.val, p.property.1⟩, p.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_eq_fintype_card)

set_option maxHeartbeats 2000000 in
-- Check all source fan incidences and cyclic turns against the decoded rows.
def d0092 : Source 7 11 where
  graph := upper.graph
  decAdj := inferInstance
  boundary_size := by decide
  core_size := by decide
  turn := ThreeBlockDiskBoundary.Turn
  core_nonempty := ThreeBlockDiskBoundary.core_nonempty
  core_predecessor := ThreeBlockDiskBoundary.core_predecessor
  core_boundary_turn := ThreeBlockDiskBoundary.core_boundary_turn
  fan := ThreeBlockDiskBoundary.fan
  fan_size := ThreeBlockDiskBoundary.fan_size
  fan_adjacent := ThreeBlockDiskBoundary.fan_adjacent
  fan_first := ThreeBlockDiskBoundary.fan_first
  fan_last := ThreeBlockDiskBoundary.fan_last
  fan_internal := ThreeBlockDiskBoundary.fan_internal
  fan_chain := by decide +kernel
  boundary_adjacent := ThreeBlockDiskBoundary.boundary_adjacent
  tip := ![17,15,15,12,12,13,13,14,16,16,17]
  tip_core := by decide +kernel
  tip_adjacent := by decide +kernel
  tip_turn := by decide +kernel
  core_dart_count := by rw [ThreeBlockDiskBoundary.core_dart_count]

def fan0099 (j : Fin 11) : List (Fin 19) :=
  match j.val with
  | 0 => [10,18,1]
  | 1 => [0,18,16,2]
  | 2 => [1,16,3]
  | 3 => [2,16,13,4]
  | 4 => [3,13,14,5]
  | 5 => [4,14,6]
  | 6 => [5,14,11,7]
  | 7 => [6,11,8]
  | 8 => [7,11,12,15,9]
  | 9 => [8,15,17,10]
  | _ => [9,17,18,0]

set_option maxHeartbeats 2000000 in
-- Check all source fan incidences and cyclic turns against the decoded rows.
def d0099 : Source 8 11 where
  graph := input0099.graph
  decAdj := inferInstance
  boundary_size := by decide
  core_size := by decide
  turn := StripCyclicReading.Turn
  core_nonempty := StripCyclicReading.core_nonempty
  core_predecessor := StripCyclicReading.core_predecessor
  core_boundary_turn := by decide +kernel
  fan := fan0099
  fan_size := by decide +kernel
  fan_adjacent := by decide +kernel
  fan_first := by decide +kernel
  fan_last := by decide +kernel
  fan_internal := by decide +kernel
  fan_chain := by decide +kernel
  boundary_adjacent := by decide +kernel
  tip := ![18,16,16,13,14,14,11,11,15,17,18]
  tip_core := by decide +kernel
  tip_adjacent := by decide +kernel
  tip_turn := by decide +kernel
  core_dart_count := by
    rw [core_darts, Fintype.card_subtype]
    decide +kernel

variable {V : Type*} {G : SimpleGraph V} {data : Data G}

def of_d0092 (r : ThreeBlockDiskBoundary.Reading data) : Reading d0092 data where
  hom := r.hom
  core_injective := r.injective.injOn
  no_capture a ha := by
    rintro ⟨i,hi,eq⟩
    exact ha (r.injective eq ▸ hi)
  local_injective _ _ := r.injective.injOn
  turn := r.turn

/-- The actual prescribed degrees supply local injectivity; boundary
injectivity is not required by this adapter. -/
def of_d0099 [Fintype V] [DecidableRel G.Adj]
    (r : StripCyclicReading.Reading data) (cyclic : data.IsVertexwiseCyclic)
    (injective : Set.InjOn r.hom {i : Fin 19 | 11 ≤ i.val})
    (no_capture : ∀ a : Fin 19, ¬11 ≤ a.val → r.hom a ∉ r.hom '' {i | 11 ≤ i.val})
    (degree : ∀ i : Fin 19, 11 ≤ i.val → G.degree (r.hom i) = input0099.graph.degree i) :
    Reading d0099 data where
  hom := r.hom
  core_injective := injective
  no_capture := no_capture
  local_injective i hi := neighbours_injective (s := d0099) r.hom r.turn cyclic i hi (degree i hi)
  turn := r.turn

end FourColor.PatchDiskSources
