import MettapediaFourColor.InducedGraphRotation
import MettapediaFourColor.ThreeBlockGeometry
import MettapediaFourColor.ExceptionalCoreOrientation

/-!
# The D0092 boundary after deleting its core

Complete cyclic core readings and triangular ambient faces determine the
source's inner faces and the short deleted fan at every boundary vertex.
No bound on the ambient graph is imposed. The source is the pinned D0092
input of `FiveTriangleCollapseObstruction`, with attribution retained there.
-/

namespace FourColor.ThreeBlockDiskBoundary

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open FiveTriangleCollapseObstruction ExceptionalCoreOrientation ExceptionalOverlap
open GoertzelV24OrderedCutFaceReturnProfile PermutationFirstReturnRestriction

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def faces : List (Fin 18 × Fin 18 × Fin 18) :=
  [(0,1,17), (0,17,10), (1,2,15), (1,15,17), (2,3,15), (3,4,12),
   (3,12,15), (4,5,12), (5,6,13), (5,13,12), (6,7,13), (7,8,14),
   (7,14,13), (8,9,16), (8,11,14), (8,16,11), (9,10,16),
   (10,17,16), (11,12,14), (11,15,12), (11,16,17), (11,17,15), (12,13,14)]

def Turn (i j k : Fin 18) : Prop :=
  11 ≤ i.val ∧ (j.val + 1, k.val + 1) ∈
    (upper.neighbors i).zip ((upper.neighbors i).rotate 1)

instance (i j k) : Decidable (Turn i j k) := inferInstanceAs (Decidable (_ ∧ _))

def Face (a b c : Fin 18) : Prop :=
  (a,b,c) ∈ faces ∨ (b,c,a) ∈ faces ∨ (c,a,b) ∈ faces

instance (a b c) : Decidable (Face a b c) := inferInstanceAs (Decidable (_ ∨ _))

theorem face_turn : ∀ t ∈ faces,
    Turn t.1 t.2.1 t.2.2 ∨ Turn t.2.1 t.2.2 t.1 ∨ Turn t.2.2 t.1 t.2.1 := by
  have h : faces.all (fun t => decide
    (Turn t.1 t.2.1 t.2.2 ∨ Turn t.2.1 t.2.2 t.1 ∨ Turn t.2.2 t.1 t.2.1)) = true := by
    decide +kernel
  exact fun t ht => of_decide_eq_true (List.all_eq_true.mp h t ht)

def fan (j : Fin 11) : List (Fin 18) :=
  match j.val with
  | 0 => [10,17,1]
  | 1 => [0,17,15,2]
  | 2 => [1,15,3]
  | 3 => [2,15,12,4]
  | 4 => [3,12,5]
  | 5 => [4,12,13,6]
  | 6 => [5,13,7]
  | 7 => [6,13,14,8]
  | 8 => [7,14,11,16,9]
  | 9 => [8,16,10]
  | _ => [9,16,17,0]

theorem fan_chain : ∀ j, (fan j).IsChain (fun b c => Face (j.castAdd 7) c b) := by
  decide +kernel

theorem fan_size : ∀ j, 3 ≤ (fan j).length := by decide +kernel

theorem fan_adjacent : ∀ j (i : Fin (fan j).length),
    upper.graph.Adj (j.castAdd 7) ((fan j).get i) := by decide +kernel

theorem fan_first : ∀ j, (fan j).get ⟨0, by have := fan_size j; omega⟩ =
    (j - 1).castAdd 7 := by decide +kernel

theorem fan_last : ∀ j, (fan j).get
    ⟨(fan j).length - 1, by have := fan_size j; omega⟩ = (j + 1).castAdd 7 := by
  decide +kernel

theorem fan_internal : ∀ j (i : Fin (fan j).length),
    0 < i.val → i.val + 1 < (fan j).length → 11 ≤ ((fan j).get i).val := by
  decide +kernel

theorem boundary_adjacent : ∀ j : Fin 11,
    upper.graph.Adj (j.castAdd 7) ((j + 1).castAdd 7) := by decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (data : Data G)

/-- Cyclic core rows are read in the orientation whose ordered boundary
is the forward source port order. This contains no deletion conclusion. -/
structure Reading where
  hom : upper.graph →g G
  injective : Function.Injective hom
  turn : ∀ i j k, Turn i j k → Corner data (hom i) (hom k) (hom j)

variable {data} (r : Reading data) (tri : Triangular data)

include tri

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem corner_of_mem {a b c : Fin 18} (h : (a,b,c) ∈ faces) :
    Corner data (r.hom a) (r.hom c) (r.hom b) := by
  rcases face_turn _ h with h | h | h
  · exact r.turn _ _ _ h
  · exact (r.turn _ _ _ h).rotate data tri
  · exact ((r.turn _ _ _ h).rotate data tri).rotate data tri

theorem corner {a b c : Fin 18} (h : Face a b c) :
    Corner data (r.hom a) (r.hom c) (r.hom b) := by
  rcases h with h | h | h
  · exact corner_of_mem r tri h
  · exact (corner_of_mem r tri h).rotate data tri
  · exact ((corner_of_mem r tri h).rotate data tri).rotate data tri

/-- Every triangle used by the existing geometric repair contract is supplied
by the same complete core reading. -/
def patch : ThreeBlockGeometry.Patch data where
  point := r.hom
  injective := r.injective
  adjacent := fun _ _ h => r.hom.map_rel h
  facial a b c h := by
    have hf : Face a b c := by
      have included : ∀ a b c, (a,b,c) ∈ ThreeBlockGeometry.triangles → Face a b c := by
        decide +kernel
      exact included a b c h
    obtain ⟨ac, ab, ha⟩ := corner r tri hf
    obtain ⟨ba, bc, hb⟩ := (corner r tri hf).rotate data tri |>.rotate data tri
    obtain ⟨cb, ca, hc⟩ := (corner r tri hf).rotate data tri
    exact ⟨ab, bc, ca, hb, hc, ha⟩

end FourColor.ThreeBlockDiskBoundary
