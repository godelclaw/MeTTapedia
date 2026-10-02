import MettapediaFourColor.D3009Colouring
import MettapediaFourColor.BoundaryTriangleRepair

/-!
# Six boundary collapses of one wheel

Removing the single outer fan vertex at any of the six degree-six rim
positions changes that rim degree to five. Reversing the operation is an
actual boundary-triangle subdivision, with the same D3009 source graph.
The complete source adjacency, cyclic orders and ordered boundary are
retained. The six targets are instances of one operation, not six repair
certificates. The original D3009 source and attribution are in D3009Wheel.
-/

namespace FourColor.TwoFiveWheelData

open NearLinearDiamondData
open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

set_option maxRecDepth 32768
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 4000000

local instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V) : DecidableRel (subdivide G a b c).Adj := fun x y => by
  cases x <;> cases y <;> dsimp [subdivide, removed] <;> infer_instance

def source : Fin 6 → String :=
  !["20 12\n13 7 14 20 19 18 17 15 16\n14 5 6 20 13 16 5\n15 6 2 3 16 13 17 1\n16 6 4 5 14 13 15 3\n17 6 1 15 13 18 11 12\n18 6 10 11 17 13 19 9\n19 6 8 9 18 13 20 7\n20 5 7 19 13 14 6\n",
    "20 12\n13 7 14 20 19 18 17 15 16\n14 5 6 20 13 16 5\n15 6 2 3 16 13 17 1\n16 6 4 5 14 13 15 3\n17 6 1 15 13 18 11 12\n18 6 10 11 17 13 19 9\n19 5 9 18 13 20 8\n20 6 7 8 19 13 14 6\n",
    "20 12\n13 7 14 20 19 18 17 15 16\n14 5 6 20 13 16 5\n15 6 2 3 16 13 17 1\n16 6 4 5 14 13 15 3\n17 6 1 15 13 18 11 12\n18 5 11 17 13 19 10\n19 6 9 10 18 13 20 8\n20 6 7 8 19 13 14 6\n",
    "20 12\n13 7 14 20 19 18 17 15 16\n14 5 6 20 13 16 5\n15 6 2 3 16 13 17 1\n16 6 4 5 14 13 15 3\n17 5 1 15 13 18 12\n18 6 11 12 17 13 19 10\n19 6 9 10 18 13 20 8\n20 6 7 8 19 13 14 6\n",
    "20 12\n13 7 14 20 19 18 17 15 16\n14 5 5 20 13 16 4\n15 5 2 16 13 17 1\n16 6 3 4 14 13 15 2\n17 6 1 15 13 18 11 12\n18 6 10 11 17 13 19 9\n19 6 8 9 18 13 20 7\n20 6 6 7 19 13 14 5\n",
    "20 12\n13 7 14 20 19 18 17 15 16\n14 5 5 20 13 16 4\n15 6 2 3 16 13 17 1\n16 5 4 14 13 15 3\n17 6 1 15 13 18 11 12\n18 6 10 11 17 13 19 9\n19 6 8 9 18 13 20 7\n20 6 6 7 19 13 14 5\n"]

def input (p : Fin 6) : Input 20 12 where
  source := source p
  valid := by revert p; decide +kernel

def cut : Fin 6 → Fin 13 := ![6,8,10,12,1,3]
def selected (p : Fin 6) : Fin 7 := ⟨p.val+1,by omega⟩
def left (p : Fin 6) : Fin 20 := ⟨(cut p).val-1,by have := (cut p).isLt; omega⟩
def right (p : Fin 6) : Fin 20 := ⟨(cut p).val % 12,by have := Nat.mod_lt (cut p).val (by decide : 0<12); omega⟩
def apex (p : Fin 6) : Fin 20 := (D3009Wheel.rim (selected p)).natAdd 12

def retained (p : Fin 6) (v : Fin 20) : Fin 21 :=
  ⟨if v.val < (cut p).val then v.val else v.val+1,by split <;> omega⟩

def project (p : Fin 6) (v : Fin 21) : Fin 20 :=
  ⟨if v.val < (cut p).val then v.val else v.val-1,by
    have := (cut p).isLt
    split <;> omega⟩

def expandVertex (p : Fin 6) (v : Option (Fin 20)) : Fin 21 :=
  v.elim ((cut p).castAdd 8) (retained p)
def collapseVertex (p : Fin 6) (v : Fin 21) : Option (Fin 20) :=
  if v = (cut p).castAdd 8 then none else some (project p v)

/-- The source is the subdivision of each smaller wheel, with all edges checked. -/
def insertion (p : Fin 6) :
    subdivide (input p).graph (left p) (right p) (apex p) ≃g D3009Wheel.input.graph where
  toEquiv := {
    toFun := expandVertex p
    invFun := collapseVertex p
    left_inv := by revert p; decide +kernel
    right_inv := by revert p; decide +kernel }
  map_rel_iff' := by revert p; decide +kernel

theorem triangle : ∀ p, (input p).graph.Adj (left p) (right p) ∧
    (input p).graph.Adj (left p) (apex p) ∧
    (input p).graph.Adj (right p) (apex p) := by decide +kernel

/-- The full target stars are reconstructed from the source by the same collapse. -/
def stars (p : Fin 6) (v : Fin 20) : List (Fin 20) :=
  (D3009Construction.stars (retained p v)).flatMap fun w =>
    if w = (cut p).castAdd 8 then
      if v = left p then [right p] else if v = right p then [left p] else []
    else [project p w]

theorem star_edges : ∀ (p : Fin 6) (v w : Fin 20),
    (input p).graph.Adj v w ↔ w ∈ stars p v := by decide +kernel

theorem core_stars : ∀ (p : Fin 6) (i : Fin 8),
    stars p (i.natAdd 12) = (input p).internalStar (i.natAdd 12) := by decide +kernel

theorem degrees : ∀ (p : Fin 6) (i : Fin 7),
    (stars p ((D3009Wheel.rim i).natAdd 12)).length =
      if i = 0 ∨ i = selected p then 5 else 6 := by decide +kernel

/-- Rotation transport includes the boundary vertices and the inserted vertex. -/
theorem rotation : ∀ (p : Fin 6) (v : Option (Fin 20)), ∃ shift : Fin 8,
    D3009Construction.stars (insertion p v) =
      ((ConfigurationFaceGraph.triangleStar (stars p) (left p) (right p) (apex p) v).map
        (insertion p)).rotate shift.val := by decide +kernel

def tail (p : Fin 6) : List (Fin 20) :=
  ((input p).boundary.rotate ((cut p).val-1)).drop 2

theorem tail_length : ∀ p, (tail p).length = 10 := by decide +kernel

theorem base_boundary : ∀ p,
    (input p).boundary.rotate ((cut p).val-1) = left p :: right p :: tail p := by
  decide +kernel

theorem source_boundary : ∀ p,
    ((BoundaryTriangleRepair.ports (left p) (right p) (tail p)).map (insertion p)).rotate
      (14-(cut p).val) = D3009Wheel.input.boundary := by decide +kernel

end FourColor.TwoFiveWheelData
