import Mettapedia.GraphTheory.FourColor.PresentedEnum

/-!
# Two thickness-2 rungs, the second mirrored: the layer of a strip growing at both ends

Width 8.  No word table: the corridor bound comes from the tube-free
lemma; only the shape check is needed.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair2
open Presented Slot

def tri : Fin 12 → Fin 3 → Slot 10 8 := ![
  ![inp 0, out 0, edge 0],
  ![edge 0, edge 1, inp 1],
  ![edge 1, edge 2, out 1],
  ![edge 2, edge 3, inp 2],
  ![edge 3, edge 4, out 2],
  ![edge 4, inp 3, out 3],
  ![edge 5, out 4, inp 4],
  ![inp 5, edge 6, edge 5],
  ![out 5, edge 7, edge 6],
  ![inp 6, edge 8, edge 7],
  ![out 6, edge 9, edge 8],
  ![out 7, inp 7, edge 9]]

def endTab : Fin 10 → Pos 12 × Pos 12 := ![
  ((0, 2), (1, 0)),
  ((1, 1), (2, 0)),
  ((2, 1), (3, 0)),
  ((3, 1), (4, 0)),
  ((4, 1), (5, 0)),
  ((6, 0), (7, 2)),
  ((7, 1), (8, 2)),
  ((8, 1), (9, 2)),
  ((9, 1), (10, 2)),
  ((10, 1), (11, 2))]

def endPos (e : Fin 10) (b : Bool) : Pos 12 := if b then (endTab e).2 else (endTab e).1
def inPos : Fin 8 → Pos 12 := ![(0, 0), (1, 2), (3, 2), (5, 1), (6, 2), (7, 0), (9, 0), (11, 1)]
def outPos : Fin 8 → Pos 12 := ![(0, 1), (2, 2), (4, 2), (5, 2), (6, 1), (8, 0), (10, 0), (11, 0)]

def P : Pres 12 10 8 := ⟨tri, endPos, inPos, outPos⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid : P.Valid := by decide +kernel

def labTable : List Nat := [
]

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair2
