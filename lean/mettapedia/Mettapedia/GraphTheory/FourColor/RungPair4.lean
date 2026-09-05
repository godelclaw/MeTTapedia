import Mettapedia.GraphTheory.FourColor.PresentedEnum

/-!
# Two thickness-4 rungs, the second mirrored: the layer of a strip growing at both ends

Width 12.  No word table: the corridor bound comes from the tube-free
lemma; only the shape check is needed.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair4
open Presented Slot

def tri : Fin 20 → Fin 3 → Slot 18 12 := ![
  ![inp 0, out 0, edge 0],
  ![edge 0, edge 1, inp 1],
  ![edge 1, edge 2, out 1],
  ![edge 2, edge 3, inp 2],
  ![edge 3, edge 4, out 2],
  ![edge 4, edge 5, inp 3],
  ![edge 5, edge 6, out 3],
  ![edge 6, edge 7, inp 4],
  ![edge 7, edge 8, out 4],
  ![edge 8, inp 5, out 5],
  ![edge 9, out 6, inp 6],
  ![inp 7, edge 10, edge 9],
  ![out 7, edge 11, edge 10],
  ![inp 8, edge 12, edge 11],
  ![out 8, edge 13, edge 12],
  ![inp 9, edge 14, edge 13],
  ![out 9, edge 15, edge 14],
  ![inp 10, edge 16, edge 15],
  ![out 10, edge 17, edge 16],
  ![out 11, inp 11, edge 17]]

def endTab : Fin 18 → Pos 20 × Pos 20 := ![
  ((0, 2), (1, 0)),
  ((1, 1), (2, 0)),
  ((2, 1), (3, 0)),
  ((3, 1), (4, 0)),
  ((4, 1), (5, 0)),
  ((5, 1), (6, 0)),
  ((6, 1), (7, 0)),
  ((7, 1), (8, 0)),
  ((8, 1), (9, 0)),
  ((10, 0), (11, 2)),
  ((11, 1), (12, 2)),
  ((12, 1), (13, 2)),
  ((13, 1), (14, 2)),
  ((14, 1), (15, 2)),
  ((15, 1), (16, 2)),
  ((16, 1), (17, 2)),
  ((17, 1), (18, 2)),
  ((18, 1), (19, 2))]

def endPos (e : Fin 18) (b : Bool) : Pos 20 := if b then (endTab e).2 else (endTab e).1
def inPos : Fin 12 → Pos 20 := ![(0, 0), (1, 2), (3, 2), (5, 2), (7, 2), (9, 1), (10, 2), (11, 0), (13, 0), (15, 0), (17, 0), (19, 1)]
def outPos : Fin 12 → Pos 20 := ![(0, 1), (2, 2), (4, 2), (6, 2), (8, 2), (9, 2), (10, 1), (12, 0), (14, 0), (16, 0), (18, 0), (19, 0)]

def P : Pres 20 18 12 := ⟨tri, endPos, inPos, outPos⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid : P.Valid := by decide +kernel

def labTable : List Nat := [
]

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair4
