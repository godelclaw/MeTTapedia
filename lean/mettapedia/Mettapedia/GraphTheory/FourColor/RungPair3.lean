import Mettapedia.GraphTheory.FourColor.PresentedEnum

/-!
# Two thickness-3 rungs, the second mirrored: the layer of a strip growing at both ends

Width 10.  No word table: the corridor bound comes from the tube-free
lemma; only the shape check is needed.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair3
open Presented Slot

def tri : Fin 16 → Fin 3 → Slot 14 10 := ![
  ![inp 0, out 0, edge 0],
  ![edge 0, edge 1, inp 1],
  ![edge 1, edge 2, out 1],
  ![edge 2, edge 3, inp 2],
  ![edge 3, edge 4, out 2],
  ![edge 4, edge 5, inp 3],
  ![edge 5, edge 6, out 3],
  ![edge 6, inp 4, out 4],
  ![edge 7, out 5, inp 5],
  ![inp 6, edge 8, edge 7],
  ![out 6, edge 9, edge 8],
  ![inp 7, edge 10, edge 9],
  ![out 7, edge 11, edge 10],
  ![inp 8, edge 12, edge 11],
  ![out 8, edge 13, edge 12],
  ![out 9, inp 9, edge 13]]

def endTab : Fin 14 → Pos 16 × Pos 16 := ![
  ((0, 2), (1, 0)),
  ((1, 1), (2, 0)),
  ((2, 1), (3, 0)),
  ((3, 1), (4, 0)),
  ((4, 1), (5, 0)),
  ((5, 1), (6, 0)),
  ((6, 1), (7, 0)),
  ((8, 0), (9, 2)),
  ((9, 1), (10, 2)),
  ((10, 1), (11, 2)),
  ((11, 1), (12, 2)),
  ((12, 1), (13, 2)),
  ((13, 1), (14, 2)),
  ((14, 1), (15, 2))]

def endPos (e : Fin 14) (b : Bool) : Pos 16 := if b then (endTab e).2 else (endTab e).1
def inPos : Fin 10 → Pos 16 := ![(0, 0), (1, 2), (3, 2), (5, 2), (7, 1), (8, 2), (9, 0), (11, 0), (13, 0), (15, 1)]
def outPos : Fin 10 → Pos 16 := ![(0, 1), (2, 2), (4, 2), (6, 2), (7, 2), (8, 1), (10, 0), (12, 0), (14, 0), (15, 0)]

def P : Pres 16 14 10 := ⟨tri, endPos, inPos, outPos⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid : P.Valid := by decide +kernel

def labTable : List Nat := [
]

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair3
