import Mettapedia.GraphTheory.FourColor.PresentedEnum

/-!
# Two thickness-1 rungs, the second mirrored: the layer of a strip growing at both ends

Width 6.  No word table: the corridor bound comes from the tube-free
lemma; only the shape check is needed.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair1
open Presented Slot

def tri : Fin 8 → Fin 3 → Slot 6 6 := ![
  ![inp 0, out 0, edge 0],
  ![edge 0, edge 1, inp 1],
  ![edge 1, edge 2, out 1],
  ![edge 2, inp 2, out 2],
  ![edge 3, out 3, inp 3],
  ![inp 4, edge 4, edge 3],
  ![out 4, edge 5, edge 4],
  ![out 5, inp 5, edge 5]]

def endTab : Fin 6 → Pos 8 × Pos 8 := ![
  ((0, 2), (1, 0)),
  ((1, 1), (2, 0)),
  ((2, 1), (3, 0)),
  ((4, 0), (5, 2)),
  ((5, 1), (6, 2)),
  ((6, 1), (7, 2))]

def endPos (e : Fin 6) (b : Bool) : Pos 8 := if b then (endTab e).2 else (endTab e).1
def inPos : Fin 6 → Pos 8 := ![(0, 0), (1, 2), (3, 1), (4, 2), (5, 0), (7, 1)]
def outPos : Fin 6 → Pos 8 := ![(0, 1), (2, 2), (3, 2), (4, 1), (6, 0), (7, 0)]

def P : Pres 8 6 6 := ⟨tri, endPos, inPos, outPos⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid : P.Valid := by decide +kernel

def labTable : List Nat := [
]

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair1
