import Mettapedia.GraphTheory.FourColor.PresentedEnum

/-!
# The thickness-1 rung as a presented slab shape

Path `c, d1, e1, …, d1, e1, c'` of width 3: in-ports at `c`, the `d`s and `c'`,
out-ports at `c`, the `e`s and `c'`.  `labTable` is the enumerator's table as
computed by the lab, re-derived word by word in the kernel.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungThick1
open Presented Slot

def tri : Fin 4 → Fin 3 → Slot 3 3 := ![
  ![inp 0, out 0, edge 0],
  ![edge 0, edge 1, inp 1],
  ![edge 1, edge 2, out 1],
  ![edge 2, inp 2, out 2]]

def endTab : Fin 3 → Pos 4 × Pos 4 := ![
  ((0, 2), (1, 0)),
  ((1, 1), (2, 0)),
  ((2, 1), (3, 0))]

def endPos (e : Fin 3) (b : Bool) : Pos 4 := if b then (endTab e).2 else (endTab e).1
def inPos : Fin 3 → Pos 4 := ![(0, 0), (1, 2), (3, 1)]
def outPos : Fin 3 → Pos 4 := ![(0, 1), (2, 2), (3, 2)]

def P : Pres 4 3 3 := ⟨tri, endPos, inPos, outPos⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid : P.Valid := by decide +kernel

def labTable : List Nat := [
  1049600,
  512,
  262144,
  33562624,
  17829888,
  524288,
  67125248,
  2048,
  16782336,
  41943042,
  16777217,
  2097152,
  16,
  8388616,
  4194304,
  32,
  67108868,
  33554442,
  81924,
  32768,
  4097,
  128,
  16452,
  8194,
  256,
  131072,
  65600]

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungThick1
