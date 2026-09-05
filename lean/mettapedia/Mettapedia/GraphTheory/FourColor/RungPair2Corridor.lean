import Mettapedia.GraphTheory.FourColor.GeneralTubeAny
import Mettapedia.GraphTheory.FourColor.RungPair2Shape

/-! No long `RungPair2` chain in a least counterexample, from the tube-free lemma. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair2

open Presented Pres
open GoertzelV24TwoEdgeCutMinimality GoertzelV24ConnectedEdgeShoreMajority

variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
variable {rotation : SimpleGraphDartRotation.Data G}

/-- **No long `RungPair2` chain in a least counterexample.** -/
theorem le_of_tube (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {inner : V → Prop} {n : Nat}
    (t : TubeOf rotation.toRotationSystem (P.toTangle valid) inner n)
    (hgood : GoodSide (G := G) inner) (hconn : EdgeShoreConnected G (sideShore inner))
    (hcconn : EdgeShoreConnected G (ZigzagSlab.compShore (t.side n))) :
    n + 1 ≤ Nat.factorial 8 * (Nat.factorial 8 * (6 * 8 + 1)) * 2 ^ (4 ^ 8) :=
  TubeOf.le_of_tubeOf_any shapeW minimal (by norm_num) t hgood hconn hcconn

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair2
