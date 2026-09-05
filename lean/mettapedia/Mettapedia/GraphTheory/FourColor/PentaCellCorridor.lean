import Mettapedia.GraphTheory.FourColor.PentaCellTable
import Mettapedia.GraphTheory.FourColor.PentaCellShape

/-! No long `PentaCell` tube in a least counterexample. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.PentaCell

open Presented Pres TubeRingOrbit ZigzagRing
open GoertzelV24TwoEdgeCutMinimality GoertzelV24ConnectedEdgeShoreMajority

/-- **the abstract stabilisation hypothesis at index 4, period 1** -/
theorem hstab (W : Set (Fin 6 → Color)) :
    (relImage (P.toTangle valid))^[4 + 1] W = (relImage (P.toTangle valid))^[4] W :=
  P.hstab_of_stabilizesAt valid stabilizes (by norm_num) W

variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
variable {rotation : SimpleGraphDartRotation.Data G}

/-- **No long `PentaCell` tube in a least counterexample.** -/
theorem le_of_tube (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {inner : V → Prop} {n : Nat}
    (t : TubeOf rotation.toRotationSystem (P.toTangle valid) inner n) (hc : t.Coherent)
    (hgood : GoodSide (G := G) inner) (hconn : EdgeShoreConnected G (sideShore inner))
    (hcconn : EdgeShoreConnected G (ZigzagSlab.compShore (t.side n))) :
    n ≤ 19180803 := by
  have := TubeOf.le_of_tubeOf shape minimal hstab (by norm_num) t hc hgood hconn hcconn
  norm_num [Nat.factorial] at this
  omega

end Mettapedia.GraphTheory.FourColor.TubeSlab.PentaCell
