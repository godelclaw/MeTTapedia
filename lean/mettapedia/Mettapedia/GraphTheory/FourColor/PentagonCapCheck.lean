import Mettapedia.GraphTheory.FourColor.PresentedCap

/-! The pentagon cap on five ports passes the disc check: it is cubic with cyclic rotations,
connected, boundary-essential, and its hub closure is a sphere with distinct hub faces. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation.PresentedCap
namespace PentagonCap

/-- five vertices in a cycle, each with one port; at vertex `v` the slots are the edge to
`v + 1`, the port, the edge from `v - 1` -/
def pentagon : Pres 5 5 5 where
  tri v s := if s = 0 then Slot.edge v else if s = 1 then Slot.port v else Slot.edge (v - 1)
  endPos e b := if b then (e + 1, 2) else (e, 0)
  portPos i := (i, 1)

theorem valid : pentagon.Valid := by decide

theorem disc : pentagon.discCheck valid = true := by decide +kernel

end PentagonCap
end Mettapedia.GraphTheory.FourColor.KempeDerivation.PresentedCap
