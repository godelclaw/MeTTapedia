import MettapediaFourColor.ResidualExteriorDiskData

/-! # Finite adjacency and spanning-tour checks for the exterior rows -/

namespace FourColor.ResidualExteriorDisk
open SimpleGraph KempeDetachExample
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem row_nodup : ∀ u, (star u).Nodup := by decide +kernel

theorem forward_check : ∀ u, (star u).all (fun v => decide (graph.Adj u v)) = true := by
  decide +kernel

theorem reverse_check : edges.all (fun e => decide (e.2 ∈ star e.1 ∧ e.1 ∈ star e.2)) = true := by
  decide +kernel

theorem tour_chain : tour.IsChain graph.Adj := by decide +kernel
theorem tour_covers : ∀ v : Fin 155, v ∈ tour := by decide +kernel

theorem row_nonempty : ∀ v, star v ≠ [] := by decide +kernel

end FourColor.ResidualExteriorDisk
