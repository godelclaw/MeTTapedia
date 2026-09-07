import Mettapedia.GraphTheory.FourColor.MeshRegionOrderData
import Mettapedia.GraphTheory.FourColor.GoertzelV24MeshIsoperimetry
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! # The finite ambient graph of the region-ordering obstruction -/

namespace Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction

open SimpleGraph GoertzelV24BoundaryEssentialGluing GoertzelV24MeshIsoperimetry
open MeshRegionOrderData

set_option maxRecDepth 100000

def vertex (n : Nat) : Fin 180 := ⟨n % 180, Nat.mod_lt _ (by decide)⟩
def edge (n : Nat) : Fin 270 := ⟨n % 270, Nat.mod_lt _ (by decide)⟩

def ambient : Multigraph (Fin 180) (Fin 270) where
  fst e := vertex (edgeNumbers.getD (2 * e.val) 0)
  snd e := vertex (edgeNumbers.getD (2 * e.val + 1) 0)

theorem edges_increasing : ∀ e, ambient.fst e < ambient.snd e := by decide +kernel
theorem edge_pairs_nodup : (List.ofFn fun e => (ambient.fst e, ambient.snd e)).Nodup := by
  decide +kernel
theorem ambient_cubic : ∀ v : Fin 180,
    (Finset.univ.filter fun e => ambient.fst e = v ∨ ambient.snd e = v).card = 3 := by
  decide +kernel

def graph : SimpleGraph (Fin 180) where
  Adj u v := ∃ e, (ambient.fst e = u ∧ ambient.snd e = v) ∨
    (ambient.fst e = v ∧ ambient.snd e = u)
  symm := ⟨by rintro u v ⟨e, h⟩; exact ⟨e, h.symm⟩⟩
  loopless := ⟨by
    rintro v ⟨e, h | h⟩ <;>
      exact (ne_of_lt (edges_increasing e)) (h.1.trans h.2.symm)⟩

end Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
