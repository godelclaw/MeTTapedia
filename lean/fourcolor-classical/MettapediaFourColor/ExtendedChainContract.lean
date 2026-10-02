import MettapediaFourColor.ExtendedChainOccurrence
import MettapediaFourColor.NearLinearChainRepair
import MettapediaFourColor.KempeRepairContract
import MettapediaFourColor.CompatibleTraces

/-!
# A nonempty contract for the transferred chain repair

The existing all-proper-trace repair of D0006 applies to its exact
constructed disk. An internal singleton contraction supplies a concrete contract for
actual-map consumers; no new rank certificate is introduced.
-/

namespace FourColor.ExtendedChainContract

open ExtendedChainOccurrence KempeBoundarySplit Hypermap

theorem ring_length : (cfring config).length = 9 := by
  change (cfmap config).cpring.reverse.length = 9
  rw [List.length_reverse]
  have h := congrArg List.length realization.ring
  rw [List.length_map, NearLinearChainData.cpring007] at h
  exact h

/-- The existing configuration-7 repair covers all proper nine-port traces. -/
theorem repair : Repairs ((cfmap config).map.RingTrace (cfring config).reverse) 9 :=
  NearLinearChainRepair.reference_repair

/-- All valid contracts share the same finite D-repair theorem. -/
theorem reducible {cc : List (cfmap config).Dart}
    (valid : (cfmap config).map.ValidContract (cfring config) cc) :
    (cfmap config).map.CReducible (cfring config) cc := by
  apply KempeRepairContract.reducible_of_repair embeddable.base.base.base.cycle valid
  rw [ring_length]
  exact repair

/-- An interior edge between source core vertices 10 and 9. -/
def contractDart : (cfmap config).Dart := realization.numbering.symm 46

theorem contract_endpoints :
    (vertex (realization.numbering contractDart),
      vertex (realization.numbering ((cfmap config).map.edge contractDart))) =
      (10, 9) := by
  have edge (d : (cfmap config).Dart) :
      realization.numbering ((cfmap config).map.edge d) =
        table.map.edge (realization.numbering d) := by
    rw [← realization.map_eq, Hypermap.relabel_edge]
  rw [edge]
  simp only [contractDart, Equiv.apply_symm_apply]
  decide +kernel

/-- The repair has a concrete nonempty contract, not just a conditional
consumer for contracts that might not exist. -/
theorem valid_contract :
    (cfmap config).map.ValidContract (cfring config) [contractDart] := by
  have ringMap : (cfring config).map realization.numbering = ring.reverse := by
    change ((cfmap config).cpring.reverse).map realization.numbering = _
    rw [List.map_reverse, realization.ring, NearLinearChainData.cpring007]
  have edge (d : (cfmap config).Dart) :
      realization.numbering ((cfmap config).map.edge d) =
        table.map.edge (realization.numbering d) := by
    rw [← realization.map_eq, Hypermap.relabel_edge]
  apply KempeRepairContract.valid_singleton
  · intro h
    have hm := List.mem_map_of_mem (f := realization.numbering) h
    rw [ringMap] at hm
    have hn : (46 : Fin 60) ∉ ring.reverse := by decide +kernel
    exact hn (by simpa [contractDart] using hm)
  · intro h
    have hm := List.mem_map_of_mem (f := realization.numbering) h
    rw [ringMap, edge] at hm
    have hn : table.map.edge (46 : Fin 60) ∉ ring.reverse := by decide +kernel
    exact hn (by simpa [contractDart] using hm)
  · intro h
    have hn : ¬ table.map.CNode (46 : Fin 60) (table.map.edge 46) := by
      decide +kernel
    apply hn
    have ht := (Hypermap.sameCycle_relabel realization.numbering
      (cfmap config).map.node contractDart ((cfmap config).map.edge contractDart)).mpr h
    change ((cfmap config).map.relabel realization.numbering).CNode
      (realization.numbering contractDart)
      (realization.numbering ((cfmap config).map.edge contractDart)) at ht
    rw [realization.map_eq, edge] at ht
    simpa [contractDart] using ht

theorem singleton_reducible :
    (cfmap config).map.CReducible (cfring config) [contractDart] :=
  reducible valid_contract

end FourColor.ExtendedChainContract
