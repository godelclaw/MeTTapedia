import MettapediaFourColor.NearLinearChainConstruction
import MettapediaFourColor.NearLinearChainRepair
import MettapediaFourColor.KempeRepairContract
import MettapediaFourColor.CompatibleTraces

/-!
# A nonempty contract for the transferred chain repair

The all-proper-trace repair of D0004 is transported to its exact constructed
disk. An internal singleton contraction supplies a concrete contract for
actual-map consumers; no new rank certificate is introduced.
-/

namespace FourColor.NearLinearChainContract

open NearLinearChainConstruction KempeBoundarySplit Hypermap

theorem ring_length : (cfring config).length = 8 := by
  change (cfmap config).cpring.reverse.length = 8
  rw [List.length_reverse]
  have h := congrArg List.length realization.ring
  rw [List.length_map, NearLinearChainConstruction.cpring] at h
  exact h

/-- The repair concludes with an actual colouring of the constructed map. -/
theorem repair : Repairs ((cfmap config).map.RingTrace (cfring config).reverse) 8 := by
  have source : Repairs (GraphTrace NearLinearChainData.input0004.graph boundary) 8 :=
    BoundaryRepairTransport.repairs (SimpleGraph.Iso.refl (G := NearLinearChainData.input0004.graph))
      boundary NearLinearChainData.boundary0004 2 (by decide +kernel)
      NearLinearChainRepair.repair0004
  intro et hlen hzero hsum outside closed initial
  obtain ⟨es, inside, compatible⟩ := source et hlen hzero hsum outside closed initial
  exact ⟨es, (ringTrace_iff es).mpr inside, compatible⟩

/-- All valid contracts share the same finite D-repair theorem. -/
theorem reducible {cc : List (cfmap config).Dart}
    (valid : (cfmap config).map.ValidContract (cfring config) cc) :
    (cfmap config).map.CReducible (cfring config) cc := by
  apply KempeRepairContract.reducible_of_repair embeddable.base.base.base.cycle valid
  rw [ring_length]
  exact repair

/-- An interior edge between source core vertices 8 and 9. -/
def contractDart : (cfmap config).Dart := realization.numbering.symm 28

theorem contract_endpoints :
    (vertex (realization.numbering contractDart),
      vertex (realization.numbering ((cfmap config).map.edge contractDart))) =
      (8, 9) := by
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
    rw [List.map_reverse, realization.ring, NearLinearChainConstruction.cpring]
  have edge (d : (cfmap config).Dart) :
      realization.numbering ((cfmap config).map.edge d) =
        table.map.edge (realization.numbering d) := by
    rw [← realization.map_eq, Hypermap.relabel_edge]
  apply KempeRepairContract.valid_singleton
  · intro h
    have hm := List.mem_map_of_mem (f := realization.numbering) h
    rw [ringMap] at hm
    have hn : (28 : Fin 56) ∉ ring.reverse := by decide +kernel
    exact hn (by simpa [contractDart] using hm)
  · intro h
    have hm := List.mem_map_of_mem (f := realization.numbering) h
    rw [ringMap, edge] at hm
    have hn : table.map.edge (28 : Fin 56) ∉ ring.reverse := by decide +kernel
    exact hn (by simpa [contractDart] using hm)
  · intro h
    have hn : ¬ table.map.CNode (28 : Fin 56) (table.map.edge 28) := by
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

end FourColor.NearLinearChainContract
