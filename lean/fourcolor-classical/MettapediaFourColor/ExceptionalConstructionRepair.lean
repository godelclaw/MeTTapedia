import MettapediaFourColor.ExceptionalConstruction
import MettapediaFourColor.ExceptionalRepairChecked
import MettapediaFourColor.KempeRepairContract
import MettapediaFourColor.CompatibleTraces

/-!
# The exceptional source repair in the reference embedding interface

The exact source construction transports the checked joint-chord repair to
actual configuration-map colourings. Every valid contraction can use that
repair. The final consumer reuses the reference exterior-closure and patch
reconstruction theorems; its ambient preembedding and contract colouring
remain explicit inputs.
-/

namespace FourColor.ExceptionalConstructionRepair

open ExceptionalConstruction KempeBoundarySplit Hypermap

theorem ring_length : (cfring config).length = 11 := by
  change (cfmap config).cpring.reverse.length = 11
  rw [List.length_reverse]
  have h := congrArg List.length realization.ring
  rw [List.length_map, ExceptionalConstruction.cpring] at h
  exact h

/-- The repair concludes with an actual colouring of the constructed map. -/
theorem repair : Repairs ((cfmap config).map.RingTrace (cfring config).reverse) 11 := by
  intro et hlen hzero hsum outside closed initial
  obtain ⟨es, inside, compatible⟩ :=
    ExceptionalRepairCertificate.repair et hlen hzero hsum outside closed initial
  exact ⟨es, (ringTrace_iff es).mpr inside, compatible⟩

/-- All valid contracts share the same finite D-repair theorem. -/
theorem reducible {cc : List (cfmap config).Dart}
    (valid : (cfmap config).map.ValidContract (cfring config) cc) :
    (cfmap config).map.CReducible (cfring config) cc := by
  apply KempeRepairContract.reducible_of_repair embeddable.base.base.base.cycle valid
  rw [ring_length]
  exact repair

/-- An interior edge between source core vertices 13 and 14. -/
def contractDart : (cfmap config).Dart := realization.numbering.symm 28

theorem contract_endpoints :
    (vertex (realization.numbering contractDart),
      vertex (realization.numbering ((cfmap config).map.edge contractDart))) =
      (13, 14) := by
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
    rw [List.map_reverse, realization.ring, ExceptionalConstruction.cpring]
  have edge (d : (cfmap config).Dart) :
      realization.numbering ((cfmap config).map.edge d) =
        table.map.edge (realization.numbering d) := by
    rw [← realization.map_eq, Hypermap.relabel_edge]
  apply KempeRepairContract.valid_singleton
  · intro h
    have hm := List.mem_map_of_mem (f := realization.numbering) h
    rw [ringMap] at hm
    have hn : (28 : Fin 86) ∉ ring.reverse := by decide +kernel
    exact hn (by simpa [contractDart] using hm)
  · intro h
    have hm := List.mem_map_of_mem (f := realization.numbering) h
    rw [ringMap, edge] at hm
    have hn : table.map.edge (28 : Fin 86) ∉ ring.reverse := by decide +kernel
    exact hn (by simpa [contractDart] using hm)
  · intro h
    have hn : ¬ table.map.CNode (28 : Fin 86) (table.map.edge 28) := by
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

variable {Dm : Type*} [Finite Dm] {Gm : Hypermap Dm}
  {h : (cfmap config).Dart → Dm} {cc : List (cfmap config).Dart}

/-- A genuine preembedding and a contract colouring discharge exterior closure
through the existing embedding theorem, retaining actual witnesses. -/
theorem colorable_of_contract
    (planar : Gm.Planar) (plain : Gm.Plain) (bridgeless : Gm.Bridgeless)
    (connected : Gm.Connected) (cubic : Gm.Cubic)
    (birkhoff : Gm.BirkhoffRings) (pentagonal : Gm.Pentagonal)
    (pre : Preembedding (cfmap config).map Gm h
      {z | (cfmap config).map.Kernel (cfring config) z})
    (valid : (cfmap config).map.ValidContract (cfring config) cc)
    {k : Dm → Color}
    (hk : Gm.CcColoring (cc.map (embed (cfmap config).map Gm (cfring config) h)) k) :
    Gm.FourColorable :=
  colorable_of_contractColoring embeddable planar plain bridgeless connected cubic
    birkhoff pentagonal pre (reducible valid) hk

/-- The exact constructed source cannot preembed in a reference minimal
counterexample. Producing that preembedding from the two exceptional
occurrences is the remaining representation bridge. -/
theorem not_preembedding (minimal : Gm.MinimalCounterExample)
    (pre : Preembedding (cfmap config).map Gm h
      {z | (cfmap config).map.Kernel (cfring config) z}) : False :=
  not_embed_reducible embeddable minimal pre singleton_reducible

/-- The compiled local degree query is sufficient: its established compiler
constructs the preembedding, so consumers need only prove the actual query
fits their retained geometric reading. -/
theorem not_fitted (minimal : Gm.MinimalCounterExample) (d : Dm)
    (fit : Gm.Fitqz d (cfquiz config)) : False := by
  obtain ⟨root, validQuiz⟩ := valid_cfquiz quiz_right
  exact not_preembedding minimal
    (quiz_preembedding minimal.plain minimal.cubic
      embeddable.base.base.base.base.plain
      embeddable.base.base.base.base.quasicubic validQuiz fit)

end FourColor.ExceptionalConstructionRepair
