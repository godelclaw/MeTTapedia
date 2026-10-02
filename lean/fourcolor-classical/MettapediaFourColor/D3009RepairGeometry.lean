import MettapediaFourColor.D3009Preembedding
import MettapediaFourColor.KempeRepairContract
import MettapediaFourColor.InjectiveEmbeddedRepair
import MettapediaFourColor.ActualWheelOccurrence

/-!
# Geometric consumers of the thirteen-port wheel repair contract

The same recognised wheel supplies an injective disk and a valid singleton
contract. Vertex minimality supplies the initial colouring through a strict
two-vertex reduction. A repair law for the entire joint boundary relation
then reconstructs an ordinary colouring of the ambient map.

The all-input repair law is an explicit hypothesis in this module. It is
separate from the geometric proof and can be supplied by a checked finite
certificate or by a uniform mathematical argument.
-/

namespace FourColor.D3009RepairGeometry

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open D3009Construction Hypermap KempeBoundarySplit

abbrev SourceRepair :=
  Repairs (GraphTrace D3009Wheel.input.graph D3009Wheel.input.boundary) 13

theorem ring_length : (cfring config).length = 13 := by
  change (cfmap config).cpring.reverse.length = 13
  rw [List.length_reverse]
  have h := congrArg List.length realization.ring
  rw [List.length_map, D3009Construction.cpring] at h
  exact h

theorem construction_repair (repair : SourceRepair) :
    Repairs ((cfmap config).map.RingTrace (cfring config).reverse) 13 := by
  intro et hlen hzero hsum outside closed initial
  obtain ⟨es, inside, compatible⟩ := repair et hlen hzero hsum outside closed initial
  exact ⟨es, (ringTrace_iff es).mpr inside, compatible⟩

theorem reducible (repair : SourceRepair) {cc : List (cfmap config).Dart}
    (valid : (cfmap config).map.ValidContract (cfring config) cc) :
    (cfmap config).map.CReducible (cfring config) cc := by
  apply KempeRepairContract.reducible_of_repair embeddable.base.base.base.cycle valid
  rw [ring_length]
  exact construction_repair repair

/-- The edge joining the degree-seven centre to the degree-five rim vertex. -/
def contractDart : (cfmap config).Dart := realization.numbering.symm 69

theorem contract_endpoints :
    (vertex (realization.numbering contractDart),
      vertex (realization.numbering ((cfmap config).map.edge contractDart))) = (13, 14) := by
  rw [D3009Preembedding.numbered_edge]
  simp only [contractDart, Equiv.apply_symm_apply]
  decide +kernel

theorem valid_contract :
    (cfmap config).map.ValidContract (cfring config) [contractDart] := by
  apply KempeRepairContract.valid_singleton
  · intro h
    have hm := List.mem_map_of_mem (f := realization.numbering) h
    rw [D3009Preembedding.numbered_ring] at hm
    have hn : (69 : Fin 94) ∉ ring.reverse := by decide +kernel
    exact hn (by simpa [contractDart] using hm)
  · intro h
    have hm := List.mem_map_of_mem (f := realization.numbering) h
    rw [D3009Preembedding.numbered_ring, D3009Preembedding.numbered_edge] at hm
    have hn : table.map.edge (69 : Fin 94) ∉ ring.reverse := by decide +kernel
    exact hn (by simpa [contractDart] using hm)
  · intro h
    have hn : ¬ table.map.CNode (69 : Fin 94) (table.map.edge 69) := by decide +kernel
    apply hn
    have ht := (Hypermap.sameCycle_relabel realization.numbering
      (cfmap config).map.node contractDart ((cfmap config).map.edge contractDart)).mpr h
    change ((cfmap config).map.relabel realization.numbering).CNode
      (realization.numbering contractDart)
      (realization.numbering ((cfmap config).map.edge contractDart)) at ht
    rw [realization.map_eq, D3009Preembedding.numbered_edge] at ht
    simpa [contractDart] using ht

theorem singleton_reducible (repair : SourceRepair) :
    (cfmap config).map.CReducible (cfring config) [contractDart] :=
  reducible repair valid_contract

noncomputable section

open GoertzelV24TwoEdgeCutMinimality
open MinimalExceptionalEmbedding (graph rotation)
open D3009Boundary (Occurrence)

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- The occurrence, contract and repaired colouring retain one disk reading.
The repair contract is the only remaining local input. -/
theorem colorable (repair : SourceRepair) (r : Occurrence (rotation original minimal)) :
    (DualGraphQuery.map (rotation original minimal)).FourColorable := by
  classical
  let h := D3009Preembedding.reading r
  let M := DualGraphQuery.map (rotation original minimal)
  obtain ⟨k, initial⟩ := ActualDualContract.singleton_colorable original minimal
    (embed (cfmap config).map M (cfring config) h contractDart)
  exact InjectiveEmbeddedRepair.colorable embeddable
    (ActualDualLocalGeometry.planar original minimal) (DualGraphQuery.plain _)
    (DualGraphQuery.cubic _ (MinimalExceptionalEmbedding.triangular original minimal))
    (D3009Preembedding.preembedding r (MinimalExceptionalEmbedding.cyclic original minimal))
    (D3009Preembedding.disk_injective r (MinimalExceptionalEmbedding.cyclic original minimal)
      (MinimalExceptionalEmbedding.triangular original minimal))
    (singleton_reducible repair) initial

theorem not_in_minimal (repair : SourceRepair)
    (r : Occurrence (rotation original minimal)) : False :=
  ActualDualContract.not_colorable original minimal (colorable original minimal repair r)

/-- The degree profile supplies all occurrence and embedding hypotheses.
The boundary repair is still required for the contradiction. -/
theorem profile_excluded (repair : SourceRepair) (d : (graph original minimal).Dart)
    (seven : (graph original minimal).degree d.fst = 7)
    (five : (graph original minimal).degree d.snd = 5)
    (six : ∀ w, (graph original minimal).Adj d.fst w → w ≠ d.snd →
      (graph original minimal).degree w = 6) : False :=
  not_in_minimal original minimal repair
    (ActualWheelOccurrence.occurrence original minimal d seven five six)

open RuleFanSupply ExtraChargeReduction CyclicCharge CyclicFanContinuation ExactCyclicCharge

/-- The exact flat residual yields a further high-degree neighbour once the
wheel's complete repair contract is supplied. -/
theorem residual_high_neighbor (repair : SourceRepair) (d : (graph original minimal).Dart)
    (fixed : Fixed (rotation original minimal) d)
    (seven : (graph original minimal).degree (firstFree (rotation original minimal) d) = 7)
    (flat : NearLinearCharge.finalCharge (rotation original minimal)
      (firstFree (rotation original minimal) d) = 0) :
    ∃ w, w ≠ d.snd ∧ w ≠ firstFree (rotation original minimal) d ∧
      (graph original minimal).Adj (firstFree (rotation original minimal) d) w ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 3 ∧
      7 ≤ (graph original minimal).degree w := by
  rcases ActualWheelOccurrence.residual_occurrence original minimal d fixed seven flat with
    high | ⟨r, _⟩
  · exact high
  · exact False.elim (not_in_minimal original minimal repair r)

end
end FourColor.D3009RepairGeometry
