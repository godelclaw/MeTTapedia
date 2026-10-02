import MettapediaFourColor.TwoFiveWheelPreembedding
import MettapediaFourColor.TwoFiveWheelRepair
import MettapediaFourColor.D3009RepairGeometry
import MettapediaFourColor.SecondFanWheelOccurrence

/-!
# Strict ambient reconstruction for every second-five position

The same complete source repair descends to each twelve-port wheel. Its
recognised occurrence supplies an injective disk and the centre-to-marked-five
singleton contract. Vertex minimality supplies the initial witness by strict
two-vertex descent; compatible repair reconstructs an ambient colouring.
The full D3009 repair remains an explicit input, shared by all six positions.
-/

namespace FourColor.TwoFiveWheelRepairGeometry

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open TwoFiveWheelConstruction Hypermap KempeBoundarySplit

set_option maxRecDepth 32768

variable (p : Fin 6)

theorem ring_length : (cfring (config p)).length = 12 := by
  change (cfmap (config p)).cpring.reverse.length = 12
  rw [List.length_reverse]
  have h := congrArg List.length (realization p).ring
  rw [List.length_map, TwoFiveWheelConstruction.cpring] at h
  have size : (ring p).length = 12 := by clear h; revert p; decide +kernel
  exact h.trans size

theorem construction_repair (repair : D3009RepairGeometry.SourceRepair) :
    Repairs ((cfmap (config p)).map.RingTrace (cfring (config p)).reverse) 12 := by
  intro et hlen hzero hsum outside closed initial
  obtain ⟨es, inside, compatible⟩ := TwoFiveWheelRepair.transfer repair p
    et hlen hzero hsum outside closed initial
  exact ⟨es, (ringTrace_iff p es).mpr inside, compatible⟩

theorem reducible (repair : D3009RepairGeometry.SourceRepair)
    {cc : List (cfmap (config p)).Dart}
    (valid : (cfmap (config p)).map.ValidContract (cfring (config p)) cc) :
    (cfmap (config p)).map.CReducible (cfring (config p)) cc := by
  apply KempeRepairContract.reducible_of_repair (embeddable p).base.base.base.cycle valid
  rw [ring_length]
  exact construction_repair p repair

/-- Every source uses the same labelled centre-to-first-five dart. -/
def contractDart : (cfmap (config p)).Dart := (realization p).numbering.symm 65

theorem contract_endpoints :
    (vertex p ((realization p).numbering (contractDart p)),
      vertex p ((realization p).numbering ((cfmap (config p)).map.edge (contractDart p)))) =
        (12, 13) := by
  rw [TwoFiveWheelPreembedding.numbered_edge]
  simp only [contractDart, Equiv.apply_symm_apply]
  revert p; decide +kernel

theorem valid_contract :
    (cfmap (config p)).map.ValidContract (cfring (config p)) [contractDart p] := by
  apply KempeRepairContract.valid_singleton
  · intro h
    have hm := List.mem_map_of_mem (f := (realization p).numbering) h
    rw [TwoFiveWheelPreembedding.numbered_ring] at hm
    have hn : (65 : Fin 90) ∉ (ring p).reverse := by clear h hm; revert p; decide +kernel
    exact hn (by simpa [contractDart] using hm)
  · intro h
    have hm := List.mem_map_of_mem (f := (realization p).numbering) h
    rw [TwoFiveWheelPreembedding.numbered_ring, TwoFiveWheelPreembedding.numbered_edge] at hm
    have hn : (table p).map.edge (65 : Fin 90) ∉ (ring p).reverse := by
      clear h hm; revert p; decide +kernel
    exact hn (by simpa [contractDart] using hm)
  · intro h
    have hn : ¬ (table p).map.CNode (65 : Fin 90) ((table p).map.edge 65) := by
      clear h; revert p; decide +kernel
    apply hn
    have ht := (Hypermap.sameCycle_relabel (realization p).numbering
      (cfmap (config p)).map.node (contractDart p)
        ((cfmap (config p)).map.edge (contractDart p))).mpr h
    change ((cfmap (config p)).map.relabel (realization p).numbering).CNode
      ((realization p).numbering (contractDart p))
      ((realization p).numbering ((cfmap (config p)).map.edge (contractDart p))) at ht
    rw [(realization p).map_eq, TwoFiveWheelPreembedding.numbered_edge] at ht
    simpa [contractDart] using ht

theorem singleton_reducible (repair : D3009RepairGeometry.SourceRepair) :
    (cfmap (config p)).map.CReducible (cfring (config p)) [contractDart p] :=
  reducible p repair (valid_contract p)

noncomputable section

open GoertzelV24TwoEdgeCutMinimality
open MinimalExceptionalEmbedding (graph rotation)

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- Occurrence, initial contract witness and reconstructed colouring belong
 to the same actual ambient map. No exterior augmentation is introduced. -/
theorem colorable (repair : D3009RepairGeometry.SourceRepair)
    (r : WheelBoundaryCompletion.Occurrence (WheelBoundaryLayouts.twoFive p)
      (rotation original minimal)) :
    (DualGraphQuery.map (rotation original minimal)).FourColorable := by
  classical
  let h := TwoFiveWheelPreembedding.reading p r
  let M := DualGraphQuery.map (rotation original minimal)
  obtain ⟨k, initial⟩ := ActualDualContract.singleton_colorable original minimal
    (embed (cfmap (config p)).map M (cfring (config p)) h (contractDart p))
  exact InjectiveEmbeddedRepair.colorable (embeddable p)
    (ActualDualLocalGeometry.planar original minimal) (DualGraphQuery.plain _)
    (DualGraphQuery.cubic _ (MinimalExceptionalEmbedding.triangular original minimal))
    (TwoFiveWheelPreembedding.preembedding p r (MinimalExceptionalEmbedding.cyclic original minimal))
    (TwoFiveWheelPreembedding.disk_injective p r (MinimalExceptionalEmbedding.cyclic original minimal)
      (MinimalExceptionalEmbedding.triangular original minimal))
    (singleton_reducible p repair) initial

theorem not_in_minimal (repair : D3009RepairGeometry.SourceRepair)
    (r : WheelBoundaryCompletion.Occurrence (WheelBoundaryLayouts.twoFive p)
      (rotation original minimal)) : False :=
  ActualDualContract.not_colorable original minimal (colorable p original minimal repair r)

omit p in
/-- The supplied degree profile reconstructs through whichever of the six
positions contains the same actual second five. -/
theorem profile_excluded (repair : D3009RepairGeometry.SourceRepair)
    (d : (graph original minimal).Dart)
    (seven : (graph original minimal).degree d.fst = 7)
    (five : (graph original minimal).degree d.snd = 5)
    (q : _) (adj : (graph original minimal).Adj d.fst q)
    (other_five : (graph original minimal).degree q = 5) (distinct : q ≠ d.snd)
    (six : ∀ w, (graph original minimal).Adj d.fst w → w ≠ d.snd → w ≠ q →
      (graph original minimal).degree w = 6) : False := by
  obtain ⟨p,r,_,_,_⟩ := TwoFiveWheelOccurrence.supplied original minimal
    d seven five q adj other_five distinct six
  exact not_in_minimal p original minimal repair r

open RuleFanSupply CyclicCharge CyclicFanContinuation ExactCyclicCharge

omit p in
/-- Both wheel outcomes of the second-fan classifier are excluded by the
single source repair. Its remaining outcome is an actual new high neighbour. -/
theorem second_high_neighbor (repair : D3009RepairGeometry.SourceRepair)
    (d : (graph original minimal).Dart)
    (fixed : Fixed (rotation original minimal) d)
    (seven : (graph original minimal).degree (secondFree (rotation original minimal) d) = 7)
    (flat : NearLinearCharge.finalCharge (rotation original minimal)
      (secondFree (rotation original minimal) d) = 0) :
    ∃ w, w ≠ d.snd ∧ w ≠ secondFree (rotation original minimal) d ∧
      (graph original minimal).Adj (secondFree (rotation original minimal) d) w ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 3 ∧
      7 ≤ (graph original minimal).degree w := by
  rcases SecondFanWheelOccurrence.alternatives original minimal d fixed seven flat with
    high | ⟨r,_,_⟩ | ⟨p,r,_⟩
  · exact high
  · exact False.elim (D3009RepairGeometry.not_in_minimal original minimal repair r)
  · exact False.elim (not_in_minimal p original minimal repair r)

end
end FourColor.TwoFiveWheelRepairGeometry
