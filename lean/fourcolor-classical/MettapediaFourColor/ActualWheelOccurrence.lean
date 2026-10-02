import MettapediaFourColor.D3009Boundary
import MettapediaFourColor.ExceptionalCoreInduced
import MettapediaFourColor.ExactFanResidual

/-!
# The exact residual supplies an actual D3009 wheel

Short-cycle laws of the same minimal facial dual discharge all collision
hypotheses of the wheel construction. The shared-fan residual now supplies
the complete twenty-one-vertex source occurrence, including its thirteen
distinct ordered boundary ports. Colouring repair and strict reduction are
separate obligations; the source catalogue is not used as a proof of them.
-/

namespace FourColor.ActualWheelOccurrence

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality
open MinimalExceptionalEmbedding (graph rotation)
open D3009Boundary (Occurrence)
open RuleFanSupply ExtraChargeReduction CyclicCharge CyclicFanContinuation ExactCyclicCharge
open ChainFanRecognition (walk)

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- Construct the source occurrence from the degree profile alone. -/
def occurrence (d : (graph original minimal).Dart)
    (seven : (graph original minimal).degree d.fst = 7)
    (five : (graph original minimal).degree d.snd = 5)
    (six : ∀ w, (graph original minimal).Adj d.fst w → w ≠ d.snd →
      (graph original minimal).degree w = 6) : Occurrence (rotation original minimal) := by
  let tri := MinimalExceptionalEmbedding.triangular original minimal
  let cyc := MinimalExceptionalEmbedding.cyclic original minimal
  let r := D3009Wheel.reading (rotation original minimal) d tri cyc seven five six
  have inj : Function.Injective r.map := D3009Wheel.injective _ d cyc seven
  have reflect : ∀ i j, (graph original minimal).Adj (r.map i) (r.map j) →
      D3009Wheel.core.Adj i j := by
    intro i j h
    exact (D3009Wheel.edge_iff _ d tri cyc seven
      (fun _ _ _ => MinimalExceptionalEmbedding.triangle_facial original minimal) i j).mp h
  refine {
    hom := D3009Boundary.hom r tri cyc
    degree_eq := ?_
    turn := D3009Boundary.full_turn r tri cyc
    injective := D3009Boundary.vertex_injective r tri cyc inj reflect
      (fun _ _ _ => MinimalExceptionalEmbedding.triangle_facial original minimal)
      (fun _ _ _ _ => ExceptionalCoreInduced.four_cycle_chord original minimal)
    near := D3009Boundary.vertex_near r }
  intro i
  change (graph original minimal).degree (D3009Boundary.vertex r (i.natAdd 13)) = _
  rw [D3009Boundary.vertex_core, r.degree_eq]

theorem center (d : (graph original minimal).Dart)
    (seven : (graph original minimal).degree d.fst = 7)
    (five : (graph original minimal).degree d.snd = 5)
    (six : ∀ w, (graph original minimal).Adj d.fst w → w ≠ d.snd →
      (graph original minimal).degree w = 6) :
    (occurrence original minimal d seven five six).hom 13 = d.fst := rfl

theorem marked_neighbor (d : (graph original minimal).Dart)
    (seven : (graph original minimal).degree d.fst = 7)
    (five : (graph original minimal).degree d.snd = 5)
    (six : ∀ w, (graph original minimal).Adj d.fst w → w ≠ d.snd →
      (graph original minimal).degree w = 6) :
    (occurrence original minimal d seven five six).hom 14 = d.snd := rfl

/-- The retained charge alternatives and the source occurrence use the same
centre and the same marked neighbour. No new profile is chosen independently. -/
theorem residual_occurrence (d : (graph original minimal).Dart)
    (fixed : Fixed (rotation original minimal) d)
    (seven : (graph original minimal).degree (firstFree (rotation original minimal) d) = 7)
    (flat : NearLinearCharge.finalCharge (rotation original minimal)
      (firstFree (rotation original minimal) d) = 0) :
    (∃ w, w ≠ d.snd ∧ w ≠ firstFree (rotation original minimal) d ∧
      (graph original minimal).Adj (firstFree (rotation original minimal) d) w ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 3 ∧
      7 ≤ (graph original minimal).degree w) ∨
    ∃ o : Occurrence (rotation original minimal),
      o.hom 13 = firstFree (rotation original minimal) d ∧
      o.hom 14 = (walk (rotation original minimal) d 2).snd ∧
      RuleMatcher.check (rotation original minimal) 5
        (fanRoot (rotation original minimal)
          (MinimalExceptionalEmbedding.triangular original minimal) d) = false ∧
      ((tipCount (rotation original minimal) (o.hom 13) = 2 ∧
        residualCount (rotation original minimal) (o.hom 13) = 2) ∨
       (tipCount (rotation original minimal) (o.hom 13) = 3 ∧
        residualCount (rotation original minimal) (o.hom 13) = 0)) := by
  rcases ExactFanResidual.alternatives original minimal d fixed seven flat with
    high | ⟨six,no,budget⟩
  · exact Or.inl high
  · let e := (fanRoot (rotation original minimal)
      (MinimalExceptionalEmbedding.triangular original minimal) d).symm
    let o := occurrence original minimal e seven fixed.second six
    exact Or.inr ⟨o,rfl,rfl,no,budget⟩

end
end FourColor.ActualWheelOccurrence
