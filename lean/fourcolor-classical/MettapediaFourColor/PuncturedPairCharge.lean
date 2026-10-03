import MettapediaFourColor.PuncturedCyclicCharge
import MettapediaFourColor.JointTripodRuleSupply

/-! Exact low-neighbour elimination applied to the retained flat-seven pair.
The common high edge remains one signed exchange. Its two directions must
cancel together when the two views are composed. -/

namespace FourColor.PuncturedPairCharge

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality RuleFanSevenCluster NearLinearCharge
open MinimalExceptionalEmbedding (graph rotation)

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- Every actual dual neighbour has the required degree floor. -/
theorem neighbor_lower (v w : GoertzelV24FaceOrbitIncidence.OrbitFace original.toRotationSystem)
    (adj : (graph original minimal).Adj v w) : 5 ≤ (graph original minimal).degree w :=
  ActualRuleFanSupply.degree_five original minimal ⟨(w,v),adj.symm⟩

/-- In a 5-6-6-5 consecutive rim segment at a seven, the outer tip
between the sixes cannot be five. The three source matches are constructed
from the shared cyclic geometry, then excluded by actual tripod repair. -/
theorem tip_ne_five
    {v : GoertzelV24FaceOrbitIncidence.OrbitFace original.toRotationSystem}
    (d : CyclicCharge.Star (G := graph original minimal) v)
    (seven : (graph original minimal).degree v = 7)
    (six : (graph original minimal).degree d.val.snd = 6)
    (other_six : (graph original minimal).degree
      ((CyclicCharge.step (rotation original minimal) v).symm d).val.snd = 6)
    (left_five : (graph original minimal).degree
      (CyclicCharge.step (rotation original minimal) v d).val.snd = 5)
    (right_five : (graph original minimal).degree
      ((CyclicCharge.step (rotation original minimal) v).symm
        ((CyclicCharge.step (rotation original minimal) v).symm d)).val.snd = 5) :
    (graph original minimal).degree
      (CyclicCharge.tip (rotation original minimal)
        ((CyclicCharge.step (rotation original minimal) v).symm d)) ≠ 5 := by
  intro tip_five
  let r := rotation original minimal
  let prev := (CyclicCharge.step r v).symm d
  have low : 5 ≤ (graph original minimal).degree d.val.snd ∧
      (graph original minimal).degree d.val.snd ≤ 6 := by omega
  have other_six' : (graph original minimal).degree prev.val.snd = 6 := other_six
  have other : 5 ≤ (graph original minimal).degree prev.val.snd ∧
      (graph original minimal).degree prev.val.snd ≤ 6 := by rw [other_six']; decide
  have a := LocalCyclicRules.basic_iff r
    (MinimalExceptionalEmbedding.triangular original minimal) v
    (by change 7 ≤ (graph original minimal).degree v; rw [seven]) d low
  have b := LocalCyclicRules.basic_iff r
    (MinimalExceptionalEmbedding.triangular original minimal) v
    (by change 7 ≤ (graph original minimal).degree v; rw [seven]) prev other
  have checked (i : Fin 84) (e : CyclicCharge.Star (G := graph original minimal) v)
      (h : Applies r i e.val.snd v) : RuleMatcher.check r i e.val.symm = true := by
    apply (RuleMatcher.check_iff r e.val.symm).mpr
    change Applies r i e.val.snd e.val.fst
    rwa [e.property]
  have left := checked 1 d (a.2.1.mpr left_five)
  have cap := checked 3 d (a.2.2.2.1.mpr ⟨other,tip_five⟩)
  have right := checked 2 prev (b.2.2.1.mpr right_five)
  apply ActualJointTripodRuleSupply.not_checks original minimal d.val.symm six
    (by change (graph original minimal).degree d.val.fst = 7; rwa [d.property])
    ?_ left cap ?_
  · exact other_six
  · exact right

/-- The original pair retains the exact high-edge transfer in its first-centre budget. -/
theorem first_budget {d : (graph original minimal).Dart}
    (p : Pair original minimal d) (unique : Unique p) :
    PuncturedCyclicCharge.lowBudget (rotation original minimal) p.first +
      net (rotation original minimal) p.second p.first = 10 :=
  PuncturedCyclicCharge.flat_unique_seven (rotation original minimal)
    (MinimalExceptionalEmbedding.triangular original minimal) p.first p.second
    p.first_degree p.adjacent (by rw [p.second_degree])
    (neighbor_lower original minimal p.first) unique p.first_flat

/-- The second centre keeps all other high neighbours as actual signed inputs. -/
theorem second_budget {d : (graph original minimal).Dart}
    (p : Pair original minimal d) :
    PuncturedCyclicCharge.lowBudget (rotation original minimal) p.second +
      PuncturedCyclicCharge.highBoundary (rotation original minimal) p.second = 10 := by
  have h := PuncturedCyclicCharge.exact_charge (rotation original minimal)
    (MinimalExceptionalEmbedding.triangular original minimal) p.second
    (by rw [p.second_degree]) (neighbor_lower original minimal p.second)
  rw [p.second_flat, p.second_degree] at h
  norm_num at h
  omega

/-- When the high edge is isolated at both ends, it cancels exactly.
No independent maxima of its two directions are used. -/
theorem isolated_pair_budget {d : (graph original minimal).Dart}
    (p : Pair original minimal d) (unique : Unique p)
    (other_unique : ∀ w, (graph original minimal).Adj p.second w → w ≠ p.first →
      (graph original minimal).degree w ≤ 6) :
    PuncturedCyclicCharge.lowBudget (rotation original minimal) p.first +
      PuncturedCyclicCharge.lowBudget (rotation original minimal) p.second = 20 := by
  have first := first_budget original minimal p unique
  have second := second_budget original minimal p
  rw [PuncturedCyclicCharge.unique_boundary (rotation original minimal)
    p.second p.first p.adjacent.symm (by rw [p.first_degree]) other_unique] at second
  have cancel := net_reverse (rotation original minimal) p.first p.second
  omega

end
end FourColor.PuncturedPairCharge
