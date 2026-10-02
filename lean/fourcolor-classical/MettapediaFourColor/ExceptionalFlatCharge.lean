import MettapediaFourColor.NearLinearCharge
import MettapediaFourColor.ExceptionalLocalRepair

/-!
# Charge pruning in the actual exceptional-coverage domain

The degree-five-free branch is excluded by the complete pinned discharging
rules. Classification can therefore restrict to centres with an actual
degree-five witness in radius two. The surviving classification remains
an explicit input. The second centre and joint exceptional closing law
are supplied by the already established actual-map repair.
-/

namespace FourColor.ExceptionalFlatCharge

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality LocalCoverageAssembly ExceptionalOverlap
open NearLinearCharge

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

local instance : (MinimalExceptionalEmbedding.graph original minimal).LocallyFinite :=
  fun _ => Fintype.ofFinite _

/-- The zero predicate now refers to the actual oriented-rule charge,
and the omitted five-free branch is proved impossible. -/
theorem overlap_supply {R : Type*}
    (support : R → Set (GoertzelV24FaceOrbitIncidence.OrbitFace original.toRotationSystem))
    (valid : R → Prop)
    (classify : ∀ c, (MinimalExceptionalEmbedding.graph original minimal).degree c = 8 →
      OnBall (MinimalExceptionalEmbedding.graph original minimal) c 1
        (fun v => finalCharge (MinimalExceptionalEmbedding.rotation original minimal) v = 0) →
      OnBall (MinimalExceptionalEmbedding.graph original minimal) c 3
        (fun v => (MinimalExceptionalEmbedding.graph original minimal).degree v ≤ 8) →
      (∃ w ∈ closedBall (MinimalExceptionalEmbedding.graph original minimal) c 2,
        (MinimalExceptionalEmbedding.graph original minimal).degree w = 5) →
      Occurs (MinimalExceptionalEmbedding.graph original minimal) support valid c 3 ∨
      Nonempty (Centered (MinimalExceptionalEmbedding.rotation original minimal) c)) :
    EightOverlapSupply (MinimalExceptionalEmbedding.graph original minimal)
      support valid
      (fun v => finalCharge (MinimalExceptionalEmbedding.rotation original minimal) v = 0)
      (Centered (MinimalExceptionalEmbedding.rotation original minimal))
      (Mate (rotation := MinimalExceptionalEmbedding.rotation original minimal)) := by
  apply ExceptionalLocalRepair.overlap_supply original minimal support valid
  intro c hd hz hb
  apply classify c hd hz hb
  obtain ⟨w, hw, hw5⟩ := flat_has_five (MinimalExceptionalEmbedding.rotation original minimal)
    (lt_of_lt_of_eq
      (show 6 < (MinimalExceptionalEmbedding.graph original minimal).degree c by omega)
      (SimpleGraph.degree_instance_independent c _ _)) (hz c (centre_mem _ _ _))
  exact ⟨w, hw, (SimpleGraph.degree_instance_independent w _ _).trans hw5⟩

/-- In particular, every adjacent flat eight-eight branch carries an exact
external charge bill, before any independent cartwheel bounds are applied. -/
theorem adjacent_eight_budget
    (u v : GoertzelV24FaceOrbitIncidence.OrbitFace original.toRotationSystem)
    (h : (MinimalExceptionalEmbedding.graph original minimal).Adj u v)
    (hu : (MinimalExceptionalEmbedding.graph original minimal).degree u = 8)
    (hv : (MinimalExceptionalEmbedding.graph original minimal).degree v = 8)
    (hzu : finalCharge (MinimalExceptionalEmbedding.rotation original minimal) u = 0)
    (hzv : finalCharge (MinimalExceptionalEmbedding.rotation original minimal) v = 0) :
    pairBoundary (MinimalExceptionalEmbedding.rotation original minimal) u v = 40 :=
  flat_eight_pair_budget _ h.ne
    ((SimpleGraph.degree_instance_independent u _ _).trans hu)
    ((SimpleGraph.degree_instance_independent v _ _).trans hv) hzu hzv

end
end FourColor.ExceptionalFlatCharge
