import MettapediaFourColor.TwoFiveWheelRepairGeometry
import MettapediaFourColor.ActualRuleFanSupply

/-!
# A surviving shared fan supplies a joint seven-valent view

The wheel repair and the three small fan reductions force an adjacent pair
of flat degree-seven centres. The pair retains its actual place in the
original fan. Its first centre either has a unique high neighbour, belongs
to an induced three-centre path, or belongs to a facial seven-triangle.

These are the geometric inputs to the joint classifications in Lemmas 8.5
and 8.6 of Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen and Thorup,
arXiv:2603.24880v1. Those classifications are not assumed to be proved here.
The entire radius-two views lie within radius five of the original receiver.
-/

namespace FourColor.RuleFanSevenCluster

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24FaceOrbitIncidence
open MinimalExceptionalEmbedding (graph rotation)
open RuleFanSupply LocalCoverageAssembly ExceptionalOverlap

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- One adjacent pair, retaining the original fan position and both flatness
observations. Its second vertex is not the original receiver. -/
structure Pair (d : (graph original minimal).Dart) where
  first : OrbitFace original.toRotationSystem
  second : OrbitFace original.toRotationSystem
  picked : first = firstFree (rotation original minimal) d ∨
    first = secondFree (rotation original minimal) d
  first_other : first ≠ d.snd
  first_nonadjacent : ¬ (graph original minimal).Adj d.snd first
  second_other : second ≠ d.snd
  adjacent : (graph original minimal).Adj first second
  first_degree : (graph original minimal).degree first = 7
  second_degree : (graph original minimal).degree second = 7
  first_flat : NearLinearCharge.finalCharge (rotation original minimal) first = 0
  second_flat : NearLinearCharge.finalCharge (rotation original minimal) second = 0
  first_near : first ∈ closedBall (graph original minimal) d.snd 2
  second_near : second ∈ closedBall (graph original minimal) d.snd 3

/-- The same full wheel repair discharges either choice of high free vertex.
No independent choice of exterior colourings is made for the two centres. -/
theorem pair_exists (repair : D3009RepairGeometry.SourceRepair)
    (d : (graph original minimal).Dart)
    (fixed : Fixed (rotation original minimal) d)
    (flat : OnBall (graph original minimal) d.snd 3
      (fun v => NearLinearCharge.finalCharge (rotation original minimal) v = 0))
    (bound : OnBall (graph original minimal) d.snd 3
      (fun v => (graph original minimal).degree v ≤ 7)) :
    Nonempty (Pair original minimal d) := by
  let r := rotation original minimal
  have nearA := walk_near r d 3
  have nearB := walk_near r d 4
  have nearA3 := ball_mono (graph original minimal) (by decide : 2 ≤ 3) nearA
  have nearB3 := ball_mono (graph original minimal) (by decide : 2 ≤ 3) nearB
  have other := walk_ne_receiver r (MinimalExceptionalEmbedding.cyclic original minimal)
    d fixed.center
  by_cases highA : 7 ≤ (graph original minimal).degree (firstFree r d)
  · have seven : (graph original minimal).degree (firstFree r d) = 7 :=
      Nat.le_antisymm (bound _ nearA3) highA
    obtain ⟨w, hw, _, adj, near, high⟩ :=
      D3009RepairGeometry.residual_high_neighbor original minimal repair d fixed seven
        (flat _ nearA3)
    exact ⟨{ first := firstFree r d
             second := w
             picked := Or.inl rfl
             first_other := other 3 (by decide) (by decide)
             first_nonadjacent := ActualSecondFanResidual.star_nonadjacent original minimal
               d fixed.center 3 (by decide) (by decide)
             second_other := hw
             adjacent := adj
             first_degree := seven
             second_degree := Nat.le_antisymm (bound _ near) high
             first_flat := flat _ nearA3
             second_flat := flat _ near
             first_near := nearA
             second_near := near }⟩
  · have highB : 7 ≤ (graph original minimal).degree (secondFree r d) := by
      by_contra h
      exact ActualRuleFanSupply.not_low_fan original minimal d fixed
        (by change (graph original minimal).degree (firstFree r d) ≤ 6; omega)
        (by change (graph original minimal).degree (secondFree r d) ≤ 6; omega)
    have seven : (graph original minimal).degree (secondFree r d) = 7 :=
      Nat.le_antisymm (bound _ nearB3) highB
    obtain ⟨w, hw, _, adj, near, high⟩ :=
      TwoFiveWheelRepairGeometry.second_high_neighbor original minimal repair d fixed seven
        (flat _ nearB3)
    exact ⟨{ first := secondFree r d
             second := w
             picked := Or.inr rfl
             first_other := other 4 (by decide) (by decide)
             first_nonadjacent := ActualSecondFanResidual.star_nonadjacent original minimal
               d fixed.center 4 (by decide) (by decide)
             second_other := hw
             adjacent := adj
             first_degree := seven
             second_degree := Nat.le_antisymm (bound _ near) high
             first_flat := flat _ nearB3
             second_flat := flat _ near
             first_near := nearB
             second_near := near }⟩

variable {original minimal}

/-- All other neighbours of the selected first centre have lower degree. -/
def Unique {d : (graph original minimal).Dart} (p : Pair original minimal d) : Prop :=
  ∀ v, (graph original minimal).Adj p.first v → v ≠ p.second →
    (graph original minimal).degree v ≤ 6

/-- The third centre is an actual vertex, with its own retained observations.
It is distinct from both ends of the existing edge. -/
structure Third {d : (graph original minimal).Dart} (p : Pair original minimal d) where
  vertex : OrbitFace original.toRotationSystem
  adjacent : (graph original minimal).Adj p.first vertex
  other : vertex ≠ p.second
  degree : (graph original minimal).degree vertex = 7
  flat : NearLinearCharge.finalCharge (rotation original minimal) vertex = 0
  near : vertex ∈ closedBall (graph original minimal) d.snd 3

theorem third_other_receiver {d : (graph original minimal).Dart}
    (p : Pair original minimal d) (q : Third p) : q.vertex ≠ d.snd := by
  intro h
  exact p.first_nonadjacent (h ▸ q.adjacent.symm)

/-- In the nonadjacent-ends branch these are the three distinct vertices
of the induced path; in the other branch they are the same facial triangle. -/
theorem three_distinct {d : (graph original minimal).Dart}
    (p : Pair original minimal d) (q : Third p) :
    [p.second, p.first, q.vertex].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
  exact ⟨⟨p.adjacent.ne.symm, q.other.symm⟩, q.adjacent.ne⟩

/-- The alternative to a unique neighbour retains both high edges at the
same first centre. Its radius bound is three, not an iterated search bound. -/
theorem unique_or_third {d : (graph original minimal).Dart}
    (p : Pair original minimal d)
    (flat : OnBall (graph original minimal) d.snd 3
      (fun v => NearLinearCharge.finalCharge (rotation original minimal) v = 0))
    (bound : OnBall (graph original minimal) d.snd 3
      (fun v => (graph original minimal).degree v ≤ 7)) :
    Unique p ∨ Nonempty (Third p) := by
  by_cases h : Unique p
  · exact Or.inl h
  · obtain ⟨v, adj, ne, high⟩ : ∃ v, (graph original minimal).Adj p.first v ∧
        v ≠ p.second ∧ ¬ (graph original minimal).degree v ≤ 6 := by
      simpa only [Unique, not_forall, not_imp, exists_prop] using h
    have step : v ∈ closedBall (graph original minimal) p.first 1 := by
      exact (show (graph original minimal).Walk p.first v from .cons adj .nil).edist_le
    have near : v ∈ closedBall (graph original minimal) d.snd 3 :=
      ball_recenter (graph original minimal) p.first_near step
    exact Or.inr ⟨⟨v, adj, ne, by have := bound v near; omega, flat v near, near⟩⟩

/-- If the two outer centres are adjacent, the same actual triangle is
facial. Otherwise they give an induced path of length two. -/
theorem path_or_triangle {d : (graph original minimal).Dart}
    (p : Pair original minimal d) (q : Third p) :
    (¬ (graph original minimal).Adj p.second q.vertex) ∨
      (ExceptionalCoreOrientation.Corner (rotation original minimal)
          p.first p.second q.vertex ∨
       ExceptionalCoreOrientation.Corner (rotation original minimal)
          p.first q.vertex p.second) := by
  by_cases h : (graph original minimal).Adj p.second q.vertex
  · exact Or.inr (MinimalExceptionalEmbedding.triangle_facial original minimal
      p.adjacent h q.adjacent.symm)
  · exact Or.inl h

/-- The full pair of radius-two views keeps the same vertices and lies
within radius five of the original receiver. -/
theorem pair_support {d : (graph original minimal).Dart} (p : Pair original minimal d) :
    closedBall (graph original minimal) p.first 2 ∪
      closedBall (graph original minimal) p.second 2 ⊆
        closedBall (graph original minimal) d.snd 5 := by
  intro v hv
  rcases hv with h | h
  · exact ball_mono _ (by decide : 4 ≤ 5) (ball_recenter _ p.first_near h)
  · exact ball_recenter _ p.second_near h

/-- The third view does not enlarge the radius-five observation envelope. -/
theorem triple_support {d : (graph original minimal).Dart}
    (p : Pair original minimal d) (q : Third p) :
    closedBall (graph original minimal) p.first 2 ∪
      closedBall (graph original minimal) p.second 2 ∪
      closedBall (graph original minimal) q.vertex 2 ⊆
        closedBall (graph original minimal) d.snd 5 := by
  intro v hv
  rcases hv with h | h
  · exact pair_support p h
  · exact ball_recenter _ q.near h

variable (original minimal)

/-- Joint local classifications can consume the actual pair or triple.
The result keeps the exact occurrence and all its observations when it is
recentered at the original receiver. The three closing laws remain explicit
mathematical obligations; this theorem does not establish them. -/
theorem occurs_of_joint_laws {W : Type*}
    (support : W → Set (OrbitFace original.toRotationSystem)) (valid : W → Prop)
    (repair : D3009RepairGeometry.SourceRepair)
    (d : (graph original minimal).Dart)
    (fixed : Fixed (rotation original minimal) d)
    (flat : OnBall (graph original minimal) d.snd 3
      (fun v => NearLinearCharge.finalCharge (rotation original minimal) v = 0))
    (bound : OnBall (graph original minimal) d.snd 5
      (fun v => (graph original minimal).degree v ≤ 7))
    (close_pair : ∀ p : Pair original minimal d, Unique p →
      ∃ w, valid w ∧ support w ⊆
        closedBall (graph original minimal) p.first 2 ∪
        closedBall (graph original minimal) p.second 2)
    (close_path : ∀ (p : Pair original minimal d) (q : Third p),
      ¬ (graph original minimal).Adj p.second q.vertex →
      ∃ w, valid w ∧ support w ⊆
        closedBall (graph original minimal) p.first 2 ∪
        closedBall (graph original minimal) p.second 2 ∪
        closedBall (graph original minimal) q.vertex 2)
    (close_triangle : ∀ (p : Pair original minimal d) (q : Third p),
      (ExceptionalCoreOrientation.Corner (rotation original minimal)
          p.first p.second q.vertex ∨
       ExceptionalCoreOrientation.Corner (rotation original minimal)
          p.first q.vertex p.second) →
      ∃ w, valid w ∧ support w ⊆
        closedBall (graph original minimal) p.first 2 ∪
        closedBall (graph original minimal) p.second 2 ∪
        closedBall (graph original minimal) q.vertex 2) :
    Occurs (graph original minimal) support valid d.snd 5 := by
  obtain ⟨p⟩ := pair_exists original minimal repair d fixed flat (bound.mono (by decide))
  rcases unique_or_third p flat (bound.mono (by decide)) with unique | more
  · obtain ⟨w, hw, hs⟩ := close_pair p unique
    exact ⟨w, hw, hs.trans (pair_support p)⟩
  · obtain ⟨q⟩ := more
    rcases path_or_triangle p q with path | triangle
    · obtain ⟨w, hw, hs⟩ := close_path p q path
      exact ⟨w, hw, hs.trans (triple_support p q)⟩
    · obtain ⟨w, hw, hs⟩ := close_triangle p q triangle
      exact ⟨w, hw, hs.trans (triple_support p q)⟩

end
end FourColor.RuleFanSevenCluster
