import MettapediaFourColor.FourTriangleCompletedOccurrence
import MettapediaFourColor.RuleFanSevenCluster

/-!
# Joint closing information at either free side of a shared fan

When the two free neighbours of the six-star have degrees seven and six,
a five-valent outer seam tip completes the four-face tripod D0052. The same
construction covers both positions of the seven. In an actual minimal map,
repair excludes that tip degree. If the seven has a unique high neighbour,
the tip is six or is literally that same high neighbour.

Thus the two local views retain a shared vertex constraint. No classification
of every flat pair, or universal coverage, is assumed.
-/

namespace FourColor.FourTriangleFaces

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open FourTriangleCore ExceptionalCoreOrientation ExceptionalOverlap

/-- Every source core edge is read in one of the four retained faces. -/
theorem edge_in_face : ∀ (s : Fin 2) (i j : Fin 6), (core s).Adj i j →
    ∃ k : Fin 4,
      (i = first s k ∧ j = second s k) ∨ (i = second s k ∧ j = first s k) ∨
      (i = second s k ∧ j = third s k) ∨ (i = third s k ∧ j = second s k) ∨
      (i = third s k ∧ j = first s k) ∨ (i = first s k ∧ j = third s k) := by
  decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}
  (s : Fin 2) (tri : Triangular rotation) (f : Fin 6 → V)
  (faces : ∀ k : Fin 4, Corner rotation (f (first s k)) (f (second s k)) (f (third s k)))

/-- Shared facial witnesses supply the core edges; no separate graph map is assumed. -/
def reading : Reading s rotation where
  map := {
    toFun := f
    map_rel' := by
      intro i j h
      obtain ⟨k, h⟩ := edge_in_face s i j h
      have a := (faces k).choose
      have b := (Corner.rotate rotation tri (faces k)).choose
      have c := (Corner.rotate rotation tri (Corner.rotate rotation tri (faces k))).choose
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact a
      · exact a.symm
      · exact b
      · exact b.symm
      · exact c
      · exact c.symm }
  face := faces

end FourColor.FourTriangleFaces

namespace FourColor.RuleFanTripodSupply

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open RuleFanSupply ExceptionalCoreOrientation ExceptionalOverlap
open ChainFanRecognition (walk walk_fst walk_next)

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  (rotation : Data G) (tri : Triangular rotation) (d : G.Dart)

/-- The outer face across the edge joining the two free neighbours. -/
def seam : G.Dart :=
  ⟨(secondFree rotation d, firstFree rotation d), by
    have h := consecutive_adjacent rotation tri (walk rotation d 3)
    rw [walk_next] at h
    exact h.symm⟩

def tip : V := (rotation.vertexRotation (seam rotation tri d)).snd

def vertices : Fin 2 → Fin 6 → V :=
  ![![(walk rotation d 5).snd, d.fst, secondFree rotation d,
      firstFree rotation d, tip rotation tri d, (walk rotation d 2).snd],
    ![(walk rotation d 2).snd, firstFree rotation d, d.fst,
      secondFree rotation d, (walk rotation d 5).snd, tip rotation tri d]]

/-- The two placements use the same four actual faces, with different labels. -/
def reading (side : Fin 2) : FourTriangleCore.Reading 1 rotation := by
  apply FourTriangleFaces.reading 1 tri (vertices rotation tri d side)
  intro k
  have a := RuleFanCharge.walk_corner (rotation := rotation) d 3
  have b := RuleFanCharge.walk_corner (rotation := rotation) d 4
  have c := RuleFanCharge.walk_corner (rotation := rotation) (seam rotation tri d) 0
  have e := RuleFanCharge.walk_corner (rotation := rotation) d 2
  have ea := Corner.rotate rotation tri (Corner.rotate rotation tri e)
  have aa := Corner.rotate rotation tri a
  fin_cases side <;> fin_cases k
  · exact a
  · exact b
  · exact c
  · exact ea
  · exact aa
  · exact ea
  · exact b
  · exact c

def freeDegree : Fin 2 → Fin 2 → ℕ := ![![7,6], ![6,7]]

theorem degree_word : FourTriangleCore.degree 1 = ![5,6,6,7,5,5] := by decide +kernel

/-- The retained six-star and one seam degree provide the entire degree profile. -/
theorem degrees (side : Fin 2) (fixed : Fixed rotation d)
    (ha : G.degree (firstFree rotation d) = freeDegree side 0)
    (hb : G.degree (secondFree rotation d) = freeDegree side 1)
    (ht : G.degree (tip rotation tri d) = 5) :
    ∀ i, G.degree ((reading rotation tri d side).map i) = FourTriangleCore.degree 1 i := by
  intro i
  change G.degree (vertices rotation tri d side i) = FourTriangleCore.degree 1 i
  rw [degree_word]
  fin_cases side <;> fin_cases i
  · exact fixed.last
  · exact fixed.center
  · exact hb
  · exact ha
  · exact ht
  · exact fixed.second
  · exact fixed.second
  · exact ha
  · exact fixed.center
  · exact hb
  · exact fixed.last
  · exact ht

/-- Both centres see the very same seam tip as a neighbour. -/
theorem tip_adjacent : G.Adj (firstFree rotation d) (tip rotation tri d) ∧
    G.Adj (secondFree rotation d) (tip rotation tri d) := by
  have h := RuleFanCharge.walk_corner (rotation := rotation) (seam rotation tri d) 0
  exact ⟨(Corner.rotate rotation tri h).choose, h.choose_spec.choose⟩

end FourColor.RuleFanTripodSupply

namespace FourColor.ActualRuleFanTripodSupply

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality RuleFanSupply RuleFanTripodSupply
open MinimalExceptionalEmbedding (graph rotation)

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

abbrev outerTip (d : (graph original minimal).Dart) :=
  tip (rotation original minimal) (MinimalExceptionalEmbedding.triangular original minimal) d

/-- A five at this exact seam supplies a complete tripod reduction on either side. -/
theorem not_five (d : (graph original minimal).Dart) (side : Fin 2)
    (fixed : Fixed (rotation original minimal) d)
    (ha : (graph original minimal).degree (firstFree (rotation original minimal) d) =
      freeDegree side 0)
    (hb : (graph original minimal).degree (secondFree (rotation original minimal) d) =
      freeDegree side 1)
    (ht : (graph original minimal).degree (outerTip original minimal d) = 5) : False := by
  let r := rotation original minimal
  let tri := MinimalExceptionalEmbedding.triangular original minimal
  exact ActualFourTrianglePatch.not_in_minimal original minimal 1
    (reading r tri d side) (degrees r tri d side fixed ha hb ht)

/-- The common boundary's seam observation becomes a necessary degree bound. -/
theorem tip_lower (d : (graph original minimal).Dart) (side : Fin 2)
    (fixed : Fixed (rotation original minimal) d)
    (ha : (graph original minimal).degree (firstFree (rotation original minimal) d) =
      freeDegree side 0)
    (hb : (graph original minimal).degree (secondFree (rotation original minimal) d) =
      freeDegree side 1) :
    6 ≤ (graph original minimal).degree (outerTip original minimal d) := by
  have lower := ActualRuleFanSupply.degree_five original minimal
    ((rotation original minimal).vertexRotation
      (seam (rotation original minimal)
        (MinimalExceptionalEmbedding.triangular original minimal) d)).symm
  change 5 ≤ (graph original minimal).degree (outerTip original minimal d) at lower
  by_contra h
  exact not_five original minimal d side fixed ha hb (by omega)

/-- At a unique-high-neighbour pair, a high seam tip is that same second
centre. Independent choices of a second high vertex are not permitted. -/
theorem unique_tip {d : (graph original minimal).Dart}
    (p : RuleFanSevenCluster.Pair original minimal d) (unique : RuleFanSevenCluster.Unique p)
    (side : Fin 2) (fixed : Fixed (rotation original minimal) d)
    (picked : p.first = ![firstFree (rotation original minimal) d,
      secondFree (rotation original minimal) d] side)
    (ha : (graph original minimal).degree (firstFree (rotation original minimal) d) =
      freeDegree side 0)
    (hb : (graph original minimal).degree (secondFree (rotation original minimal) d) =
      freeDegree side 1) :
    (graph original minimal).degree (outerTip original minimal d) = 6 ∨
      outerTip original minimal d = p.second := by
  have lower := tip_lower original minimal d side fixed ha hb
  by_cases eq : outerTip original minimal d = p.second
  · exact Or.inr eq
  have adj := tip_adjacent (rotation original minimal)
    (MinimalExceptionalEmbedding.triangular original minimal) d
  have atFirst : (graph original minimal).Adj p.first (outerTip original minimal d) := by
    rw [picked]
    fin_cases side
    · exact adj.1
    · exact adj.2
  have upper := unique _ atFirst eq
  exact Or.inl (by omega)

/-- The existing pair supplies its choice of side. Only the degree of the
other free position is needed to apply the joint closing law. -/
theorem unique_tip_of_other_six {d : (graph original minimal).Dart}
    (p : RuleFanSevenCluster.Pair original minimal d) (unique : RuleFanSevenCluster.Unique p)
    (fixed : Fixed (rotation original minimal) d)
    (other : ∀ side : Fin 2,
      p.first = ![firstFree (rotation original minimal) d,
        secondFree (rotation original minimal) d] side →
      (graph original minimal).degree (![secondFree (rotation original minimal) d,
        firstFree (rotation original minimal) d] side) = 6) :
    (graph original minimal).degree (outerTip original minimal d) = 6 ∨
      outerTip original minimal d = p.second := by
  rcases p.picked with a | b
  · exact unique_tip original minimal p unique 0 fixed a
      (a ▸ p.first_degree) (other 0 a)
  · exact unique_tip original minimal p unique 1 fixed b
      (other 1 b) (b ▸ p.first_degree)

/-- The new seam observation is in the existing pair's observation envelope.
It is not a new independently chosen centre or a larger-radius hypothesis. -/
theorem tip_support {d : (graph original minimal).Dart}
    (p : RuleFanSevenCluster.Pair original minimal d) :
    outerTip original minimal d ≠ d.snd ∧
      outerTip original minimal d ∈
        LocalCoverageAssembly.closedBall (graph original minimal) p.first 1 ∧
      outerTip original minimal d ∈
        LocalCoverageAssembly.closedBall (graph original minimal) d.snd 3 := by
  have adj := tip_adjacent (rotation original minimal)
    (MinimalExceptionalEmbedding.triangular original minimal) d
  have atFirst : (graph original minimal).Adj p.first (outerTip original minimal d) := by
    rcases p.picked with a | b
    · exact a ▸ adj.1
    · exact b ▸ adj.2
  have near : outerTip original minimal d ∈
      LocalCoverageAssembly.closedBall (graph original minimal) p.first 1 :=
    (show (graph original minimal).Walk p.first (outerTip original minimal d) from
      .cons atFirst .nil).edist_le
  refine ⟨?_, near, LocalCoverageAssembly.ball_recenter _ p.first_near near⟩
  intro same
  exact p.first_nonadjacent (same ▸ atFirst.symm)

end
end FourColor.ActualRuleFanTripodSupply
