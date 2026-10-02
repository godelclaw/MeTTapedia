import MettapediaFourColor.CyclicCharge
import MettapediaFourColor.ActualRuleFanCharge

/-!
# The remaining low-neighbour branch of a shared fan

The cyclic charge law counts the two outer tips retained by the original
same-root fan. At a flat seven-valent first free vertex, either a high
neighbour is present or there is at most one five-valent neighbour. The
degree-eight case obeys the same law with a different initial deficit.
-/

namespace FourColor.CyclicFanContinuation

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalOverlap ExceptionalCoreOrientation NearLinearCharge
open RuleFanSupply RuleFanCharge CyclicCharge
open ChainFanRecognition (walk walk_fst walk_next)
open scoped BigOperators

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (rotation : Data G)

omit [G.LocallyFinite] in
/-- The other reading of an outer triangle retains the identical tip. -/
theorem tip_reverse (tri : Triangular rotation) {v : V} (d : Star (G := G) v) :
    tip rotation ((step rotation v).symm d) =
      (rotation.vertexRotation.symm (rotation.vertexRotation.symm d.val.symm)).snd := by
  have h := congrArg (fun e : G.Dart => e.fst) (tri d.val.symm)
  simp only [SimpleGraph.Dart.symm_symm, rotation.vertexRotation_fst] at h
  change (rotation.vertexRotation (rotation.vertexRotation d.val).symm).snd = d.val.snd at h
  have eq : rotation.vertexRotation (rotation.vertexRotation d.val).symm =
      (rotation.vertexRotation.symm d.val.symm).symm := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · change (rotation.vertexRotation (rotation.vertexRotation d.val).symm).fst =
        (rotation.vertexRotation.symm d.val.symm).snd
      rw [rotation.vertexRotation_fst,
        FacialStarCompletion.across_edge rotation tri, SimpleGraph.Dart.symm_symm]
      rfl
    · change (rotation.vertexRotation (rotation.vertexRotation d.val).symm).snd =
        (rotation.vertexRotation.symm d.val.symm).fst
      rw [prev_fst]
      exact h
  change (rotation.vertexRotation
    (rotation.vertexRotation (rotation.vertexRotation d.val).symm)).snd = _
  rw [eq, ← FacialStarCompletion.across_edge rotation tri]

theorem five_nonneg (v : V) : 0 ≤ five (G := G) v := by
  unfold five
  split <;> norm_num

/-- Two marked, distinct wedges contribute twice even if their outer tips coincide. -/
theorem two_tips (v : V) (a b : Star (G := G) v) (ne : a ≠ b)
    (ha : G.degree (tip rotation a) = 5) (hb : G.degree (tip rotation b) = 5) :
    2 ≤ tipCount rotation v := by
  classical
  have h := Finset.sum_le_univ_sum_of_nonneg (s := {a,b})
    (f := fun d : Star (G := G) v => five (G := G) (tip rotation d))
    (fun d => five_nonneg _)
  simpa [tipCount, Finset.sum_pair ne, five, ha, hb] using h

/-- Both outer tips come from the single retained sender star. -/
theorem fan_tips (tri : Triangular rotation) (d : G.Dart) (fixed : Fixed rotation d) :
    2 ≤ tipCount rotation (firstFree rotation d) := by
  classical
  let e := walk rotation d 3
  let a : Star (G := G) e.snd := ⟨e.symm, rfl⟩
  let b := (step rotation e.snd).symm a
  have pred (n : ℕ) : rotation.vertexRotation.symm (walk rotation d (n+1)) =
      walk rotation d n := by rw [← walk_next, Equiv.symm_apply_apply]
  have bdegree : G.degree b.val.snd = 5 := by
    change G.degree (rotation.vertexRotation e.symm).snd = 5
    rw [← FacialStarCompletion.across_edge rotation tri]
    change G.degree (rotation.vertexRotation.symm (walk rotation d 3)).snd = 5
    rw [pred]
    exact fixed.second
  apply two_tips rotation e.snd a b
  · intro eq
    have hh := congrArg (fun x : Star (G := G) e.snd => G.degree x.val.snd) eq
    have ha : G.degree a.val.snd = 6 := by
      change G.degree (walk rotation d 3).fst = 6
      rw [walk_fst]
      exact fixed.center
    omega
  · change G.degree (rotation.vertexRotation (rotation.vertexRotation (walk rotation d 3))).snd = 5
    rw [walk_next, walk_next]
    exact fixed.last
  · rw [tip_reverse rotation tri]
    change G.degree (rotation.vertexRotation.symm
      (rotation.vertexRotation.symm (walk rotation d 3))).snd = 5
    rw [pred, pred]
    exact fixed.first

variable [Fintype V]

/-- This closes the charge accounting for all low-neighbour continuations,
including the formerly unhandled second-free degree-six branch. -/
theorem seven_bound (tri : Triangular rotation) (d : G.Dart) (fixed : Fixed rotation d)
    (seven : G.degree (firstFree rotation d) = 7)
    (low : ∀ w, G.Adj (firstFree rotation d) w → 5 ≤ G.degree w ∧ G.degree w ≤ 6)
    (flat : finalCharge rotation (firstFree rotation d) = 0) :
    fiveCount (G := G) (firstFree rotation d) ≤ 1 := by
  classical
  have ht := fan_tips rotation tri d fixed
  have h := CyclicCharge.flat_budget rotation tri _ (by omega) low flat
  rw [seven] at h
  omega

/-- At degree eight the same two tips leave room for at most four fives.
This is a constraint, not a contradiction or a complete classification. -/
theorem eight_bound (tri : Triangular rotation) (d : G.Dart) (fixed : Fixed rotation d)
    (eight : G.degree (firstFree rotation d) = 8)
    (low : ∀ w, G.Adj (firstFree rotation d) w → 5 ≤ G.degree w ∧ G.degree w ≤ 6)
    (flat : finalCharge rotation (firstFree rotation d) = 0) :
    fiveCount (G := G) (firstFree rotation d) ≤ 4 := by
  classical
  have ht := fan_tips rotation tri d fixed
  have h := CyclicCharge.flat_budget rotation tri _ (by omega) low flat
  rw [eight] at h
  omega

omit [Fintype V] in
/-- A unit neighbour budget retains the identity of its unique five. -/
theorem unique_five (v q : V) (adj : G.Adj v q) (fiveq : G.degree q = 5)
    (budget : fiveCount (G := G) v ≤ 1) :
    ∀ w, G.Adj v w → G.degree w = 5 → w = q := by
  classical
  intro w hw hf
  by_contra ne
  let a : Star (G := G) v := ⟨⟨(v,q),adj⟩,rfl⟩
  let b : Star (G := G) v := ⟨⟨(v,w),hw⟩,rfl⟩
  have ab : a ≠ b := by
    intro eq
    exact ne (congrArg (fun x : Star (G := G) v => x.val.snd) eq).symm
  have h := Finset.sum_le_univ_sum_of_nonneg (s := {a,b})
    (f := fun d : Star (G := G) v => five (G := G) d.val.snd) (fun d => five_nonneg _)
  have htwo : 2 ≤ fiveCount (G := G) v := by
    simpa [fiveCount, Finset.sum_pair ab, a, b, five, fiveq, hf] using h
  omega

end FourColor.CyclicFanContinuation

namespace FourColor.ActualCyclicFanContinuation

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality
open ActualRulePairDiamond (graph rotation)
open RuleFanSupply CyclicCharge CyclicFanContinuation
open ChainFanRecognition (walk walk_fst walk_next)

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- Opposite positions in the same six-valent star cannot have a chord
in the actual minimal map, independently of their degrees. -/
theorem opposite_nonadjacent (d : (graph original minimal).Dart)
    (six : (graph original minimal).degree d.fst = 6) :
    ¬ (graph original minimal).Adj d.snd (firstFree (rotation original minimal) d) := by
  let r := rotation original minimal
  let e := walk r d 3
  have es : e.fst = d.fst := walk_fst _ _ _
  have adjacent : (graph original minimal).Adj d.fst e.snd := by
    simpa only [es] using e.adj
  have other := walk_ne_receiver r (MinimalExceptionalEmbedding.cyclic original minimal) d six
  intro chord
  rcases MinimalExceptionalEmbedding.triangle_facial original minimal d.adj chord adjacent.symm with
    first | second
  · obtain ⟨_, he, turn⟩ := first
    have ee : (⟨(d.fst, firstFree r d), he⟩ : (graph original minimal).Dart) = e := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext es.symm rfl
    rw [ee] at turn
    have eq : r.vertexRotation d = e := turn
    have pred : r.vertexRotation.symm e = walk r d 2 := by
      change r.vertexRotation.symm (walk r d (2+1)) = _
      rw [← walk_next, Equiv.symm_apply_apply]
    have same := congrArg (fun x => (r.vertexRotation.symm x).snd) eq
    rw [Equiv.symm_apply_apply, pred] at same
    exact other 2 (by decide) (by decide) same.symm
  · obtain ⟨he, _, turn⟩ := second
    have ee : (⟨(d.fst, firstFree r d), he⟩ : (graph original minimal).Dart) = e := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext es.symm rfl
    rw [ee] at turn
    have eq : r.vertexRotation e = d := turn
    change r.vertexRotation (walk r d 3) = d at eq
    rw [walk_next] at eq
    exact other 4 (by decide) (by decide) (congrArg (fun x => x.snd) eq)

/-- The unresolved degree-seven branch has an exact residual profile:
unless a third high centre exists, its only five is the shared second
neighbour of the original sender, and all its other neighbours are six.
No degree assumption on the second free position is required. -/
theorem third_or_single_five (d : (graph original minimal).Dart)
    (fixed : Fixed (rotation original minimal) d)
    (seven : (graph original minimal).degree (firstFree (rotation original minimal) d) = 7)
    (flat : NearLinearCharge.finalCharge (rotation original minimal)
      (firstFree (rotation original minimal) d) = 0) :
    (∃ w, w ≠ d.snd ∧ w ≠ firstFree (rotation original minimal) d ∧
      (graph original minimal).Adj (firstFree (rotation original minimal) d) w ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 3 ∧
      7 ≤ (graph original minimal).degree w) ∨
    (∀ w, (graph original minimal).Adj (firstFree (rotation original minimal) d) w →
      w ≠ (walk (rotation original minimal) d 2).snd → (graph original minimal).degree w = 6) := by
  let r := rotation original minimal
  let a := firstFree r d
  let q := (walk r d 2).snd
  have tri := MinimalExceptionalEmbedding.triangular original minimal
  have qa : (graph original minimal).Adj q a := by
    have h := ExceptionalOverlap.consecutive_adjacent r tri (walk r d 2)
    rw [walk_next] at h
    exact h
  by_cases hh : ∃ w, (graph original minimal).Adj a w ∧ 7 ≤ (graph original minimal).degree w
  · obtain ⟨w, hw, high⟩ := hh
    have no := opposite_nonadjacent original minimal d fixed.center
    refine Or.inl ⟨w, ?_, hw.ne.symm, hw, ?_, high⟩
    · intro eq; subst w
      exact no hw.symm
    · have sa : (graph original minimal).Adj d.fst a := by
        simpa only [a, firstFree, walk_fst] using (walk r d 3).adj
      let path : (graph original minimal).Walk d.snd w :=
        .cons d.adj.symm (.cons sa (.cons hw .nil))
      simpa [LocalCoverageAssembly.closedBall, path] using path.edist_le
  · have low (w : _) (hw : (graph original minimal).Adj a w) :
        5 ≤ (graph original minimal).degree w ∧ (graph original minimal).degree w ≤ 6 := by
      have hm := ActualRuleFanSupply.degree_five original minimal ⟨(w,a),hw.symm⟩
      exact ⟨hm, by by_contra hn; exact hh ⟨w, hw, by omega⟩⟩
    have budget := seven_bound r tri d fixed seven low flat
    have uq := unique_five a q qa.symm fixed.second budget
    apply Or.inr
    intro w hw ne
    have h := low w hw
    have hn : (graph original minimal).degree w ≠ 5 := fun he => ne (uq w hw he)
    omega

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

/-- The exact two source-rule matches feed the residual classification. -/
theorem of_checks (d : (graph original minimal).Dart)
    (left : RuleMatcher.check (rotation original minimal) 2 d = true)
    (right : RuleMatcher.check (rotation original minimal) 4 d = true)
    (six : (graph original minimal).degree d.fst = 6)
    (shared : (graph original minimal).degree
      (RuleMatcher.candidate (rotation original minimal) 4 d 2) = 5)
    (seven : (graph original minimal).degree (firstFree (rotation original minimal) d) = 7)
    (flat : NearLinearCharge.finalCharge (rotation original minimal)
      (firstFree (rotation original minimal) d) = 0) :
    (∃ w, w ≠ d.snd ∧ w ≠ firstFree (rotation original minimal) d ∧
      (graph original minimal).Adj (firstFree (rotation original minimal) d) w ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 3 ∧
      7 ≤ (graph original minimal).degree w) ∨
    (∀ w, (graph original minimal).Adj (firstFree (rotation original minimal) d) w →
      w ≠ (walk (rotation original minimal) d 2).snd → (graph original minimal).degree w = 6) := by
  have fixed := fixed_of_checks (rotation original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal) d left right six shared
  exact third_or_single_five original minimal d fixed seven flat

end
end FourColor.ActualCyclicFanContinuation
