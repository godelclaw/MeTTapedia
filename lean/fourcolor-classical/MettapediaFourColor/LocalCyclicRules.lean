import MettapediaFourColor.ExtraChargeReduction

/-!
# Source-rule semantics at a single low-neighbour edge

The first five rules retain the exact low-degree guards at both ends of
each facial wedge. These local equivalences support both the complete
low-neighbour cyclic formula and its version with high neighbours.
-/

namespace FourColor.LocalCyclicRules

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge CyclicCharge CyclicFanContinuation
open RuleFanCharge RulePairBudget RulePairCharge ExceptionalCoreOrientation ExceptionalOverlap
open scoped BigOperators

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] [G.LocallyFinite] (rotation : Data G)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Both source orientations use the same low-low wedge and outer tip. -/
theorem local_tip_rules (tri : Triangular rotation) (v : V)
    (high : 7 ≤ G.degree v) (d : Star (G := G) v)
    (low : 5 ≤ G.degree d.val.snd ∧ G.degree d.val.snd ≤ 6)
    (other : 5 ≤ G.degree (step rotation v d).val.snd ∧
      G.degree (step rotation v d).val.snd ≤ 6)
    (h : G.degree (tip rotation d) = 5) :
    Applies rotation 4 d.val.snd v ∧ Applies rotation 3 (step rotation v d).val.snd v := by
  classical
  have c0 : Corner rotation d.val.snd d.val.fst
      (rotation.vertexRotation d.val.symm).snd := walk_corner d.val.symm 0
  have c1 : Corner rotation d.val.snd (rotation.vertexRotation d.val.symm).snd
      (tip rotation d) := walk_corner d.val.symm 1
  have a := face_checks tri c0 c1 low (by rw [d.property]; omega)
    (by rw [← step_snd rotation tri]; exact other) h
  rwa [d.property, ← step_snd rotation tri] at a

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The first five rules at one low sender, with adjacent degree guards retained. -/
theorem basic_iff (tri : Triangular rotation) (v : V)
    (high : 7 ≤ G.degree v) (d : Star (G := G) v)
    (low : 5 ≤ G.degree d.val.snd ∧ G.degree d.val.snd ≤ 6) :
    (Applies rotation 0 d.val.snd v ↔ G.degree d.val.snd = 5) ∧
    (Applies rotation 1 d.val.snd v ↔ G.degree (step rotation v d).val.snd = 5) ∧
    (Applies rotation 2 d.val.snd v ↔ G.degree ((step rotation v).symm d).val.snd = 5) ∧
    (Applies rotation 3 d.val.snd v ↔
      (5 ≤ G.degree ((step rotation v).symm d).val.snd ∧
        G.degree ((step rotation v).symm d).val.snd ≤ 6) ∧
      G.degree (tip rotation ((step rotation v).symm d)) = 5) ∧
    (Applies rotation 4 d.val.snd v ↔
      (5 ≤ G.degree (step rotation v d).val.snd ∧
        G.degree (step rotation v d).val.snd ≤ 6) ∧ G.degree (tip rotation d) = 5) := by
  classical
  have hd : G.Adj v d.val.snd := by simpa only [d.property] using d.val.adj
  have rooted {r : Fin 84} (x : Occurrence rotation r) (hs : sender r = 0)
      (ht : receiver r = 1) (xs : x.vertex (sender r) = d.val.snd)
      (xt : x.vertex (receiver r) = v) (edge : (graph r).Adj 0 1) :
      (⟨(x.vertex 0,x.vertex 1),x.edge 0 1 edge⟩ : G.Dart) = d.val.symm := by
    rw [hs] at xs
    rw [ht] at xt
    apply SimpleGraph.Dart.ext
    exact Prod.ext xs (xt.trans d.property.symm)
  constructor
  · constructor
    · rintro ⟨x,xs,xt⟩
      have h := x.degree 0
      change x.vertex 0 = d.val.snd at xs
      rw [show lower 0 0 = 5 from by decide +kernel,
        show upper 0 0 = 5 from by decide +kernel, xs] at h
      omega
    · intro h
      exact (RuleMatcher.check_iff rotation ⟨(d.val.snd,v),hd.symm⟩).mp
        (zero_of_five _ h (by change 5 ≤ G.degree v; omega))
  constructor
  · constructor
    · rintro ⟨x,xs,xt⟩
      have eq := rooted x (by decide +kernel) (by decide +kernel) xs xt (by decide +kernel)
      have turn := x.turn 0 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      rw [eq] at turn
      have same := congrArg (fun e : G.Dart => e.snd) turn
      rw [← step_snd rotation tri] at same
      have h := x.degree 2
      rw [show lower 1 2 = 5 from by decide +kernel,
        show upper 1 2 = 5 from by decide +kernel] at h
      rw [same]
      change G.degree (x.vertex 2) = 5
      omega
    · intro h
      have c0 : Corner rotation d.val.snd d.val.fst
          (rotation.vertexRotation d.val.symm).snd := walk_corner d.val.symm 0
      let x := ofFace tri c0 low (by rw [d.property]; exact high)
        (by rwa [← step_snd rotation tri])
      exact ⟨x,rfl,d.property⟩
  constructor
  · constructor
    · rintro ⟨x,xs,xt⟩
      have eq := rooted x (by decide +kernel) (by decide +kernel) xs xt (by decide +kernel)
      have turn := x.turn 0 2 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      rw [eq] at turn
      have same := congrArg (fun e : G.Dart => (rotation.vertexRotation.symm e).snd) turn
      rw [Equiv.symm_apply_apply] at same
      have h := x.degree 2
      rw [show lower 2 2 = 5 from by decide +kernel,
        show upper 2 2 = 5 from by decide +kernel] at h
      change G.degree (rotation.vertexRotation d.val).snd = 5
      rw [FacialStarCompletion.across_edge rotation tri, SimpleGraph.Dart.symm_symm] at same
      rw [← same]
      change G.degree (x.vertex 2) = 5
      omega
    · intro h
      let p := rotation.vertexRotation.symm d.val.symm
      have corner : Corner rotation d.val.snd p.snd d.val.fst := by
        change Corner rotation d.val.symm.fst p.snd d.val.symm.snd
        simpa only [ChainFanRecognition.walk, Nat.zero_add, pow_zero, pow_one,
          Equiv.Perm.one_apply, p, prev_fst, Equiv.apply_symm_apply] using
          (walk_corner (rotation := rotation) p 0)
      have same : p.snd = ((step rotation v).symm d).val.snd := by
        change (rotation.vertexRotation.symm d.val.symm).snd = (rotation.vertexRotation d.val).snd
        rw [FacialStarCompletion.across_edge rotation tri, SimpleGraph.Dart.symm_symm]
      exact ⟨ofReverseFace tri corner low (by rw [d.property]; exact high)
        (by rwa [same]),rfl,d.property⟩
  constructor
  · constructor
    · rintro ⟨x,xs,xt⟩
      have eq := rooted x (by decide +kernel) (by decide +kernel) xs xt (by decide +kernel)
      have first := x.turn 0 2 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      have second := x.turn 0 3 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      rw [eq] at first
      have back := congrArg rotation.vertexRotation.symm first
      rw [Equiv.symm_apply_apply] at back
      have back2 := congrArg rotation.vertexRotation.symm second
      rw [Equiv.symm_apply_apply, back] at back2
      have other := x.degree 2
      change 5 ≤ G.degree (x.vertex 2) ∧ (6 = 0 ∨ G.degree (x.vertex 2) ≤ 6) at other
      have same : ((step rotation v).symm d).val.snd = x.vertex 2 := by
        have h := congrArg (fun e : G.Dart => e.snd) back
        change (rotation.vertexRotation d.val).snd = x.vertex 2
        rw [FacialStarCompletion.across_edge rotation tri, SimpleGraph.Dart.symm_symm] at h
        exact h.symm
      refine ⟨by rw [same]; omega, ?_⟩
      rw [tip_reverse rotation tri, ← back2]
      have h := x.degree 3
      rw [show lower 3 3 = 5 from by decide +kernel,
        show upper 3 3 = 5 from by decide +kernel] at h
      change G.degree (x.vertex 3) = 5
      omega
    · rintro ⟨other,h⟩
      simpa only [Equiv.apply_symm_apply] using
        (local_tip_rules rotation tri v high ((step rotation v).symm d) other
          (by rw [(step rotation v).apply_symm_apply]; exact low) h).2
  · constructor
    · rintro ⟨x,xs,xt⟩
      have eq := rooted x (by decide +kernel) (by decide +kernel) xs xt (by decide +kernel)
      have first := x.turn 0 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      have second := x.turn 0 2 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      rw [eq] at first
      have other := x.degree 2
      change 5 ≤ G.degree (x.vertex 2) ∧ (6 = 0 ∨ G.degree (x.vertex 2) ≤ 6) at other
      have same := congrArg (fun e : G.Dart => e.snd) first
      rw [← step_snd rotation tri] at same
      refine ⟨?_, ?_⟩
      · rw [same]
        change 5 ≤ G.degree (x.vertex 2) ∧ G.degree (x.vertex 2) ≤ 6
        omega
      unfold tip
      rw [first,second]
      have h := x.degree 3
      rw [show lower 4 3 = 5 from by decide +kernel,
        show upper 4 3 = 5 from by decide +kernel] at h
      change G.degree (x.vertex 3) = 5
      omega
    · exact fun h => (local_tip_rules rotation tri v high d low h.1 h.2).1


end FourColor.LocalCyclicRules
