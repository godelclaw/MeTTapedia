import MettapediaFourColor.RuleFanCharge

/-!
# A cyclic budget from shared triangles

At a high-degree receiver whose neighbours have degrees five or six, the
first five oriented source rules give a uniform bound. Each five-valent
neighbour contributes four units after summing around the receiver, and
each five-valent outer triangular tip contributes two. Cyclic reindexing
preserves the actual shared vertices; oriented rules are counted once.
-/

namespace FourColor.CyclicCharge

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearCharge NearLinearRuleData ExceptionalOverlap ExceptionalCoreOrientation
open RuleFanCharge RulePairBudget RulePairCharge
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] [G.LocallyFinite] (rotation : Data G)

abbrev Star (v : V) := {d : G.Dart // d.fst = v}

/-- Outgoing darts and actual neighbours carry the same finite data. -/
def neighborEquiv (v : V) : Star (G := G) v ≃ G.neighborSet v where
  toFun d := ⟨d.val.snd, by
    change G.Adj v d.val.snd
    simpa only [d.property] using d.val.adj⟩
  invFun w := ⟨⟨(v,w.val),w.property⟩,rfl⟩
  left_inv d := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    exact Prod.ext d.property.symm rfl
  right_inv _ := rfl

instance starFintype (v : V) : Fintype (Star (G := G) v) :=
  Fintype.ofEquiv (G.neighborSet v) (neighborEquiv (G := G) v).symm

def step (v : V) : Equiv.Perm (Star (G := G) v) :=
  rotation.vertexRotation.symm.subtypeEquiv (fun d => by rw [prev_fst])

def tip {v : V} (d : Star (G := G) v) : V :=
  (rotation.vertexRotation (rotation.vertexRotation d.val.symm)).snd

def five (v : V) : ℤ := if G.degree v = 5 then 1 else 0

omit [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
theorem step_snd (tri : Triangular rotation) {v : V} (d : Star (G := G) v) :
    (step rotation v d).val.snd = (rotation.vertexRotation d.val.symm).snd :=
  FacialStarCompletion.across_edge rotation tri d.val

omit [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
theorem star_snd_injective (v : V) :
    Function.Injective (fun d : Star (G := G) v => d.val.snd) := by
  intro a b eq
  apply Subtype.ext
  apply SimpleGraph.Dart.ext
  exact Prod.ext (a.property.trans b.property.symm) eq

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Both rule orientations are built from the same outer triangle. -/
theorem tip_rules (tri : Triangular rotation) (v : V)
    (low : ∀ w, G.Adj v w → 5 ≤ G.degree w ∧ G.degree w ≤ 6)
    (high : 7 ≤ G.degree v) (d : Star (G := G) v)
    (h : G.degree (tip rotation d) = 5) :
    Applies rotation 4 d.val.snd v ∧ Applies rotation 3 (step rotation v d).val.snd v := by
  classical
  have hd : G.Adj v d.val.snd := by simpa only [d.property] using d.val.adj
  have hs : G.Adj v (step rotation v d).val.snd :=
    by simpa only [(step rotation v d).property] using (step rotation v d).val.adj
  have c0 : Corner rotation d.val.snd d.val.fst
      (rotation.vertexRotation d.val.symm).snd := walk_corner d.val.symm 0
  have c1 : Corner rotation d.val.snd (rotation.vertexRotation d.val.symm).snd
      (tip rotation d) := walk_corner d.val.symm 1
  have a := face_checks tri c0 c1 (low _ hd) (by rw [d.property]; omega)
    (by rw [← step_snd rotation tri]; exact low _ hs) h
  rwa [d.property, ← step_snd rotation tri] at a

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Per-edge accounting uses five distinct rule identifiers. -/
theorem edge_lower (tri : Triangular rotation) (v : V)
    (low : ∀ w, G.Adj v w → 5 ≤ G.degree w ∧ G.degree w ≤ 6)
    (high : 7 ≤ G.degree v) (d : Star (G := G) v) :
    2 * five (G := G) d.val.snd + five (G := G) (step rotation v d).val.snd +
      five (G := G) ((step rotation v).symm d).val.snd + five (G := G) (tip rotation d) +
      five (G := G) (tip rotation ((step rotation v).symm d)) ≤ sent rotation d.val.snd v := by
  classical
  have hd : G.Adj v d.val.snd := by simpa only [d.property] using d.val.adj
  have zero (h : G.degree d.val.snd = 5) : Applies rotation 0 d.val.snd v :=
    (RuleMatcher.check_iff rotation ⟨(d.val.snd,v),hd.symm⟩).mp
      (zero_of_five _ h (by change 5 ≤ G.degree v; omega))
  have one (h : G.degree (step rotation v d).val.snd = 5) :
      Applies rotation 1 d.val.snd v := by
    have c0 : Corner rotation d.val.snd d.val.fst
        (rotation.vertexRotation d.val.symm).snd := walk_corner d.val.symm 0
    let x := ofFace tri c0 (low _ hd)
      (by rw [d.property]; exact high) (by rwa [← step_snd rotation tri])
    exact ⟨x, rfl, d.property⟩
  have two (h : G.degree ((step rotation v).symm d).val.snd = 5) :
      Applies rotation 2 d.val.snd v := by
    let p := rotation.vertexRotation.symm d.val.symm
    have corner : Corner rotation d.val.snd p.snd d.val.fst := by
      change Corner rotation d.val.symm.fst p.snd d.val.symm.snd
      simpa only [ChainFanRecognition.walk, Nat.zero_add, pow_zero, pow_one, Equiv.Perm.one_apply,
        p, prev_fst, Equiv.apply_symm_apply] using (walk_corner (rotation := rotation) p 0)
    have same : p.snd = ((step rotation v).symm d).val.snd := by
      change (rotation.vertexRotation.symm d.val.symm).snd = (rotation.vertexRotation d.val).snd
      rw [FacialStarCompletion.across_edge rotation tri, SimpleGraph.Dart.symm_symm]
    let x := ofReverseFace tri corner (low _ hd) (by rw [d.property]; exact high)
      (by rwa [same])
    exact ⟨x, rfl, d.property⟩
  have four (h : G.degree (tip rotation d) = 5) :=
    (tip_rules rotation tri v low high d h).1
  have three (h : G.degree (tip rotation ((step rotation v).symm d)) = 5) :
      Applies rotation 3 d.val.snd v := by
    simpa only [Equiv.apply_symm_apply] using
      (tip_rules rotation tri v low high ((step rotation v).symm d) h).2
  let w : Fin 84 → ℤ := fun r =>
    (if r = 0 then 2 * five (G := G) d.val.snd else 0) +
    (if r = 1 then five (G := G) (step rotation v d).val.snd else 0) +
    (if r = 2 then five (G := G) ((step rotation v).symm d).val.snd else 0) +
    (if r = 3 then five (G := G) (tip rotation ((step rotation v).symm d)) else 0) +
    (if r = 4 then five (G := G) (tip rotation d) else 0)
  have bound (r : Fin 84) : w r ≤
      if Applies rotation r d.val.snd v then (amount r : ℤ) else 0 := by
    by_cases r0 : r = 0
    · subst r
      have ha : amount 0 = 2 := by decide +kernel
      by_cases h : G.degree d.val.snd = 5
      · simp [w, five, h, zero h, ha]
      · simp [w, five, h, ha]
        split <;> norm_num
    by_cases r1 : r = 1
    · subst r
      have ha : amount 1 = 1 := by decide +kernel
      by_cases h : G.degree (step rotation v d).val.snd = 5
      · simp [w, five, h, one h, ha]
      · simp [w, five, h, ha]
        split <;> norm_num
    by_cases r2 : r = 2
    · subst r
      have ha : amount 2 = 1 := by decide +kernel
      by_cases h : G.degree ((step rotation v).symm d).val.snd = 5
      · simp [w, five, h, two h, ha]
      · simp [w, five, h, ha]
        split <;> norm_num
    by_cases r3 : r = 3
    · subst r
      have ha : amount 3 = 1 := by decide +kernel
      by_cases h : G.degree (tip rotation ((step rotation v).symm d)) = 5
      · simp [w, five, h, three h, ha]
      · simp [w, five, h, ha]
        split <;> norm_num
    by_cases r4 : r = 4
    · subst r
      have ha : amount 4 = 1 := by decide +kernel
      by_cases h : G.degree (tip rotation d) = 5
      · simp [w, five, h, four h, ha]
      · simp [w, five, h, ha]
        split <;> norm_num
    · simp only [w, r0, r1, r2, r3, r4, ite_false, add_zero]
      split <;> positivity
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun r _ => bound r)
  have eq : (∑ r : Fin 84, w r) =
      2 * five (G := G) d.val.snd + five (G := G) (step rotation v d).val.snd +
      five (G := G) ((step rotation v).symm d).val.snd +
      five (G := G) (tip rotation d) +
      five (G := G) (tip rotation ((step rotation v).symm d)) := by
    simp only [w, Finset.sum_add_distrib]
    simp
    ring
  rw [eq] at sum
  exact sum

variable [Fintype V]

/-- Count degree-five neighbours, using each actual outgoing dart once. -/
def fiveCount (v : V) : ℤ := ∑ d : Star (G := G) v, five (G := G) d.val.snd

/-- Count receiver wedges whose opposite facial tip has degree five.
Different wedges may share a tip; their oriented rule-edge pairs differ. -/
def tipCount (v : V) : ℤ := ∑ d : Star (G := G) v, five (G := G) (tip rotation d)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The five source rules combine uniformly at every receiver degree. -/
theorem lower (tri : Triangular rotation) (v : V)
    (high : 7 ≤ G.degree v)
    (low : ∀ w, G.Adj v w → 5 ≤ G.degree w ∧ G.degree w ≤ 6) :
    10 * (6 - (G.degree v : ℤ)) + 4 * fiveCount (G := G) v +
      2 * tipCount rotation v ≤ finalCharge rotation v := by
  classical
  have zero (w : V) : sent rotation v w = 0 := by
    by_cases hw : G.Adj v w
    · exact high_to_low_zero high (low w hw).2
    · exact sent_eq_zero_of_not_adj rotation hw
  have nonneg (w : V) : 0 ≤ net rotation w v := by
    simpa only [net, zero, sub_zero] using sent_nonneg rotation w v
  have localBound (d : Star (G := G) v) := edge_lower rotation tri v low high d
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun d _ => localBound d)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum] at bound
  have forward := Equiv.sum_comp (step rotation v) (fun d => five (G := G) d.val.snd)
  have backward := Equiv.sum_comp (step rotation v).symm (fun d => five (G := G) d.val.snd)
  have tips := Equiv.sum_comp (step rotation v).symm (fun d => five (G := G) (tip rotation d))
  rw [forward, backward, tips] at bound
  have injective := star_snd_injective (G := G) v
  have same : (∑ w ∈ Finset.univ.image (fun d : Star (G := G) v => d.val.snd),
      net rotation w v) = ∑ d : Star (G := G) v, net rotation d.val.snd v :=
    Finset.sum_image (fun a _ b _ h => injective h)
  have total := Finset.sum_le_univ_sum_of_nonneg
    (s := Finset.univ.image (fun d : Star (G := G) v => d.val.snd))
    (f := fun w => net rotation w v) nonneg
  rw [same] at total
  simp only [net, zero, sub_zero] at total
  unfold finalCharge fiveCount tipCount
  simp only [net, zero, sub_zero]
  linarith

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Flat low-neighbourhoods have a joint budget for fives and outer tips. -/
theorem flat_budget (tri : Triangular rotation) (v : V)
    (high : 7 ≤ G.degree v)
    (low : ∀ w, G.Adj v w → 5 ≤ G.degree w ∧ G.degree w ≤ 6)
    (flat : finalCharge rotation v = 0) :
    2 * fiveCount (G := G) v + tipCount rotation v ≤ 5 * ((G.degree v : ℤ) - 6) := by
  have h := lower rotation tri v high low
  rw [flat] at h
  omega

end FourColor.CyclicCharge
